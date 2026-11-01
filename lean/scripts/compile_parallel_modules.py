#!/usr/bin/env python3
"""Build Lean modules in dependency order and reuse matching compiled results.

Only ordinary invocations of the pinned Lean compiler produce PASS records.
Existing objects are reused only when a previous PASS binds the current source,
the object, every direct import, and the same compiler/options by SHA256.
Timestamps are never used to decide that a module is up to date.

Example:
  python3 scripts/compile_parallel_modules.py --jobs 4 CodedSorting.Interchange.OneLevel.Allocation

Use --plan-only while restoring sources. Start a build only after the source
tree, pinned toolchain, and external package oleans have all been restored.
No virtual-address-space limit is imposed: Lean reserves a large address range.
"""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import fcntl
import hashlib
import heapq
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 1
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")
    temporary.replace(path)


def local_module(module):
    return module == "CodedSorting" or module.startswith("CodedSorting.")


def relative_module(module, suffix):
    if not MODULE.fullmatch(module):
        raise ValueError("Unsupported module identifier: " + module)
    return Path(*module.split(".")).with_suffix(suffix)


def without_comments(text):
    """Remove nested Lean block comments and line comments, retaining newlines."""
    result, depth, index, quoted = [], 0, 0, False
    while index < len(text):
        pair = text[index:index + 2]
        if not depth and quoted:
            result.append(text[index])
            if text[index] == "\\" and index + 1 < len(text):
                result.append(text[index + 1])
                index += 2
                continue
            if text[index] == '"':
                quoted = False
            index += 1
        elif not depth and text[index] == '"':
            quoted = True
            result.append(text[index])
            index += 1
        elif pair == "/-":
            depth += 1
            result.append("  ")
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            result.append("  ")
            index += 2
        elif not depth and pair == "--":
            end = text.find("\n", index)
            if end < 0:
                break
            result.append("\n")
            index = end + 1
        else:
            char = text[index]
            result.append(char if not depth or char == "\n" else " ")
            index += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(result)


def imports_of(data):
    imports = []
    for line in without_comments(data.decode("utf-8")).splitlines():
        tokens = line.strip().split()
        if not tokens or tokens == ["prelude"]:
            continue
        if tokens[0] != "import":
            break
        for module in tokens[1:]:
            relative_module(module, ".lean")
            if module not in imports:
                imports.append(module)
    return imports


def dependency_graph(targets):
    nodes, pending, state = {}, {}, {}

    def load(module):
        if not local_module(module):
            raise ValueError("Only CodedSorting modules may be targets: " + module)
        source = ROOT / relative_module(module, ".lean")
        if not source.is_file():
            raise FileNotFoundError("Source restoration incomplete: " + str(source))
        data = source.read_bytes()
        imports = imports_of(data)
        return {"source": source, "source_sha256": sha_bytes(data),
                "imports": imports,
                "dependencies": [x for x in imports if local_module(x)]}

    for target in targets:
        if target in nodes:
            continue
        # Iterative DFS also supports generated import chains exceeding
        # Python's recursion limit. Nodes are inserted dependency-first.
        stack = [(target, None)]
        while stack:
            module, dependencies = stack[-1]
            if dependencies is None:
                pending[module] = load(module)
                state[module] = 1
                dependencies = iter(pending[module]["dependencies"])
                stack[-1] = (module, dependencies)
            dependency = next(dependencies, None)
            if dependency is None:
                nodes[module] = pending.pop(module)
                state[module] = 2
                stack.pop()
            elif state.get(dependency) == 1:
                raise ValueError("Import cycle: " + " -> ".join(
                    [item[0] for item in stack] + [dependency]))
            elif state.get(dependency) != 2:
                stack.append((dependency, None))
    return nodes


def compiler_environment(args):
    runtime = ROOT.parent / "lean-runtime"
    toolchain = Path(os.environ.get("CODED_SORTING_TOOLCHAIN",
                                   runtime / "lean-4.19.0-linux")).resolve()
    executable = toolchain / "bin/lean"
    if not executable.is_file():
        raise FileNotFoundError("Toolchain restoration incomplete: " + str(executable))
    # The existing wrapper prepares the known-executable shim once, before any
    # parallel worker starts. This is an actual toolchain check, not a build PASS.
    check_command = [sys.executable, "scripts/run_lean_tool.py", "lean", "--version"]
    check = subprocess.run(check_command, cwd=ROOT, capture_output=True, text=True,
                           timeout=60)
    if check.returncode:
        raise RuntimeError("Lean startup failed:\n" + check.stdout + check.stderr)
    pin = (ROOT / "lean-toolchain").read_text().strip()
    expected = pin.rsplit(":v", 1)[-1]
    if expected not in check.stdout:
        raise RuntimeError(f"Toolchain mismatch: {pin!r} / {check.stdout.strip()!r}")
    package_roots = sorted((ROOT / ".lake/packages").glob("*"))
    import_roots = [ROOT / ".lake/build/lib/lean"] + [
        p / ".lake/build/lib/lean" for p in package_roots
        if (p / ".lake/build/lib/lean").is_dir()]
    import_roots.append(toolchain / "lib/lean")
    env = os.environ.copy()
    env["LEAN_SYSROOT"] = str(toolchain)
    env["PATH"] = str(toolchain / "bin") + os.pathsep + env.get("PATH", "")
    env["LD_LIBRARY_PATH"] = os.pathsep.join(
        [str(toolchain / "lib/lean"), str(toolchain / "lib"),
         env.get("LD_LIBRARY_PATH", "")])
    env["LEAN_PATH"] = os.pathsep.join(map(str, import_roots[:-1]))
    if not Path("/proc/self/exe").exists():
        shim = runtime / "known_executable_path.so"
        if not shim.is_file():
            raise FileNotFoundError("Required executable-path shim absent: " + str(shim))
        env["CODED_SORTING_KNOWN_EXE"] = str(executable)
        env["LD_PRELOAD"] = str(shim) + (
            os.pathsep + env["LD_PRELOAD"] if env.get("LD_PRELOAD") else "")
    runtime_hashes = {"bin/lean": sha_file(executable)}
    for name in ("lib/lean/libleanshared.so", "lib/lean/libleanshared_1.so", "lib/lean/Init.olean"):
        path = toolchain / name
        if path.is_file():
            runtime_hashes[name] = sha_file(path)
    fingerprint = {"pin": pin, "version": check.stdout.strip(),
                   "runtime_sha256": runtime_hashes,
                   "package_manifest_sha256": sha_file(ROOT / "lake-manifest.json"),
                   "lean_arguments": ["-j", str(args.lean_threads), "-s", "32768", "--profile"]}
    return executable, env, import_roots, package_roots, fingerprint


class Builder:
    def __init__(self, args, graph, run_dir):
        self.args, self.graph, self.run_dir = args, graph, run_dir
        (self.executable, self.env, self.import_roots, self.package_roots,
         self.compiler) = compiler_environment(args)
        self.cache_dir = ROOT / "logs/parallel_build/cache"
        self.object_dir = ROOT / ".lake/build/lib/lean"
        self.hash_cache, self.hash_lock = {}, threading.Lock()
        self.runner_sha256 = sha_file(Path(__file__))

    def digest(self, path):
        # Stat data only avoids repeatedly hashing the same unchanged file in
        # one process. Reuse decisions compare the recorded SHA256 values.
        stat = path.stat()
        key = (str(path), stat.st_dev, stat.st_ino, stat.st_size,
               stat.st_mtime_ns, stat.st_ctime_ns)
        with self.hash_lock:
            cached = self.hash_cache.get(key)
        if cached is not None:
            return cached
        digest = sha_file(path)
        with self.hash_lock:
            self.hash_cache[key] = digest
        return digest

    def import_object(self, module):
        relative = relative_module(module, ".olean")
        for root in self.import_roots:
            path = root / relative
            if path.is_file():
                return path
        raise FileNotFoundError("Missing imported olean: " + module)

    def bindings(self, module):
        sources, objects = {}, {}
        for imported in self.graph[module]["imports"]:
            objects[imported] = self.digest(self.import_object(imported))
            relative = relative_module(imported, ".lean")
            roots = [ROOT] if local_module(imported) else self.package_roots
            for root in roots:
                path = root / relative
                if path.is_file():
                    sources[imported] = self.digest(path)
                    if local_module(imported) and sources[imported] != self.graph[imported]["source_sha256"]:
                        raise RuntimeError("Imported local source changed since DAG discovery: " + imported)
                    break
        return {"direct_import_source_sha256": sources,
                "direct_import_olean_sha256": objects}

    def preflight(self):
        missing = []
        external = sorted({dep for node in self.graph.values()
                           for dep in node["imports"] if not local_module(dep)})
        for imported in external:
            try:
                self.import_object(imported)
            except FileNotFoundError:
                missing.append(imported)
        if missing:
            raise FileNotFoundError("External cache restoration incomplete:\n" +
                                    "\n".join(missing))

    def compile(self, module):
        node = self.graph[module]
        source = node["source"]
        output = self.object_dir / relative_module(module, ".olean")
        record_path = self.run_dir / (module + ".json")
        log_path = self.run_dir / (module + ".stdout.log")
        cache_path = self.cache_dir / (module + ".json")
        record = {"schema": SCHEMA, "module": module,
                  "runner_sha256": self.runner_sha256,
                  "source": str(source.relative_to(ROOT)),
                  "source_sha256": node["source_sha256"],
                  "compiler": self.compiler, "started_at_utc": utc_now(),
                  "started_at_unix": time.time(), "status": "PREPARING"}
        temporary = None
        try:
            data = source.read_bytes()
            if sha_bytes(data) != node["source_sha256"]:
                raise RuntimeError("Source changed since DAG discovery: " + module)
            record.update(self.bindings(module))
            can_reuse = not self.args.force and (
                module not in self.args.targets or self.args.reuse_targets)
            previous = None
            if can_reuse and cache_path.is_file() and output.is_file():
                try:
                    previous = json.loads(cache_path.read_text())
                except (OSError, ValueError):
                    previous = None
            binding_keys = ("schema", "source_sha256", "compiler",
                            "direct_import_source_sha256", "direct_import_olean_sha256")
            if (previous and previous.get("status") == "PASS" and
                    previous.get("exit_code") == 0 and
                    (ROOT / previous.get("record", "missing-pass-record")).is_file() and
                    all(previous.get(k) == record[k] for k in binding_keys) and
                    previous.get("olean_sha256") == self.digest(output)):
                record.update(status="REUSED", olean_sha256=previous["olean_sha256"],
                              reused_pass_record=previous["record"])
            else:
                snapshot = ROOT / "logs/snapshots" / (module + "-" + node["source_sha256"] + ".lean")
                snapshot.parent.mkdir(parents=True, exist_ok=True)
                if not snapshot.is_file():
                    snapshot.write_bytes(data)
                elif self.digest(snapshot) != node["source_sha256"]:
                    raise RuntimeError("Source snapshot hash mismatch: " + str(snapshot))
                output.parent.mkdir(parents=True, exist_ok=True)
                temporary = output.with_name("." + output.stem + "." + self.run_dir.name + ".olean")
                command = [str(self.executable), *self.compiler["lean_arguments"],
                           "-o", str(temporary), str(source.relative_to(ROOT))]
                record.update(command=command, status="RUNNING",
                              source_snapshot=str(snapshot.relative_to(ROOT)),
                              log=str(log_path.relative_to(ROOT)),
                              output=str(output.relative_to(ROOT)))
                atomic_json(record_path, record)
                with log_path.open("w") as log:
                    process = subprocess.Popen(command, cwd=ROOT, env=self.env,
                                               stdout=log, stderr=subprocess.STDOUT)
                    try:
                        exit_code = process.wait(timeout=self.args.timeout)
                        timed_out = False
                    except subprocess.TimeoutExpired:
                        process.kill()
                        exit_code = process.wait()
                        timed_out = True
                record.update(exit_code=exit_code, timed_out=timed_out)
                record["source_unchanged"] = sha_file(source) == node["source_sha256"]
                final_bindings = self.bindings(module)
                record["imports_unchanged"] = all(record[k] == v for k, v in final_bindings.items())
                if exit_code != 0 or timed_out:
                    record["status"] = "TIMEOUT" if timed_out else "FAIL"
                elif not record["source_unchanged"] or not record["imports_unchanged"]:
                    record.update(status="INVALIDATED", error="Source or import changed during compilation")
                elif not temporary.is_file():
                    record.update(status="FAIL", error="Lean exited zero without an output object")
                else:
                    record["olean_sha256"] = sha_file(temporary)
                    temporary.replace(output)
                    record["status"] = "PASS"
        except Exception as error:
            record.update(status="ERROR", error=f"{type(error).__name__}: {error}")
        finally:
            if temporary is not None and temporary.exists():
                temporary.unlink()
            record.update(finished_at_utc=utc_now(), finished_at_unix=time.time(),
                          record=str(record_path.relative_to(ROOT)))
            record["elapsed_seconds"] = record["finished_at_unix"] - record["started_at_unix"]
            atomic_json(record_path, record)
            if record["status"] == "PASS":
                atomic_json(cache_path, record)
        return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+", help="local module names, e.g. CodedSorting.Interchange.OneLevel.Allocation")
    parser.add_argument("--jobs", type=int, default=4, help="maximum simultaneous Lean processes (default 4)")
    parser.add_argument("--lean-threads", type=int, default=1, help="threads per Lean process (default 1)")
    parser.add_argument("--timeout", type=float, default=300, help="seconds per module (default 300)")
    parser.add_argument("--force", action="store_true", help="rebuild every dependency")
    parser.add_argument("--reuse-targets", action="store_true", help="also allow exact-hash reuse of explicit targets")
    parser.add_argument("--keep-going", action="store_true", help="continue independent branches after a failure")
    parser.add_argument("--plan-only", action="store_true", help="validate the source DAG without starting Lean")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 32 or args.lean_threads < 1 or args.timeout <= 0:
        parser.error("jobs must be 1..32, lean-threads positive, and timeout positive")
    args.targets = list(dict.fromkeys(args.targets))
    graph = dependency_graph(args.targets)
    dependents = {module: [] for module in graph}
    remaining = {module: len(node["dependencies"]) for module, node in graph.items()}
    for module, node in graph.items():
        for dependency in node["dependencies"]:
            dependents[dependency].append(module)
    # Nodes were inserted dependency-first. Reversing that order computes each
    # ready node's longest remaining path to a requested target.
    priority = {}
    for module in reversed(graph):
        priority[module] = 1 + max((priority[x] for x in dependents[module]), default=0)
    plan = {"targets": args.targets, "local_modules": len(graph), "jobs": args.jobs,
            "initially_ready": sum(count == 0 for count in remaining.values()),
            "source_closure_sha256": sha_bytes(json.dumps(
                {m: graph[m]["source_sha256"] for m in sorted(graph)}, sort_keys=True).encode())}
    print(json.dumps({"event": "PLAN", **plan}), flush=True)
    if args.plan_only:
        return 0
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%f") + "-" + str(os.getpid())
    run_dir = ROOT / "logs/parallel_build" / stamp
    run_dir.mkdir(parents=True, exist_ok=False)
    lock_path = ROOT / ".lake/compile_parallel_modules.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    run_lock = lock_path.open("a+")
    try:
        fcntl.flock(run_lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise RuntimeError("Another parallel module compiler is already running in this project")
    builder = Builder(args, graph, run_dir)
    builder.preflight()
    manifest = {"schema": SCHEMA, "status": "RUNNING", **plan,
                "runner_sha256": builder.runner_sha256,
                "compiler": builder.compiler, "started_at_utc": utc_now(),
                "arguments": vars(args), "completed": 0, "passed": 0, "reused": 0, "failed": 0}
    manifest_path = run_dir / "manifest.json"
    atomic_json(manifest_path, manifest)
    atomic_json(run_dir / "sources.json", {m: graph[m]["source_sha256"] for m in sorted(graph)})
    ready = [(-priority[m], m) for m, n in remaining.items() if n == 0]
    heapq.heapify(ready)
    running, results = {}, {}
    last_progress = time.monotonic()
    with (run_dir / "events.jsonl").open("w") as events, ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while ready or running:
            while ready and len(running) < args.jobs and (not manifest["failed"] or args.keep_going):
                _, module = heapq.heappop(ready)
                running[pool.submit(builder.compile, module)] = module
            if not running:
                break
            done, _ = wait(running, timeout=5, return_when=FIRST_COMPLETED)
            for future in done:
                module = running.pop(future)
                record = future.result()
                results[module] = record["status"]
                success = record["status"] in {"PASS", "REUSED"}
                manifest["completed"] += 1
                manifest["passed" if record["status"] == "PASS" else
                         "reused" if record["status"] == "REUSED" else "failed"] += 1
                event = {"module": module, "status": record["status"],
                         "elapsed_seconds": round(record["elapsed_seconds"], 3),
                         "completed": manifest["completed"], "total": len(graph),
                         "record": record["record"]}
                if "error" in record:
                    event["error"] = record["error"]
                events.write(json.dumps(event, ensure_ascii=False) + "\n")
                events.flush()
                print(json.dumps(event, ensure_ascii=False), flush=True)
                atomic_json(manifest_path, manifest)
                if success:
                    for parent in dependents[module]:
                        remaining[parent] -= 1
                        if remaining[parent] == 0:
                            heapq.heappush(ready, (-priority[parent], parent))
                last_progress = time.monotonic()
            if time.monotonic() - last_progress >= 30:
                print(json.dumps({"event": "RUNNING", "modules": sorted(running.values()),
                                  "completed": manifest["completed"], "total": len(graph)}), flush=True)
                last_progress = time.monotonic()
    unfinished = sorted(set(graph) - results.keys())
    changed_sources = [module for module, node in graph.items()
                       if not node["source"].is_file() or sha_file(node["source"]) != node["source_sha256"]]
    manifest.update(status="PASS" if not manifest["failed"] and not unfinished and not changed_sources else "FAIL",
                    finished_at_utc=utc_now(), unfinished=unfinished,
                    changed_sources=changed_sources,
                    target_status={target: results.get(target, "NOT_BUILT") for target in args.targets})
    atomic_json(manifest_path, manifest)
    print(json.dumps({"event": "FINISHED", "status": manifest["status"],
                      "passed": manifest["passed"], "reused": manifest["reused"],
                      "failed": manifest["failed"], "unfinished": len(unfinished),
                      "manifest": str(manifest_path.relative_to(ROOT))}), flush=True)
    run_lock.close()
    return 0 if manifest["status"] == "PASS" else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"Build setup failed: {type(error).__name__}: {error}", file=sys.stderr)
        raise SystemExit(1)
