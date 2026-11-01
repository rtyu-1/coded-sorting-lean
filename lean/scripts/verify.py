#!/usr/bin/env python3
"""Build the proofs and check theorem statements, model definitions, and axioms."""
from pathlib import Path
import argparse
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess
import sys
import check_model_baseline

ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"
TARGETS = {
    "CodedSorting.Sorting.Theorem31.theorem_3_1",
    "CodedSorting.NetworkCoding.Theorem32.theorem_3_2",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

REVIEW_SECTIONS = [('sorting.statement', 'Sorting theorem', '排序定理', 'Size parameters, word width, and the two memory cases.', '规模参数、字长和两个内存情形。'), ('sorting.guarantees', 'Sorting result', '排序结果', 'Output, termination, and resource bounds for the constructed execution.', '构造出的执行所满足的输出、终止和资源界。'), ('sorting.inputs', 'Input files', '输入文件', 'The input length and the disk representation of its words.', '输入长度及各个字在磁盘上的表示。'), ('sorting.execution', 'Program execution', '程序执行', 'Resident operations and block transfers; the small-memory controller follows the model convention.', '内存操作与块传输；小内存控制器采用模型页说明的约定。'), ('sorting.resources', 'Resource bounds', '资源界', 'Memory, disk space, I/O units, and coefficient dependence.', '内存、磁盘空间、I/O 单位及系数依赖。'), ('network.statement', 'Network theorem', '网络定理', 'Coding and routing results on the constructed network.', '所构造网络上的编码和路由结论。'), ('network.sessions', 'Network and messages', '网络与消息', 'Sessions enumerate the independent original messages.', '通信会话对应独立的原始消息。'), ('network.protocol', 'Coding protocols', '编码协议', 'Initialization, local communication, decoding, and binary linearity.', '初始化、本地通信、译码和二元线性性。'), ('network.rates', 'Coding and routing rates', '编码与路由速率', 'Achievable rates and shared capacity in both directions of each edge.', '可达速率，以及每条边两个方向共用的容量。'), ('bridges', 'Supporting results', '支撑结果', 'The lemmas connecting finite computation, execution, rank bounds, and finite block length.', '联系有限计算、执行、秩界和有限块长的引理。'), ('axioms', 'Axiom dependencies', '公理依赖', 'The checked proofs use propext, Classical.choice, and Quot.sound.', '检查证明所用的 propext、Classical.choice 和 Quot.sound。')]


def write_review_reports(output):
    sections = {}
    current = None
    for line in output.splitlines():
        if line.startswith("CS_REVIEW "):
            current = line.removeprefix("CS_REVIEW ")
            if current in sections:
                raise RuntimeError("Duplicate review section: " + current)
            sections[current] = []
        elif current is not None:
            sections[current].append(line)
        elif line.strip():
            raise RuntimeError("Unexpected output before the first review section.")
    if list(sections) != [s[0] for s in REVIEW_SECTIONS] or any(
            not "\n".join(body).strip() for body in sections.values()):
        raise RuntimeError("The review output has missing, empty, or unexpected sections.")
    for language, filename, title, intro in [
        (1, "review.md", "Main theorem and model declarations",
         "This reference groups the Lean declarations used by the two main results: "
         "inputs, execution, resources, communication protocols, and rates. "
         "The [sorting theorem guide](../docs/SortingTheorem.md) and "
         "[model guide](../docs/Model.md) explain their mathematical meaning. "
         "The declarations are produced by `ReviewEndpoints.lean`; "
         "`verification.json` records the checked sources and results, and "
         "`endpoints.log` contains the compiler output."),
        (2, "review.zh-CN.md", "主定理与模型声明",
         "本页按主题列出两个主结果使用的 Lean 声明，包括输入、执行、资源、通信协议和速率。"
         "[排序定理详解](../docs/SortingTheorem.zh-CN.md)和"
         "[模型说明](../docs/Model.zh-CN.md)解释这些定义的数学含义。"
         "声明由 `ReviewEndpoints.lean` 输出；`verification.json` 记录对应源码和检查结果，"
         "`endpoints.log` 保存编译器的原始输出。"),
    ]:
        parts = ["# " + title, "[English](review.md) · [简体中文](review.zh-CN.md)", intro]
        for index, section in enumerate(REVIEW_SECTIONS, 1):
            body = "\n".join(sections[section[0]]).strip()
            parts += [f"## {index}. {section[language]}", section[language + 2],
                      "```lean\n" + body + "\n```"]
        (REPORTS / filename).write_text("\n\n".join(parts) + "\n")
    return list(sections)


def run(command, log_name):
    print("Running: " + " ".join(command), flush=True)
    with (REPORTS / log_name).open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print((REPORTS / log_name).read_text(errors="replace")[-6000:])
        raise RuntimeError("Command failed; see reports/" + log_name)
    return (REPORTS / log_name).read_text(errors="replace")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--builder", choices=["lake", "parallel"], default="lake",
                        help="Lake normally; bounded parallel compilation with a standalone toolchain")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=1200)
    args = parser.parse_args()
    if args.jobs < 1 or args.jobs > 32 or args.timeout <= 0:
        parser.error("jobs must be 1..32 and timeout must be positive")
    if args.builder == "lake" and shutil.which("lake") is None:
        raise SystemExit("Lake is not installed. Follow the Lean installation link in README.md.")
    lake = (["lake"] if args.builder == "lake" else
            [sys.executable, "scripts/run_lean_tool.py", "lake"])
    REPORTS.mkdir(exist_ok=True)
    for name in ["verification.json", "review.md", "review.zh-CN.md"]:
        (REPORTS / name).unlink(missing_ok=True)
    version = run([*lake, "env", "lean", "--version"], "lean_version.txt").strip()
    if "version 4.19.0," not in version:
        raise RuntimeError("Use the Lean version pinned in lean-toolchain.")
    if args.builder == "lake":
        build_command = [*lake, "build"]
        scope = "All numbered paper entry modules and their imports"
    else:
        audits = sorted('.'.join(p.relative_to(ROOT).with_suffix('').parts)
                        for p in (ROOT / 'CodedSorting').rglob('*Audit.lean')
                        if 'Archive' not in p.relative_to(ROOT).parts)
        build_command = [sys.executable, "scripts/compile_parallel_modules.py",
                         "--jobs", str(args.jobs), "--timeout", str(args.timeout),
                         "--reuse-targets", "CodedSorting", *audits]
        scope = "All numbered paper entry modules, active audit modules and their imports"
    run([sys.executable, "scripts/source_inventory.py"], "source-inventory.log")
    run(build_command, "build.log")
    run([*lake, "env", "lean", "DefinitionContracts.lean"], "definition-contracts.log")
    run([*lake, "env", "lean", "DefinitionClosure.lean"], "definition-closure.log")
    run([sys.executable, "scripts/definition_reference.py", "reports/definition-closure.log"],
        "definition-check.log")
    definition_check = json.loads((REPORTS / "definition-check.json").read_text())
    model_output = run([*lake, "env", "lean", "ModelSnapshot.lean"], "model-snapshot.log")
    model_result = check_model_baseline.check(model_output)
    run([sys.executable, "scripts/test_model_baseline.py"], "model-gate-tests.log")
    review_output = run([*lake, "env", "lean", "ReviewEndpoints.lean"], "endpoints.log")
    output = run([*lake, "env", "lean", "Audit.lean"], "axioms.log")
    records = []
    auxiliary = []
    statements = []
    for line in output.splitlines():
        if "CS_ENDPOINT {" in line:
            records.append(json.loads(line.split("CS_ENDPOINT ", 1)[1]))
        if "CS_AUXILIARY {" in line:
            auxiliary.append(json.loads(line.split("CS_AUXILIARY ", 1)[1]))
        if "CS_STATEMENT {" in line:
            statements.append(json.loads(line.split("CS_STATEMENT ", 1)[1]))
    if len(records) != len(TARGETS) or {x["theorem"] for x in records} != TARGETS:
        raise RuntimeError("The endpoint audit is incomplete or contains duplicates.")
    if any(set(x["axioms"]) - ALLOWED for x in records):
        raise RuntimeError("An endpoint depends on an unapproved axiom.")
    if (len(statements) != len(TARGETS) or {x["theorem"] for x in statements} != TARGETS
            or any(x["exact_type_equal"] is not True for x in statements)):
        raise RuntimeError("The public statement equality audit is incomplete or failed.")
    if (len(auxiliary) != 1 or auxiliary[0]["theorem"] !=
            "CodedSorting.Construction.NetworkCodingResult.paper_finite_block"
            or set(auxiliary[0]["axioms"]) - ALLOWED):
        raise RuntimeError("The finite-block coding axiom check is incomplete or failed.")
    review_sections = write_review_reports(review_output)
    sources = [*sorted((ROOT / "CodedSorting").rglob("*.lean")),
               *(ROOT / n for n in ["CodedSorting.lean", "ReviewEndpoints.lean", "ModelSnapshot.lean", "Audit.lean", "DefinitionClosure.lean", "DefinitionContracts.lean",
                                    "lean-toolchain", "lakefile.lean", "lake-manifest.json",
                                    "docs/model-baseline.json", "docs/statement-correspondence.json",
                                    "docs/source-inventory.json"]),
               *sorted(p for p in (ROOT / "scripts").iterdir() if p.suffix in {".py", ".lean", ".c"})]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    result = {"passed": True, "lean_version": version,
              "finished_at_utc": datetime.now(timezone.utc).isoformat(),
              "source_modules_present": len(list((ROOT / "CodedSorting").rglob("*.lean"))),
              "endpoint_axioms": records, "auxiliary_axioms": auxiliary, "source_sha256": hashes,
              "definition_check": definition_check, "definition_contracts_checked": True,
              "model_baseline_checked": True, "model_gate_regression_cases": 9, "model_declarations_checked": len(model_result["declarations"]),
              "public_statement_checks": statements, "review_sections": review_sections,
              "review_sha256": {name: hashlib.sha256((REPORTS / name).read_bytes()).hexdigest()
                                for name in ["review.md", "review.zh-CN.md", "endpoints.log"]},
              "build_mode": args.builder,
              "build_command": build_command,
              "scope": scope + "; fresh final-theorem axiom audit; source hashes cover all current modules, including independent audit modules"}
    (REPORTS / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: build, source inventory, model definitions, theorem types, and axiom dependencies.")
    print("Read reports/review.md or reports/review.zh-CN.md for the actual model definitions.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError) as error:
        print("Verification failed: " + str(error), file=sys.stderr)
        raise SystemExit(1)
