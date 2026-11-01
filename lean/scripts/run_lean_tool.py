#!/usr/bin/env python3
"""Run the pinned toolchain, supplying known executable paths when /proc is absent."""
import os
from pathlib import Path
import subprocess
import sys

project = Path(__file__).resolve().parents[1]
runtime = project.parent / 'lean-runtime'
toolchain = Path(os.environ.get('CODED_SORTING_TOOLCHAIN', runtime / 'lean-4.19.0-linux'))
if len(sys.argv) < 2 or sys.argv[1] not in {'lean', 'lake'}:
    raise SystemExit('usage: run_lean_tool.py lean|lake [arguments ...]')
tool = toolchain / 'bin' / sys.argv[1]
env = os.environ.copy()
env['PATH'] = str(toolchain / 'bin') + os.pathsep + env.get('PATH', '')
env['LD_LIBRARY_PATH'] = os.pathsep.join([str(toolchain / 'lib/lean'), str(toolchain / 'lib'), env.get('LD_LIBRARY_PATH', '')])
env['LEAN_SYSROOT'] = str(toolchain)
if not Path('/proc/self/exe').exists():
    shim = runtime / 'known_executable_path.so'
    if not shim.exists():
        subprocess.run(['cc', '-shared', '-fPIC', str(project / 'scripts/known_executable_path.c'), '-ldl', '-o', str(shim)], check=True)
    env['CODED_SORTING_KNOWN_EXE'] = str(tool)
    env['LD_PRELOAD'] = str(shim) + (':' + env['LD_PRELOAD'] if env.get('LD_PRELOAD') else '')
raise SystemExit(subprocess.run([str(tool), *sys.argv[2:]], cwd=project, env=env).returncode)
