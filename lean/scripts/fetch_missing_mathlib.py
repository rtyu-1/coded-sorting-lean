#!/usr/bin/env python3
"""Fetch only missing modules from the pinned official Mathlib cache.

Existing oleans are never unpacked or rewritten, so concurrent project
elaboration can continue safely. This does not change package source files.
"""
from pathlib import Path
import datetime
import json
import os
import subprocess
import sys

project = Path(__file__).resolve().parents[1]
runtime = project.parent / 'lean-runtime'
cache = runtime / 'mathlib-cache'
mods = sys.argv[1:]
if not mods:
    raise SystemExit('usage: fetch_missing_mathlib.py Mathlib.Module ...')
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
env = os.environ.copy()
env['MATHLIB_CACHE_DIR'] = str(cache)
manifest_command = ['python', 'scripts/run_lean_tool.py', 'lake', 'env', 'lean',
                    '--run', 'scripts/cache_manifest.lean', *mods]
p = subprocess.run(manifest_command, cwd=project, env=env, capture_output=True, text=True)
if p.returncode:
    print(p.stdout, p.stderr)
    raise SystemExit(p.returncode)
rows = [line.split('\t') for line in p.stdout.splitlines()]
manifest = json.loads((project / 'lake-manifest.json').read_text())
# Include package output paths even when a clean restore has not created them yet.
roots = [project / '.lake/build/lib/lean'] + [
    project / manifest['packagesDir'] / package['name'] / '.lake/build/lib/lean'
    for package in manifest['packages']]
def exists(module):
    rel = module.replace('.', '/') + '.olean'
    return any((root / rel).exists() for root in roots)
missing = [row for row in rows if not exists(row[0])]
print('closure', len(rows), 'missing oleans', len(missing), flush=True)

cache.mkdir(parents=True, exist_ok=True)
to_download = [row for row in missing if not (cache / row[1]).exists()]
part_suffix = '.missing-part-' + stamp
download_command = None
if to_download:
    # A single curl process can reuse HTTPS connections. One urllib request per
    # module otherwise repeats the relatively expensive connection setup.
    download_config = cache / ('missing-' + stamp + '.curl.cfg')
    lines = []
    for _, filename in to_download:
        lines.extend(['url = ' + json.dumps('https://lakecache.blob.core.windows.net/mathlib4/f/' + filename),
                      'output = ' + json.dumps(str(cache / (filename + part_suffix))),
                      'fail', 'retry = 2', 'max-time = 120', 'silent', 'show-error', 'next'])
    download_config.write_text('\n'.join(lines[:-1]) + '\n')
    download_command = ['curl', '--parallel', '--parallel-max', '16', '--fail-early',
                        '--config', str(download_config)]
    result = subprocess.run(download_command, cwd=project, capture_output=True, text=True)
    if result.returncode:
        print(result.stdout, result.stderr)
        raise SystemExit(result.returncode)
    for _, filename in to_download:
        (cache / (filename + part_suffix)).rename(cache / filename)
downloaded = missing
config = []
for name, filename in downloaded:
    if exists(name):
        continue
    entry = {'file': str(cache / filename), 'base': str(project / '.lake/packages/mathlib')} \
            if name.startswith('Mathlib.') else str(cache / filename)
    config.append(entry)
command = [str(cache / 'leantar-0.1.15'), '-x', '-j', '-']
p = subprocess.run(command, cwd=project, input=json.dumps(config), text=True,
                   capture_output=True)
report = {'manifest_command': manifest_command, 'roots': mods, 'closure_count': len(rows),
          'download_command': download_command, 'download_count': len(to_download),
          'missing_before': missing, 'unpack_command': command, 'unpack_exit_code': p.returncode,
          'stdout': p.stdout, 'stderr': p.stderr,
          'missing_after': [name for name, _ in rows if not exists(name)],
          'policy': 'Unpack only modules whose olean did not exist; do not rewrite existing modules.'}
log = project / 'logs' / ('mathlib_missing_' + stamp + '.json')
log.write_text(json.dumps(report, indent=2) + '\n')
print(p.stdout, p.stderr, end='')
print('unpack exit', p.returncode, 'remaining', len(report['missing_after']), 'log', log, flush=True)
raise SystemExit(p.returncode or bool(report['missing_after']))
