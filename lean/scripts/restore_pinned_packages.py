#!/usr/bin/env python3
"""Restore exact Git revisions from lake-manifest.json, without updating it."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

project = Path(__file__).resolve().parents[1]
manifest_path = project / 'lake-manifest.json'
before = manifest_path.read_bytes()
manifest = json.loads(before)
packages = project / manifest['packagesDir']
packages.mkdir(parents=True, exist_ok=True)
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
logdir = project / 'logs' / ('restore-pinned-' + stamp)
logdir.mkdir(parents=True, exist_ok=True)

def restore(pkg):
    target = packages / pkg['name']
    target.mkdir(parents=True, exist_ok=True)
    commands = []
    def run(args):
        p = subprocess.run(args, cwd=target, text=True, capture_output=True)
        commands.append({'command': args, 'exit_code': p.returncode,
                         'stdout': p.stdout, 'stderr': p.stderr})
        if p.returncode:
            raise RuntimeError(p.stderr)
        return p.stdout.strip()
    report = {'name': pkg['name'], 'url': pkg['url'], 'expected_revision': pkg['rev'],
              'commands': commands}
    try:
        if not (target / '.git').exists():
            run(['git', 'init'])
            run(['git', 'remote', 'add', 'origin', pkg['url']])
        run(['git', 'fetch', '--depth', '1', 'origin', pkg['rev']])
        # ProofWidgets' release cache identifies its release by tag. A shallow
        # SHA-only fetch does not restore that tag. Keep the pinned commit.
        tag = pkg.get('inputRev', '')
        if re.fullmatch(r'v[0-9][A-Za-z0-9._-]*', tag):
            run(['git', 'fetch', '--depth', '1', 'origin', 'tag', tag])
            if run(['git', 'rev-parse', 'refs/tags/' + tag + '^{commit}']) != pkg['rev']:
                raise RuntimeError('Release tag does not match the pinned revision: ' + tag)
        run(['git', 'checkout', '--detach', pkg['rev']])
        report['actual_revision'] = run(['git', 'rev-parse', 'HEAD'])
        report['success'] = report['actual_revision'] == pkg['rev']
    except Exception as exc:
        report['success'] = False
        report['error'] = str(exc)
    (logdir / (pkg['name'] + '.json')).write_text(json.dumps(report, indent=2) + '\n')
    print(pkg['name'], 'OK' if report['success'] else report.get('error', 'FAILED'), flush=True)
    return report

with ThreadPoolExecutor(max_workers=4) as pool:
    reports = list(pool.map(restore, manifest['packages']))
after = manifest_path.read_bytes()
summary = {'manifest_sha256': hashlib.sha256(before).hexdigest(),
           'manifest_unchanged': before == after,
           'packages': [{k: r[k] for k in ('name', 'expected_revision', 'success')} for r in reports]}
(logdir / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(logdir, flush=True)
raise SystemExit(not (before == after and all(r['success'] for r in reports)))
