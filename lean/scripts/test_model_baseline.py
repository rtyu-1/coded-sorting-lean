#!/usr/bin/env python3
"""Fault-inject the frozen-model gate using a fresh compiler snapshot.

Only temporary fixture copies are changed. These cases test rejection by the
comparison gate, not compilation of deliberately weakened Lean theorems.
"""
import argparse
import json
from pathlib import Path
import shutil
import tempfile

import check_model_baseline as gate


def run_tests(log):
    root, baseline = gate.ROOT, gate.BASELINE
    review_path = root / 'docs/statement-correspondence.json'
    review_text = review_path.read_text()
    review = json.loads(review_text)
    records = []
    for line in log.splitlines():
        if 'CS_MODEL {' in line:
            records.append(json.loads(line.split('CS_MODEL ', 1)[1]))
    if not records:
        raise RuntimeError('Supply a fresh successful ModelSnapshot.lean log.')

    def altered(name, key, value):
        return '\n'.join('CS_MODEL ' + json.dumps({**item, key: value} if item['name'] == name else item)
                         for item in records)

    results = []
    with tempfile.TemporaryDirectory(prefix='model-gate-test-', dir=root / 'reports') as directory:
        fixture = Path(directory)
        for relative in set(gate.MODEL_FILES) | set(review['source_sha256']):
            target = fixture / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / relative, target)
        (fixture / 'docs').mkdir(exist_ok=True)
        shutil.copyfile(baseline, fixture / 'docs/model-baseline.json')
        fixture_review = fixture / 'docs/statement-correspondence.json'
        fixture_review.write_text(review_text)
        gate.ROOT, gate.BASELINE = fixture, fixture / 'docs/model-baseline.json'
        baseline_bytes = gate.BASELINE.read_bytes()

        def case(name, candidate, rejected=False, diagnostic=None, message=None):
            try:
                gate.check(candidate)
            except ValueError as error:
                if not rejected or (message and message not in str(error)):
                    raise AssertionError(f'{name}: unexpected rejection: {error}') from error
                if diagnostic and not (fixture / 'reports' / diagnostic).is_file():
                    raise AssertionError(name + ': missing diagnostic')
                outcome = 'rejected as expected'
            else:
                if rejected:
                    raise AssertionError(name + ': invalid fixture was accepted')
                outcome = 'accepted as expected'
            if gate.BASELINE.read_bytes() != baseline_bytes:
                raise AssertionError(name + ': baseline was rewritten')
            results.append({'case': name, 'outcome': outcome})

        try:
            case('unchanged compiled snapshot', log)
            public = 'CodedSorting.Sorting.Theorem31.theorem_3_1'
            case('changed public type, independent of implementation equality',
                 altered(public, 'type', 'Expr.const `True []'), True,
                 'model-changes.md', 'Public statements or model definitions changed')
            definition = next(item['name'] for item in records if 'value' in item)
            case('changed selected definition body with unchanged declared type',
                 altered(definition, 'value', 'Expr.const `True []'), True,
                 'model-changes.diff', 'Public statements or model definitions changed')
            case('presentation-only type formatting',
                 altered(public, 'readable_type', 'presentation-only change'))
            missing = '\n'.join('CS_MODEL ' + json.dumps(item) for item in records if item['name'] != public)
            case('missing public theorem', missing, True, message='Missing public theorem')
            source = fixture / gate.MODEL_FILES[0]
            original = source.read_bytes()
            source.write_bytes(original + b'\n-- fault injection\n')
            case('changed protected model source', log, True,
                 'model-changes.md', 'Public statements or model definitions changed')
            source.write_bytes(original)
            reviewed_only = sorted(set(review['source_sha256']) - set(gate.MODEL_FILES))
            if not reviewed_only:
                raise AssertionError('Need a reviewed source outside the frozen model files')
            source = fixture / reviewed_only[0]
            original = source.read_bytes()
            source.write_bytes(original + b'\n-- fault injection\n')
            case('stale correspondence source hash', log, True,
                 'review-changes.md', 'Correspondence review has stale source hashes')
            source.write_bytes(original)
            fixture_review.write_text(json.dumps({**review, 'items': review['items'][:-1]}))
            case('incomplete S1-S9/N1-N8 review', log, True,
                 message='Incomplete itemized correspondence review')
            fixture_review.write_text(review_text)
            case('restored fixture', log)
            for name in ['model-changes.md', 'model-changes.diff', 'review-changes.md']:
                if (fixture / 'reports' / name).exists():
                    raise AssertionError('Stale diagnostic remains after success: ' + name)
        finally:
            gate.ROOT, gate.BASELINE = root, baseline
    return {'passed': True, 'scope': 'Fault injection into temporary snapshot/source/review fixtures; no Lean theorem was weakened.',
            'cases': results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', nargs='?', type=Path, default=gate.ROOT / 'reports/model-snapshot.log')
    args = parser.parse_args()
    result = run_tests(args.log.read_text())
    (gate.ROOT / 'reports/model-gate-tests.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS:', len(result['cases']), 'frozen-model gate regression cases')


if __name__ == '__main__':
    main()
