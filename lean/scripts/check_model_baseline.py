#!/usr/bin/env python3
"""Compare elaborated public statements and model definitions with a frozen baseline.

Verification never updates the baseline. A mismatch writes a candidate and a
readable diff to reports/ and fails. Review the reason for every change before
explicitly replacing the baseline and updating the correspondence review.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / 'docs/model-baseline.json'
MODEL_FILES = [
    'CodedSorting/Shared/Words/WordConvention.lean',
    'CodedSorting/Shared/Memory/NormalizationController.lean',
    'CodedSorting/Shared/Programs/ControlledNormalization.lean',
    'CodedSorting/Sorting/Theorem31/Proof.lean',
    'CodedSorting/Sorting/Theorem31/LargeMemory.lean',
    'CodedSorting/Sorting/Theorem31/SmallMemory.lean',
    'CodedSorting/Sorting/Execution/Framework/PhysicalHalted.lean',
    'CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean',
    'CodedSorting/Sorting/SmallMemory/SmallSort.lean',
    'CodedSorting/Sorting/SmallMemory/SmallMemorySorting.lean',
    'CodedSorting/Sorting/SmallMemory/PublicUnrolledBlockSort.lean',
    'CodedSorting/Sorting/SmallMemory/NarrowWords/PublicUnrolledComplete.lean',
    'CodedSorting/NetworkCoding/Model/NetworkRates.lean',
    'CodedSorting/NetworkCoding/FiniteCodes/BinaryLinearPipeline.lean',
    'CodedSorting/NetworkCoding/Theorem32/Coding.lean',
    'CodedSorting/NetworkCoding/Theorem32/Proof.lean',
]


def snapshot(log):
    declarations = {}
    for line in log.splitlines():
        if 'CS_MODEL {' not in line:
            continue
        item = json.loads(line.split('CS_MODEL ', 1)[1])
        name = item.pop('name')
        if name in declarations:
            raise ValueError('Duplicate model declaration: ' + name)
        # Keep the baseline compact. The full exact expressions remain in the
        # fresh compiler log; hash them before storing readable type summaries.
        record = {'type_sha256': hashlib.sha256(item['type'].encode()).hexdigest(),
                  'readable_type': item['readable_type']}
        if 'value' in item:
            record['value_sha256'] = hashlib.sha256(item['value'].encode()).hexdigest()
        declarations[name] = record
    for name in ['CodedSorting.Sorting.Theorem31.theorem_3_1',
                 'CodedSorting.NetworkCoding.Theorem32.theorem_3_2']:
        if name not in declarations:
            raise ValueError('Missing public theorem: ' + name)
    if len(declarations) < 56:
        raise ValueError('Incomplete model snapshot')
    return {'schema': 1, 'declarations': declarations,
            'model_source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in MODEL_FILES}}


def formatted(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n'


def comparable(value):
    """Compare exact expressions, not incidental pretty-printer presentation."""
    return {**value, 'declarations': {
        name: {k: v for k, v in item.items() if k != 'readable_type'}
        for name, item in value['declarations'].items()}}


def check(log, candidate_only=False):
    current = snapshot(log)
    reports = ROOT / 'reports'
    reports.mkdir(exist_ok=True)
    (reports / 'model-candidate.json').write_text(formatted(current))
    if candidate_only:
        return current
    review = json.loads((ROOT / 'docs/statement-correspondence.json').read_text())
    expected = {f'S{i}' for i in range(1, 10)} | {f'N{i}' for i in range(1, 9)}
    if len(review['items']) != 17 or {item['id'] for item in review['items']} != expected:
        raise ValueError('Incomplete itemized correspondence review')
    stale = [p for p, digest in review['source_sha256'].items()
             if hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != digest]
    if stale:
        (reports / 'review-changes.md').write_text(
            '# Reviewed sources changed\n\n' + '\n'.join('- `' + p + '`' for p in stale) + '\n')
    else:
        (reports / 'review-changes.md').unlink(missing_ok=True)
    if not BASELINE.exists():
        raise ValueError('Missing model baseline; review reports/model-candidate.json before accepting it.')
    previous = json.loads(BASELINE.read_text())['snapshot']
    if comparable(previous) != comparable(current):
        diff = ''.join(difflib.unified_diff(formatted(previous).splitlines(True),
                                          formatted(current).splitlines(True),
                                          fromfile='reviewed model', tofile='current model'))
        (reports / 'model-changes.diff').write_text(diff)
        changes = ['# Model changes requiring correspondence review', '']
        before, after = previous['declarations'], current['declarations']
        for name in sorted(before.keys() | after.keys()):
            if ({k: v for k, v in before.get(name, {}).items() if k != 'readable_type'} ==
                    {k: v for k, v in after.get(name, {}).items() if k != 'readable_type'}):
                continue
            changes += ['## ' + name, '']
            for label, entries in [('Previous', before), ('Current', after)]:
                entry = entries.get(name)
                readable = entry['readable_type'] if entry else '(absent)'
                changes += [label + ':', '```lean', readable, '```', '']
            if before.get(name, {}).get('value_sha256') != after.get(name, {}).get('value_sha256'):
                changes += ['Definition body changed; inspect the exact diff and source definition.', '']
        for path in sorted(previous['model_source_sha256'].keys() | current['model_source_sha256'].keys()):
            if previous['model_source_sha256'].get(path) != current['model_source_sha256'].get(path):
                changes += ['Model source changed: `' + path + '`', '']
        (reports / 'model-changes.md').write_text('\n'.join(changes))
        raise ValueError('Public statements or model definitions changed. Review reports/model-changes.diff; '
                         'update the review record and baseline explicitly. No automatic acceptance.')
    (reports / 'model-changes.diff').unlink(missing_ok=True)
    (reports / 'model-changes.md').unlink(missing_ok=True)
    if stale:
        raise ValueError('Correspondence review has stale source hashes: ' + ', '.join(stale))
    return current


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--candidate-only', action='store_true')
    args = parser.parse_args()
    try:
        data = check(args.log.read_text(), args.candidate_only)
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))
    print('Model declarations:', len(data['declarations']), '; protected source files:', len(MODEL_FILES))


if __name__ == '__main__':
    main()
