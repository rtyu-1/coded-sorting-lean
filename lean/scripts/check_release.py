#!/usr/bin/env python3
"""Check the public documentation, paper map, and complete local import graph."""
from pathlib import Path
import json
import re
import subprocess
import sys

from compile_parallel_modules import dependency_graph, imports_of

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def check_source_excerpts(root, errors):
    record = json.loads((root / 'docs/sorting-theorem-snippets.json').read_text())
    documents = {name: (root / name).read_text() for name in record['documents']}
    source_blocks = set()
    for excerpt in record['snippets']:
        try:
            source = (root / excerpt['path']).read_text()
            start = source.index(excerpt['start'])
            stop = source.index(excerpt['stop'], start + len(excerpt['start']))
        except (OSError, ValueError) as error:
            errors.append(f'Source excerpt {excerpt["path"]}: {error}')
            continue
        block = '```lean\n' + source[start:stop].rstrip() + '\n```'
        source_blocks.add(block)
        for document, text in documents.items():
            if block not in text:
                errors.append(f'{document}: refresh excerpt {excerpt["start"]}')
    for document, text in documents.items():
        for match in re.finditer(r'^```lean\n[\s\S]*?^```', text, re.MULTILINE):
            if match[0] not in source_blocks:
                line = text.count('\n', 0, match.start()) + 1
                errors.append(f'{document}:{line}: Lean excerpt has no matching source entry')
    return record


def main():
    errors = []
    links = 0
    markdown = sorted(p for p in REPO.rglob('*.md')
                      if not any(part in {'.git', '.lake', 'reports', 'logs', 'lean-runtime'}
                                 for part in p.relative_to(REPO).parts))
    for path in markdown:
        source = path.read_text()
        for target in re.findall(r'\]\(([^)]+)\)', source):
            if re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:', target):
                continue
            local = target.split('#', 1)[0]
            if local:
                links += 1
                resolved = (path.parent / local).resolve()
                if not resolved.is_relative_to(REPO.resolve()) or not resolved.exists():
                    errors.append(f'{path.relative_to(REPO)}: missing link {target}')
    mapping = json.loads((ROOT / 'CodedSorting/paper-map.json').read_text())
    numbers = []
    for entry in mapping['results']:
        numbers.append(entry['number'])
        for relative in [entry['lean_entry'], *entry['guides'].values()]:
            if not (ROOT / 'CodedSorting' / relative).is_file():
                errors.append('Paper map: missing ' + relative)
    if len(numbers) != len(set(numbers)):
        errors.append('Paper map: repeated result number')
    excerpt_record = check_source_excerpts(ROOT, errors)
    definition_path = ROOT / 'docs/definition-closure.json.gz'
    if definition_path.exists():
        import gzip, hashlib
        definition_record = json.loads(gzip.decompress(definition_path.read_bytes()))
        definitions = {x['name']: x for x in definition_record['declarations']}
        page_text = {}
        for definition in definitions.values():
            for dependency in definition['project_dependencies']:
                if dependency not in definitions:
                    errors.append('Unresolved definition: ' + dependency)
            page = ROOT.joinpath(*definition['module'].split('.')).with_suffix('.definitions.md')
            anchor = 'def-' + hashlib.sha256(definition['name'].encode()).hexdigest()[:16]
            if page not in page_text:
                page_text[page] = page.read_text() if page.exists() else ''
            if ('id="' + anchor + '"') not in page_text[page]:
                errors.append('Missing definition entry: ' + definition['name'])
        for relative, expected in definition_record['source_sha256'].items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
                errors.append('Refresh definition reference for changed source: ' + relative)
    modules = sorted((ROOT / 'CodedSorting').rglob('*.lean'))
    for path in modules + [ROOT / p for p in ['CodedSorting.lean', 'Audit.lean',
                                            'ModelSnapshot.lean', 'ReviewEndpoints.lean',
                                            'DefinitionClosure.lean', 'DefinitionContracts.lean']]:
        for name in imports_of(path.read_bytes()):
            if name == 'CodedSorting' or name.startswith('CodedSorting.'):
                if not ROOT.joinpath(*name.split('.')).with_suffix('.lean').is_file():
                    errors.append(f'{path.relative_to(ROOT)}: missing import {name}')
    closure = dependency_graph(['CodedSorting'])
    for name in ['model-baseline.json', 'statement-correspondence.json']:
        record = json.loads((ROOT / 'docs' / name).read_text())
        hashes = (record['snapshot']['model_source_sha256'] if name == 'model-baseline.json'
                  else record['source_sha256'])
        import hashlib
        for relative, expected in hashes.items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
                errors.append(f'{name}: changed source {relative}')
    if errors:
        raise SystemExit('\n'.join(errors))
    subprocess.run([sys.executable, 'scripts/source_inventory.py'], cwd=ROOT, check=True)
    print(json.dumps({'passed': True, 'markdown_files': len(markdown),
                      'local_links': links, 'paper_results': len(numbers),
                      'exact_source_excerpts_per_language': len(excerpt_record['snippets']),
                      'lean_modules': len(modules), 'main_imports': len(closure)}, indent=2))


if __name__ == '__main__':
    main()
