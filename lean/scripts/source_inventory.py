#!/usr/bin/env python3
"""Generate and check the source inventory."""
import argparse
import json
from pathlib import Path
from compile_parallel_modules import dependency_graph

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'docs/source-inventory.json'
STRUCTURE = ROOT / 'docs/Structure.md'
START = '<!-- source-inventory:start -->'
END = '<!-- source-inventory:end -->'


def inventory():
    files = sorted((ROOT / 'CodedSorting').rglob('*.lean'))
    generated = [p for p in files if 'Generated' in p.relative_to(ROOT).parts]
    manual = [p for p in files if p not in generated]
    def count(paths):
        return {'files': len(paths), 'lines': sum(len(p.read_text().splitlines()) for p in paths)}
    return {'schema': 1, 'scope': 'CodedSorting/**/*.lean; includes comments and blank lines; excludes dependencies and root entry files',
            'total': count(files), 'generated': count(generated), 'other': count(manual),
            'default_import_closure_including_root': len(dependency_graph(['CodedSorting']))}


def render(data, chinese=False):
    rows = [('其余证明与定义' if chinese else 'Other proofs and definitions', data['other']),
            ('有限计算数据与证明' if chinese else 'Finite computation data and proofs', data['generated']),
            ('合计' if chinese else 'Total', data['total'])]
    title = '源码统计' if chinese else 'Source inventory'
    table = '\n'.join(f"| {name} | {v['files']} | {v['lines']:,} |" for name, v in rows)
    intro = ('下表统计证明目录中的 Lean 文件和行数。有限计算数据及其逐项证明单独列出。'
             if chinese else 'The table counts Lean files and lines in the proof directory, with finite computation data and their proofs listed separately.')
    header = '| 类别 | 文件 | 行 |' if chinese else '| Category | Files | Lines |'
    closure = data['default_import_closure_including_root']
    note = (f'从 `CodedSorting.lean` 入口直接或间接导入的模块共有 **{closure}** 个，包含入口本身。\n\n'
            '行数覆盖 `CodedSorting/**/*.lean`，包含注释和空行，不含依赖、构建产物、历史记录及顶层入口。'
            if chinese else f'`CodedSorting.lean` directly or indirectly imports **{closure}** modules, including the entry itself.\n\n'
            'Counts cover `CodedSorting/**/*.lean`, including comments and blank lines. Dependencies, build output, '
            'historical records, and root entry files are excluded from the line counts.')
    return (f'{START}\n## {title}\n\n'
            + intro + '\n\n' + header + '\n| --- | ---: | ---: |\n' + table + '\n\n' + note + '\n\n' + ('运行 `python3 scripts/source_inventory.py --write` 更新统计，`scripts/verify.py` 检查统计是否与源码一致。' if chinese else 'Regenerate with `python3 scripts/source_inventory.py --write`; `scripts/verify.py` checks that the inventory matches the source.') + '\n')


def update_section(path, data, chinese=False):
    text = path.read_text()
    if text.count(START) != 1 or text.count(END) != 1:
        raise ValueError('Expected one source inventory section in ' + str(path))
    start, end = text.index(START), text.index(END)
    if end < start:
        raise ValueError('Invalid source inventory section in ' + str(path))
    return text[:start] + render(data, chinese) + text[end:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    data = inventory()
    chinese = STRUCTURE.with_name('Structure.zh-CN.md')
    outputs = {OUTPUT: json.dumps(data, indent=2) + '\n',
               STRUCTURE: update_section(STRUCTURE, data),
               chinese: update_section(chinese, data, True)}
    if args.write:
        for path, content in outputs.items():
            path.write_text(content)
    else:
        stale = [str(p.relative_to(ROOT)) for p, c in outputs.items() if not p.exists() or p.read_text() != c]
        if stale:
            raise SystemExit('Stale source inventory: ' + ', '.join(stale) + '; run with --write and review the diff.')
    print(json.dumps(data))


if __name__ == '__main__':
    main()
