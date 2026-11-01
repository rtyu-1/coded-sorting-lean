#!/usr/bin/env python3
"""Build a source-linked reference from Lean's transitive definition export."""
from pathlib import Path
import argparse,collections,gzip,hashlib,json,os,re
ROOT=Path(__file__).resolve().parents[1]
ROOT_NAME='CodedSorting.Sorting.Theorem31.theorem_3_1'

def read_records(path):
    records=[];total=None
    for line in path.read_text().splitlines():
        if 'CS_DEFINITION {' in line:records.append(json.loads(line.split('CS_DEFINITION ',1)[1]))
        elif 'CS_DEFINITION_TOTAL ' in line:total=int(line.split('CS_DEFINITION_TOTAL ',1)[1])
    if total!=len(records):raise ValueError('Incomplete compiler output')
    names={x['name'] for x in records}
    if len(names)!=len(records) or ROOT_NAME not in names:raise ValueError('Missing or duplicated declarations')
    unresolved={(x['name'],n) for x in records for n in x['project_dependencies'] if n not in names}
    if unresolved:raise ValueError('Unresolved project definitions: '+str(sorted(unresolved)))
    unsupported=[x['name'] for x in records if x['kind'] in {'axiom','opaque'}]
    if unsupported:raise ValueError('Project axioms/opaque declarations require review: '+str(unsupported))
    return records

def anchor(name):return 'def-'+hashlib.sha256(name.encode()).hexdigest()[:16]
def path_of(x):return ROOT.joinpath(*x['module'].split('.')).with_suffix('.lean')
def ref_of(x):return path_of(x).with_suffix('.definitions.md')
def rel(a,b):return Path(os.path.relpath(b,a.parent)).as_posix()
def link(a,x):return f'[{x["name"]}]({rel(a,ref_of(x))}#{anchor(x["name"])})'

def source_excerpt(x):
    p=path_of(x);lines=p.read_text().splitlines();s=x['source_line'];e=x['source_end_line']
    if not s or not e:return ''
    return '\n'.join(lines[max(0,s-1):e])

def explain(x,known):
    n=x['name'];short=n.rsplit('.',1)[-1]
    if x['kind']=='root_theorem':return '主排序定理的完整声明；沿下面的项目定义继续展开输入、执行与资源条件。'
    if x['kind']=='checked_lemma':return '已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。'
    if x['kind']=='inductive':return '下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。'
    if x['kind']=='constructor':return '按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。'
    if x['kind']=='recursor':return 'Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。'
    parent=n.rsplit('.',1)[0]
    if parent in known and known[parent]['kind']=='inductive':return f'读取 `{parent}` 的 `{short}` 字段。下面的函数说明怎样从结构中取出这个字段。'
    if '.match_' in n:return 'Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。'
    if short in {'casesOn','recOn','brecOn','below'}:return 'Lean 生成的分情况或递归辅助函数，依据同一归纳类型的构造规则工作。'
    if 'FiniteCertificate' in n:return '这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。'
    if x['value'].lstrip().startswith('Classical.choose') or ':= Classical.choose' in source_excerpt(x):return '从已证明的存在性命题中选取一个满足条件的对象。下面链接的命题列出选取条件；阅读时需要看清先选取对象、后允许哪些参数变化。'
    return '下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。'

def build(records,output,generate):
    known={x['name']:x for x in records};modules=collections.defaultdict(list)
    for x in records:
        if not x.get('module'):raise ValueError('No source module for '+x['name'])
        if not path_of(x).exists():raise ValueError('Missing source '+str(path_of(x)))
        modules[x['module']].append(x)
    foundation=sorted({n for x in records for n in x['foundation_dependencies']})
    record={'root':ROOT_NAME,'declarations':records,'foundation_dependencies':foundation,
            'source_sha256':{str(path_of(xs[0]).relative_to(ROOT)):hashlib.sha256(path_of(xs[0]).read_bytes()).hexdigest() for xs in modules.values()}}
    stats={'root':ROOT_NAME,'declarations':len(records),'kinds':dict(collections.Counter(x['kind'] for x in records)),
           'source_modules':len(modules),'project_edges':sum(len(x['project_dependencies']) for x in records),
           'foundation_constants':len(foundation),'unresolved_project_dependencies':0,'project_axioms':0,'project_opaque_declarations':0}
    output.mkdir(parents=True,exist_ok=True)
    (output/'definition-closure.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
    (output/'definition-check.json').write_text(json.dumps(stats,ensure_ascii=False,indent=2)+'\n')
    if generate:
        intro=ROOT/'CodedSorting/Sorting/Theorem31/Definitions.zh-CN.md'
        foundation_page=ROOT/'docs/FoundationDefinitions.zh-CN.md'
        for module,xs in sorted(modules.items()):
            dest=ref_of(xs[0]);src=path_of(xs[0]);rows=[f'# {src.stem} 的定义','',f'[源码]({rel(dest,src)}) · [主定理导读]({rel(dest,intro)}) · [基础概念]({rel(dest,foundation_page)})','',
              '本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。','']
            for x in sorted(xs,key=lambda x:(x['source_line'] or 10**9,x['name'])):
                rows += [f'<a id="{anchor(x["name"])}"></a>',f'## `{x["name"]}`','',explain(x,known),'']
                suffix='#L'+str(x['source_line']) if x['source_line'] else ''
                rows += [f'[源码位置]({rel(dest,src)}{suffix})','', '**类型**','', '```lean',x['type'],'```','']
                if x['kind']=='definition':
                    value=x['value']
                    if len(value)<=16000:rows += ['**定义**','','```lean',value,'```','']
                    else:rows += ['**定义**','',f'此定义包含较长的固定数据或构造表达式，完整内容见[源码]({rel(dest,src)}{suffix})。其全部自定义依赖仍列在下面。','']
                if x['project_dependencies']:rows += ['**继续展开**','',*['- '+link(dest,known[n]) for n in x['project_dependencies']],'']
                else:rows += ['此声明没有进一步的项目自定义依赖。','']
                if x['foundation_dependencies']:rows += ['**基础库名称**','',', '.join('`'+n+'`' for n in x['foundation_dependencies']), '']
            dest.write_text('\n'.join(rows))
        index=ROOT/'docs/DefinitionIndex.zh-CN.md'
        rows=['# 主排序定理的全部定义','',f'从 `{ROOT_NAME}` 的类型出发，共找到 {len(records)} 项声明，分布于 {len(modules)} 个源码模块。所有项目依赖均有对应条目。','',
              '[按模块查找定义](../CodedSorting/Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](FoundationDefinitions.zh-CN.md) · [机器可读记录](definition-closure.json.gz)','',
              '| 模块 | 声明数 |','| --- | ---: |']
        rows += [f'| [{m}]({rel(index,ref_of(xs[0]))}) | {len(xs)} |' for m,xs in sorted(modules.items())]
        index.write_text('\n'.join(rows)+'\n')
        (ROOT/'docs/definition-closure.json.gz').write_bytes(gzip.compress((json.dumps(record,ensure_ascii=False,indent=2)+'\n').encode(),mtime=0))
        (ROOT/'docs/definition-check.json').write_text(json.dumps(stats,ensure_ascii=False,indent=2)+'\n')
    return stats

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('log',type=Path);p.add_argument('--output',type=Path,default=ROOT/'reports');p.add_argument('--generate',action='store_true');a=p.parse_args()
    print(json.dumps(build(read_records(a.log),a.output,a.generate),ensure_ascii=False,indent=2))
