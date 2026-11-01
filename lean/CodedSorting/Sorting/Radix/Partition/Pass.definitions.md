# Pass 的定义

[源码](Pass.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-a4a2740124386cfb"></a>
## `CodedSorting.Construction.Sorting.CommonMSDNodePass.instChunkSorterNormalized`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L6)

**类型**

```lean
CodedSorting.RadixNode.ChunkSorter CodedSorting.Construction.RecursiveParameters.Normalized
```

**定义**

```lean
{ space := CodedSorting.Construction.Sorting.CommonMSDChunks.space,
  charge := CodedSorting.Construction.Sorting.CommonMSDChunks.charge,
  program := CodedSorting.Construction.Sorting.CommonMSDChunks.program,
  program_charge_le := CodedSorting.Construction.Sorting.CommonMSDChunks.program_charge_le }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDChunks.program_charge_le](../SemanticCost.definitions.md#def-f26dec5f36f23e44)
- [CodedSorting.RadixNode.ChunkSorter.mk](Framework/Pass.definitions.md#def-950b58602165129a)
- [CodedSorting.RadixNode.ChunkSorter](Framework/Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.charge](../SemanticCost.definitions.md#def-b2f906314e475a2f)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.space](../SemanticCost.definitions.md#def-ca744a79f4318f82)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.program](../SemanticCost.definitions.md#def-ce459c3458041f1e)
