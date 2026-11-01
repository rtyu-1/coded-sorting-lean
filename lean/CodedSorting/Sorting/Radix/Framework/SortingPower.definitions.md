# SortingPower 的定义

[源码](SortingPower.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-162ad3c71821ad20"></a>
## `CodedSorting.CommonMSDSortingRun.output`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SortingPower.lean#L17)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  List (CodedSorting.KeyRecordWords.Record q.w) → List (CodedSorting.KeyRecordWords.Record q.w)
```

**定义**

```lean
fun q xs =>
  CodedSorting.CommonMSDSemantics.recordSort q.w (CodedSorting.CommonMSDParameters.radix q) ⋯ q.height ⋯
    (CodedSorting.CommonMSDGlobalEntry.levels q) xs
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDGlobalEntry.levels](../Program/Framework/Execution.definitions.md#def-1cc3a3fe283668cf)
- [CodedSorting.CommonMSDSemantics.recordSort](Chunks.definitions.md#def-1ce5b05bacc178bb)
- [CodedSorting.CommonMSDParameters.radix](Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonMSDRadixCost.radixPositive](RadixCost.definitions.md#def-f72ab7395f5a785c)
- [CodedSorting.CommonLocalRecursion.height_pos](../../Local/Framework/Program.definitions.md#def-3d224d9e59995f0f)

**基础库名称**

`List`
