# Execution 的定义

[源码](Execution.lean) · [主定理导读](../../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-1cc3a3fe283668cf"></a>
## `CodedSorting.CommonMSDGlobalEntry.levels`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L496)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.CommonMSDRadixCost.depth q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDRadixCost.depth](../../Framework/RadixCost.definitions.md#def-a15d9000a7ef719c)

**基础库名称**

`Nat`
