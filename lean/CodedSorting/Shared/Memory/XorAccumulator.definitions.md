# XorAccumulator 的定义

[源码](XorAccumulator.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-0235e8cfbceff142"></a>
## `CodedSorting.CommonXorAccumulator.foldCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](XorAccumulator.lean#L16)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → List ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader V scratch sources =>
  List.flatMap (fun source => CodedSorting.CommonStaticXor.code q reader V scratch source scratch) sources
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticXor.code](../Programs/Static/Xor.definitions.md#def-f5c3d4facfcfece0)

**基础库名称**

`List`, `Nat`, `Fin`, `List.flatMap`

<a id="def-0b3750a8a06a174e"></a>
## `CodedSorting.CommonXorAccumulator.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](XorAccumulator.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → List ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader V scratch sources =>
  CodedSorting.CommonStaticXor.code q reader V scratch scratch scratch ++
    CodedSorting.CommonXorAccumulator.foldCode q reader V scratch sources
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticXor.code](../Programs/Static/Xor.definitions.md#def-f5c3d4facfcfece0)
- [CodedSorting.CommonXorAccumulator.foldCode](XorAccumulator.definitions.md#def-0235e8cfbceff142)

**基础库名称**

`instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `Fin`, `HAppend.hAppend`
