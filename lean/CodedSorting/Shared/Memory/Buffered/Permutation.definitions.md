# Permutation 的定义

[源码](Permutation.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-7b06574df737f80c"></a>
## `CodedSorting.CommonBufferedCosts.rawCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Permutation.lean#L104)

**类型**

```lean
{V K L : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin V ≃ Fin K × Fin L → Fin V ≃ Fin K × Fin L → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V K L} q hfit reader input output source arena =>
  (CodedSorting.CommonBufferedDistribution.program q hfit reader input source fun k j =>
      CodedSorting.CommonPermutationPairs.address q arena (↑k * CodedSorting.CommonPermutationPairs.count q L + j)) ++
    CodedSorting.CommonBufferedGather.code q hfit reader output arena source
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonBufferedGather.code](GatherProgram.definitions.md#def-846da812fe155804)
- [CodedSorting.CommonPermutationPairs.address](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-841830e6780927fe)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBufferedDistribution.program](DistributionCorrectness.definitions.md#def-95c9c92d87ae04e4)
- [CodedSorting.CommonPermutationPairs.count](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Equiv`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `Prod`, `Fin`, `HAppend.hAppend`, `instHMul`

<a id="def-c705e7b426b934c0"></a>
## `CodedSorting.CommonBufferedCosts.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Permutation.lean#L113)

**类型**

```lean
{V K L : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin V ≃ Fin K × Fin L → Fin V ≃ Fin K × Fin L → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V K L} q hfit reader input output source arena =>
  CodedSorting.CommonStaticFusion.fuse q
    (CodedSorting.CommonBufferedCosts.rawCode q hfit reader input output source arena)
```

**继续展开**

- [CodedSorting.CommonStaticFusion.fuse](../../Programs/Static/Fusion.definitions.md#def-a8d53d872c4a7e53)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBufferedCosts.rawCode](Permutation.definitions.md#def-7b06574df737f80c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Equiv`, `instMulNat`, `LE.le`, `instLENat`, `List`, `Nat`, `Prod`, `Fin`, `instHMul`
