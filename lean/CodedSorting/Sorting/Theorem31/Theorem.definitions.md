# Theorem 的定义

[源码](Theorem.lean) · [主定理导读](Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-904d5ebbdf15ba2e"></a>
## `CodedSorting.Sorting.Theorem31.theorem_3_1`

主排序定理的完整声明；沿下面的项目定义继续展开输入、执行与资源条件。

[源码位置](Theorem.lean#L10)

**类型**

```lean
∀ (c : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) (N M B w : ℕ) (hN : 2 ≤ N) (hB : 0 < B) (hBM : 2 * B ≤ M) (hMN : M ≤ N)
  (hw : CodedSorting.WordConvention.Covers N w c) (hword : ↑w * Real.log 2 ≤ κ * Real.log ↑N),
  (∃ (hM : CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut c κ ≤ M),
      CodedSorting.Construction.Sorting.GeneralWordSorting.NormalGuarantee c κ hκ N M B w hN hB hBM hMN hM hw hword) ∨
    M < CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut c κ ∧
      CodedSorting.Construction.Sorting.GeneralWordSorting.SmallGuarantee c κ N M B w hB
```

**继续展开**

- [CodedSorting.Construction.Sorting.GeneralWordSorting.SmallGuarantee](Proof.definitions.md#def-43ffc9a7fd29c19d)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut](LargeMemory.definitions.md#def-f01e8967f500224d)
- [CodedSorting.WordConvention.Covers](../../Shared/Words/WordConvention.definitions.md#def-a9dbb84e85202da9)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.NormalGuarantee](Proof.definitions.md#def-0aeb97724b306816)

**基础库名称**

`Real.instLE`, `Real`, `HMul.hMul`, `Real.instZero`, `Exists`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.cast`, `Real.log`, `And`, `instNatAtLeastTwo`, `Nat`, `Real.instMul`, `LT.lt`, `Zero.toOfNat0`, `Or`, `instLTNat`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`
