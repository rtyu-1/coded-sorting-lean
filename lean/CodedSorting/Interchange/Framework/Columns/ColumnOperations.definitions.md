# ColumnOperations 的定义

[源码](ColumnOperations.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-72d3a9464453bd7c"></a>
## `CodedSorting.CommonColumnSplit.address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnOperations.lean#L555)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → Fin (q.N ^ q.exponent)
```

**定义**

```lean
fun q source a => if h : source + a < q.N ^ q.exponent then ⟨source + a, h⟩ else ⟨0, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonColumnSplit.address._proof_4](ColumnOperations.definitions.md#def-b4dd00f80427859a)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `instOfNatNat`, `dite`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`

<a id="def-b4dd00f80427859a"></a>
## `CodedSorting.CommonColumnSplit.address._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ColumnOperations.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), ℕ → ℕ → 0 < q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `Monoid.toNatPow`, `Nat.instMonoidWithZero`, `MonoidWithZero.toMulZeroOneClass`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instPartialOrder`, `Zero.toOfNat0`, `instHPow`, `MulZeroOneClass.toMulZeroClass`, `OfNat.ofNat`, `MonoidWithZero.toMonoid`, `MulZeroClass.toZero`
