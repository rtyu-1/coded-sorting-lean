# MarginsRecords 的定义

[源码](MarginsRecords.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-299c5b27906f0156"></a>
## `CodedSorting.CommonStaticMargins.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginsRecords.lean#L15)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader L N R O source target =>
  CodedSorting.CommonStaticMarginGather.code q reader (CodedSorting.CommonMarginTransform.scheme q)
    (CodedSorting.CommonMarginTransform.shape q L N R O) source target
```

**继续展开**

- [CodedSorting.CommonMarginTransform.scheme](../../Memory/MarginTransform.definitions.md#def-6fd80bba14bc47a7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonMarginTransform.shape](../../Memory/MarginTransform.definitions.md#def-5233771e9df465d1)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticMarginGather.code](MarginGather.definitions.md#def-2bd16bea3675aa9e)

**基础库名称**

`List`, `Nat`, `Fin`

<a id="def-513df08f5eb2dd0d"></a>
## `CodedSorting.CommonStaticMargins.ShapeFits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginsRecords.lean#L20)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → Prop
```

**定义**

```lean
fun q L N R O =>
  L < (2 ^ q.w) ^ q.digits ∧ N < (2 ^ q.w) ^ q.digits ∧ R < (2 ^ q.w) ^ q.digits ∧ O < (2 ^ q.w) ^ q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `And`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-5b243d9616c260d3"></a>
## `CodedSorting.CommonStaticMarginsRecords.margin`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginsRecords.lean#L142)

**类型**

```lean
{w K : ℕ} →
  (L N R O : ℕ) →
    O + N ≤ K → (Fin K → CodedSorting.KeyRecordWords.Record w) → Fin (L + N + R) → CodedSorting.KeyRecordWords.Record w
```

**定义**

```lean
fun {w K} L N R O h f i =>
  if hl : ↑i < L then CodedSorting.KeyRecordWords.Record.bottom
  else if hu : ↑i < L + N then f ⟨O + (↑i - L), ⋯⟩ else CodedSorting.KeyRecordWords.Record.top
```

**继续展开**

- [CodedSorting.CommonStaticMarginsRecords.margin._proof_2](MarginsRecords.definitions.md#def-0c9679bd4c53030c)
- [CodedSorting.KeyRecordWords.Record](../../Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](../../Records/KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.KeyRecordWords.Record.top](../../Records/KeyRecordWords.definitions.md#def-dfff22d085934d4b)

**基础库名称**

`HSub.hSub`, `Fin.mk`, `instSubNat`, `LE.le`, `instLENat`, `Fin.val`, `dite`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instLTNat`, `Fin`, `Not`

<a id="def-0c9679bd4c53030c"></a>
## `CodedSorting.CommonStaticMarginsRecords.margin._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MarginsRecords.lean)

**类型**

```lean
∀ {K : ℕ} (L N R O : ℕ), O + N ≤ K → ∀ (i : Fin (L + N + R)), ¬↑i < L → ↑i < L + N → O + (↑i - L) < K
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HSub.hSub`, `instSubNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`, `Not`
