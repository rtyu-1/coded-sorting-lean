# RadixCost 的定义

[源码](RadixCost.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-ceb2aa51e1b9fa44"></a>
## `CodedSorting.CommonMSDRecordDigits.wordDigit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RadixCost.lean#L404)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (base : ℕ) → 0 < base → ℕ → CodedSorting.WordControl.Word q.w → Fin base
```

**定义**

```lean
fun q base hb fuel x => CodedSorting.MSD.digit base hb fuel ↑x
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.MSD.digit](../Model/ExternalMSD.definitions.md#def-621d9c0b96834a0d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `Fin.val`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-49653fc97a33c8a2"></a>
## `CodedSorting.CommonMSDRowDirectory.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RadixCost.lean#L543)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin q.inventory.readers →
      K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
        (CodedSorting.WordControl.Word q.w → Fin K) →
          ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {K} q reader hfit key O L source scratch target =>
  CodedSorting.CommonIntervalCopy.code q reader (3 * O) 0 (3 * L) source scratch ++
    CodedSorting.CommonMSDDirectory.code q hfit key scratch L target
```

**继续展开**

- [CodedSorting.CommonIntervalCopy.code](../../../Shared/Memory/IntervalCopyBounds.definitions.md#def-873421a048c5b5e6)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonMSDDirectory.code](Directory.definitions.md#def-120095f3e5df81f1)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `instHMul`

<a id="def-f72ab7395f5a785c"></a>
## `CodedSorting.CommonMSDRadixCost.radixPositive`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RadixCost.lean#L671)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), 0 < CodedSorting.CommonMSDParameters.radix q
```

**定义**

```lean
fun q => lt_of_lt_of_le (of_decide_eq_true (id (Eq.refl true))) (CodedSorting.CommonMSDParameters.radix_two q)
```

**继续展开**

- [CodedSorting.CommonMSDParameters.radix_two](Directory.definitions.md#def-dc8222ade65c70b2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](Directory.definitions.md#def-c229910078c8e8d8)

**基础库名称**

`of_decide_eq_true`, `id`, `instOfNatNat`, `Bool.true`, `Nat.instPreorder`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `Eq.refl`, `instLTNat`, `OfNat.ofNat`, `Decidable.decide`, `Eq`, `lt_of_lt_of_le`

<a id="def-a15d9000a7ef719c"></a>
## `CodedSorting.CommonMSDRadixCost.depth`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RadixCost.lean#L673)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.GlobalSortingBound.depth (CodedSorting.CommonMSDParameters.radix q) q.w
```

**继续展开**

- [CodedSorting.GlobalSortingBound.depth](../../Bounds/GlobalSortingBound.definitions.md#def-82c139647b2d2e4e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](Directory.definitions.md#def-c229910078c8e8d8)

**基础库名称**

`Nat`

<a id="def-4246d329afb4786f"></a>
## `CodedSorting.CommonMSDPublicWordBounds.wordFactor`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RadixCost.lean#L725)

**类型**

```lean
ℝ → ℕ
```

**定义**

```lean
fun κ => max 1 ⌈κ⌉₊
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Real.partialOrder`, `Real`, `FloorRing.toFloorSemiring`, `Real.semiring`, `Nat.instMax_mathlib`, `Real.instFloorRing`, `Real.instRing`, `instOfNatNat`, `Max.max`, `Nat`, `Nat.ceil`, `OfNat.ofNat`, `Real.linearOrder`, `Real.instIsStrictOrderedRing`
