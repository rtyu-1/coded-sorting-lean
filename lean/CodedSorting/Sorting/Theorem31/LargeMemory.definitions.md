# LargeMemory 的定义

[源码](LargeMemory.lean) · [主定理导读](Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-b2f4a9d1d544b1ef"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.inventory`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LargeMemory.lean#L16)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory
```

**定义**

```lean
{ readers := 1, writers := 0, keys := 0, pc := 0,
  ratio :=
    CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount }
```

**继续展开**

- [CodedSorting.PhysicalLeafParameters.minimumRatio](../../Shared/Memory/EdgeReadBit.definitions.md#def-5b3ccb2ea10f8cb1)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.SortingResourceBudget.Inventory.mk](../Bounds/SortingResourceBudget.definitions.md#def-0e997c35e77a1441)
- [CodedSorting.SortingResourceBudget.Inventory](../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-e88d6c67523dff28"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LargeMemory.lean#L24)

**类型**

```lean
ℝ → ℕ
```

**定义**

```lean
fun κ =>
  CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent
    (CodedSorting.CommonMSDPublicWordBounds.wordFactor κ)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent](../Execution/AllInputPhysical.definitions.md#def-7f70c65dfd9697d3)
- [CodedSorting.CommonMSDPublicWordBounds.wordFactor](../Radix/Framework/RadixCost.definitions.md#def-4246d329afb4786f)

**基础库名称**

`Real`, `Nat`

<a id="def-715398975901f705"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.digits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LargeMemory.lean#L25)

**类型**

```lean
ℕ → ℝ → ℕ
```

**定义**

```lean
fun c κ =>
  CodedSorting.SortingResourceBudget.digits c (CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent κ)
```

**继续展开**

- [CodedSorting.SortingResourceBudget.digits](../Bounds/SortingResourceBudget.definitions.md#def-ea371db150e4467a)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent](LargeMemory.definitions.md#def-e88d6c67523dff28)

**基础库名称**

`Real`, `Nat`

<a id="def-391a7b1a2006d0d2"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.reserveSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LargeMemory.lean#L26)

**类型**

```lean
ℕ → ℝ → ℕ
```

**定义**

```lean
fun c κ =>
  CodedSorting.SortingResourceBudget.reserve CodedSorting.Construction.Sorting.GeneralWordNormalSorting.inventory c
    (CodedSorting.Construction.Sorting.GeneralWordNormalSorting.digits c κ)
```

**继续展开**

- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.inventory](LargeMemory.definitions.md#def-b2f4a9d1d544b1ef)
- [CodedSorting.SortingResourceBudget.reserve](../Bounds/SortingResourceBudget.definitions.md#def-9e7e2eeee9930238)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.digits](LargeMemory.definitions.md#def-715398975901f705)

**基础库名称**

`Real`, `Nat`

<a id="def-f01e8967f500224d"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LargeMemory.lean#L28)

**类型**

```lean
ℕ → ℝ → ℕ
```

**定义**

```lean
fun c κ => CodedSorting.Construction.Sorting.GeneralWordNormalSorting.reserveSize c κ ^ 2
```

**继续展开**

- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.reserveSize](LargeMemory.definitions.md#def-391a7b1a2006d0d2)

**基础库名称**

`Real`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-7ec8595f8cc1576a"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LargeMemory.lean#L30)

**类型**

```lean
(c : ℕ) →
  (κ : ℝ) →
    (N M B w : ℕ) →
      2 ≤ N →
        0 < B →
          2 * B ≤ M →
            M ≤ N →
              CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut c κ ≤ M →
                CodedSorting.WordConvention.Covers N w c → CodedSorting.CommonSortingNormalization.Configuration
```

**定义**

```lean
fun c κ N M B w hN hB hBM hMN hM hw =>
  { inventory := CodedSorting.Construction.Sorting.GeneralWordNormalSorting.inventory, N := N, M := M, B := B, w := w,
    c := c, exponent := CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent κ, input_large := hN,
    memory_input := hMN, block_pos := hB, block_memory := hBM, exponent_pos := ⋯, word_convention := hw,
    memory_large := hM }
```

**继续展开**

- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut](LargeMemory.definitions.md#def-f01e8967f500224d)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.inventory](LargeMemory.definitions.md#def-b2f4a9d1d544b1ef)
- [CodedSorting.CommonSortingNormalization.Configuration.mk](../Resources/Framework/NormalizationFrames.definitions.md#def-fedce2cf7e9f973a)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent](LargeMemory.definitions.md#def-e88d6c67523dff28)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.WordConvention.Covers](../../Shared/Words/WordConvention.definitions.md#def-a9dbb84e85202da9)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration._proof_2](LargeMemory.definitions.md#def-c8ddf540f75c58d4)

**基础库名称**

`Real`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-4feabc92be03297f"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LargeMemory.lean#L49)

**类型**

```lean
(c : ℕ) →
  (κ : ℝ) →
    0 ≤ κ →
      (N M B w : ℕ) →
        (hN : 2 ≤ N) →
          (hB : 0 < B) →
            (hBM : 2 * B ≤ M) →
              (hMN : M ≤ N) →
                (hM : CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut c κ ≤ M) →
                  (hw : CodedSorting.WordConvention.Covers N w c) →
                    ↑w * Real.log 2 ≤ κ * Real.log ↑N →
                      CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters
                        (CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration c κ N M B w hN hB hBM
                          hMN hM hw)
```

**定义**

```lean
fun c κ hκ N M B w hN hB hBM hMN hM hw hword =>
  { reader := ⟨0, ⋯⟩, ratio := CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_5,
    kappa := κ, kappa_nonnegative := hκ, word_bound := hword, exponent := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_5](LargeMemory.definitions.md#def-e2588d21b4979085)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut](LargeMemory.definitions.md#def-f01e8967f500224d)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](../Execution/AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.mk](../Execution/AllInputPhysical.definitions.md#def-d7904f0dfd436a54)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_6](LargeMemory.definitions.md#def-8cbcf97cacd1703b)
- [CodedSorting.WordConvention.Covers](../../Shared/Words/WordConvention.definitions.md#def-a9dbb84e85202da9)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_4](LargeMemory.definitions.md#def-2e05593ca7050545)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_3](LargeMemory.definitions.md#def-8075cfb9314819b0)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration](LargeMemory.definitions.md#def-7ec8595f8cc1576a)

**基础库名称**

`Real.instLE`, `Real`, `HMul.hMul`, `Real.instZero`, `Fin.mk`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.cast`, `Real.log`, `instNatAtLeastTwo`, `Nat`, `Real.instMul`, `LT.lt`, `Zero.toOfNat0`, `instLTNat`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-cbf3356fe3cb2b34"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LargeMemory.lean#L62)

**类型**

```lean
ℕ → ℝ → ℝ
```

**定义**

```lean
fun c κ =>
  2 * ↑(CodedSorting.Construction.Sorting.GeneralWordNormalSorting.reserveSize c κ) ^ 2 *
      (1 + Real.log (2 * ↑(CodedSorting.Construction.Sorting.GeneralWordNormalSorting.reserveSize c κ)) / Real.log 2) ^
        2 *
    (12 * 22194000000 *
          CodedSorting.GlobalSortingBound.rateConstant CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K
            CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau *
        (κ *
            (1 + Real.log (4 * ↑(CodedSorting.Construction.Sorting.GeneralWordNormalSorting.digits c κ)) / Real.log 2) +
          2) +
      2 * 16)
```

**继续展开**

- [CodedSorting.GlobalSortingBound.rateConstant](../Bounds/GlobalSortingBound.definitions.md#def-62c2c2bf2fffe5cf)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient._proof_9](LargeMemory.definitions.md#def-89b8ccdc560a5375)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient._proof_8](LargeMemory.definitions.md#def-7c4df708c620b8ff)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient._proof_10](LargeMemory.definitions.md#def-f55be58ae3b1a548)
- [CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K](../Local/CostBound.definitions.md#def-5fb3aac9f5fefeed)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient._proof_7](LargeMemory.definitions.md#def-34077cbb7ecfcfc6)
- [CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau](../Local/CostBound.definitions.md#def-b1cf14663ae7df26)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.digits](LargeMemory.definitions.md#def-715398975901f705)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.reserveSize](LargeMemory.definitions.md#def-391a7b1a2006d0d2)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_3](LargeMemory.definitions.md#def-8075cfb9314819b0)

**基础库名称**

`Real`, `instHDiv`, `HMul.hMul`, `Real.instDivInvMonoid`, `Monoid.toNatPow`, `HDiv.hDiv`, `instOfNatNat`, `Nat.cast`, `Real.log`, `Real.instAdd`, `Real.instOne`, `Real.instMonoid`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `DivInvMonoid.toDiv`, `One.toOfNat1`, `instHPow`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-f55be58ae3b1a548"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
(14 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-34077cbb7ecfcfc6"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
(10 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-7c4df708c620b8ff"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
(22193999998 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-89b8ccdc560a5375"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
(2 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-c8ddf540f75c58d4"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
ℕ → ∀ (κ : ℝ), ℕ → ℕ → ℕ → 1 ≤ CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent κ
```

**继续展开**

- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent](LargeMemory.definitions.md#def-e88d6c67523dff28)

**基础库名称**

`Real`, `Preorder.toLE`, `instOfNatNat`, `LE.le`, `Nat.instPreorder`, `Nat`, `OfNat.ofNat`

<a id="def-8075cfb9314819b0"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
(0 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-2e05593ca7050545"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
∀ (c : ℕ) (κ : ℝ) (N M B w : ℕ) (hN : 2 ≤ N) (hB : 0 < B) (hBM : 2 * B ≤ M) (hMN : M ≤ N)
  (hM : CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut c κ ≤ M)
  (hw : CodedSorting.WordConvention.Covers N w c),
  0 <
    (CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration c κ N M B w hN hB hBM hMN hM
          hw).inventory.readers
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut](LargeMemory.definitions.md#def-f01e8967f500224d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.WordConvention.Covers](../../Shared/Words/WordConvention.definitions.md#def-a9dbb84e85202da9)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration](LargeMemory.definitions.md#def-7ec8595f8cc1576a)

**基础库名称**

`Real`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-e2588d21b4979085"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
    CodedSorting.Construction.streamCount ≤
  CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
    CodedSorting.Construction.streamCount
```

**继续展开**

- [CodedSorting.PhysicalLeafParameters.minimumRatio](../../Shared/Memory/EdgeReadBit.definitions.md#def-5b3ccb2ea10f8cb1)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Preorder.toLE`, `instOfNatNat`, `LE.le`, `Nat.instPreorder`, `Nat`, `OfNat.ofNat`

<a id="def-8cbcf97cacd1703b"></a>
## `CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LargeMemory.lean)

**类型**

```lean
∀ (κ : ℝ),
  CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent
      (CodedSorting.CommonMSDPublicWordBounds.wordFactor κ) ≤
    CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent
      (CodedSorting.CommonMSDPublicWordBounds.wordFactor κ)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent](../Execution/AllInputPhysical.definitions.md#def-7f70c65dfd9697d3)
- [CodedSorting.CommonMSDPublicWordBounds.wordFactor](../Radix/Framework/RadixCost.definitions.md#def-4246d329afb4786f)

**基础库名称**

`Real`, `Preorder.toLE`, `LE.le`, `Nat.instPreorder`, `Nat`
