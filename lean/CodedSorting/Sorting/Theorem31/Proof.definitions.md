# Proof 的定义

[源码](Proof.lean) · [主定理导读](Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-a7daccfa04d52195"></a>
## `CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Proof.lean#L19)

**类型**

```lean
ℕ → ℝ → ℝ
```

**定义**

```lean
fun c κ =>
  max 1
    (max (CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient c κ)
      (max
        (5000 * ↑(CodedSorting.SmallMemorySortingRate.wordFactor κ) *
          ↑(CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut c κ))
        (305 * (↑c + 2) * ↑(CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut c κ))))
```

**继续展开**

- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.coefficient](LargeMemory.definitions.md#def-cbf3356fe3cb2b34)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient._proof_3](Proof.definitions.md#def-ba5619114fdfa876)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient._proof_1](Proof.definitions.md#def-c2477643a3867fef)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut](LargeMemory.definitions.md#def-f01e8967f500224d)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient._proof_2](Proof.definitions.md#def-682184f5a736c522)
- [CodedSorting.SmallMemorySortingRate.wordFactor](../SmallMemory/SmallMemoryPhysicalRate.definitions.md#def-3ce136832ceec971)

**基础库名称**

`Real`, `HMul.hMul`, `Nat.cast`, `Real.instAdd`, `Real.instOne`, `instHAdd`, `Real.instMax`, `HAdd.hAdd`, `Max.max`, `Nat`, `Real.instMul`, `One.toOfNat1`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-31b7c9a7aad80a45"></a>
## `CodedSorting.Construction.Sorting.GeneralWordSorting.factor`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Proof.lean#L27)

**类型**

```lean
ℕ → ℕ → ℕ → ℝ
```

**定义**

```lean
fun N M B =>
  CodedSorting.SmallMemorySortingRate.paperFactor N M B CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau
    ↑CodedSorting.Construction.epsilon
```

**继续展开**

- [CodedSorting.SmallMemorySortingRate.paperFactor](../SmallMemory/SmallMemoryPhysicalRate.definitions.md#def-5af158548a3f45f0)
- [CodedSorting.Construction.epsilon](../../Circuit/Parameters/Exponent.definitions.md#def-38e0b13c0209d8a9)
- [CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau](../Local/CostBound.definitions.md#def-b1cf14663ae7df26)

**基础库名称**

`Real`, `Real.instRatCast`, `Rat.cast`, `Nat`

<a id="def-0aeb97724b306816"></a>
## `CodedSorting.Construction.Sorting.GeneralWordSorting.NormalGuarantee`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Proof.lean#L44)

**类型**

```lean
(c : ℕ) →
  (κ : ℝ) →
    0 ≤ κ →
      (N M B w : ℕ) →
        2 ≤ N →
          0 < B →
            2 * B ≤ M →
              M ≤ N →
                CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut c κ ≤ M →
                  CodedSorting.WordConvention.Covers N w c → ↑w * Real.log 2 ≤ κ * Real.log ↑N → Prop
```

**定义**

```lean
fun c κ hκ N M B w hN hB hBM hMN hM hw hword =>
  let q := CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration c κ N M B w hN hB hBM hMN hM hw;
  let p :=
    CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters c κ hκ N M B w hN hB hBM hMN hM hw hword;
  ∀ (store : CodedSorting.CommonLeafProgram.Store q)
    (disk : CodedSorting.CommonNormalizationController.Disk (q.N ^ q.exponent) q.B q.w)
    (xs : List (CodedSorting.WordControl.Word w)),
    xs.length = N →
      CodedSorting.CommonIntegerPhysical.InputFile q disk xs →
        ∃ fuel,
          let prog :=
            CodedSorting.CommonSortingNormalization.program q
              (CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm q p);
          let s := CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.start q p store disk;
          let blocks := CodedSorting.CommonIntegerPhysical.blocks q q.N;
          let result := CodedSorting.CommonNormalizationController.run prog (blocks + 1 + fuel + 1 + blocks + 1) s;
          (∀ (i : Fin (CodedSorting.CommonIntegerFile.output q xs).length),
              CodedSorting.CommonNormalizationController.outputWord prog result.1 ↑i =
                (CodedSorting.CommonIntegerFile.output q xs).get i) ∧
            (CodedSorting.CommonIntegerFile.output q xs).Perm xs ∧
              List.Pairwise (fun x1 x2 => x1 ≤ x2) (CodedSorting.CommonIntegerFile.output q xs) ∧
                CodedSorting.CommonNormalizationController.step prog result.1 = (result.1, 0) ∧
                  Fintype.card (CodedSorting.CommonSortingNormalization.ResidentIndex q) ≤ M ∧
                    Fintype.card (CodedSorting.CommonNormalizationController.Address (q.N ^ q.exponent)) ≤
                        N ^ (CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent κ + 2) ∧
                      Fintype.card (CodedSorting.CommonNormalizationController.Address (q.N ^ q.exponent)) * B ≤
                          N ^ (CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent κ + 3) ∧
                        ↑result.2 ≤
                          CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient c κ * (↑N / ↑B) *
                            CodedSorting.Construction.Sorting.GeneralWordSorting.factor N M B
```

**继续展开**

- [CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient._proof_3](Proof.definitions.md#def-ba5619114fdfa876)
- [CodedSorting.CommonNormalizationController.State](../../Shared/Memory/NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.Program](../../Shared/Memory/NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.CommonNormalizationController.Disk](../../Shared/Memory/NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.CommonNormalizationController.Address](../../Shared/Memory/NormalizationController.definitions.md#def-1cfe9467af4437b1)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.Mcut](LargeMemory.definitions.md#def-f01e8967f500224d)
- [CodedSorting.CommonNormalizationController.run](../../Shared/Memory/NormalizationController.definitions.md#def-264bc12b56c5844a)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](../Execution/AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.exponent](LargeMemory.definitions.md#def-e88d6c67523dff28)
- [CodedSorting.CommonIntegerFile.output](../Execution/Framework/File.definitions.md#def-22e1c41173dbab7f)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.parameters](LargeMemory.definitions.md#def-4feabc92be03297f)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.ResidentIndex](../Resources/Framework/NormalizationFrames.definitions.md#def-8a95fd2c7fba5be8)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient](Proof.definitions.md#def-a7daccfa04d52195)
- [CodedSorting.CommonNormalizationController.outputWord](../../Shared/Memory/NormalizationController.definitions.md#def-2e4323c264f6c9d9)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.factor](Proof.definitions.md#def-31b7c9a7aad80a45)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.program](../Resources/Framework/NormalizationFrames.definitions.md#def-0d844079adca6559)
- [CodedSorting.CommonNormalizationController.step](../../Shared/Memory/NormalizationController.definitions.md#def-35b0e81743543f27)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.start](../Execution/AllInputPhysical.definitions.md#def-93ed69328300992d)
- [CodedSorting.WordConvention.Covers](../../Shared/Words/WordConvention.definitions.md#def-a9dbb84e85202da9)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm](../Execution/AllInputPhysical.definitions.md#def-b74db009407c6497)
- [CodedSorting.CommonSortingNormalization.MachineState](../Resources/Framework/NormalizationFrames.definitions.md#def-90721c68825dbf3f)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonIntegerPhysical.InputFile](../Execution/Framework/PhysicalHalted.definitions.md#def-d768a06a6e018cb4)
- [CodedSorting.CommonIntegerPhysical.blocks](../Execution/Framework/PhysicalHalted.definitions.md#def-129cc4c709eafa04)
- [CodedSorting.Construction.Sorting.GeneralWordNormalSorting.configuration](LargeMemory.definitions.md#def-7ec8595f8cc1576a)
- [CodedSorting.CommonSortingNormalization.Configuration.B](../Resources/Framework/NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Real.instLE`, `Real`, `instFintypeSum`, `instHDiv`, `HMul.hMul`, `List.Pairwise`, `Real.instZero`, `List.get`, `Nat.instMonoid`, `Real.instDivInvMonoid`, `Exists`, `Monoid.toNatPow`, `Fintype.card`, `Sum`, `HDiv.hDiv`, `Prod.mk`, `List.Perm`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Nat.cast`, `Real.log`, `Prod.fst`, `instLEFin`, `Fin.fintype`, `List`, `instHAdd`, `And`, `instNatAtLeastTwo`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `LT.lt`, `DivInvMonoid.toDiv`, `instAddNat`, `Zero.toOfNat0`, `instHPow`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `List.length`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-2e5aa059ace77602"></a>
## `CodedSorting.Construction.Sorting.GeneralWordSorting.smallSpaceBound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Proof.lean#L86)

**类型**

```lean
ℕ → ℝ → ℕ → ℕ
```

**定义**

```lean
fun c κ N => (N + 13 + 6 * N ^ (2 * CodedSorting.SmallMemorySortingRate.wordFactor κ)) * N + (2 * c + 16) * N ^ 2
```

**继续展开**

- [CodedSorting.SmallMemorySortingRate.wordFactor](../SmallMemory/SmallMemoryPhysicalRate.definitions.md#def-3ce136832ceec971)

**基础库名称**

`Real`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-43ffc9a7fd29c19d"></a>
## `CodedSorting.Construction.Sorting.GeneralWordSorting.SmallGuarantee`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Proof.lean#L89)

**类型**

```lean
ℕ → ℝ → ℕ → ℕ → (B : ℕ) → ℕ → 0 < B → Prop
```

**定义**

```lean
fun c κ N M B w hB =>
  ∃ code allocation output,
    CodedSorting.TwoWordSmallMemoryFootprint.BoundedCode allocation code ∧
      allocation * B ≤ CodedSorting.Construction.Sorting.GeneralWordSorting.smallSpaceBound c κ N ∧
        ∀ (s : CodedSorting.TwoWordBlockLift.State B (CodedSorting.WordControl.Word w))
          (xs : List (CodedSorting.WordControl.Word w)),
          xs.length = N →
            CodedSorting.TwoWordBlockFormat.File hB s.disk xs →
              ∃ t cost,
                CodedSorting.TwoWordSmallMemorySorting.Executes hB code s t cost ∧
                  CodedSorting.TwoWordBlockFormat.File hB t.disk (output xs) ∧
                    (output xs).Perm xs ∧
                      List.Pairwise (fun x y => ↑x ≤ ↑y) (output xs) ∧
                        Fintype.card (Fin B ⊕ Fin B) ≤ M ∧
                          ↑cost ≤
                            CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient c κ * (↑N / ↑B) *
                              CodedSorting.Construction.Sorting.GeneralWordSorting.factor N M B
```

**继续展开**

- [CodedSorting.TwoWordSmallMemorySorting.Executes](../SmallMemory/SmallMemorySorting.definitions.md#def-1a41d1fc1b157ab5)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.TwoWordRadixInsert.Word](../SmallMemory/Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemoryFootprint.BoundedCode](../SmallMemory/PublicUnrolledBlockSort.definitions.md#def-1ba4ebc7d39a7d39)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](../SmallMemory/SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordBlockLift.State](../SmallMemory/SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient](Proof.definitions.md#def-a7daccfa04d52195)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.smallSpaceBound](Proof.definitions.md#def-2e5aa059ace77602)
- [CodedSorting.Construction.Sorting.GeneralWordSorting.factor](Proof.definitions.md#def-31b7c9a7aad80a45)
- [CodedSorting.TwoWordBlockLift.State.disk](../SmallMemory/SmallSort.definitions.md#def-1abac0bb04792a30)
- [CodedSorting.TwoWordBlockFormat.File](../SmallMemory/SmallSort.definitions.md#def-b0a7b147d4de0b57)

**基础库名称**

`Real.instLE`, `Real`, `instFintypeSum`, `instHDiv`, `HMul.hMul`, `List.Pairwise`, `Nat.instMonoid`, `Real.instDivInvMonoid`, `Exists`, `Monoid.toNatPow`, `Fintype.card`, `Sum`, `HDiv.hDiv`, `List.Perm`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Nat.cast`, `Fin.fintype`, `List`, `And`, `HPow.hPow`, `Nat`, `Real.instMul`, `LT.lt`, `DivInvMonoid.toDiv`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `List.length`, `instHMul`, `Real.instNatCast`

<a id="def-c2477643a3867fef"></a>
## `CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Proof.lean)

**类型**

```lean
(4998 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-682184f5a736c522"></a>
## `CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Proof.lean)

**类型**

```lean
(303 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-ba5619114fdfa876"></a>
## `CodedSorting.Construction.Sorting.GeneralWordSorting.coefficient._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Proof.lean)

**类型**

```lean
(0 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`
