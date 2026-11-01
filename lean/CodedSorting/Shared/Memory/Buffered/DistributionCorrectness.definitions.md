# DistributionCorrectness 的定义

[源码](DistributionCorrectness.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-42da0de0fb3b1054"></a>
## `CodedSorting.CommonBufferedDistribution.slot`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DistributionCorrectness.lean#L21)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → CodedSorting.CommonBlockPair.BitIndex q
```

**定义**

```lean
fun q r => ⟨r % CodedSorting.CommonPermutationPairs.width q, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonBufferedDistribution.slot._proof_1](DistributionCorrectness.definitions.md#def-90f0515b8f0975b6)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonPermutationPairs.width](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Fin.mk`, `Nat.instMod`, `instHMod`, `instMulNat`, `HMod.hMod`, `Nat`, `instHMul`

<a id="def-8e4169c529ebabbf"></a>
## `CodedSorting.CommonBufferedDistribution.selection`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DistributionCorrectness.lean#L24)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → CodedSorting.CommonBlockPair.Selection q
```

**定义**

```lean
fun q i r j =>
  if j = CodedSorting.CommonBufferedDistribution.slot q r then some (CodedSorting.CommonBufferedDistribution.slot q i)
  else none
```

**继续展开**

- [CodedSorting.CommonBlockPair.Selection](../BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonBufferedDistribution.slot](DistributionCorrectness.definitions.md#def-42da0de0fb3b1054)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instDecidableEqFin`, `Option.some`, `instMulNat`, `Option.none`, `Nat`, `Eq`, `instHMul`, `Option`, `ite`

<a id="def-2c2e772d031b6dfa"></a>
## `CodedSorting.CommonBufferedDistribution.Flush`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DistributionCorrectness.lean#L27)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → Prop
```

**定义**

```lean
fun q L r =>
  r % CodedSorting.CommonPermutationPairs.width q = CodedSorting.CommonPermutationPairs.width q - 1 ∨ r + 1 = L
```

**继续展开**

- [CodedSorting.CommonPermutationPairs.width](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HSub.hSub`, `Nat.instMod`, `instHMod`, `instSubNat`, `instOfNatNat`, `instHAdd`, `HMod.hMod`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Or`, `OfNat.ofNat`, `Eq`

<a id="def-f4642c926aca9fe6"></a>
## `CodedSorting.CommonBufferedDistribution.instDecidableFlush`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DistributionCorrectness.lean#L30)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (L r : ℕ) → Decidable (CodedSorting.CommonBufferedDistribution.Flush q L r)
```

**定义**

```lean
fun q L r =>
  inferInstanceAs
    (Decidable
      (r % CodedSorting.CommonPermutationPairs.width q = CodedSorting.CommonPermutationPairs.width q - 1 ∨ r + 1 = L))
```

**继续展开**

- [CodedSorting.CommonBufferedDistribution.Flush](DistributionCorrectness.definitions.md#def-2c2e772d031b6dfa)
- [CodedSorting.CommonPermutationPairs.width](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`inferInstanceAs`, `HSub.hSub`, `Decidable`, `Nat.instMod`, `instHMod`, `instSubNat`, `instOfNatNat`, `instHAdd`, `HMod.hMod`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instDecidableEqNat`, `Or`, `OfNat.ofNat`, `Eq`, `instDecidableOr`

<a id="def-df6f1e3f93061e4d"></a>
## `CodedSorting.CommonBufferedDistribution.fragment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DistributionCorrectness.lean#L33)

**类型**

```lean
{V K L : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin V ≃ Fin K × Fin L →
          ℕ → (Fin K → ℕ → Fin (q.N ^ q.exponent)) → Fin V → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V K L} q hfit reader e source target i =>
  (if ↑i % CodedSorting.CommonPermutationPairs.width q = 0 then
        [CodedSorting.CommonBlockPair.sourceRead q reader
            (CodedSorting.CommonPermutationPairs.address q source (↑i / CodedSorting.CommonPermutationPairs.width q))]
      else []) ++
      [CodedSorting.CommonBufferedBank.blendInstruction q hfit reader (e i).1
          (CodedSorting.CommonBufferedDistribution.selection q ↑i ↑(e i).2)] ++
    if CodedSorting.CommonBufferedDistribution.Flush q L ↑(e i).2 then
      CodedSorting.CommonBufferedBank.writeCode q hfit (e i).1
        (target (e i).1 (↑(e i).2 / CodedSorting.CommonPermutationPairs.width q))
    else []
```

**继续展开**

- [CodedSorting.CommonBufferedDistribution.instDecidableFlush](DistributionCorrectness.definitions.md#def-f4642c926aca9fe6)
- [CodedSorting.CommonBufferedBank.blendInstruction](GatherProgram.definitions.md#def-31aa3d52aeaa81e0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonBufferedDistribution.selection](DistributionCorrectness.definitions.md#def-8e4169c529ebabbf)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonBufferedDistribution.Flush](DistributionCorrectness.definitions.md#def-2c2e772d031b6dfa)
- [CodedSorting.CommonBlockPair.sourceRead](../BlockPair.definitions.md#def-5dc5b806044bea03)
- [CodedSorting.CommonPermutationPairs.address](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-841830e6780927fe)
- [CodedSorting.CommonPermutationPairs.width](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBufferedBank.writeCode](GatherProgram.definitions.md#def-d8d3ec6687d5fb09)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Equiv.instFunLike`, `instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List.cons`, `instHAppendOfAppend`, `List`, `HMod.hMod`, `HPow.hPow`, `Nat`, `Nat.instDiv`, `instDecidableEqNat`, `instHPow`, `List.instAppend`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `HAppend.hAppend`, `instHMul`, `List.nil`, `ite`

<a id="def-ac180ece0f88af57"></a>
## `CodedSorting.CommonBufferedDistribution.codePrefix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DistributionCorrectness.lean#L131)

**类型**

```lean
{V K L : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin V ≃ Fin K × Fin L →
          ℕ → (Fin K → ℕ → Fin (q.N ^ q.exponent)) → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V K L} q hfit reader e source target x =>
  Nat.brecOn x fun x f =>
    (match (motive := (x : ℕ) → Nat.below x → List (CodedSorting.CommonStaticSchedule.Instruction q)) x with
      | 0 => fun x => []
      | n.succ => fun x =>
        x.1 ++
          if h : n < V then CodedSorting.CommonBufferedDistribution.fragment q hfit reader e source target ⟨n, h⟩
          else [])
      f
```

**继续展开**

- [CodedSorting.CommonBufferedDistribution.codePrefix.match_1](DistributionCorrectness.definitions.md#def-24a2c8e6f5871a1e)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonBufferedDistribution.fragment](DistributionCorrectness.definitions.md#def-df6f1e3f93061e4d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `Nat.brecOn`, `Equiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `dite`, `Nat.below`, `instHAppendOfAppend`, `List`, `Unit`, `PProd`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.decLt`, `instHPow`, `instLTNat`, `List.instAppend`, `Prod`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `Not`, `HAppend.hAppend`, `instHMul`, `List.nil`

<a id="def-95c9c92d87ae04e4"></a>
## `CodedSorting.CommonBufferedDistribution.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DistributionCorrectness.lean#L139)

**类型**

```lean
{V K L : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin V ≃ Fin K × Fin L →
          ℕ → (Fin K → ℕ → Fin (q.N ^ q.exponent)) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V K L} q hfit reader e source target =>
  CodedSorting.CommonBufferedDistribution.codePrefix q hfit reader e source target V
```

**继续展开**

- [CodedSorting.CommonBufferedDistribution.codePrefix](DistributionCorrectness.definitions.md#def-ac180ece0f88af57)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instMulNat`, `LE.le`, `instLENat`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Prod`, `Fin`, `instHMul`

<a id="def-24a2c8e6f5871a1e"></a>
## `CodedSorting.CommonBufferedDistribution.codePrefix.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](DistributionCorrectness.lean)

**类型**

```lean
(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 => Nat.casesOn x (h_1 ()) fun n => h_2 n
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `instOfNatNat`, `Unit`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-90f0515b8f0975b6"></a>
## `CodedSorting.CommonBufferedDistribution.slot._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](DistributionCorrectness.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (r : ℕ),
  r % CodedSorting.CommonPermutationPairs.width q < CodedSorting.CommonPermutationPairs.width q
```

**继续展开**

- [CodedSorting.CommonPermutationPairs.width](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`
