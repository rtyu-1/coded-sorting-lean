# Reflection 的定义

[源码](Reflection.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-481ddff84990854c"></a>
## `CodedSorting.CommonPermutationPairs.Entry`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L19)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun K => Fin K × ℕ × ℕ
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`, `Prod`, `Fin`

<a id="def-841830e6780927fe"></a>
## `CodedSorting.CommonPermutationPairs.address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → Fin (q.N ^ q.exponent)
```

**定义**

```lean
CodedSorting.CommonColumnSplit.address
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonColumnSplit.address](../Columns/ColumnOperations.definitions.md#def-72d3a9464453bd7c)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-cf4f87b7a0e5726b"></a>
## `CodedSorting.CommonPermutationPairs.width`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L22)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => q.block * q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-3c63dad660cc6543"></a>
## `CodedSorting.CommonPermutationPairs.count`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L26)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q V => CodedSorting.PhysicalStreamCursor.blockCount (CodedSorting.CommonPermutationPairs.width q) V
```

**继续展开**

- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonPermutationPairs.width](Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-96a76826e3991d5f"></a>
## `CodedSorting.CommonPermutationPairs.readBit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L32)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonLeafProgram.Disk q → ℕ → ℕ → CodedSorting.Circuit.Bit
```

**定义**

```lean
fun q disk base i =>
  (CodedSorting.BitWordPacking.blockBits q.block q.w)
    (disk (CodedSorting.CommonPermutationPairs.address q base (i / CodedSorting.CommonPermutationPairs.width q)))
    ⟨i % CodedSorting.CommonPermutationPairs.width q, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonPermutationPairs.readBit._proof_1](Reflection.definitions.md#def-403bc80c8529e96d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafProgram.Disk](../../../Shared/Memory/Leaf/Program.definitions.md#def-e343337119cf665f)
- [CodedSorting.BitWordPacking.blockBits](../../../Shared/Words/WordConvention.definitions.md#def-a9a13aad90fdf19b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonPermutationPairs.address](Reflection.definitions.md#def-841830e6780927fe)
- [CodedSorting.CommonPermutationPairs.width](Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Equiv.instFunLike`, `instHDiv`, `HMul.hMul`, `Fin.mk`, `Equiv`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `HMod.hMod`, `Nat`, `Nat.instDiv`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-4d4fb8e53c32e375"></a>
## `CodedSorting.CommonPermutationPairs.select`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L36)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V K : ℕ} →
    Equiv.Perm (Fin V) →
      (Fin V → Fin K) → CodedSorting.CommonPermutationPairs.Entry K → CodedSorting.CommonBlockPair.Selection q
```

**定义**

```lean
fun q {V K} e key p j =>
  if h : p.2.2 * CodedSorting.CommonPermutationPairs.width q + ↑j < V then
    let x := (Equiv.symm e) ⟨p.2.2 * CodedSorting.CommonPermutationPairs.width q + ↑j, h⟩;
    if key x = p.1 ∧ ↑x / CodedSorting.CommonPermutationPairs.width q = p.2.1 then
      some ⟨↑x % CodedSorting.CommonPermutationPairs.width q, ⋯⟩
    else none
  else none
```

**继续展开**

- [CodedSorting.CommonBlockPair.Selection](../../../Shared/Memory/BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonPermutationPairs.width](Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../../../Shared/Memory/BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonPermutationPairs.Entry](Reflection.definitions.md#def-481ddff84990854c)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonPermutationPairs.select._proof_2](Reflection.definitions.md#def-1db3ffa172fb917b)

**基础库名称**

`Equiv.instFunLike`, `instHDiv`, `HMul.hMul`, `instDecidableEqFin`, `Option.some`, `Fin.mk`, `Equiv`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `Fin.val`, `Prod.fst`, `dite`, `Option.none`, `instHAdd`, `HMod.hMod`, `And`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `Nat.instDiv`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `instDecidableAnd`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `Not`, `instHMul`, `Option`, `ite`

<a id="def-3ad9a877733193d2"></a>
## `CodedSorting.CommonPermutationPairs.fragment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L58)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V K : ℕ} →
    Fin q.inventory.readers →
      Equiv.Perm (Fin V) →
        (Fin V → Fin K) →
          ℕ → ℕ → CodedSorting.CommonPermutationPairs.Entry K → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q {V K} reader e key source target p =>
  CodedSorting.CommonBlockPair.code q reader (CodedSorting.CommonPermutationPairs.address q source p.2.1)
    (CodedSorting.CommonPermutationPairs.address q target p.2.2) (CodedSorting.CommonPermutationPairs.select q e key p)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonPermutationPairs.select](Reflection.definitions.md#def-4d4fb8e53c32e375)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonPermutationPairs.address](Reflection.definitions.md#def-841830e6780927fe)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonPermutationPairs.Entry](Reflection.definitions.md#def-481ddff84990854c)
- [CodedSorting.CommonBlockPair.code](../../../Shared/Memory/BlockPair.definitions.md#def-1132aa9fc93f6ac6)

**基础库名称**

`Prod.fst`, `List`, `Equiv.Perm`, `Nat`, `Prod`, `Fin`, `Prod.snd`

<a id="def-b5059e45dcb61590"></a>
## `CodedSorting.CommonPermutationPairs.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L64)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V K : ℕ} →
    Fin q.inventory.readers →
      Equiv.Perm (Fin V) →
        (Fin V → Fin K) →
          ℕ →
            ℕ →
              List (CodedSorting.CommonPermutationPairs.Entry K) →
                List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q {V K} reader e key source target ps =>
  List.flatMap (CodedSorting.CommonPermutationPairs.fragment q reader e key source target) ps
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonPermutationPairs.fragment](Reflection.definitions.md#def-3ad9a877733193d2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonPermutationPairs.Entry](Reflection.definitions.md#def-481ddff84990854c)

**基础库名称**

`List`, `Equiv.Perm`, `Nat`, `Fin`, `List.flatMap`

<a id="def-7ada41d9d7d54209"></a>
## `CodedSorting.CommonReflectionPairs.key`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L247)

**类型**

```lean
ℕ → (T L : ℕ) → Fin (T * L) → Fin 4
```

**定义**

```lean
fun B T L x =>
  let y := (CodedSorting.BlockReflection.segmentReverseEquiv T L) x;
  CodedSorting.BlockReflection.sourceSlot B L (↑y / B) ↑y
```

**继续展开**

- [CodedSorting.BlockReflection.sourceSlot](LayoutMachine.definitions.md#def-98c9023027af1808)
- [CodedSorting.BlockReflection.segmentReverseEquiv](LayoutMachine.definitions.md#def-5d59a52eabcd3361)

**基础库名称**

`Equiv.instFunLike`, `instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Equiv.Perm`, `Nat`, `Nat.instDiv`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-23f1f1749bea1453"></a>
## `CodedSorting.CommonReflectionPairs.entry`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L251)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → Fin 4 → Fin 4 × ℕ × ℕ
```

**定义**

```lean
fun B L blocks b slot => (slot, min (CodedSorting.BlockReflection.sourceBlock B L b slot) (blocks - 1), b)
```

**继续展开**

- [CodedSorting.BlockReflection.sourceBlock](LayoutMachine.definitions.md#def-f1b696dcb523faea)

**基础库名称**

`HSub.hSub`, `Prod.mk`, `instSubNat`, `instOfNatNat`, `instHSub`, `Nat`, `Nat.instMin_mathlib`, `Prod`, `OfNat.ofNat`, `Fin`, `Min.min`

<a id="def-677f669100033c21"></a>
## `CodedSorting.CommonReflectionPairs.schedule`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L254)

**类型**

```lean
ℕ → ℕ → ℕ → List (Fin 4 × ℕ × ℕ)
```

**定义**

```lean
fun B T L =>
  List.flatMap
    (fun b =>
      List.map (CodedSorting.CommonReflectionPairs.entry B L (CodedSorting.PhysicalStreamCursor.blockCount B (T * L)) b)
        (List.finRange 4))
    (List.range (CodedSorting.PhysicalStreamCursor.blockCount B (T * L)))
```

**继续展开**

- [CodedSorting.CommonReflectionPairs.entry](Reflection.definitions.md#def-23f1f1749bea1453)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)

**基础库名称**

`HMul.hMul`, `List.map`, `instMulNat`, `instOfNatNat`, `List.range`, `List`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`, `List.finRange`, `List.flatMap`, `instHMul`

<a id="def-40c5a71a42c86359"></a>
## `CodedSorting.CommonPermutationScan.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L375)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V K : ℕ} →
    Fin q.inventory.readers →
      Equiv.Perm (Fin V) → (Fin V → Fin K) → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q {V K} reader e key source target =>
  CodedSorting.CommonPermutationPairs.code q reader e key source target
    (CodedSorting.MonotoneBlockPairs.schedule e key (CodedSorting.CommonPermutationPairs.width q))
```

**继续展开**

- [CodedSorting.CommonPermutationPairs.code](Reflection.definitions.md#def-b5059e45dcb61590)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.MonotoneBlockPairs.schedule](../../../Shared/Programs/MonotoneBlockPairs.definitions.md#def-92fbad4edf5c50a1)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonPermutationPairs.width](Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List`, `Equiv.Perm`, `Nat`, `Fin`

<a id="def-4be803cd6e4d42f8"></a>
## `CodedSorting.CommonReflection.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Reflection.lean#L454)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader T L source target =>
  CodedSorting.CommonPermutationPairs.code q reader (CodedSorting.BlockReflection.segmentReverseEquiv T L)
    (CodedSorting.CommonReflectionPairs.key (CodedSorting.CommonPermutationPairs.width q) T L) source target
    (CodedSorting.CommonReflectionPairs.schedule (CodedSorting.CommonPermutationPairs.width q) T L)
```

**继续展开**

- [CodedSorting.CommonPermutationPairs.code](Reflection.definitions.md#def-b5059e45dcb61590)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonReflectionPairs.schedule](Reflection.definitions.md#def-677f669100033c21)
- [CodedSorting.CommonReflectionPairs.key](Reflection.definitions.md#def-7ada41d9d7d54209)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonPermutationPairs.width](Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.BlockReflection.segmentReverseEquiv](LayoutMachine.definitions.md#def-5d59a52eabcd3361)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-403bc80c8529e96d"></a>
## `CodedSorting.CommonPermutationPairs.readBit._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Reflection.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (i : ℕ),
  i % CodedSorting.CommonPermutationPairs.width q < CodedSorting.CommonPermutationPairs.width q
```

**继续展开**

- [CodedSorting.CommonPermutationPairs.width](Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`

<a id="def-1db3ffa172fb917b"></a>
## `CodedSorting.CommonPermutationPairs.select._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Reflection.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
  (p : CodedSorting.CommonPermutationPairs.Entry K) (j : CodedSorting.CommonBlockPair.BitIndex q)
  (h : p.2.2 * CodedSorting.CommonPermutationPairs.width q + ↑j < V),
  ↑((Equiv.symm e) ⟨p.2.2 * CodedSorting.CommonPermutationPairs.width q + ↑j, h⟩) %
      CodedSorting.CommonPermutationPairs.width q <
    CodedSorting.CommonPermutationPairs.width q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonPermutationPairs.width](Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../../../Shared/Memory/BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonPermutationPairs.Entry](Reflection.definitions.md#def-481ddff84990854c)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Fin.mk`, `Equiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`
