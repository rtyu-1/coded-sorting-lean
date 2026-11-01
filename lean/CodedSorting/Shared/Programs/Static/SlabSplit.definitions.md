# SlabSplit 的定义

[源码](SlabSplit.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-9c0caa71a653d3ae"></a>
## `CodedSorting.CommonStaticSlabSplit.address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L13)

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
- [CodedSorting.CommonColumnSplit.address](../../../Interchange/Framework/Columns/ColumnOperations.definitions.md#def-72d3a9464453bd7c)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-5b139c54049cb9ce"></a>
## `CodedSorting.CommonStaticSlabSplit.start`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L14)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
CodedSorting.CommonColumnJoin.start
```

**继续展开**

- [CodedSorting.CommonColumnJoin.start](../../../Interchange/Framework/Columns/Join.definitions.md#def-251fd32fca912bc3)

**基础库名称**

`Nat`

<a id="def-b266d1225fe0e234"></a>
## `CodedSorting.CommonStaticSlabSplit.useful`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L15)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
CodedSorting.CommonColumnJoin.useful
```

**继续展开**

- [CodedSorting.CommonColumnJoin.useful](../../../Interchange/Framework/Columns/Join.definitions.md#def-0987e91e181b2328)

**基础库名称**

`Nat`

<a id="def-d51c68e2ff92843c"></a>
## `CodedSorting.CommonStaticSlabSplit.first`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L16)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
CodedSorting.CommonColumnJoin.first
```

**继续展开**

- [CodedSorting.CommonColumnJoin.first](../../../Interchange/Framework/Columns/Join.definitions.md#def-22fe08bf7f06f79b)

**基础库名称**

`Nat`

<a id="def-377f6651efc19894"></a>
## `CodedSorting.CommonStaticSlabSplit.last`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L17)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
CodedSorting.CommonColumnJoin.last
```

**继续展开**

- [CodedSorting.CommonColumnJoin.last](../../../Interchange/Framework/Columns/Join.definitions.md#def-20711c68bc03c466)

**基础库名称**

`Nat`

<a id="def-ed87d0802abfc2ef"></a>
## `CodedSorting.CommonStaticSlabSplit.inputWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L21)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → CodedSorting.CommonBlockPair.BitIndex q → ℕ
```

**定义**

```lean
fun q n k i => CodedSorting.CommonStaticSlabSplit.start q.block n k + ↑i / q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../../Memory/BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticSlabSplit.start](SlabSplit.definitions.md#def-5b139c54049cb9ce)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `instMulNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instHMul`

<a id="def-92d4d30bf6c195b3"></a>
## `CodedSorting.CommonStaticSlabSplit.select`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L24)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → ℕ → CodedSorting.CommonBlockPair.Selection q
```

**定义**

```lean
fun q n k sourceBlock i =>
  if h :
      ↑i / q.w < CodedSorting.CommonStaticSlabSplit.useful q.block n k ∧
        CodedSorting.CommonStaticSlabSplit.inputWord q n k i / q.block = sourceBlock then
    some ⟨CodedSorting.CommonStaticSlabSplit.inputWord q n k i % q.block * q.w + ↑i % q.w, ⋯⟩
  else none
```

**继续展开**

- [CodedSorting.CommonStaticSlabSplit.inputWord](SlabSplit.definitions.md#def-ed87d0802abfc2ef)
- [CodedSorting.CommonBlockPair.Selection](../../Memory/BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonStaticSlabSplit.useful](SlabSplit.definitions.md#def-b266d1225fe0e234)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../../Memory/BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticSlabSplit.select._proof_2](SlabSplit.definitions.md#def-f470ed850d443098)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Option.some`, `Fin.mk`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `Fin.val`, `dite`, `Option.none`, `instHAdd`, `HMod.hMod`, `And`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `instDecidableAnd`, `Eq`, `Not`, `instHMul`, `Option`

<a id="def-c5ea0ee234200b06"></a>
## `CodedSorting.CommonStaticSlabSplit.part`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L33)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    ℕ → ℕ → (ℕ → Fin (q.N ^ q.exponent)) → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n source target k b =>
  CodedSorting.CommonBlockPair.code q reader (CodedSorting.CommonStaticSlabSplit.address q source b) (target k)
    (CodedSorting.CommonStaticSlabSplit.select q n k b)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonStaticSlabSplit.select](SlabSplit.definitions.md#def-92d4d30bf6c195b3)
- [CodedSorting.CommonStaticSlabSplit.address](SlabSplit.definitions.md#def-9c0caa71a653d3ae)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBlockPair.code](../../Memory/BlockPair.definitions.md#def-1132aa9fc93f6ac6)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-1f288e90723b1f8a"></a>
## `CodedSorting.CommonStaticSlabSplit.fragment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L37)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    ℕ → ℕ → (ℕ → Fin (q.N ^ q.exponent)) → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n source target k =>
  CodedSorting.CommonStaticSlabSplit.part q reader n source target k
      (CodedSorting.CommonStaticSlabSplit.first q.block n k) ++
    CodedSorting.CommonStaticSlabSplit.part q reader n source target k
      (CodedSorting.CommonStaticSlabSplit.last q.block n k)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonStaticSlabSplit.first](SlabSplit.definitions.md#def-d51c68e2ff92843c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSlabSplit.last](SlabSplit.definitions.md#def-377f6651efc19894)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticSlabSplit.part](SlabSplit.definitions.md#def-c5ea0ee234200b06)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instHAppendOfAppend`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-70924b7f561a7e35"></a>
## `CodedSorting.CommonStaticSlabSplit.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabSplit.lean#L42)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    ℕ → ℕ → ℕ → (ℕ → Fin (q.N ^ q.exponent)) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader C n source target =>
  List.flatMap (CodedSorting.CommonStaticSlabSplit.fragment q reader n source target)
    (List.range (C * CodedSorting.PhysicalStreamCursor.blockCount q.block n))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonStaticSlabSplit.fragment](SlabSplit.definitions.md#def-1f288e90723b1f8a)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `List.range`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `List.flatMap`, `instHMul`

<a id="def-f470ed850d443098"></a>
## `CodedSorting.CommonStaticSlabSplit.select._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SlabSplit.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n k : ℕ),
  ℕ →
    ∀ (i : CodedSorting.CommonBlockPair.BitIndex q),
      CodedSorting.CommonStaticSlabSplit.inputWord q n k i % q.block * q.w + ↑i % q.w < q.block * q.w
```

**继续展开**

- [CodedSorting.CommonStaticSlabSplit.inputWord](SlabSplit.definitions.md#def-ed87d0802abfc2ef)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../../Memory/BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMod`, `instHMod`, `instMulNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `instHMul`
