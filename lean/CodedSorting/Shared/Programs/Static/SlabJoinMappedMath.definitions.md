# SlabJoinMappedMath 的定义

[源码](SlabJoinMappedMath.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-b1e9d0f76b263e4d"></a>
## `CodedSorting.CommonStaticSlabJoin.select`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabJoinMappedMath.lean#L18)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → ℕ → CodedSorting.CommonBlockPair.Selection q
```

**定义**

```lean
fun q n k targetBlock j =>
  let pair := finProdFinEquiv.symm j;
  if h :
      CodedSorting.CommonColumnJoin.start q.block n k ≤ targetBlock * q.block + ↑pair.1 ∧
        targetBlock * q.block + ↑pair.1 <
          CodedSorting.CommonColumnJoin.start q.block n k + CodedSorting.CommonColumnJoin.useful q.block n k then
    some
      (finProdFinEquiv (⟨targetBlock * q.block + ↑pair.1 - CodedSorting.CommonColumnJoin.start q.block n k, ⋯⟩, pair.2))
  else none
```

**继续展开**

- [CodedSorting.CommonBlockPair.Selection](../../Memory/BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonColumnJoin.start](../../../Interchange/Framework/Columns/Join.definitions.md#def-251fd32fca912bc3)
- [CodedSorting.CommonColumnJoin.useful](../../../Interchange/Framework/Columns/Join.definitions.md#def-0987e91e181b2328)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../../Memory/BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonStaticSlabJoin.select._proof_2](SlabJoinMappedMath.definitions.md#def-a6669bca125a2807)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `HSub.hSub`, `Option.some`, `Fin.mk`, `Equiv`, `Prod.mk`, `instSubNat`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `dite`, `Option.none`, `instHAdd`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `finProdFinEquiv`, `Nat.decLt`, `instAddNat`, `instLTNat`, `instDecidableAnd`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `Not`, `Nat.decLe`, `instHMul`, `Option`

<a id="def-1df0e875562015aa"></a>
## `CodedSorting.CommonStaticSlabJoinMapped.address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabJoinMappedMath.lean#L159)

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

<a id="def-dce76a083be5a031"></a>
## `CodedSorting.CommonStaticSlabJoinMapped.select`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabJoinMappedMath.lean#L160)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → ℕ → CodedSorting.CommonBlockPair.Selection q
```

**定义**

```lean
CodedSorting.CommonStaticSlabJoin.select
```

**继续展开**

- [CodedSorting.CommonBlockPair.Selection](../../Memory/BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonStaticSlabJoin.select](SlabJoinMappedMath.definitions.md#def-b1e9d0f76b263e4d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-8be1a08f5b731b49"></a>
## `CodedSorting.CommonStaticSlabJoinMapped.fragment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabJoinMappedMath.lean#L177)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    ℕ → ℕ → ℕ → (ℕ → Fin (q.N ^ q.exponent)) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n target k source =>
  CodedSorting.CommonBlockPair.code q reader (source k)
      (CodedSorting.CommonStaticSlabJoinMapped.address q target (CodedSorting.CommonColumnJoin.first q.block n k))
      (CodedSorting.CommonStaticSlabJoinMapped.select q n k (CodedSorting.CommonColumnJoin.first q.block n k)) ++
    CodedSorting.CommonBlockPair.code q reader (source k)
      (CodedSorting.CommonStaticSlabJoinMapped.address q target (CodedSorting.CommonColumnJoin.last q.block n k))
      (CodedSorting.CommonStaticSlabJoinMapped.select q n k (CodedSorting.CommonColumnJoin.last q.block n k))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonColumnJoin.last](../../../Interchange/Framework/Columns/Join.definitions.md#def-20711c68bc03c466)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonStaticSlabJoinMapped.address](SlabJoinMappedMath.definitions.md#def-1df0e875562015aa)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSlabJoinMapped.select](SlabJoinMappedMath.definitions.md#def-dce76a083be5a031)
- [CodedSorting.CommonBlockPair.code](../../Memory/BlockPair.definitions.md#def-1132aa9fc93f6ac6)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonColumnJoin.first](../../../Interchange/Framework/Columns/Join.definitions.md#def-22fe08bf7f06f79b)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instHAppendOfAppend`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-745d2d839f86224b"></a>
## `CodedSorting.CommonStaticSlabJoinMapped.codeFrom`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabJoinMappedMath.lean#L184)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    ℕ → ℕ → ℕ → (ℕ → Fin (q.N ^ q.exponent)) → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n target k source x =>
  Nat.brecOn (motive := fun x => ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x
    (fun x f k =>
      (match (motive :=
          (x : ℕ) →
            Nat.below (motive := fun x => ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x →
              List (CodedSorting.CommonStaticSchedule.Instruction q))
          x with
        | 0 => fun x => []
        | left.succ => fun x =>
          CodedSorting.CommonStaticSlabJoinMapped.fragment q reader n target k source ++ x.1 (k + 1))
        f)
    k
```

**继续展开**

- [CodedSorting.CommonStaticSlabJoin.codeFrom.match_1](SlabJoinMappedMath.definitions.md#def-9f60014bc09a03ae)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonStaticSlabJoinMapped.fragment](SlabJoinMappedMath.definitions.md#def-8be1a08f5b731b49)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.brecOn`, `instOfNatNat`, `Nat.below`, `instHAppendOfAppend`, `List`, `instHAdd`, `Unit`, `PProd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `HAppend.hAppend`, `List.nil`

<a id="def-3e50765d291b2bd7"></a>
## `CodedSorting.CommonStaticSlabJoinMapped.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabJoinMappedMath.lean#L189)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    ℕ → ℕ → ℕ → (ℕ → Fin (q.N ^ q.exponent)) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n C target source =>
  CodedSorting.CommonStaticSlabJoinMapped.codeFrom q reader n target 0 source
    (C * CodedSorting.PhysicalStreamCursor.blockCount q.block n)
```

**继续展开**

- [CodedSorting.CommonStaticSlabJoinMapped.codeFrom](SlabJoinMappedMath.definitions.md#def-745d2d839f86224b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-9f60014bc09a03ae"></a>
## `CodedSorting.CommonStaticSlabJoin.codeFrom.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](SlabJoinMappedMath.lean)

**类型**

```lean
(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((left : ℕ) → motive left.succ) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 => Nat.casesOn x (h_1 ()) fun n => h_2 n
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `instOfNatNat`, `Unit`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-a6669bca125a2807"></a>
## `CodedSorting.CommonStaticSlabJoin.select._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SlabJoinMappedMath.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n k targetBlock : ℕ)
  (j : CodedSorting.CommonBlockPair.BitIndex q),
  CodedSorting.CommonColumnJoin.start q.block n k ≤ targetBlock * q.block + ↑(finProdFinEquiv.symm j).1 ∧
      targetBlock * q.block + ↑(finProdFinEquiv.symm j).1 <
        CodedSorting.CommonColumnJoin.start q.block n k + CodedSorting.CommonColumnJoin.useful q.block n k →
    targetBlock * q.block + ↑(finProdFinEquiv.symm j).1 - CodedSorting.CommonColumnJoin.start q.block n k < q.block
```

**继续展开**

- [CodedSorting.CommonColumnJoin.start](../../../Interchange/Framework/Columns/Join.definitions.md#def-251fd32fca912bc3)
- [CodedSorting.CommonColumnJoin.useful](../../../Interchange/Framework/Columns/Join.definitions.md#def-0987e91e181b2328)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../../Memory/BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `HSub.hSub`, `Equiv`, `instSubNat`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `finProdFinEquiv`, `instAddNat`, `instLTNat`, `Equiv.symm`, `Prod`, `Fin`, `DFunLike.coe`, `instHMul`
