# Xor 的定义

[源码](Xor.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-b8bf134eb98bca4e"></a>
## `CodedSorting.CommonStaticXor.address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Xor.lean#L18)

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

<a id="def-fd0cf06162cd0f44"></a>
## `CodedSorting.CommonStaticXor.width`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Xor.lean#L20)

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

<a id="def-21cb86c0575eb8d5"></a>
## `CodedSorting.CommonStaticXor.count`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Xor.lean#L25)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q V => CodedSorting.PhysicalStreamCursor.blockCount (CodedSorting.CommonStaticXor.width q) V
```

**继续展开**

- [CodedSorting.PhysicalStreamCursor.blockCount](../../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticXor.width](Xor.definitions.md#def-fd0cf06162cd0f44)

**基础库名称**

`Nat`

<a id="def-1a278fd6bf88d262"></a>
## `CodedSorting.CommonStaticXor.secondRead`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Xor.lean#L31)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → Fin (q.N ^ q.exponent) → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q reader right =>
  {
    operation :=
      CodedSorting.Normalization.Command.read right
        (CodedSorting.CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    resume := fun ram =>
      let s := CodedSorting.CommonSortingNormalization.unpack ram;
      CodedSorting.CommonSortingNormalization.pack
        { leaf := s.leaf, readers := s.readers, writers := s.writers,
          transfer :=
            CodedSorting.PhysicalFileHandlesXor.xorBlock (CodedSorting.CommonBlockPair.buffer q reader s) s.transfer,
          scalars := s.scalars, directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs } }
```

**继续展开**

- [CodedSorting.CommonBlockPair.buffer](../../Memory/BlockPair.definitions.md#def-af60041b169cb3ab)
- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafWindow.transferWindow](../../Memory/Leaf/Program.definitions.md#def-e331864fad0a6a8e)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.Normalization.Command.read](../Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.PhysicalFileHandlesXor.xorBlock](../../Memory/AllocatedDirectoryXor.definitions.md#def-add5104abba71517)
- [CodedSorting.Normalization.Words](../Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonSortingNormalization.SourceState](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-d5e26459d8d546cb"></a>
## `CodedSorting.CommonStaticXor.blockCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Xor.lean#L36)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    Fin (q.N ^ q.exponent) →
      Fin (q.N ^ q.exponent) → Fin (q.N ^ q.exponent) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader left right target =>
  [CodedSorting.CommonBlockPair.sourceRead q reader left, CodedSorting.CommonStaticXor.secondRead q reader right,
    CodedSorting.CommonBlockPair.targetWrite q target]
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonStaticXor.secondRead](Xor.definitions.md#def-1a278fd6bf88d262)
- [CodedSorting.CommonBlockPair.sourceRead](../../Memory/BlockPair.definitions.md#def-5dc5b806044bea03)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBlockPair.targetWrite](../../Memory/BlockPair.definitions.md#def-3b05497ae0c5b9b7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `List.cons`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `List.nil`

<a id="def-06a9f846ee47012a"></a>
## `CodedSorting.CommonStaticXor.blocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Xor.lean#L83)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader left right target x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x_1
    (fun x f x_2 =>
      (match (motive :=
          ℕ →
            (x : ℕ) →
              Nat.below (motive := fun x => ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x →
                List (CodedSorting.CommonStaticSchedule.Instruction q))
          x_2, x with
        | x, 0 => fun x => []
        | cursor, n.succ => fun x =>
          CodedSorting.CommonStaticXor.blockCode q reader (CodedSorting.CommonStaticXor.address q left cursor)
              (CodedSorting.CommonStaticXor.address q right cursor)
              (CodedSorting.CommonStaticXor.address q target cursor) ++
            x.1 (cursor + 1))
        f)
    x
```

**继续展开**

- [CodedSorting.CommonStaticXor.blockCode](Xor.definitions.md#def-d5e26459d8d546cb)
- [CodedSorting.CommonStaticXor.blocks.match_1](Xor.definitions.md#def-c4d02d6b96b2a598)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonStaticXor.address](Xor.definitions.md#def-b8bf134eb98bca4e)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`Nat.brecOn`, `instOfNatNat`, `Nat.below`, `instHAppendOfAppend`, `List`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `HAppend.hAppend`, `List.nil`

<a id="def-f5c3d4facfcfece0"></a>
## `CodedSorting.CommonStaticXor.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Xor.lean#L89)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader V left right target =>
  CodedSorting.CommonStaticXor.blocks q reader left right target 0 (CodedSorting.CommonStaticXor.count q V)
```

**继续展开**

- [CodedSorting.CommonStaticXor.count](Xor.definitions.md#def-21cb86c0575eb8d5)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticXor.blocks](Xor.definitions.md#def-06a9f846ee47012a)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-c4d02d6b96b2a598"></a>
## `CodedSorting.CommonStaticXor.blocks.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Xor.lean)

**类型**

```lean
(motive : ℕ → ℕ → Sort u_1) →
  (x x_1 : ℕ) → ((x : ℕ) → motive x 0) → ((cursor n : ℕ) → motive cursor n.succ) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x_1 (h_1 x) fun n => h_2 x n
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`
