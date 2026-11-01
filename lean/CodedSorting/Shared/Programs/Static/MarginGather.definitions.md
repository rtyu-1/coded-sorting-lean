# MarginGather 的定义

[源码](MarginGather.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-f28024dd78f6b499"></a>
## `CodedSorting.CommonStaticMarginGather.secondRead`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginGather.lean#L13)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    Fin (q.N ^ q.exponent) →
      (CodedSorting.WordControl.Words q.block q.w →
          CodedSorting.WordControl.Words q.block q.w → CodedSorting.WordControl.Words q.block q.w) →
        CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q reader a combine =>
  {
    operation :=
      CodedSorting.Normalization.Command.read a
        (CodedSorting.CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    resume := fun ram =>
      let s := CodedSorting.CommonSortingNormalization.unpack ram;
      CodedSorting.CommonSortingNormalization.pack
        { leaf := s.leaf, readers := s.readers, writers := s.writers,
          transfer := combine (CodedSorting.CommonBlockPair.buffer q reader s) s.transfer, scalars := s.scalars,
          directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs } }
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
- [CodedSorting.WordControl.Words](../../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-e44008d7b78888bb"></a>
## `CodedSorting.CommonStaticMarginGather.fragment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginGather.lean#L36)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    CodedSorting.CommonMarginGather.Scheme q →
      CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader p shape source target k =>
  [CodedSorting.CommonBlockPair.sourceRead q reader (p.first shape source k),
    CodedSorting.CommonStaticMarginGather.secondRead q reader (p.second shape source k) (p.assemble shape k),
    CodedSorting.CommonBlockPair.targetWrite q (CodedSorting.CommonColumnSplit.address q target k)]
```

**继续展开**

- [CodedSorting.CommonStaticMarginGather.secondRead](MarginGather.definitions.md#def-f28024dd78f6b499)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonMarginGather.Scheme.second](../../Memory/MarginTransform.definitions.md#def-d83cfea00172f9a6)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMarginGather.Scheme](../../Memory/MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonMarginGather.Scheme.first](../../Memory/MarginTransform.definitions.md#def-32c4d05bb49d8940)
- [CodedSorting.CommonBlockPair.sourceRead](../../Memory/BlockPair.definitions.md#def-5dc5b806044bea03)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBlockPair.targetWrite](../../Memory/BlockPair.definitions.md#def-3b05497ae0c5b9b7)
- [CodedSorting.CommonMarginGather.Scheme.assemble](../../Memory/MarginTransform.definitions.md#def-825c4a6a93d18362)
- [CodedSorting.CommonMarginGather.Shape](../../Memory/MarginTransform.definitions.md#def-1b196fc79b9f7c83)
- [CodedSorting.CommonColumnSplit.address](../../../Interchange/Framework/Columns/ColumnOperations.definitions.md#def-72d3a9464453bd7c)

**基础库名称**

`List.cons`, `List`, `Nat`, `Fin`, `List.nil`

<a id="def-93c865ab379b3d80"></a>
## `CodedSorting.CommonStaticMarginGather.codeFrom`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginGather.lean#L42)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    CodedSorting.CommonMarginGather.Scheme q →
      CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader p shape source target x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x_1
    (fun x f x_2 =>
      (match (motive :=
          ℕ →
            (x : ℕ) →
              Nat.below (motive := fun x => ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x →
                List (CodedSorting.CommonStaticSchedule.Instruction q))
          x_2, x with
        | x, 0 => fun x => []
        | k, n.succ => fun x =>
          CodedSorting.CommonStaticMarginGather.fragment q reader p shape source target k ++ x.1 (k + 1))
        f)
    x
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMarginGather.Scheme](../../Memory/MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticMarginGather.codeFrom.match_1](MarginGather.definitions.md#def-af684a80bcdde8e2)
- [CodedSorting.CommonStaticMarginGather.fragment](MarginGather.definitions.md#def-e44008d7b78888bb)
- [CodedSorting.CommonMarginGather.Shape](../../Memory/MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Nat.brecOn`, `instOfNatNat`, `Nat.below`, `instHAppendOfAppend`, `List`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `HAppend.hAppend`, `List.nil`

<a id="def-2bd16bea3675aa9e"></a>
## `CodedSorting.CommonStaticMarginGather.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginGather.lean#L47)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    CodedSorting.CommonMarginGather.Scheme q →
      CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader p shape source target =>
  CodedSorting.CommonStaticMarginGather.codeFrom q reader p shape source target 0 (p.count shape)
```

**继续展开**

- [CodedSorting.CommonMarginGather.Scheme.count](../../Memory/MarginTransform.definitions.md#def-1fac543175746adf)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMarginGather.Scheme](../../Memory/MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMarginGather.Shape](../../Memory/MarginTransform.definitions.md#def-1b196fc79b9f7c83)
- [CodedSorting.CommonStaticMarginGather.codeFrom](MarginGather.definitions.md#def-93c865ab379b3d80)

**基础库名称**

`instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-af684a80bcdde8e2"></a>
## `CodedSorting.CommonStaticMarginGather.codeFrom.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](MarginGather.lean)

**类型**

```lean
(motive : ℕ → ℕ → Sort u_1) → (x x_1 : ℕ) → ((x : ℕ) → motive x 0) → ((k n : ℕ) → motive k n.succ) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x_1 (h_1 x) fun n => h_2 x n
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`
