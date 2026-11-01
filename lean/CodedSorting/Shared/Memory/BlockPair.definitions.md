# BlockPair 的定义

[源码](BlockPair.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-31b415875e0e521a"></a>
## `CodedSorting.CommonBlockPair.Block`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L16)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.WordControl.Words q.block q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

<a id="def-092d69d0915ad7fc"></a>
## `CodedSorting.CommonBlockPair.BitIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L17)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => Fin (q.block * q.w)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Fin`, `instHMul`

<a id="def-72875a088545ca0b"></a>
## `CodedSorting.CommonBlockPair.Selection`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L18)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.CommonBlockPair.BitIndex q → Option (CodedSorting.CommonBlockPair.BitIndex q)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](BlockPair.definitions.md#def-092d69d0915ad7fc)

**基础库名称**

`Option`

<a id="def-6a0b5a24c95ca446"></a>
## `CodedSorting.CommonBlockPair.blend`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonBlockPair.Selection q →
    CodedSorting.CommonBlockPair.Block q → CodedSorting.CommonBlockPair.Block q → CodedSorting.CommonBlockPair.Block q
```

**定义**

```lean
fun q select source target =>
  (CodedSorting.BitWordPacking.blockBits q.block q.w).symm fun i =>
    match select i with
    | none => (CodedSorting.BitWordPacking.blockBits q.block q.w) target i
    | some j => (CodedSorting.BitWordPacking.blockBits q.block q.w) source j
```

**继续展开**

- [CodedSorting.CommonBlockPair.blend.match_1](BlockPair.definitions.md#def-22729a70d5a74982)
- [CodedSorting.CommonBlockPair.Selection](BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.BitWordPacking.blockBits](../Words/WordConvention.definitions.md#def-a9a13aad90fdf19b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBlockPair.Block](BlockPair.definitions.md#def-31b415875e0e521a)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Unit`, `Nat`, `Equiv.symm`, `Fin`, `DFunLike.coe`, `instHMul`, `Option`

<a id="def-af60041b169cb3ab"></a>
## `CodedSorting.CommonBlockPair.buffer`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L33)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonBlockPair.Block q
```

**定义**

```lean
fun q reader s => CodedSorting.CommonSortingNormalizationStreams.payload (s.readers reader).resident
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalizationStreams.payload](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-c9dd272a76ec9d14)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonBlockPair.Block](BlockPair.definitions.md#def-31b415875e0e521a)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.resident](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-b265f9ce048f8da7)

**基础库名称**

`Fin`

<a id="def-8a544bc0c7186b7b"></a>
## `CodedSorting.CommonBlockPair.stash`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L36)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    CodedSorting.CommonBlockPair.Block q →
      CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun q reader block s =>
  { leaf := s.leaf,
    readers :=
      Function.update s.readers reader
        (let __src := s.readers reader;
        { base := __src.base, records := __src.records,
          resident :=
            Fin.append
              (Fin.append block
                (CodedSorting.CommonSortingNormalizationStreams.lengthWords (s.readers reader).resident))
              (CodedSorting.CommonSortingNormalizationStreams.cursorWords (s.readers reader).resident) }),
    writers := s.writers, transfer := s.transfer, scalars := s.scalars, directories := s.directories,
    shapes := s.shapes, top := s.top, pcs := s.pcs }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalizationStreams.cursorWords](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-05d4c3b81554a68a)
- [CodedSorting.CommonSortingNormalizationStreams.lengthWords](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-08c958193c72d21a)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.records](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-84c098bea2a6f007)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.base](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-707b2982a343dd0c)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.mk](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-616c4e863be5bc33)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalizationStreams.InputState](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonBlockPair.Block](BlockPair.definitions.md#def-31b415875e0e521a)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.resident](../../Sorting/Resources/Framework/NormalizationStreams.definitions.md#def-b265f9ce048f8da7)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)

**基础库名称**

`Function.update`, `instDecidableEqFin`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `Fin.append`

<a id="def-5dc5b806044bea03"></a>
## `CodedSorting.CommonBlockPair.sourceRead`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L48)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → Fin (q.N ^ q.exponent) → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q reader source =>
  {
    operation :=
      CodedSorting.Normalization.Command.read source
        (CodedSorting.CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    resume := fun ram =>
      let s := CodedSorting.CommonSortingNormalization.unpack ram;
      CodedSorting.CommonSortingNormalization.pack (CodedSorting.CommonBlockPair.stash q reader s.transfer s) }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonBlockPair.stash](BlockPair.definitions.md#def-8a544bc0c7186b7b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafWindow.transferWindow](Leaf/Program.definitions.md#def-e331864fad0a6a8e)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.Normalization.Command.read](../Programs/Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonSortingNormalization.SourceState](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-9b628bf2dc6f9652"></a>
## `CodedSorting.CommonBlockPair.targetRead`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L53)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    Fin (q.N ^ q.exponent) → CodedSorting.CommonBlockPair.Selection q → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q reader target select =>
  {
    operation :=
      CodedSorting.Normalization.Command.read target
        (CodedSorting.CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    resume := fun ram =>
      let s := CodedSorting.CommonSortingNormalization.unpack ram;
      CodedSorting.CommonSortingNormalization.pack
        { leaf := s.leaf, readers := s.readers, writers := s.writers,
          transfer :=
            CodedSorting.CommonBlockPair.blend q select (CodedSorting.CommonBlockPair.buffer q reader s) s.transfer,
          scalars := s.scalars, directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs } }
```

**继续展开**

- [CodedSorting.CommonBlockPair.buffer](BlockPair.definitions.md#def-af60041b169cb3ab)
- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonBlockPair.blend](BlockPair.definitions.md#def-6a0b5a24c95ca446)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonBlockPair.Selection](BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafWindow.transferWindow](Leaf/Program.definitions.md#def-e331864fad0a6a8e)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.Normalization.Command.read](../Programs/Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonSortingNormalization.SourceState](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-3b05497ae0c5b9b7"></a>
## `CodedSorting.CommonBlockPair.targetWrite`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L58)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin (q.N ^ q.exponent) → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q target =>
  {
    operation :=
      CodedSorting.Normalization.Command.write target
        (CodedSorting.CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafWindow.transferWindow](Leaf/Program.definitions.md#def-e331864fad0a6a8e)
- [CodedSorting.Normalization.Command.write](../Programs/Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-1132aa9fc93f6ac6"></a>
## `CodedSorting.CommonBlockPair.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockPair.lean#L61)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    Fin (q.N ^ q.exponent) →
      Fin (q.N ^ q.exponent) →
        CodedSorting.CommonBlockPair.Selection q → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader source target select =>
  [CodedSorting.CommonBlockPair.sourceRead q reader source,
    CodedSorting.CommonBlockPair.targetRead q reader target select, CodedSorting.CommonBlockPair.targetWrite q target]
```

**继续展开**

- [CodedSorting.CommonBlockPair.Selection](BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonBlockPair.targetRead](BlockPair.definitions.md#def-9b628bf2dc6f9652)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonBlockPair.sourceRead](BlockPair.definitions.md#def-5dc5b806044bea03)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBlockPair.targetWrite](BlockPair.definitions.md#def-3b05497ae0c5b9b7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `List.cons`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `List.nil`

<a id="def-22729a70d5a74982"></a>
## `CodedSorting.CommonBlockPair.blend.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](BlockPair.lean)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (motive : Option (CodedSorting.CommonBlockPair.BitIndex q) → Sort u_1) →
    (x : Option (CodedSorting.CommonBlockPair.BitIndex q)) →
      (Unit → motive none) → ((j : CodedSorting.CommonBlockPair.BitIndex q) → motive (some j)) → motive x
```

**定义**

```lean
fun q motive x h_1 h_2 => Option.casesOn x (h_1 ()) fun val => h_2 val
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](BlockPair.definitions.md#def-092d69d0915ad7fc)

**基础库名称**

`Unit.unit`, `Option.casesOn`, `Option.some`, `Option.none`, `Unit`, `Option`
