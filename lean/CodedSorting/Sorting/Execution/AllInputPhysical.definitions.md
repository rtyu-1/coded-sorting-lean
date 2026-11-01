# AllInputPhysical 的定义

[源码](AllInputPhysical.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-94f0dff8aa110e18"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerControl.routine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L68)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q →
    (n : ℕ) →
      n ≤ q.N →
        (pre post : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
          (∀ i ∈ pre, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
            (∀ i ∈ post, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
              CodedSorting.CommonMSDRoutine.Routine q
                (CodedSorting.RadixController.tagCount q.N
                    (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
                    (CodedSorting.CommonMSDNodeTagBound.bound q (CodedSorting.CommonMSDParameters.radix q))
                    (CodedSorting.CommonMSDParameters.radix q) +
                  3)
```

**定义**

```lean
fun q p n hn pre post hpre hpost =>
  CodedSorting.CommonRoutineSandwich.routine q pre post hpre hpost
    (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.program q p n hn)
```

**继续展开**

- [CodedSorting.RadixController.tagCount](../Radix/Program/Shared/Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.CommonRoutineSandwich.routine](../../Shared/Memory/RoutineSandwich.definitions.md#def-173e31029a8382dd)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.program](../Radix/Program/Execution.definitions.md#def-35bd519ad31cff35)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](../Radix/Program/Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonMSDRoutine.Routine](../Radix/Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDParameters.radix](../Radix/Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Radix/Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-9d0de0a59c7833fc"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerControl.stride`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L73)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q →
    (n : ℕ) →
      n ≤ q.N →
        (pre post : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
          (∀ i ∈ pre, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
            (∀ i ∈ post, CodedSorting.CommonStaticSchedule.RespectsPC q i) → ℕ
```

**定义**

```lean
fun q p n hn pre post hpre hpost =>
  (Finset.univ.sup fun tag =>
      ((CodedSorting.Construction.Sorting.CommonIntegerControl.routine q p n hn pre post hpre hpost).body tag).length) +
    1
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerControl.routine](AllInputPhysical.definitions.md#def-94f0dff8aa110e18)
- [CodedSorting.RadixController.tagCount](../Radix/Program/Shared/Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.CommonMSDRoutine.Routine.body](../Radix/Framework/Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](../Radix/Program/Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDParameters.radix](../Radix/Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Radix/Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Nat.instLattice`, `Lattice.toSemilatticeSup`, `Finset.univ`, `Membership.mem`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.fintype`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Finset.sup`, `Nat.instOrderBot`, `OfNat.ofNat`, `Fin`, `List.length`

<a id="def-a395be10026b2cbe"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerControl.threshold`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L78)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun κ => 8 * CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.threshold κ
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.threshold](../Radix/Program/Execution.definitions.md#def-c3b72f2d74ffa04b)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-9bb30db0e091ff34"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L196)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q →
    ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q p n => CodedSorting.CommonIntegerExpand.code q p.reader n 0
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](../Radix/Program/Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.reader](../Radix/Program/Execution.definitions.md#def-11ddc110e589ac63)
- [CodedSorting.CommonIntegerExpand.code](Framework/File.definitions.md#def-9fbe4953afb337fe)

**基础库名称**

`instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`

<a id="def-58cf320b4d8ccb5c"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L199)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q n => CodedSorting.CommonIntegerProjection.code q n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonIntegerProjection.code](Framework/File.definitions.md#def-acb6500e31fe8928)

**基础库名称**

`List`, `Nat`

<a id="def-63e86d1459e1c566"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L201)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q →
    (n : ℕ) →
      n ≤ q.N →
        CodedSorting.CommonMSDRoutine.Routine q
          (CodedSorting.RadixController.tagCount q.N (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
              (CodedSorting.CommonMSDNodeTagBound.bound q (CodedSorting.CommonMSDParameters.radix q))
              (CodedSorting.CommonMSDParameters.radix q) +
            3)
```

**定义**

```lean
fun q p n hn =>
  CodedSorting.Construction.Sorting.CommonIntegerControl.routine q p n hn
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n)
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n) ⋯ ⋯
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerControl.routine](AllInputPhysical.definitions.md#def-94f0dff8aa110e18)
- [CodedSorting.RadixController.tagCount](../Radix/Program/Shared/Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre](AllInputPhysical.definitions.md#def-9bb30db0e091ff34)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine._proof_1](AllInputPhysical.definitions.md#def-7deaad65e3374193)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](../Radix/Program/Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonMSDRoutine.Routine](../Radix/Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](../Radix/Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post](AllInputPhysical.definitions.md#def-58cf320b4d8ccb5c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonIntegerProjection.safe](Framework/File.definitions.md#def-d8bf223ac75bbc0f)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Radix/Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-1152b926ae0f69f6"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L205)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q → (n : ℕ) → n ≤ q.N → ℕ
```

**定义**

```lean
fun q p n hn =>
  CodedSorting.Construction.Sorting.CommonIntegerControl.stride q p n hn
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n)
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n) ⋯ ⋯
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerControl.stride](AllInputPhysical.definitions.md#def-9d0de0a59c7833fc)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre](AllInputPhysical.definitions.md#def-9bb30db0e091ff34)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine._proof_1](AllInputPhysical.definitions.md#def-7deaad65e3374193)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post](AllInputPhysical.definitions.md#def-58cf320b4d8ccb5c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonIntegerProjection.safe](Framework/File.definitions.md#def-d8bf223ac75bbc0f)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-a6083278b0d28485"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L209)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q →
    (n : ℕ) → n ≤ q.N → CodedSorting.CommonSortingNormalization.SourcePolicy q
```

**定义**

```lean
fun q p n hn =>
  (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).policy
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourcePolicy](../Resources/Framework/NormalizationFrames.definitions.md#def-1812a6349a1bc9a7)
- [CodedSorting.RadixController.tagCount](../Radix/Program/Shared/Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine](AllInputPhysical.definitions.md#def-63e86d1459e1c566)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride](AllInputPhysical.definitions.md#def-1152b926ae0f69f6)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](../Radix/Program/Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonMSDRoutine.Routine.policy](../Radix/Framework/Routine.definitions.md#def-965de1a0fdc439c9)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](../Radix/Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Radix/Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-3aa5a358114bbcc9"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initStore`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L216)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q →
    (n : ℕ) → n ≤ q.N → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun q p n hn store =>
  { leaf := store.leaf, readers := store.readers, writers := store.writers, transfer := store.transfer,
    scalars := store.scalars, directories := store.directories, shapes := store.shapes,
    top :=
      CodedSorting.PhysicalStreamCursor.encodeNat q.digits q.w
        (↑(CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).entry *
          CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn),
    pcs := store.pcs }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.RadixController.tagCount](../Radix/Program/Shared/Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine](AllInputPhysical.definitions.md#def-63e86d1459e1c566)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.PhysicalStreamCursor.encodeNat](../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-0b39ac6782c7ab72)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../Radix/Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride](AllInputPhysical.definitions.md#def-1152b926ae0f69f6)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](../Radix/Program/Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonMSDParameters.radix](../Radix/Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Radix/Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)
- [CodedSorting.CommonLeafProgram.Store](../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-8076348bea489e3a"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.allowance`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L363)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun κ =>
  max (CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.diskThreshold κ)
    (CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.diskThreshold](../Radix/Program/AllocatedCapacity.definitions.md#def-3f47c9d86edca801)
- [CodedSorting.Construction.Sorting.CommonIntegerControl.threshold](AllInputPhysical.definitions.md#def-a395be10026b2cbe)

**基础库名称**

`Nat.instMax_mathlib`, `Max.max`, `Nat`

<a id="def-7f70c65dfd9697d3"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L367)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun κ => 17 + Nat.clog 2 (CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.allowance κ)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.allowance](AllInputPhysical.definitions.md#def-8076348bea489e3a)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.clog`

<a id="def-669e5e2bec91e9a7"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L403)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
          CodedSorting.Construction.streamCount ≤
        q.inventory.ratio →
      (κ : ℝ) →
        ↑q.w * Real.log 2 ≤ κ * Real.log ↑q.N →
          CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent
                (CodedSorting.CommonMSDPublicWordBounds.wordFactor κ) ≤
              q.exponent →
            CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q
```

**定义**

```lean
fun q reader hratio κ hword he => { reader := reader, normal := ⋯, source := 0, capacity := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent](AllInputPhysical.definitions.md#def-7f70c65dfd9697d3)
- [CodedSorting.PhysicalLeafParameters.minimumRatio](../../Shared/Memory/EdgeReadBit.definitions.md#def-5b3ccb2ea10f8cb1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters._proof_6](AllInputPhysical.definitions.md#def-2155913f834bdada)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.SortingResourceBudget.Inventory.ratio](../Bounds/SortingResourceBudget.definitions.md#def-197343a4949f7653)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters._proof_5](AllInputPhysical.definitions.md#def-7a11b7d763051480)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](../Radix/Program/Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.RecursiveParameters.normalized_of_inventory](../../Interchange/Recursion/Workspace.definitions.md#def-26fe83f7876f95ec)
- [CodedSorting.CommonMSDPublicWordBounds.wordFactor](../Radix/Framework/RadixCost.definitions.md#def-4246d329afb4786f)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.mk](../Radix/Program/Execution.definitions.md#def-f936302f9f48bf3e)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Real.instLE`, `Real`, `HMul.hMul`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.cast`, `Real.log`, `instNatAtLeastTwo`, `Nat`, `Real.instMul`, `OfNat.ofNat`, `Fin`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-848b330547989da0"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](AllInputPhysical.lean#L607)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.mk](AllInputPhysical.definitions.md#def-d7904f0dfd436a54)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

<a id="def-d7904f0dfd436a54"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](AllInputPhysical.lean#L611)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  Fin q.inventory.readers →
    CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
          CodedSorting.Construction.streamCount ≤
        q.inventory.ratio →
      (kappa : ℝ) →
        0 ≤ kappa →
          ↑q.w * Real.log 2 ≤ kappa * Real.log ↑q.N →
            CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent
                  (CodedSorting.CommonMSDPublicWordBounds.wordFactor kappa) ≤
                q.exponent →
              CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent](AllInputPhysical.definitions.md#def-7f70c65dfd9697d3)
- [CodedSorting.PhysicalLeafParameters.minimumRatio](../../Shared/Memory/EdgeReadBit.definitions.md#def-5b3ccb2ea10f8cb1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.SortingResourceBudget.Inventory.ratio](../Bounds/SortingResourceBudget.definitions.md#def-197343a4949f7653)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonMSDPublicWordBounds.wordFactor](../Radix/Framework/RadixCost.definitions.md#def-4246d329afb4786f)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Real.instLE`, `Real`, `HMul.hMul`, `Real.instZero`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.cast`, `Real.log`, `instNatAtLeastTwo`, `Nat`, `Real.instMul`, `Zero.toOfNat0`, `OfNat.ofNat`, `Fin`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-02e238feff95fcb0"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.reader`

读取 `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters` 的 `reader` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](AllInputPhysical.lean#L612)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q → Fin q.inventory.readers
```

**定义**

```lean
fun q self => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Fin`

<a id="def-5f65c0cf8c3169c4"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.ratio`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AllInputPhysical.lean#L613)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration},
  CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q →
    CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
        CodedSorting.Construction.streamCount ≤
      q.inventory.ratio
```

**继续展开**

- [CodedSorting.PhysicalLeafParameters.minimumRatio](../../Shared/Memory/EdgeReadBit.definitions.md#def-5b3ccb2ea10f8cb1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.SortingResourceBudget.Inventory.ratio](../Bounds/SortingResourceBudget.definitions.md#def-197343a4949f7653)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-d10bb6fbdfc57558"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.kappa`

读取 `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters` 的 `kappa` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](AllInputPhysical.lean#L615)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q → ℝ
```

**定义**

```lean
fun q self => self.3
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Real`

<a id="def-3efb5ee49e670f99"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.word_bound`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AllInputPhysical.lean#L617)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  (self : CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q),
  ↑q.w * Real.log 2 ≤ self.kappa * Real.log ↑q.N
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.kappa](AllInputPhysical.definitions.md#def-d10bb6fbdfc57558)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Real.instLE`, `Real`, `HMul.hMul`, `instOfNatNat`, `LE.le`, `Nat.cast`, `Real.log`, `instNatAtLeastTwo`, `Nat`, `Real.instMul`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-551dd4f1d3e48ab1"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.exponent`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AllInputPhysical.lean#L618)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  (self : CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q),
  CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent
      (CodedSorting.CommonMSDPublicWordBounds.wordFactor self.kappa) ≤
    q.exponent
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent](AllInputPhysical.definitions.md#def-7f70c65dfd9697d3)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.kappa](AllInputPhysical.definitions.md#def-d10bb6fbdfc57558)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonMSDPublicWordBounds.wordFactor](../Radix/Framework/RadixCost.definitions.md#def-4246d329afb4786f)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-55be23544375f319"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.core`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L620)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q →
    CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q
```

**定义**

```lean
fun q p => CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters q p.reader ⋯ p.kappa ⋯ ⋯
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.exponent](AllInputPhysical.definitions.md#def-551dd4f1d3e48ab1)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.kappa](AllInputPhysical.definitions.md#def-d10bb6fbdfc57558)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters](AllInputPhysical.definitions.md#def-669e5e2bec91e9a7)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.reader](AllInputPhysical.definitions.md#def-02e238feff95fcb0)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.word_bound](AllInputPhysical.definitions.md#def-3efb5ee49e670f99)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters.ratio](AllInputPhysical.definitions.md#def-5f65c0cf8c3169c4)

<a id="def-b74db009407c6497"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L623)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q →
    CodedSorting.CommonSortingNormalization.SourcePolicy q
```

**定义**

```lean
fun q p =>
  CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy q
    (CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.core q p) q.N ⋯
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourcePolicy](../Resources/Framework/NormalizationFrames.definitions.md#def-1812a6349a1bc9a7)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm._proof_7](AllInputPhysical.definitions.md#def-c508533783f1f0cf)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.core](AllInputPhysical.definitions.md#def-55be23544375f319)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy](AllInputPhysical.definitions.md#def-a6083278b0d28485)

<a id="def-93ed69328300992d"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.start`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllInputPhysical.lean#L626)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q →
    CodedSorting.CommonLeafProgram.Store q →
      CodedSorting.CommonNormalizationController.Disk (q.N ^ q.exponent) q.B q.w →
        CodedSorting.CommonSortingNormalization.MachineState q
```

**定义**

```lean
fun q p store disk =>
  CodedSorting.CommonIntegerPhysical.start q
    (CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm q p)
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initStore q
      (CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.core q p) q.N ⋯ store)
    q.N ⋯ disk
```

**继续展开**

- [CodedSorting.CommonIntegerPhysical.start](Framework/PhysicalHalted.definitions.md#def-460cd4e0577a8aad)
- [CodedSorting.CommonNormalizationController.Disk](../../Shared/Memory/NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm._proof_7](AllInputPhysical.definitions.md#def-c508533783f1f0cf)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.core](AllInputPhysical.definitions.md#def-55be23544375f319)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.start._proof_9](AllInputPhysical.definitions.md#def-d228b2a1c9cccfb1)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initStore](AllInputPhysical.definitions.md#def-3aa5a358114bbcc9)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm](AllInputPhysical.definitions.md#def-b74db009407c6497)
- [CodedSorting.CommonSortingNormalization.MachineState](../Resources/Framework/NormalizationFrames.definitions.md#def-90721c68825dbf3f)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLeafProgram.Store](../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonSortingNormalization.Configuration.B](../Resources/Framework/NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-7a11b7d763051480"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AllInputPhysical.lean)

**类型**

```lean
(0 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-2155913f834bdada"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AllInputPhysical.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (hratio :
    CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
        CodedSorting.Construction.streamCount ≤
      q.inventory.ratio)
  (κ : ℝ),
  ↑q.w * Real.log 2 ≤ κ * Real.log ↑q.N →
    CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent
          (CodedSorting.CommonMSDPublicWordBounds.wordFactor κ) ≤
        q.exponent →
      CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q ⋯ q.N
        (CodedSorting.CommonMSDParameters.radix q) (CodedSorting.CommonMSDRadixCost.depth q) 0
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent](AllInputPhysical.definitions.md#def-7f70c65dfd9697d3)
- [CodedSorting.PhysicalLeafParameters.minimumRatio](../../Shared/Memory/EdgeReadBit.definitions.md#def-5b3ccb2ea10f8cb1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.SortingResourceBudget.Inventory.ratio](../Bounds/SortingResourceBudget.definitions.md#def-197343a4949f7653)
- [CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters._proof_5](AllInputPhysical.definitions.md#def-7a11b7d763051480)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.RecursiveParameters.normalized_of_inventory](../../Interchange/Recursion/Workspace.definitions.md#def-26fe83f7876f95ec)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](../Radix/Program/Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonMSDPublicWordBounds.wordFactor](../Radix/Framework/RadixCost.definitions.md#def-4246d329afb4786f)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDRadixCost.depth](../Radix/Framework/RadixCost.definitions.md#def-a15d9000a7ef719c)
- [CodedSorting.CommonMSDParameters.radix](../Radix/Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Real.instLE`, `Real`, `HMul.hMul`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.cast`, `Real.log`, `Nat`, `Real.instMul`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-c508533783f1f0cf"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AllInputPhysical.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), q.N ≤ q.N
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Preorder.toLE`, `LE.le`, `Nat.instPreorder`, `Nat`

<a id="def-d228b2a1c9cccfb1"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.start._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AllInputPhysical.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters q →
    CodedSorting.CommonIntegerPhysical.blocks q q.N < q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters](AllInputPhysical.definitions.md#def-848b330547989da0)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonIntegerPhysical.blocks](Framework/PhysicalHalted.definitions.md#def-129cc4c709eafa04)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`

<a id="def-7deaad65e3374193"></a>
## `CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AllInputPhysical.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (p : CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q) (n : ℕ),
  ∀ i ∈ CodedSorting.CommonIntegerExpand.code q p.reader n 0, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](../Radix/Program/Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](../Radix/Program/Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.reader](../Radix/Program/Execution.definitions.md#def-11ddc110e589ac63)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonIntegerExpand.code](Framework/File.definitions.md#def-9fbe4953afb337fe)

**基础库名称**

`Membership.mem`, `instOfNatNat`, `List`, `List.instMembership`, `Nat`, `OfNat.ofNat`
