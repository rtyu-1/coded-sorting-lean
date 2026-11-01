# StackFrames 的定义

[源码](StackFrames.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-0909f815c38bd731"></a>
## `CodedSorting.CommonMSDStack.frameBlocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StackFrames.lean#L16)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.PhysicalStreamCursor.blockCount q.block q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat`

<a id="def-5e2a13bcaeb00c37"></a>
## `CodedSorting.CommonMSDStack.frameBase`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StackFrames.lean#L18)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q stack depth => stack + depth * CodedSorting.CommonMSDStack.frameBlocks q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDStack.frameBlocks](StackFrames.definitions.md#def-0909f815c38bd731)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-40ae7039b490e78c"></a>
## `CodedSorting.CommonMSDStack.stage`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StackFrames.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun q continuation s =>
  {
    leaf :=
      CodedSorting.ResidentLeafBank.putBlock 0 q.digits
        (CodedSorting.PhysicalStreamCursor.encodeNat q.digits q.w continuation) s.leaf,
    readers := s.readers, writers := s.writers, transfer := s.transfer, scalars := s.scalars,
    directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.PhysicalStreamCursor.encodeNat](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-0b39ac6782c7ab72)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafBank.putBlock](../../../Shared/Memory/ResidentLeafBank.definitions.md#def-32878637bd21e594)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-b5b0422bae22f7ac"></a>
## `CodedSorting.CommonMSDStack.stageInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StackFrames.lean#L24)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q continuation =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonMSDStack.stage q continuation (CodedSorting.CommonSortingNormalization.unpack ram)),
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../../Shared/Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonMSDStack.stage](StackFrames.definitions.md#def-40ae7039b490e78c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../../../Shared/Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-51f30c29b49e7b20"></a>
## `CodedSorting.CommonMSDStack.pushCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StackFrames.lean#L27)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q stack depth continuation =>
  CodedSorting.CommonMSDStack.stageInstruction q continuation ::
    CodedSorting.CommonStaticLeaf.writeCode q (CodedSorting.CommonMSDStack.frameBase q stack depth) q.digits
      (CodedSorting.CommonMSDStack.frameBlocks q)
```

**继续展开**

- [CodedSorting.CommonMSDStack.stageInstruction](StackFrames.definitions.md#def-b5b0422bae22f7ac)
- [CodedSorting.CommonMSDStack.frameBase](StackFrames.definitions.md#def-5e2a13bcaeb00c37)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonStaticLeaf.writeCode](../../../Shared/Programs/Static/Leaf.definitions.md#def-d8b6afa318659a57)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDStack.frameBlocks](StackFrames.definitions.md#def-0909f815c38bd731)

**基础库名称**

`List.cons`, `List`, `Nat`

<a id="def-46134f2140237a51"></a>
## `CodedSorting.CommonMSDStack.popCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StackFrames.lean#L31)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q stack depth =>
  CodedSorting.CommonStaticLeaf.readCode q (CodedSorting.CommonMSDStack.frameBase q stack depth) q.digits
    (CodedSorting.CommonMSDStack.frameBlocks q)
```

**继续展开**

- [CodedSorting.CommonMSDStack.frameBase](StackFrames.definitions.md#def-5e2a13bcaeb00c37)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticLeaf.readCode](../../../Shared/Programs/Static/Leaf.definitions.md#def-292caf1044d209bc)
- [CodedSorting.CommonMSDStack.frameBlocks](StackFrames.definitions.md#def-0909f815c38bd731)

**基础库名称**

`List`, `Nat`

<a id="def-f6624f3392766a49"></a>
## `CodedSorting.CommonMSDStack.loadedWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StackFrames.lean#L34)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonLeafProgram.Store q → CodedSorting.WordControl.Words q.digits q.w
```

**定义**

```lean
fun q s j => CodedSorting.ResidentLeafBank.getWord s.leaf ↑j
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.ResidentLeafBank.getWord](../../../Shared/Memory/ResidentLeafBank.definitions.md#def-43482f33d26d74a0)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-dcc5f7389307e9a0"></a>
## `CodedSorting.CommonMSDStack.loaded`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StackFrames.lean#L37)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonLeafProgram.Store q → ℕ
```

**定义**

```lean
fun q s => CodedSorting.WordControl.decodeWords (CodedSorting.CommonMSDStack.loadedWords q s)
```

**继续展开**

- [CodedSorting.WordControl.decodeWords](../../../Shared/Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDStack.loadedWords](StackFrames.definitions.md#def-f6624f3392766a49)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)

**基础库名称**

`Nat`
