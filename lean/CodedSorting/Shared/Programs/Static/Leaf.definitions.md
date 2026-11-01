# Leaf 的定义

[源码](Leaf.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-07673e53b36db539"></a>
## `CodedSorting.CommonStaticLeaf.loadEffect`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L16)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun q total k s =>
  { leaf := CodedSorting.ResidentLeafBank.putBlock (k * q.block) (min q.block (total - k * q.block)) s.transfer s.leaf,
    readers := s.readers, writers := s.writers, transfer := s.transfer, scalars := s.scalars,
    directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafBank.putBlock](../../Memory/ResidentLeafBank.definitions.md#def-32878637bd21e594)
- [CodedSorting.CommonLeafProgram.Store](../../Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `instOfNatNat`, `instHSub`, `Nat`, `Nat.instMin_mathlib`, `OfNat.ofNat`, `Min.min`, `instHMul`

<a id="def-f8b49d48def0a453"></a>
## `CodedSorting.CommonStaticLeaf.readAt`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L19)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q source total k =>
  if h : source + k < q.N ^ q.exponent then
    {
      operation :=
        CodedSorting.Normalization.Command.read ⟨source + k, h⟩
          (CodedSorting.CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
      resume := fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonStaticLeaf.loadEffect q total k (CodedSorting.CommonSortingNormalization.unpack ram)) }
  else { operation := CodedSorting.Normalization.Command.localOp id, resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafWindow.transferWindow](../../Memory/Leaf/Program.definitions.md#def-e331864fad0a6a8e)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.Normalization.Command.read](../Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticLeaf.loadEffect](Leaf.definitions.md#def-07673e53b36db539)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `id`, `dite`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `Not`

<a id="def-292caf1044d209bc"></a>
## `CodedSorting.CommonStaticLeaf.readCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L25)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q source total k => List.map (CodedSorting.CommonStaticLeaf.readAt q source total) (List.range k)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticLeaf.readAt](Leaf.definitions.md#def-f8b49d48def0a453)

**基础库名称**

`List.map`, `List.range`, `List`, `Nat`

<a id="def-abbb3a68ac509a2f"></a>
## `CodedSorting.CommonStaticLeaf.outputBlock`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L28)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → CodedSorting.CommonLeafTransform.Bank q → CodedSorting.CommonBlockPair.Block q
```

**定义**

```lean
fun q total k bank => CodedSorting.ResidentLeafBank.getBlock (k * q.block) (total - k * q.block) bank
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLeafTransform.Bank](../../Memory/Leaf/Correctness.definitions.md#def-46cd46b2aa6cdd76)
- [CodedSorting.ResidentLeafBank.getBlock](../../Memory/ResidentLeafBank.definitions.md#def-b47675a5946adf37)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBlockPair.Block](../../Memory/BlockPair.definitions.md#def-31b415875e0e521a)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `instOfNatNat`, `instHSub`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-3fd00f21f55b8d59"></a>
## `CodedSorting.CommonStaticLeaf.stage`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L31)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q total k =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        let s := CodedSorting.CommonSortingNormalization.unpack ram;
        CodedSorting.CommonSortingNormalization.pack
          { leaf := s.leaf, readers := s.readers, writers := s.writers,
            transfer := CodedSorting.CommonStaticLeaf.outputBlock q total k s.leaf, scalars := s.scalars,
            directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs },
    resume := id }
```

**继续展开**

- [CodedSorting.CommonStaticLeaf.outputBlock](Leaf.definitions.md#def-abbb3a68ac509a2f)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
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
- [CodedSorting.Normalization.Command.localOp](../Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-042043b77ced7fe8"></a>
## `CodedSorting.CommonStaticLeaf.writeAt`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L35)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q target k =>
  if h : target + k < q.N ^ q.exponent then CodedSorting.CommonBlockPair.targetWrite q ⟨target + k, h⟩
  else { operation := CodedSorting.Normalization.Command.localOp id, resume := id }
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.ControlledNormalization.Instruction.mk](../ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonBlockPair.targetWrite](../../Memory/BlockPair.definitions.md#def-3b05497ae0c5b9b7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `id`, `dite`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `Not`

<a id="def-d8b6afa318659a57"></a>
## `CodedSorting.CommonStaticLeaf.writeCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L39)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q target total k =>
  List.flatMap
    (fun j => [CodedSorting.CommonStaticLeaf.stage q total j, CodedSorting.CommonStaticLeaf.writeAt q target j])
    (List.range k)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticLeaf.writeAt](Leaf.definitions.md#def-042043b77ced7fe8)
- [CodedSorting.CommonStaticLeaf.stage](Leaf.definitions.md#def-3fd00f21f55b8d59)

**基础库名称**

`List.range`, `List.cons`, `List`, `Nat`, `List.flatMap`, `List.nil`

<a id="def-0932ae9c9386eedc"></a>
## `CodedSorting.CommonStaticLeaf.compute`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L42)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (V : ℕ) →
    V ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
      Equiv.Perm (Fin V) → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q V hV π =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        let s := CodedSorting.CommonSortingNormalization.unpack ram;
        CodedSorting.CommonSortingNormalization.pack
          { leaf := CodedSorting.CommonExchangeLeaf.cpu q V hV π s.leaf, readers := s.readers, writers := s.writers,
            transfer := s.transfer, scalars := s.scalars, directories := s.directories, shapes := s.shapes,
            top := s.top, pcs := s.pcs },
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
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
- [CodedSorting.CommonExchangeLeaf.cpu](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-d0d5c9a55366a7cd)
- [CodedSorting.Normalization.Command.localOp](../Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonExchangeLeaf.bankBits](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `LE.le`, `instLENat`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Fin`

<a id="def-c4f24073a5ed5287"></a>
## `CodedSorting.CommonStaticLeaf.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Leaf.lean#L47)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (V : ℕ) →
    V ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
      Equiv.Perm (Fin V) → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q V hV π source target =>
  let total := 3 * ↑(CodedSorting.CommonExchangeLeaf.roundedCount q V hV);
  let k := CodedSorting.PhysicalStreamCursor.blockCount q.block total;
  CodedSorting.CommonStaticLeaf.readCode q source total k ++ [CodedSorting.CommonStaticLeaf.compute q V hV π] ++
    CodedSorting.CommonStaticLeaf.writeCode q target total k
```

**继续展开**

- [CodedSorting.CommonStaticLeaf.compute](Leaf.definitions.md#def-0932ae9c9386eedc)
- [CodedSorting.CommonStaticLeaf.writeCode](Leaf.definitions.md#def-d8b6afa318659a57)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticLeaf.readCode](Leaf.definitions.md#def-292caf1044d209bc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.roundedCount](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-45a7ea9ade5bc038)
- [CodedSorting.CommonExchangeLeaf.bankBits](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `List.cons`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `instHMul`, `List.nil`
