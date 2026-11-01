# GatherProgram 的定义

[源码](GatherProgram.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-d60e55a1e3a34402"></a>
## `CodedSorting.CommonBufferedBank.slot_bound`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GatherProgram.lean#L155)

**类型**

```lean
∀ {K : ℕ} (q : CodedSorting.CommonSortingNormalization.Configuration),
  K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
    ∀ (slot : Fin K) (j : Fin q.block), ↑slot * q.block + ↑j < CodedSorting.CommonExchangeLeaf.bankWords q
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`, `instHMul`

<a id="def-6afe0865d2c63a5b"></a>
## `CodedSorting.CommonBufferedBank.get`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L163)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin K → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonBlockPair.Block q
```

**定义**

```lean
fun {K} q hfit slot s j => CodedSorting.ResidentLeafBank.raw s.leaf ⟨↑slot * q.block + ↑j, ⋯⟩
```

**继续展开**

- [CodedSorting.ResidentLeafBank.raw](../ResidentLeafBank.definitions.md#def-d1d4a603610970b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonBufferedBank.slot_bound](GatherProgram.definitions.md#def-d60e55a1e3a34402)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonBlockPair.Block](../BlockPair.definitions.md#def-31b415875e0e521a)

**基础库名称**

`HMul.hMul`, `Fin.mk`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-8166fe39ad9738cc"></a>
## `CodedSorting.CommonBufferedBank.put`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L167)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin K →
      CodedSorting.CommonBlockPair.Block q →
        CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun {K} q slot block s =>
  { leaf := CodedSorting.ResidentLeafBank.putBlock (↑slot * q.block) q.block block s.leaf, readers := s.readers,
    writers := s.writers, transfer := s.transfer, scalars := s.scalars, directories := s.directories,
    shapes := s.shapes, top := s.top, pcs := s.pcs }
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
- [CodedSorting.ResidentLeafBank.putBlock](../ResidentLeafBank.definitions.md#def-32878637bd21e594)
- [CodedSorting.CommonLeafProgram.Store](../Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonBlockPair.Block](../BlockPair.definitions.md#def-31b415875e0e521a)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-bcd44c7ef9d2e793"></a>
## `CodedSorting.CommonBufferedBank.blendStore`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L215)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin K →
          CodedSorting.CommonBlockPair.Selection q →
            CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun {K} q hfit reader slot select s =>
  CodedSorting.CommonBufferedBank.put q slot
    (CodedSorting.CommonBlockPair.blend q select (CodedSorting.CommonBlockPair.buffer q reader s)
      (CodedSorting.CommonBufferedBank.get q hfit slot s))
    s
```

**继续展开**

- [CodedSorting.CommonBlockPair.buffer](../BlockPair.definitions.md#def-af60041b169cb3ab)
- [CodedSorting.CommonBlockPair.blend](../BlockPair.definitions.md#def-6a0b5a24c95ca446)
- [CodedSorting.CommonBlockPair.Selection](../BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonBufferedBank.get](GatherProgram.definitions.md#def-6afe0865d2c63a5b)
- [CodedSorting.CommonBufferedBank.put](GatherProgram.definitions.md#def-8166fe39ad9738cc)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Nat`, `Fin`, `instHMul`

<a id="def-31aa3d52aeaa81e0"></a>
## `CodedSorting.CommonBufferedBank.blendInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L246)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin K → CodedSorting.CommonBlockPair.Selection q → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun {K} q hfit reader slot select =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonBufferedBank.blendStore q hfit reader slot select
            (CodedSorting.CommonSortingNormalization.unpack ram)),
    resume := id }
```

**继续展开**

- [CodedSorting.CommonBufferedBank.blendStore](GatherProgram.definitions.md#def-bcd44c7ef9d2e793)
- [CodedSorting.CommonBlockPair.Selection](../BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../../Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `id`, `instMulNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `instHMul`

<a id="def-920506083587798f"></a>
## `CodedSorting.CommonBufferedBank.loadInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L253)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin K → Fin (q.N ^ q.exponent) → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun {K} q slot source =>
  {
    operation :=
      CodedSorting.Normalization.Command.read source
        (CodedSorting.CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    resume := fun ram =>
      let s := CodedSorting.CommonSortingNormalization.unpack ram;
      CodedSorting.CommonSortingNormalization.pack (CodedSorting.CommonBufferedBank.put q slot s.transfer s) }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafWindow.transferWindow](../Leaf/Program.definitions.md#def-e331864fad0a6a8e)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonBufferedBank.put](GatherProgram.definitions.md#def-8166fe39ad9738cc)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.Normalization.Command.read](../../Programs/Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonSortingNormalization.SourceState](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-0421a40f96c58437"></a>
## `CodedSorting.CommonBufferedBank.prepareInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L258)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q → Fin K → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun {K} q hfit slot =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        let s := CodedSorting.CommonSortingNormalization.unpack ram;
        CodedSorting.CommonSortingNormalization.pack
          { leaf := s.leaf, readers := s.readers, writers := s.writers,
            transfer := CodedSorting.CommonBufferedBank.get q hfit slot s, scalars := s.scalars,
            directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs },
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonBufferedBank.get](GatherProgram.definitions.md#def-6afe0865d2c63a5b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonSortingNormalization.SourceState](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.Normalization.Command.localOp](../../Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `id`, `instMulNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `instHMul`

<a id="def-d8d3ec6687d5fb09"></a>
## `CodedSorting.CommonBufferedBank.writeCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L262)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin K → Fin (q.N ^ q.exponent) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {K} q hfit slot target =>
  [CodedSorting.CommonBufferedBank.prepareInstruction q hfit slot, CodedSorting.CommonBlockPair.targetWrite q target]
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBlockPair.targetWrite](../BlockPair.definitions.md#def-3b05497ae0c5b9b7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBufferedBank.prepareInstruction](GatherProgram.definitions.md#def-0421a40f96c58437)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `instHMul`, `List.nil`

<a id="def-7c5c79f15b9020a1"></a>
## `CodedSorting.CommonBufferedGather.position`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L417)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → CodedSorting.CommonBlockPair.BitIndex q
```

**定义**

```lean
fun q i => ⟨i % CodedSorting.CommonPermutationPairs.width q, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonBufferedGather.position._proof_2](GatherProgram.definitions.md#def-e689914335d58a9c)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonPermutationPairs.width](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Fin.mk`, `Nat.instMod`, `instHMod`, `instMulNat`, `HMod.hMod`, `Nat`, `instHMul`

<a id="def-bfbe23ea2377e408"></a>
## `CodedSorting.CommonBufferedGather.selection`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L420)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → CodedSorting.CommonBlockPair.Selection q
```

**定义**

```lean
fun q destination source j =>
  if j = CodedSorting.CommonBufferedGather.position q destination then
    some (CodedSorting.CommonBufferedGather.position q source)
  else none
```

**继续展开**

- [CodedSorting.CommonBlockPair.Selection](../BlockPair.definitions.md#def-72875a088545ca0b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBlockPair.BitIndex](../BlockPair.definitions.md#def-092d69d0915ad7fc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBufferedGather.position](GatherProgram.definitions.md#def-7c5c79f15b9020a1)

**基础库名称**

`HMul.hMul`, `instDecidableEqFin`, `Option.some`, `instMulNat`, `Option.none`, `Nat`, `Eq`, `instHMul`, `Option`, `ite`

<a id="def-88f733e4b1d1cb48"></a>
## `CodedSorting.CommonBufferedGather.assemble`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L423)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin K → ℕ → ℕ → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun {K} q hfit reader slot destination source s =>
  CodedSorting.CommonBlockPair.stash q reader
    (CodedSorting.CommonBlockPair.blend q (CodedSorting.CommonBufferedGather.selection q destination source)
      (CodedSorting.CommonBufferedBank.get q hfit slot s) (CodedSorting.CommonBlockPair.buffer q reader s))
    s
```

**继续展开**

- [CodedSorting.CommonBlockPair.buffer](../BlockPair.definitions.md#def-af60041b169cb3ab)
- [CodedSorting.CommonBlockPair.stash](../BlockPair.definitions.md#def-8a544bc0c7186b7b)
- [CodedSorting.CommonBlockPair.blend](../BlockPair.definitions.md#def-6a0b5a24c95ca446)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonBufferedGather.selection](GatherProgram.definitions.md#def-bfbe23ea2377e408)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonBufferedBank.get](GatherProgram.definitions.md#def-6afe0865d2c63a5b)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Nat`, `Fin`, `instHMul`

<a id="def-96646856b77e2140"></a>
## `CodedSorting.CommonBufferedGather.assembleInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L430)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers → Fin K → ℕ → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun {K} q hfit reader slot destination source =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonBufferedGather.assemble q hfit reader slot destination source
            (CodedSorting.CommonSortingNormalization.unpack ram)),
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonBufferedGather.assemble](GatherProgram.definitions.md#def-88f733e4b1d1cb48)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../../Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `id`, `instMulNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `instHMul`

<a id="def-d55efa1172cb548b"></a>
## `CodedSorting.CommonBufferedGather.prepareInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L435)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q reader =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        let s := CodedSorting.CommonSortingNormalization.unpack ram;
        CodedSorting.CommonSortingNormalization.pack
          { leaf := s.leaf, readers := s.readers, writers := s.writers,
            transfer := CodedSorting.CommonBlockPair.buffer q reader s, scalars := s.scalars,
            directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs },
    resume := id }
```

**继续展开**

- [CodedSorting.CommonBlockPair.buffer](../BlockPair.definitions.md#def-af60041b169cb3ab)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonSortingNormalization.SourceState](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.Normalization.Command.localOp](../../Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-e9d25cf0fde2a1de"></a>
## `CodedSorting.CommonBufferedGather.writeCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L439)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → Fin (q.N ^ q.exponent) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader target =>
  [CodedSorting.CommonBufferedGather.prepareInstruction q reader, CodedSorting.CommonBlockPair.targetWrite q target]
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonBufferedGather.prepareInstruction](GatherProgram.definitions.md#def-d55efa1172cb548b)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBlockPair.targetWrite](../BlockPair.definitions.md#def-3b05497ae0c5b9b7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `List.cons`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `List.nil`

<a id="def-1d80a7f0beef4543"></a>
## `CodedSorting.CommonBufferedGather.fragment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L443)

**类型**

```lean
{V K L : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers →
        Fin V ≃ Fin K × Fin L → ℕ → ℕ → Fin V → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V K L} q hfit reader e arena target i =>
  (if ↑(e i).2 % CodedSorting.CommonPermutationPairs.width q = 0 then
        [CodedSorting.CommonBufferedBank.loadInstruction q (e i).1
            (CodedSorting.CommonPermutationPairs.address q arena
              (↑(e i).1 * CodedSorting.CommonPermutationPairs.count q L +
                ↑(e i).2 / CodedSorting.CommonPermutationPairs.width q))]
      else []) ++
      [CodedSorting.CommonBufferedGather.assembleInstruction q hfit reader (e i).1 ↑i ↑(e i).2] ++
    if
        ↑i % CodedSorting.CommonPermutationPairs.width q = CodedSorting.CommonPermutationPairs.width q - 1 ∨
          ↑i + 1 = V then
      CodedSorting.CommonBufferedGather.writeCode q reader
        (CodedSorting.CommonPermutationPairs.address q target (↑i / CodedSorting.CommonPermutationPairs.width q))
    else []
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonBufferedBank.loadInstruction](GatherProgram.definitions.md#def-920506083587798f)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonBufferedGather.assembleInstruction](GatherProgram.definitions.md#def-96646856b77e2140)
- [CodedSorting.CommonPermutationPairs.address](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-841830e6780927fe)
- [CodedSorting.CommonPermutationPairs.width](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBufferedGather.writeCode](GatherProgram.definitions.md#def-e9d25cf0fde2a1de)
- [CodedSorting.CommonPermutationPairs.count](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Equiv.instFunLike`, `instHDiv`, `HMul.hMul`, `HSub.hSub`, `Equiv`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List.cons`, `instHAppendOfAppend`, `List`, `instHAdd`, `HMod.hMod`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instDecidableEqNat`, `Or`, `List.instAppend`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instDecidableOr`, `HAppend.hAppend`, `instHMul`, `List.nil`, `ite`

<a id="def-846da812fe155804"></a>
## `CodedSorting.CommonBufferedGather.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherProgram.lean#L453)

**类型**

```lean
{V K L : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      Fin q.inventory.readers → Fin V ≃ Fin K × Fin L → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V K L} q hfit reader e arena target =>
  List.flatMap (CodedSorting.CommonBufferedGather.fragment q hfit reader e arena target) (List.finRange V)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonBufferedGather.fragment](GatherProgram.definitions.md#def-1d80a7f0beef4543)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Equiv`, `instMulNat`, `LE.le`, `instLENat`, `List`, `Nat`, `Prod`, `Fin`, `List.finRange`, `List.flatMap`, `instHMul`

<a id="def-e689914335d58a9c"></a>
## `CodedSorting.CommonBufferedGather.position._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GatherProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (i : ℕ),
  i % CodedSorting.CommonPermutationPairs.width q < CodedSorting.CommonPermutationPairs.width q
```

**继续展开**

- [CodedSorting.CommonPermutationPairs.width](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`
