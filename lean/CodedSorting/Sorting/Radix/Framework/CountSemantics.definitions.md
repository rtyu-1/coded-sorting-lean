# CountSemantics 的定义

[源码](CountSemantics.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-46706ffe2c7d754a"></a>
## `CodedSorting.CommonMSDDirectoryScan.counterWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L17)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      CodedSorting.CommonLeafProgram.Store q → Fin K → CodedSorting.WordControl.Words q.digits q.w
```

**定义**

```lean
fun {K} q hfit s k j => CodedSorting.ResidentLeafBank.raw s.leaf (Fin.castLE hfit (finProdFinEquiv (k, j)))
```

**继续展开**

- [CodedSorting.ResidentLeafBank.raw](../../../Shared/Memory/ResidentLeafBank.definitions.md#def-d1d4a603610970b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Fin.castLE`, `Equiv`, `Prod.mk`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `finProdFinEquiv`, `Prod`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-fdbe0c02f096da72"></a>
## `CodedSorting.CommonMSDDirectoryScan.counter`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L21)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q → CodedSorting.CommonLeafProgram.Store q → Fin K → ℕ
```

**定义**

```lean
fun {K} q hfit s k => CodedSorting.WordControl.decodeWords (CodedSorting.CommonMSDDirectoryScan.counterWords q hfit s k)
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.WordControl.decodeWords](../../../Shared/Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonMSDDirectoryScan.counterWords](CountSemantics.definitions.md#def-46706ffe2c7d754a)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Nat`, `Fin`, `instHMul`

<a id="def-5029535870be07ae"></a>
## `CodedSorting.CommonMSDDirectoryScan.putCounters`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L24)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    (Fin K → ℕ) → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun {K} q values s =>
  {
    leaf :=
      CodedSorting.ResidentLeafBank.putBlock 0 (K * q.digits)
        (CodedSorting.CommonSortingNormalization.family fun k =>
          CodedSorting.PhysicalStreamCursor.encodeNat q.digits q.w (values k))
        s.leaf,
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
- [CodedSorting.CommonSortingNormalization.family](../../Resources/Framework/NormalizationFrames.definitions.md#def-e889a8cc1af89e2d)
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

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-a57f9e90a67c14da"></a>
## `CodedSorting.CommonMSDDirectoryScan.blockCounts`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L51)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    (CodedSorting.WordControl.Word q.w → Fin K) → ℕ → ℕ → CodedSorting.WordControl.Words q.block q.w → Fin K → ℕ
```

**定义**

```lean
fun {K} q key n i block k =>
  ∑ j, if i * q.block + ↑j < 3 * n ∧ (i * q.block + ↑j) % 3 = 1 ∧ key (block j) = k then 1 else 0
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `Finset.univ`, `instDecidableEqFin`, `Nat.instMod`, `instHMod`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Fin.fintype`, `instHAdd`, `HMod.hMod`, `And`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `Nat.instAddCommMonoid`, `instDecidableEqNat`, `instLTNat`, `instDecidableAnd`, `OfNat.ofNat`, `Fin`, `Eq`, `Finset.sum`, `instHMul`, `ite`

<a id="def-0b59ca69e7a4811a"></a>
## `CodedSorting.CommonMSDDirectoryScan.afterBlock`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L56)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      (CodedSorting.WordControl.Word q.w → Fin K) →
        ℕ → ℕ → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun {K} q hfit key n i s =>
  CodedSorting.CommonMSDDirectoryScan.putCounters q
    (fun k =>
      CodedSorting.CommonMSDDirectoryScan.counter q hfit s k +
        CodedSorting.CommonMSDDirectoryScan.blockCounts q key n i s.transfer k)
    s
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonMSDDirectoryScan.counter](CountSemantics.definitions.md#def-fdbe0c02f096da72)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonMSDDirectoryScan.putCounters](CountSemantics.definitions.md#def-5029535870be07ae)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDDirectoryScan.blockCounts](CountSemantics.definitions.md#def-a57f9e90a67c14da)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `instHMul`

<a id="def-b1869c2d6873593d"></a>
## `CodedSorting.CommonMSDDirectoryScan.readAt`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L60)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      (CodedSorting.WordControl.Word q.w → Fin K) → ℕ → ℕ → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun {K} q hfit key source n i =>
  if h : source + i < q.N ^ q.exponent then
    {
      operation :=
        CodedSorting.Normalization.Command.read ⟨source + i, h⟩
          (CodedSorting.CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
      resume := fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonMSDDirectoryScan.afterBlock q hfit key n i
            (CodedSorting.CommonSortingNormalization.unpack ram)) }
  else { operation := CodedSorting.Normalization.Command.localOp id, resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafWindow.transferWindow](../../../Shared/Memory/Leaf/Program.definitions.md#def-e331864fad0a6a8e)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.Normalization.Command.read](../../../Shared/Programs/Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../../Shared/Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../../../Shared/Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMSDDirectoryScan.afterBlock](CountSemantics.definitions.md#def-0b59ca69e7a4811a)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `id`, `instMulNat`, `LE.le`, `instLENat`, `dite`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `Fin`, `Not`, `instHMul`

<a id="def-db7b6a6e23cd5090"></a>
## `CodedSorting.CommonMSDDirectoryScan.initCounters`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L67)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q K =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonMSDDirectoryScan.putCounters q (fun x => 0)
            (CodedSorting.CommonSortingNormalization.unpack ram)),
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonMSDDirectoryScan.putCounters](CountSemantics.definitions.md#def-5029535870be07ae)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../../Shared/Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../../../Shared/Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-712d905df9761f0e"></a>
## `CodedSorting.CommonMSDDirectoryScan.readCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L70)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      (CodedSorting.WordControl.Word q.w → Fin K) → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {K} q hfit key source n blocks =>
  List.map (CodedSorting.CommonMSDDirectoryScan.readAt q hfit key source n) (List.range blocks)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonMSDDirectoryScan.readAt](CountSemantics.definitions.md#def-b1869c2d6873593d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`HMul.hMul`, `List.map`, `instMulNat`, `List.range`, `LE.le`, `instLENat`, `List`, `Nat`, `Fin`, `instHMul`

<a id="def-95755ebe28609e42"></a>
## `CodedSorting.CommonMSDDirectoryScan.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CountSemantics.lean#L74)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      (CodedSorting.WordControl.Word q.w → Fin K) → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {K} q hfit key source n =>
  CodedSorting.CommonMSDDirectoryScan.initCounters q K ::
    CodedSorting.CommonMSDDirectoryScan.readCode q hfit key source n (CodedSorting.CommonRecordProgram.recordBlocks q n)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDDirectoryScan.readCode](CountSemantics.definitions.md#def-712d905df9761f0e)
- [CodedSorting.CommonMSDDirectoryScan.initCounters](CountSemantics.definitions.md#def-db7b6a6e23cd5090)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `Nat`, `Fin`, `instHMul`
