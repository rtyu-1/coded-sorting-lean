# RecordLeaf 的定义

[源码](RecordLeaf.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-ac665295c063faae"></a>
## `CodedSorting.CommonStaticRecordLeaf.Records`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordLeaf.lean#L17)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → Type
```

**定义**

```lean
fun q n => Fin n → CodedSorting.KeyRecordWords.Record q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`, `Fin`

<a id="def-85d10073cd28280d"></a>
## `CodedSorting.CommonStaticRecordLeaf.Bank`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordLeaf.lean#L18)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.CommonLeafTransform.Bank q
```

**继续展开**

- [CodedSorting.CommonLeafTransform.Bank](../../Memory/Leaf/Correctness.definitions.md#def-46cd46b2aa6cdd76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

<a id="def-9d9c91c95ed7a76e"></a>
## `CodedSorting.CommonStaticRecordLeaf.readRecords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordLeaf.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) →
    n ≤ 512 * q.height → CodedSorting.CommonStaticRecordLeaf.Bank q → CodedSorting.CommonStaticRecordLeaf.Records q n
```

**定义**

```lean
fun q n hn bank i => CodedSorting.ResidentLeafSort.recordAt bank (Fin.castLE hn i)
```

**继续展开**

- [CodedSorting.CommonStaticRecordLeaf.Records](RecordLeaf.definitions.md#def-ac665295c063faae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticRecordLeaf.Bank](RecordLeaf.definitions.md#def-85d10073cd28280d)
- [CodedSorting.ResidentLeafSort.recordAt](../../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-a9cafcc8feea7341)

**基础库名称**

`HMul.hMul`, `Fin.castLE`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-3e9ce857a46398fb"></a>
## `CodedSorting.CommonStaticRecordLeaf.cpu`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordLeaf.lean#L24)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) →
    n ≤ 512 * q.height →
      (CodedSorting.CommonStaticRecordLeaf.Records q n → CodedSorting.CommonStaticRecordLeaf.Records q n) →
        CodedSorting.CommonStaticRecordLeaf.Bank q → CodedSorting.CommonStaticRecordLeaf.Bank q
```

**定义**

```lean
fun q n hn F bank =>
  Fin.append (CodedSorting.ResidentLeafSort.header bank) fun j =>
    let p := finProdFinEquiv.symm j;
    if h : ↑p.1 < n then
      CodedSorting.KeyRecordWords.encode q.w ⋯
        (F (CodedSorting.CommonStaticRecordLeaf.readRecords q n hn bank) ⟨↑p.1, h⟩) p.2
    else CodedSorting.ResidentLeafBank.raw bank j
```

**继续展开**

- [CodedSorting.CommonStaticRecordLeaf.Records](RecordLeaf.definitions.md#def-ac665295c063faae)
- [CodedSorting.ResidentLeafBank.raw](../../Memory/ResidentLeafBank.definitions.md#def-d1d4a603610970b9)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonStaticRecordLeaf.cpu._proof_2](RecordLeaf.definitions.md#def-83e2226dc43514c9)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonStaticRecordLeaf.readRecords](RecordLeaf.definitions.md#def-9d9c91c95ed7a76e)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ResidentLeafSort.header](../../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-8e5c767d09c080c6)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticRecordLeaf.Bank](RecordLeaf.definitions.md#def-85d10073cd28280d)
- [CodedSorting.KeyRecordWords.encode](../../Records/KeyRecordWords.definitions.md#def-db8b85b6def9e34c)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Fin.mk`, `Equiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `dite`, `Nat`, `LT.lt`, `finProdFinEquiv`, `Nat.decLt`, `instLTNat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`, `DFunLike.coe`, `Not`, `Fin.append`, `instHMul`

<a id="def-560bc1049771a92c"></a>
## `CodedSorting.CommonStaticRecordLeaf.compute`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordLeaf.lean#L45)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) →
    n ≤ 512 * q.height →
      (CodedSorting.CommonStaticRecordLeaf.Records q n → CodedSorting.CommonStaticRecordLeaf.Records q n) →
        CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q n hn F =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        let s := CodedSorting.CommonSortingNormalization.unpack ram;
        CodedSorting.CommonSortingNormalization.pack
          { leaf := CodedSorting.CommonStaticRecordLeaf.cpu q n hn F s.leaf, readers := s.readers, writers := s.writers,
            transfer := s.transfer, scalars := s.scalars, directories := s.directories, shapes := s.shapes,
            top := s.top, pcs := s.pcs },
    resume := id }
```

**继续展开**

- [CodedSorting.CommonStaticRecordLeaf.Records](RecordLeaf.definitions.md#def-ac665295c063faae)
- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonStaticRecordLeaf.cpu](RecordLeaf.definitions.md#def-3e9ce857a46398fb)
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

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `id`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-227ccd18dc2ba2c5"></a>
## `CodedSorting.CommonStaticRecordLeaf.blocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordLeaf.lean#L49)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n => CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * n)
```

**继续展开**

- [CodedSorting.PhysicalStreamCursor.blockCount](../../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-67e23772624467e1"></a>
## `CodedSorting.CommonStaticRecordLeaf.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordLeaf.lean#L51)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) →
    n ≤ 512 * q.height →
      (CodedSorting.CommonStaticRecordLeaf.Records q n → CodedSorting.CommonStaticRecordLeaf.Records q n) →
        ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q n hn F source target =>
  CodedSorting.CommonStaticLeaf.readCode q source (3 * n) (CodedSorting.CommonStaticRecordLeaf.blocks q n) ++
      [CodedSorting.CommonStaticRecordLeaf.compute q n hn F] ++
    CodedSorting.CommonStaticLeaf.writeCode q target (3 * n) (CodedSorting.CommonStaticRecordLeaf.blocks q n)
```

**继续展开**

- [CodedSorting.CommonStaticRecordLeaf.Records](RecordLeaf.definitions.md#def-ac665295c063faae)
- [CodedSorting.CommonStaticRecordLeaf.blocks](RecordLeaf.definitions.md#def-227ccd18dc2ba2c5)
- [CodedSorting.CommonStaticRecordLeaf.compute](RecordLeaf.definitions.md#def-560bc1049771a92c)
- [CodedSorting.CommonStaticLeaf.writeCode](Leaf.definitions.md#def-d8b6afa318659a57)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticLeaf.readCode](Leaf.definitions.md#def-292caf1044d209bc)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List.cons`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `HAppend.hAppend`, `instHMul`, `List.nil`

<a id="def-83e2226dc43514c9"></a>
## `CodedSorting.CommonStaticRecordLeaf.cpu._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordLeaf.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), ℕ → Fin (512 * q.height * 3) → 2 ≤ q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`
