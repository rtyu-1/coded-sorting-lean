# RecordProgram 的定义

[源码](RecordProgram.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-f25ae600f691ab5a"></a>
## `CodedSorting.CommonResidentRecordProgram.rawCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordProgram.lean#L27)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (n : ℕ) →
      n ≤ 512 * q.height →
        (CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n) →
          ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n hn F source buffer =>
  CodedSorting.CommonStaticRecordLeaf.code q n hn F source buffer ++
    CodedSorting.CommonRecursiveExchange.copyCode q reader (n * (3 * q.w)) buffer source
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecursiveExchange.copyCode](../Recursion/OuterCopyFrame.definitions.md#def-654a82544fb518ba)
- [CodedSorting.CommonStaticRecordLeaf.code](../../../Shared/Programs/Static/RecordLeaf.definitions.md#def-67e23772624467e1)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `instHMul`

<a id="def-2c096dd0a20f36b5"></a>
## `CodedSorting.CommonResidentRecordProgram.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordProgram.lean#L33)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (n : ℕ) →
      n ≤ 512 * q.height →
        (CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n) →
          ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n hn F source buffer =>
  CodedSorting.CommonStaticFusion.fuse q
    (CodedSorting.CommonResidentRecordProgram.rawCode q reader n hn F source buffer)
```

**继续展开**

- [CodedSorting.CommonStaticFusion.fuse](../../../Shared/Programs/Static/Fusion.definitions.md#def-a8d53d872c4a7e53)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonResidentRecordProgram.rawCode](RecordProgram.definitions.md#def-f25ae600f691ab5a)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-07959c3ff1a01746"></a>
## `CodedSorting.CommonResidentRecordProgram.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordProgram.lean#L38)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n => 8 * CodedSorting.CommonRecordProgram.recordBlocks q n + 1
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-89032800f1dc7f12"></a>
## `CodedSorting.CommonResidentRecordProgram.raw_frame`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordProgram.lean#L77)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (n : ℕ)
  (hn : n ≤ 512 * q.height)
  (F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n)
  (source buffer limit : ℕ),
  source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ limit →
      limit ≤ q.N ^ q.exponent →
        ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
          ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
            ↑a < buffer ∨ limit ≤ ↑a →
              (CodedSorting.CommonStaticSchedule.executeRaw q
                        (CodedSorting.CommonResidentRecordProgram.code q reader n hn F source buffer) s).1.disk
                  a =
                s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonResidentRecordProgram.code](RecordProgram.definitions.md#def-2c096dd0a20f36b5)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-b98c803ea5f33c23"></a>
## `CodedSorting.CommonResidentRecordProgram.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordProgram.lean#L129)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (n : ℕ) →
      n ≤ 512 * q.height →
        (F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n) →
          (source buffer limit : ℕ) →
            source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer →
              buffer + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ limit →
                limit ≤ q.N ^ q.exponent → CodedSorting.CommonRecordProgram.Program q n source buffer limit F
```

**定义**

```lean
fun q reader n hn F source buffer limit hs hb hl =>
  { instructions := CodedSorting.CommonResidentRecordProgram.code q reader n hn F source buffer,
    charge := CodedSorting.CommonResidentRecordProgram.charge q n, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonResidentRecordProgram.program._proof_3](RecordProgram.definitions.md#def-7b92efd7f1d72f7c)
- [CodedSorting.CommonResidentRecordProgram.charge](RecordProgram.definitions.md#def-07959c3ff1a01746)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonResidentRecordProgram.program._proof_5](RecordProgram.definitions.md#def-2a35d44eb6fb05ee)
- [CodedSorting.CommonRecordProgram.Program.mk](../../../Shared/Records/RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.CommonResidentRecordProgram.raw_frame](RecordProgram.definitions.md#def-89032800f1dc7f12)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonResidentRecordProgram.program._proof_2](RecordProgram.definitions.md#def-dbbba6e6145437a2)
- [CodedSorting.CommonResidentRecordProgram.program._proof_4](RecordProgram.definitions.md#def-0a4c986afbdaa5f8)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonResidentRecordProgram.code](RecordProgram.definitions.md#def-2c096dd0a20f36b5)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-dbbba6e6145437a2"></a>
## `CodedSorting.CommonResidentRecordProgram.program._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (n : ℕ)
  (hn : n ≤ 512 * q.height)
  (F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n)
  (source buffer limit : ℕ),
  source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ limit →
      limit ≤ q.N ^ q.exponent →
        ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
          CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
            CodedSorting.CommonRecordProgram.Encoded q
              (CodedSorting.CommonStaticSchedule.executeRaw q
                    (CodedSorting.CommonResidentRecordProgram.code q reader n hn F source buffer) s).1.disk
              source (F f)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](../../../Shared/Records/RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonResidentRecordProgram.code](RecordProgram.definitions.md#def-2c096dd0a20f36b5)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-7b92efd7f1d72f7c"></a>
## `CodedSorting.CommonResidentRecordProgram.program._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (n : ℕ)
  (hn : n ≤ 512 * q.height)
  (F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n) (source buffer : ℕ),
  ∀
    i ∈
      CodedSorting.CommonStaticFusion.fuse q
        (CodedSorting.CommonResidentRecordProgram.rawCode q reader n hn F source buffer),
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonStaticFusion.fuse](../../../Shared/Programs/Static/Fusion.definitions.md#def-a8d53d872c4a7e53)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonResidentRecordProgram.rawCode](RecordProgram.definitions.md#def-f25ae600f691ab5a)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`HMul.hMul`, `Membership.mem`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `List.instMembership`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-0a4c986afbdaa5f8"></a>
## `CodedSorting.CommonResidentRecordProgram.program._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (n : ℕ)
  (hn : n ≤ 512 * q.height)
  (F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n)
  (source buffer limit : ℕ),
  source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ limit →
      limit ≤ q.N ^ q.exponent →
        CodedSorting.CommonStaticSchedule.cost q
            (CodedSorting.CommonResidentRecordProgram.code q reader n hn F source buffer) ≤
          CodedSorting.CommonResidentRecordProgram.charge q n
```

**继续展开**

- [CodedSorting.CommonResidentRecordProgram.charge](RecordProgram.definitions.md#def-07959c3ff1a01746)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonResidentRecordProgram.code](RecordProgram.definitions.md#def-2c096dd0a20f36b5)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-2a35d44eb6fb05ee"></a>
## `CodedSorting.CommonResidentRecordProgram.program._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (n : ℕ)
  (hn : n ≤ 512 * q.height)
  (F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n)
  (source buffer limit : ℕ),
  source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ limit →
      limit ≤ q.N ^ q.exponent →
        (CodedSorting.CommonStaticFusion.fuse q
              (CodedSorting.CommonResidentRecordProgram.rawCode q reader n hn F source buffer)).length ≤
          CodedSorting.CommonResidentRecordProgram.charge q n
```

**继续展开**

- [CodedSorting.CommonStaticFusion.fuse](../../../Shared/Programs/Static/Fusion.definitions.md#def-a8d53d872c4a7e53)
- [CodedSorting.CommonResidentRecordProgram.charge](RecordProgram.definitions.md#def-07959c3ff1a01746)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonResidentRecordProgram.rawCode](RecordProgram.definitions.md#def-f25ae600f691ab5a)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`
