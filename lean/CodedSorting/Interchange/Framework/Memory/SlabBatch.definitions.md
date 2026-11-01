# SlabBatch 的定义

[源码](SlabBatch.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e192f85de221fbac"></a>
## `CodedSorting.CommonSlabBatch.recordBase`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L13)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q r buffer c => CodedSorting.CommonSlabBatch.base q (r * 3) buffer c
```

**继续展开**

- [CodedSorting.CommonSlabBatch.base](SlabBatchAllocation.definitions.md#def-50e910f2657056f4)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-0c2656415697d303"></a>
## `CodedSorting.CommonSlabBatch.Children`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L23)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ →
    (r : ℕ) →
      ℕ → ℕ → ℕ → (CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r) → Type
```

**定义**

```lean
fun q C r buffer work limit F =>
  (c : Fin C) →
    CodedSorting.CommonRecordProgram.Program q r (CodedSorting.CommonSlabBatch.recordBase q r buffer ↑c) work limit F
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](SlabBatch.definitions.md#def-e192f85de221fbac)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Fin.val`, `Nat`, `Fin`

<a id="def-e3148cb31fe3d290"></a>
## `CodedSorting.CommonSlabBatch.childrenCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L27)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {C r buffer work limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r} →
      CodedSorting.CommonSlabBatch.Children q C r buffer work limit F →
        List (Fin C) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} {C r buffer work limit} {F} p cs => List.flatMap (fun c => (p c).instructions) cs
```

**继续展开**

- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](SlabBatch.definitions.md#def-e192f85de221fbac)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Fin.val`, `List`, `Nat`, `Fin`, `List.flatMap`

<a id="def-6506a7cf7429e159"></a>
## `CodedSorting.CommonSlabBatch.childrenCharge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L30)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {C r buffer work limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r} →
      CodedSorting.CommonSlabBatch.Children q C r buffer work limit F → List (Fin C) → ℕ
```

**定义**

```lean
fun {q} {C r buffer work limit} {F} p cs => (List.map (fun c => (p c).charge) cs).sum
```

**继续展开**

- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](SlabBatch.definitions.md#def-e192f85de221fbac)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)

**基础库名称**

`Nat.instMulZeroClass`, `List.map`, `List.sum`, `Fin.val`, `List`, `Nat`, `instAddNat`, `Fin`, `MulZeroClass.toZero`

<a id="def-1e347b15e5d5c6a2"></a>
## `CodedSorting.CommonSlabBatch.batchOutput`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L139)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {C r : ℕ} →
    (CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r) →
      CodedSorting.CommonRecordProgram.Records q (C * r) → CodedSorting.CommonRecordProgram.Records q (C * r)
```

**定义**

```lean
fun {q} {C r} F f =>
  CodedSorting.PhysicalLocalSortPadding.flattenColumns C r fun c => F (CodedSorting.CommonLocalSemantic.columns C r f c)
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.columns](../../../Sorting/Local/Framework/Semantic.definitions.md#def-95a6d284c26943ee)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.PhysicalLocalSortPadding.flattenColumns](../../../Sorting/Local/Framework/PhysicalLocalSortNode.definitions.md#def-2fddd3888cb48ed2)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Fin`, `instHMul`

<a id="def-9f372ef1e67d2962"></a>
## `CodedSorting.CommonSlabBatch.splitCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L142)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader C r source buffer =>
  CodedSorting.CommonStaticSlabSplit.code q reader C (r * 3) source (CodedSorting.CommonSlabBatch.slabMap q buffer)
```

**继续展开**

- [CodedSorting.CommonSlabBatch.slabMap](SlabBatchAllocation.definitions.md#def-6ddb3d5718e71f73)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSlabSplit.code](../../../Shared/Programs/Static/SlabSplit.definitions.md#def-70924b7f561a7e35)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-d2f3d085709c6708"></a>
## `CodedSorting.CommonSlabBatch.joinCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L145)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader C r source buffer =>
  CodedSorting.CommonStaticSlabJoinMapped.code q reader (r * 3) C source (CodedSorting.CommonSlabBatch.slabMap q buffer)
```

**继续展开**

- [CodedSorting.CommonSlabBatch.slabMap](SlabBatchAllocation.definitions.md#def-6ddb3d5718e71f73)
- [CodedSorting.CommonStaticSlabJoinMapped.code](../../../Shared/Programs/Static/SlabJoinMappedMath.definitions.md#def-3e50765d291b2bd7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-91f3e6957c73bbb5"></a>
## `CodedSorting.CommonSlabBatch.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L148)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {C r buffer work limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r} →
      Fin q.inventory.readers →
        ℕ →
          CodedSorting.CommonSlabBatch.Children q C r buffer work limit F →
            List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} {C r buffer work limit} {F} reader source p =>
  CodedSorting.CommonSlabBatch.splitCode q reader C r source buffer ++
      CodedSorting.CommonSlabBatch.childrenCode p (List.finRange C) ++
    CodedSorting.CommonSlabBatch.joinCode q reader C r source buffer
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSlabBatch.joinCode](SlabBatch.definitions.md#def-d2f3d085709c6708)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSlabBatch.childrenCode](SlabBatch.definitions.md#def-e3148cb31fe3d290)
- [CodedSorting.CommonSlabBatch.splitCode](SlabBatch.definitions.md#def-9f372ef1e67d2962)

**基础库名称**

`instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `Fin`, `List.finRange`, `HAppend.hAppend`

<a id="def-7aaa040aa3d8e129"></a>
## `CodedSorting.CommonSlabBatch.raw_correct`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SlabBatch.lean#L202)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {C r source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r}
  (reader : Fin q.inventory.readers) (p : CodedSorting.CommonSlabBatch.Children q C r buffer work limit F),
  source + CodedSorting.CommonRecordProgram.recordBlocks q (C * r) ≤ buffer →
    buffer + C * CodedSorting.CommonSlabBatch.stride q (r * 3) ≤ work →
      work ≤ limit →
        limit ≤ q.N ^ q.exponent →
          ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q (C * r)),
            CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
              CodedSorting.CommonRecordProgram.Encoded q
                (CodedSorting.CommonStaticSchedule.executeRaw q (CodedSorting.CommonSlabBatch.code reader source p)
                      s).1.disk
                source (CodedSorting.CommonSlabBatch.batchOutput F f)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](../../../Shared/Records/RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.stride](SlabBatchAllocation.definitions.md#def-94b29694418488f5)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSlabBatch.code](SlabBatch.definitions.md#def-91f3e6957c73bbb5)
- [CodedSorting.CommonSlabBatch.batchOutput](SlabBatch.definitions.md#def-1e347b15e5d5c6a2)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-361febf05dbfd1a6"></a>
## `CodedSorting.CommonSlabBatch.raw_frame`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SlabBatch.lean#L214)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {C r source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r}
  (reader : Fin q.inventory.readers) (p : CodedSorting.CommonSlabBatch.Children q C r buffer work limit F),
  source + CodedSorting.CommonRecordProgram.recordBlocks q (C * r) ≤ buffer →
    buffer + C * CodedSorting.CommonSlabBatch.stride q (r * 3) ≤ work →
      work ≤ limit →
        limit ≤ q.N ^ q.exponent →
          ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
            ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q (C * r) ≤ ↑a →
              ↑a < buffer ∨ limit ≤ ↑a →
                (CodedSorting.CommonStaticSchedule.executeRaw q (CodedSorting.CommonSlabBatch.code reader source p)
                          s).1.disk
                    a =
                  s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.stride](SlabBatchAllocation.definitions.md#def-94b29694418488f5)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSlabBatch.code](SlabBatch.definitions.md#def-91f3e6957c73bbb5)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-d21a80ef130c91f5"></a>
## `CodedSorting.CommonSlabBatch.code_safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SlabBatch.lean#L238)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {C r source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r}
  (reader : Fin q.inventory.readers) (p : CodedSorting.CommonSlabBatch.Children q C r buffer work limit F),
  ∀ i ∈ CodedSorting.CommonSlabBatch.code reader source p, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonSlabBatch.code](SlabBatch.definitions.md#def-91f3e6957c73bbb5)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`, `Fin`

<a id="def-72e8f62ff41b13fc"></a>
## `CodedSorting.CommonSlabBatch.code_cost`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SlabBatch.lean#L247)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {C r source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r}
  (reader : Fin q.inventory.readers) (p : CodedSorting.CommonSlabBatch.Children q C r buffer work limit F),
  CodedSorting.CommonStaticSchedule.cost q (CodedSorting.CommonSlabBatch.code reader source p) ≤
    CodedSorting.CommonSlabBatch.childrenCharge p (List.finRange C) +
      12 * (C * CodedSorting.CommonSlabBatch.stride q (r * 3))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSlabBatch.stride](SlabBatchAllocation.definitions.md#def-94b29694418488f5)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSlabBatch.code](SlabBatch.definitions.md#def-91f3e6957c73bbb5)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonSlabBatch.childrenCharge](SlabBatch.definitions.md#def-6506a7cf7429e159)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `List.finRange`, `instHMul`

<a id="def-12f91ca1669f4bf4"></a>
## `CodedSorting.CommonSlabBatch.code_length`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SlabBatch.lean#L260)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {C r source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r}
  (reader : Fin q.inventory.readers) (p : CodedSorting.CommonSlabBatch.Children q C r buffer work limit F),
  (CodedSorting.CommonSlabBatch.code reader source p).length ≤
    CodedSorting.CommonSlabBatch.childrenCharge p (List.finRange C) +
      12 * (C * CodedSorting.CommonSlabBatch.stride q (r * 3))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSlabBatch.stride](SlabBatchAllocation.definitions.md#def-94b29694418488f5)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSlabBatch.code](SlabBatch.definitions.md#def-91f3e6957c73bbb5)
- [CodedSorting.CommonSlabBatch.childrenCharge](SlabBatch.definitions.md#def-6506a7cf7429e159)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `List.finRange`, `List.length`, `instHMul`

<a id="def-ae51434b8b1ab7f4"></a>
## `CodedSorting.CommonSlabBatch.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SlabBatch.lean#L273)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {C r source buffer work limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q r → CodedSorting.CommonRecordProgram.Records q r} →
      Fin q.inventory.readers →
        CodedSorting.CommonSlabBatch.Children q C r buffer work limit F →
          source + CodedSorting.CommonRecordProgram.recordBlocks q (C * r) ≤ buffer →
            buffer + C * CodedSorting.CommonSlabBatch.stride q (r * 3) ≤ work →
              work ≤ limit →
                limit ≤ q.N ^ q.exponent →
                  CodedSorting.CommonRecordProgram.Program q (C * r) source buffer limit
                    (CodedSorting.CommonSlabBatch.batchOutput F)
```

**定义**

```lean
fun {q} {C r source buffer work limit} {F} reader p hs hw hwl hl =>
  { instructions := CodedSorting.CommonSlabBatch.code reader source p,
    charge :=
      CodedSorting.CommonSlabBatch.childrenCharge p (List.finRange C) +
        12 * (C * CodedSorting.CommonSlabBatch.stride q (r * 3)),
    correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSlabBatch.Children](SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.CommonRecordProgram.Program.mk](../../../Shared/Records/RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.raw_correct](SlabBatch.definitions.md#def-7aaa040aa3d8e129)
- [CodedSorting.CommonSlabBatch.raw_frame](SlabBatch.definitions.md#def-361febf05dbfd1a6)
- [CodedSorting.CommonSlabBatch.stride](SlabBatchAllocation.definitions.md#def-94b29694418488f5)
- [CodedSorting.CommonSlabBatch.code_safe](SlabBatch.definitions.md#def-d21a80ef130c91f5)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.code_length](SlabBatch.definitions.md#def-12f91ca1669f4bf4)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSlabBatch.code](SlabBatch.definitions.md#def-91f3e6957c73bbb5)
- [CodedSorting.CommonSlabBatch.code_cost](SlabBatch.definitions.md#def-72e8f62ff41b13fc)
- [CodedSorting.CommonSlabBatch.batchOutput](SlabBatch.definitions.md#def-1e347b15e5d5c6a2)
- [CodedSorting.CommonSlabBatch.childrenCharge](SlabBatch.definitions.md#def-6506a7cf7429e159)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `List.finRange`, `instHMul`
