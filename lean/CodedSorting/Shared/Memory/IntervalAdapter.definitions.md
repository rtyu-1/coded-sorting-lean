# IntervalAdapter 的定义

[源码](IntervalAdapter.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-42ec2f93b81c97b0"></a>
## `CodedSorting.CommonIntervalAdapter.Fits`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](IntervalAdapter.lean#L15)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonIntervalAdapter.Fits.mk](IntervalAdapter.definitions.md#def-cac8a7b85ad4866f)

**基础库名称**

`Nat`

<a id="def-cac8a7b85ad4866f"></a>
## `CodedSorting.CommonIntervalAdapter.Fits.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](IntervalAdapter.lean#L15)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n base O buffer work limit : ℕ},
  base + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * n) + 2 ≤ buffer →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 ≤ work →
      work ≤ limit → limit ≤ q.N ^ q.exponent → CodedSorting.CommonIntervalAdapter.Fits q n base O buffer work limit
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.PhysicalStreamCursor.blockCount](PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-18d290b3cabddc31"></a>
## `CodedSorting.CommonIntervalAdapter.extract`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalAdapter.lean#L32)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n base O buffer => CodedSorting.CommonIntervalCopy.code q reader (3 * O) 0 (3 * n) base buffer
```

**继续展开**

- [CodedSorting.CommonIntervalCopy.code](IntervalCopyBounds.definitions.md#def-873421a048c5b5e6)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-af8ddb7ab659c71c"></a>
## `CodedSorting.CommonIntervalAdapter.restore`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalAdapter.lean#L36)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n base O buffer => CodedSorting.CommonIntervalCopy.code q reader 0 (3 * O) (3 * n) buffer base
```

**继续展开**

- [CodedSorting.CommonIntervalCopy.code](IntervalCopyBounds.definitions.md#def-873421a048c5b5e6)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-56fec5a3eaf274ee"></a>
## `CodedSorting.CommonIntervalAdapter.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalAdapter.lean#L113)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    {n : ℕ} →
      {base O : ℕ} →
        {buffer work limit : ℕ} →
          {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
            CodedSorting.CommonRecordProgram.Program q n buffer work limit F →
              List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader {n base O buffer work limit} {F} p =>
  CodedSorting.CommonIntervalAdapter.extract q reader n base O buffer ++ p.instructions ++
    CodedSorting.CommonIntervalAdapter.restore q reader n base O buffer
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.restore](IntervalAdapter.definitions.md#def-af8ddb7ab659c71c)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](../Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonIntervalAdapter.extract](IntervalAdapter.definitions.md#def-18d290b3cabddc31)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-8209b76e93bb9a78"></a>
## `CodedSorting.CommonIntervalAdapter.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalAdapter.lean#L118)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q n O innerCharge =>
  6 * CodedSorting.CommonRecordProgram.recordBlocks q n + innerCharge +
    6 * CodedSorting.CommonIntervalCopy.pages q (3 * O) (3 * n)
```

**继续展开**

- [CodedSorting.CommonIntervalCopy.pages](IntervalCopyBounds.definitions.md#def-2c29f6b867b071a0)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-d1d989edc782cfa9"></a>
## `CodedSorting.CommonIntervalAdapter.code_correct`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](IntervalAdapter.lean#L132)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n base O buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n buffer work limit F),
  CodedSorting.CommonIntervalAdapter.Fits q n base O buffer work limit →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
      CodedSorting.CommonRecordInterval.EncodedAt q s.disk base O f →
        CodedSorting.CommonRecordInterval.EncodedAt q
          (CodedSorting.CommonStaticSchedule.executeRaw q (CodedSorting.CommonIntervalAdapter.code q reader p) s).1.disk
          base O (F f)
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.code](IntervalAdapter.definitions.md#def-56fec5a3eaf274ee)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonIntervalAdapter.Fits](IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.CommonLeafProgram.Machine](Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordInterval.EncodedAt](../Records/RecordOperations.definitions.md#def-0f2418ea3a290277)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Prod.fst`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-258d2f3a9fdbe111"></a>
## `CodedSorting.CommonIntervalAdapter.code_frame`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](IntervalAdapter.lean#L141)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n base O buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n buffer work limit F),
  CodedSorting.CommonIntervalAdapter.Fits q n base O buffer work limit →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
      ↑a < base + 3 * O / q.block ∨ base + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * n) ≤ ↑a →
        ↑a < buffer ∨ limit ≤ ↑a →
          (CodedSorting.CommonStaticSchedule.executeRaw q (CodedSorting.CommonIntervalAdapter.code q reader p) s).1.disk
              a =
            s.disk a
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.code](IntervalAdapter.definitions.md#def-56fec5a3eaf274ee)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonIntervalAdapter.Fits](IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.PhysicalStreamCursor.blockCount](PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonLeafProgram.Machine](Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-2cfea1641213d380"></a>
## `CodedSorting.CommonIntervalAdapter.code_word_frame`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](IntervalAdapter.lean#L155)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n base O buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n buffer work limit F),
  CodedSorting.CommonIntervalAdapter.Fits q n base O buffer work limit →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (j : ℕ),
      base + j / q.block < q.N ^ q.exponent →
        j < 3 * O ∨ 3 * O + 3 * n ≤ j →
          base + j / q.block < buffer ∨ limit ≤ base + j / q.block →
            CodedSorting.CommonMarginTransform.wordAt q
                (CodedSorting.CommonStaticSchedule.executeRaw q (CodedSorting.CommonIntervalAdapter.code q reader p)
                      s).1.disk
                base j =
              CodedSorting.CommonMarginTransform.wordAt q s.disk base j
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.code](IntervalAdapter.definitions.md#def-56fec5a3eaf274ee)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonMarginTransform.wordAt](MarginTransform.definitions.md#def-cbb100c2961a0843)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonIntervalAdapter.Fits](IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.CommonLeafProgram.Machine](Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-59e2b5150429db35"></a>
## `CodedSorting.CommonIntervalAdapter.code_safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](IntervalAdapter.lean#L173)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n base O buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n buffer work limit F),
  ∀ i ∈ CodedSorting.CommonIntervalAdapter.code q reader p, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.code](IntervalAdapter.definitions.md#def-56fec5a3eaf274ee)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`, `Fin`

<a id="def-f7636fc02e4fb4ca"></a>
## `CodedSorting.CommonIntervalAdapter.code_cost_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](IntervalAdapter.lean#L184)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n base O buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n buffer work limit F),
  CodedSorting.CommonStaticSchedule.cost q (CodedSorting.CommonIntervalAdapter.code q reader p) ≤
    CodedSorting.CommonIntervalAdapter.charge q n O p.charge
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.charge](IntervalAdapter.definitions.md#def-8209b76e93bb9a78)
- [CodedSorting.CommonIntervalAdapter.code](IntervalAdapter.definitions.md#def-56fec5a3eaf274ee)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`LE.le`, `instLENat`, `Nat`, `Fin`

<a id="def-373149637cd6a31e"></a>
## `CodedSorting.CommonIntervalAdapter.code_length_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](IntervalAdapter.lean#L192)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n base O buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n buffer work limit F),
  (CodedSorting.CommonIntervalAdapter.code q reader p).length ≤ CodedSorting.CommonIntervalAdapter.charge q n O p.charge
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.charge](IntervalAdapter.definitions.md#def-8209b76e93bb9a78)
- [CodedSorting.CommonIntervalAdapter.code](IntervalAdapter.definitions.md#def-56fec5a3eaf274ee)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`LE.le`, `instLENat`, `Nat`, `Fin`, `List.length`

<a id="def-481f90e2408630ba"></a>
## `CodedSorting.CommonIntervalAdapter.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalAdapter.lean#L200)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    {n base O buffer work limit : ℕ} →
      {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
        CodedSorting.CommonRecordProgram.Program q n buffer work limit F →
          CodedSorting.CommonIntervalAdapter.Fits q n base O buffer work limit →
            CodedSorting.CommonRecordInterval.Program q n base O buffer limit F
```

**定义**

```lean
fun q reader {n base O buffer work limit} {F} p h =>
  { instructions := CodedSorting.CommonIntervalAdapter.code q reader p,
    charge := CodedSorting.CommonIntervalAdapter.charge q n O p.charge, correct := ⋯, word_frame := ⋯, frame := ⋯,
    safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.charge](IntervalAdapter.definitions.md#def-8209b76e93bb9a78)
- [CodedSorting.CommonIntervalAdapter.code](IntervalAdapter.definitions.md#def-56fec5a3eaf274ee)
- [CodedSorting.CommonRecordInterval.Program](../Records/RecordOperations.definitions.md#def-2721e3818979b9a7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordInterval.Program.mk](../Records/RecordOperations.definitions.md#def-314c682c284969a9)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonIntervalAdapter.code_word_frame](IntervalAdapter.definitions.md#def-2cfea1641213d380)
- [CodedSorting.CommonIntervalAdapter.Fits](IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.CommonIntervalAdapter.code_length_le](IntervalAdapter.definitions.md#def-373149637cd6a31e)
- [CodedSorting.CommonIntervalAdapter.code_frame](IntervalAdapter.definitions.md#def-258d2f3a9fdbe111)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonIntervalAdapter.code_cost_le](IntervalAdapter.definitions.md#def-f7636fc02e4fb4ca)
- [CodedSorting.CommonIntervalAdapter.code_correct](IntervalAdapter.definitions.md#def-d1d989edc782cfa9)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonIntervalAdapter.code_safe](IntervalAdapter.definitions.md#def-59e2b5150429db35)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Nat`, `Fin`
