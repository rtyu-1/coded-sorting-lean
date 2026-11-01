# Local 的定义

[源码](Local.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-cb6c05b26fef8869"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Local.lean#L21)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ
```

**定义**

```lean
fun q hnormal n =>
  CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
    CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-abd09b9ab586963a"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Local.lean#L24)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n =>
  CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 n +
    12 * (CodedSorting.CommonRecordProgram.recordBlocks q n + 1)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalBudget.budget](../../Local/Program.definitions.md#def-e7b5e8b778c9f2fd)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-6f054ddde493018b"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Local.lean#L27)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
      (n : ℕ) →
        n ≤ q.height ^ 2 →
          2 ≤ q.exponent →
            (base O buffer limit : ℕ) →
              base + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * n) + 2 ≤ buffer →
                buffer + CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q hnormal n ≤ limit →
                  limit ≤ q.N ^ q.exponent →
                    CodedSorting.CommonRecordInterval.Program q n base O buffer limit CodedSorting.Columnsort.sortColumn
```

**定义**

```lean
fun q reader hnormal n hn he base O buffer limit hs hw hl =>
  let work := buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2;
  let_fun hlocal := ⋯;
  let p :=
    CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer work limit ⋯
      hlocal hl;
  let_fun hf := ⋯;
  let adapted := CodedSorting.CommonIntervalAdapter.program q reader p hf;
  let_fun hcharge := ⋯;
  { instructions := adapted.instructions, charge := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n,
    correct := ⋯, word_frame := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_6](Local.definitions.md#def-02684e726e98da91)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_13](Local.definitions.md#def-ff02e201baf65aaa)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_8](Local.definitions.md#def-102bcd4416b843df)
- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_11](Local.definitions.md#def-d42066e94bb2d129)
- [CodedSorting.CommonRecordInterval.Program](../../../Shared/Records/RecordOperations.definitions.md#def-2721e3818979b9a7)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space](Local.definitions.md#def-cb6c05b26fef8869)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.CommonRecordInterval.Program.mk](../../../Shared/Records/RecordOperations.definitions.md#def-314c682c284969a9)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_10](Local.definitions.md#def-2effc9bf621f2775)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordInterval.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-16d82df30e410adf)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5](Local.definitions.md#def-7a27151142463a3a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonIntervalAdapter.program](../../../Shared/Memory/IntervalAdapter.definitions.md#def-481f90e2408630ba)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_12](Local.definitions.md#def-ec267d83f7dae74c)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_9](Local.definitions.md#def-f64811e1c899505c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonRecordInterval.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-63452802ff71011d)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_4](Local.definitions.md#def-0c49de9afa262c26)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_7](Local.definitions.md#def-ee47a4f76c3bb785)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge](Local.definitions.md#def-abd09b9ab586963a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `letFun`, `instHMul`

<a id="def-d07142e4e481d71a"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program_charge`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean#L51)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (hn : n ≤ q.height ^ 2)
  (he : 2 ≤ q.exponent) (base O buffer limit : ℕ)
  (hs : base + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * n) + 2 ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q hnormal n ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program q reader hnormal n hn he base O buffer limit hs hw
        hl).charge =
    CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space](Local.definitions.md#def-cb6c05b26fef8869)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonRecordInterval.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-63452802ff71011d)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program](Local.definitions.md#def-6f054ddde493018b)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge](Local.definitions.md#def-abd09b9ab586963a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-2effc9bf621f2775"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (hn : n ≤ q.height ^ 2)
  (he : 2 ≤ q.exponent) (base O buffer limit : ℕ) (hl : limit ≤ q.N ^ q.exponent)
  (hlocal :
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
      limit)
  (hf :
    CodedSorting.CommonIntervalAdapter.Fits q n base O buffer
      (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit)
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < base + 3 * O / q.block ∨ base + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * n) ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.CommonIntervalAdapter.program q reader
                    (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
                      (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
                    hf).instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordInterval.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-16d82df30e410adf)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5](Local.definitions.md#def-7a27151142463a3a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonIntervalAdapter.program](../../../Shared/Memory/IntervalAdapter.definitions.md#def-481f90e2408630ba)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-d42066e94bb2d129"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (hn : n ≤ q.height ^ 2)
  (he : 2 ≤ q.exponent) (base O buffer limit : ℕ) (hl : limit ≤ q.N ^ q.exponent)
  (hlocal :
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
      limit)
  (hf :
    CodedSorting.CommonIntervalAdapter.Fits q n base O buffer
      (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit),
  ∀
    i ∈
      (CodedSorting.CommonIntervalAdapter.program q reader
          (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
            (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
          hf).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordInterval.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-16d82df30e410adf)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5](Local.definitions.md#def-7a27151142463a3a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonIntervalAdapter.program](../../../Shared/Memory/IntervalAdapter.definitions.md#def-481f90e2408630ba)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-ec267d83f7dae74c"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (hn : n ≤ q.height ^ 2)
  (he : 2 ≤ q.exponent) (base O buffer limit : ℕ) (hl : limit ≤ q.N ^ q.exponent)
  (hlocal :
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
      limit)
  (hf :
    CodedSorting.CommonIntervalAdapter.Fits q n base O buffer
      (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit),
  (CodedSorting.CommonIntervalAdapter.program q reader
          (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
            (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
          hf).charge ≤
      CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n →
    CodedSorting.CommonStaticSchedule.cost q
        (CodedSorting.CommonIntervalAdapter.program q reader
            (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
              (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
            hf).instructions ≤
      CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordInterval.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-16d82df30e410adf)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5](Local.definitions.md#def-7a27151142463a3a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonIntervalAdapter.program](../../../Shared/Memory/IntervalAdapter.definitions.md#def-481f90e2408630ba)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonRecordInterval.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-63452802ff71011d)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge](Local.definitions.md#def-abd09b9ab586963a)

**基础库名称**

`Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-ff02e201baf65aaa"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (hn : n ≤ q.height ^ 2)
  (he : 2 ≤ q.exponent) (base O buffer limit : ℕ) (hl : limit ≤ q.N ^ q.exponent)
  (hlocal :
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
      limit)
  (hf :
    CodedSorting.CommonIntervalAdapter.Fits q n base O buffer
      (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit),
  (CodedSorting.CommonIntervalAdapter.program q reader
          (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
            (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
          hf).charge ≤
      CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n →
    (CodedSorting.CommonIntervalAdapter.program q reader
            (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
              (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
            hf).instructions.length ≤
      CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordInterval.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-16d82df30e410adf)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5](Local.definitions.md#def-7a27151142463a3a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonIntervalAdapter.program](../../../Shared/Memory/IntervalAdapter.definitions.md#def-481f90e2408630ba)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonRecordInterval.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-63452802ff71011d)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge](Local.definitions.md#def-abd09b9ab586963a)

**基础库名称**

`Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `List.length`

<a id="def-0c49de9afa262c26"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n buffer limit : ℕ),
  buffer + CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q hnormal n ≤ limit →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
      limit
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space](Local.definitions.md#def-cb6c05b26fef8869)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-7a27151142463a3a"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Construction.RecursiveParameters.Normalized q →
    ∀ (n : ℕ),
      ℕ →
        ℕ →
          ∀ (buffer : ℕ),
            ℕ →
              buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤
                buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-02684e726e98da91"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n base O buffer limit : ℕ),
  base + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * n) + 2 ≤ buffer →
    limit ≤ q.N ^ q.exponent →
      buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
            CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
          limit →
        CodedSorting.CommonIntervalAdapter.Fits q n base O buffer
          (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-ee47a4f76c3bb785"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (hn : n ≤ q.height ^ 2)
  (he : 2 ≤ q.exponent) (base O buffer limit : ℕ) (hl : limit ≤ q.N ^ q.exponent)
  (hlocal :
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
      limit)
  (hf :
    CodedSorting.CommonIntervalAdapter.Fits q n base O buffer
      (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit),
  (CodedSorting.CommonIntervalAdapter.program q reader
        (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
          (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
        hf).charge ≤
    CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5](Local.definitions.md#def-7a27151142463a3a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonIntervalAdapter.program](../../../Shared/Memory/IntervalAdapter.definitions.md#def-481f90e2408630ba)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonRecordInterval.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-63452802ff71011d)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge](Local.definitions.md#def-abd09b9ab586963a)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-102bcd4416b843df"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (hn : n ≤ q.height ^ 2)
  (he : 2 ≤ q.exponent) (base O buffer limit : ℕ) (hl : limit ≤ q.N ^ q.exponent)
  (hlocal :
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
      limit)
  (hf :
    CodedSorting.CommonIntervalAdapter.Fits q n base O buffer
      (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit)
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
  CodedSorting.CommonRecordInterval.EncodedAt q s.disk base O f →
    CodedSorting.CommonRecordInterval.EncodedAt q
      (CodedSorting.CommonStaticSchedule.executeRaw q
            (CodedSorting.CommonIntervalAdapter.program q reader
                (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
                  (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
                hf).instructions
            s).1.disk
      base O (CodedSorting.Columnsort.sortColumn f)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordInterval.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-16d82df30e410adf)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5](Local.definitions.md#def-7a27151142463a3a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonIntervalAdapter.program](../../../Shared/Memory/IntervalAdapter.definitions.md#def-481f90e2408630ba)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordInterval.EncodedAt](../../../Shared/Records/RecordOperations.definitions.md#def-0f2418ea3a290277)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-f64811e1c899505c"></a>
## `CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Local.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (hn : n ≤ q.height ^ 2)
  (he : 2 ≤ q.exponent) (base O buffer limit : ℕ) (hl : limit ≤ q.N ^ q.exponent)
  (hlocal :
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 n ≤
      limit)
  (hf :
    CodedSorting.CommonIntervalAdapter.Fits q n base O buffer
      (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit)
  (s : CodedSorting.CommonLeafProgram.Machine q) (j : ℕ),
  base + j / q.block < q.N ^ q.exponent →
    j < 3 * O ∨ 3 * O + 3 * n ≤ j →
      base + j / q.block < buffer ∨ limit ≤ base + j / q.block →
        CodedSorting.CommonMarginTransform.wordAt q
            (CodedSorting.CommonStaticSchedule.executeRaw q
                  (CodedSorting.CommonIntervalAdapter.program q reader
                      (CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal n hn he buffer
                        (buffer + CodedSorting.CommonRecordProgram.recordBlocks q n + 2) limit ⋯ hlocal hl)
                      hf).instructions
                  s).1.disk
            base j =
          CodedSorting.CommonMarginTransform.wordAt q s.disk base j
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonMarginTransform.wordAt](../../../Shared/Memory/MarginTransform.definitions.md#def-cbb100c2961a0843)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordInterval.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-16d82df30e410adf)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program._proof_5](Local.definitions.md#def-7a27151142463a3a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonIntervalAdapter.Fits](../../../Shared/Memory/IntervalAdapter.definitions.md#def-42ec2f93b81c97b0)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonIntervalAdapter.program](../../../Shared/Memory/IntervalAdapter.definitions.md#def-481f90e2408630ba)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`
