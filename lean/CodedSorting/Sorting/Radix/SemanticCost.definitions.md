# SemanticCost 的定义

[源码](SemanticCost.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-b34e4ae62fdb9563"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticCost.lean#L19)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => q.height ^ 2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-da6bf909e65853b7"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticCost.lean#L20)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n =>
  CodedSorting.PhysicalStreamCursor.blockCount (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) n
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-fc62f3f8104981a7"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticCost.lean#L22)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n =>
  CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount q n *
    CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount](SemanticCost.definitions.md#def-da6bf909e65853b7)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-9e5986ac1a1fbbc7"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.padded_covers`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean#L27)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  n ≤ CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-40ef24b228c13800"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.operation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticCost.lean#L30)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) → CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n
```

**定义**

```lean
fun q n =>
  CodedSorting.CommonRecordTopPrefix.operation ⋯
    (CodedSorting.CommonSlabBatch.batchOutput CodedSorting.Columnsort.sortColumn)
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.operation](../../Shared/Records/TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.padded_covers](SemanticCost.definitions.md#def-9e5986ac1a1fbbc7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)
- [CodedSorting.Columnsort.sortColumn](../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount](SemanticCost.definitions.md#def-da6bf909e65853b7)
- [CodedSorting.CommonRecordProgram.Records](../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonSlabBatch.batchOutput](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-1e347b15e5d5c6a2)

**基础库名称**

`Nat`

<a id="def-ca744a79f4318f82"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticCost.lean#L34)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ
```

**定义**

```lean
fun q hnormal n =>
  max 1
        (CodedSorting.CommonRecordProgram.recordBlocks q
          (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n)) +
      CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount q n *
        CodedSorting.CommonRecordProgram.recordBlocks q
          (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) +
    CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3
      (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount](SemanticCost.definitions.md#def-da6bf909e65853b7)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-b2f906314e475a2f"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticCost.lean#L39)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n =>
  3 *
        CodedSorting.CommonRecordProgram.recordBlocks q
          (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n) +
      CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount q n *
        (CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3
            (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) +
          12 *
            CodedSorting.CommonRecordProgram.recordBlocks q
              (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q)) +
    3 * CodedSorting.CommonRecordProgram.recordBlocks q n
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalBudget.budget](../Local/Program.definitions.md#def-e7b5e8b778c9f2fd)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount](SemanticCost.definitions.md#def-da6bf909e65853b7)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-6eb0883ed396c784"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticCost.lean#L44)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
      (C : ℕ) →
        2 ≤ q.exponent →
          (source buffer limit : ℕ) →
            source +
                  CodedSorting.CommonRecordProgram.recordBlocks q
                    (C * CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) ≤
                buffer →
              buffer +
                      C *
                        CodedSorting.CommonRecordProgram.recordBlocks q
                          (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) +
                    CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3
                      (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) ≤
                  limit →
                limit ≤ q.N ^ q.exponent →
                  CodedSorting.CommonRecordProgram.Program q
                    (C * CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) source buffer limit
                    (CodedSorting.CommonSlabBatch.batchOutput CodedSorting.Columnsort.sortColumn)
```

**定义**

```lean
fun q reader hnormal C he source buffer limit hs hw hl =>
  let R := CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q;
  let work := buffer + C * CodedSorting.CommonRecordProgram.recordBlocks q R;
  let_fun hwork := hw;
  let_fun hpos := ⋯;
  let kids := fun c =>
    CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal R ⋯ he
      (CodedSorting.CommonSlabBatch.recordBase q R buffer ↑c) work limit ⋯ hwork hl;
  CodedSorting.CommonSlabBatch.program reader kids hs ⋯ ⋯ hl
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSlabBatch.Children](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram](../Local/Program.definitions.md#def-c56b088bf0286946)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.program](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-ae51434b8b1ab7f4)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram._proof_3](SemanticCost.definitions.md#def-8cf2e684ca90057a)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram._proof_5](SemanticCost.definitions.md#def-509934d35bc4d01e)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-e192f85de221fbac)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Columnsort.sortColumn](../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ResidentLeafSort.recordOrder](../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram._proof_4](SemanticCost.definitions.md#def-6a6dc946519a8719)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram._proof_6](SemanticCost.definitions.md#def-dc805df6de6541e0)
- [CodedSorting.CommonSlabBatch.batchOutput](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-1e347b15e5d5c6a2)
- [CodedSorting.CommonRecordProgram.Program](../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`le_rfl`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `letFun`, `instHMul`

<a id="def-ce459c3458041f1e"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticCost.lean#L98)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
      (n : ℕ) →
        2 ≤ q.exponent →
          (source buffer limit : ℕ) →
            source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
              buffer + CodedSorting.Construction.Sorting.CommonMSDChunks.space q hnormal n ≤ limit →
                limit ≤ q.N ^ q.exponent →
                  3 * CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n < (2 ^ q.w) ^ q.digits →
                    CodedSorting.CommonRecordProgram.Program q n source buffer limit
                      (CodedSorting.Construction.Sorting.CommonMSDChunks.operation q n)
```

**定义**

```lean
fun q reader hnormal n he source buffer limit hs hw hl hshape =>
  let slabs :=
    buffer +
      max 1
        (CodedSorting.CommonRecordProgram.recordBlocks q
          (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n));
  let_fun hslabs := ⋯;
  let inner :=
    CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram q reader hnormal
      (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount q n) he buffer slabs limit ⋯ hslabs hl;
  CodedSorting.CommonRecordTopPrefix.program q reader ⋯ inner hs ⋯ ⋯ hl hshape
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDChunks.program._proof_12](SemanticCost.definitions.md#def-287a70160bb62cb0)
- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.program._proof_9](SemanticCost.definitions.md#def-ffa866ed30c82488)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.padded_covers](SemanticCost.definitions.md#def-9e5986ac1a1fbbc7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.program._proof_11](SemanticCost.definitions.md#def-6d2329b4e7ff37e2)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.operation](SemanticCost.definitions.md#def-40ef24b228c13800)
- [CodedSorting.Columnsort.sortColumn](../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount](SemanticCost.definitions.md#def-da6bf909e65853b7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.program._proof_10](SemanticCost.definitions.md#def-d67f84ac718799ad)
- [CodedSorting.ResidentLeafSort.recordOrder](../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordTopPrefix.program](../../Shared/Records/TopPrefix.definitions.md#def-f52d388ddcf14cc3)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.space](SemanticCost.definitions.md#def-ca744a79f4318f82)
- [CodedSorting.CommonSlabBatch.batchOutput](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-1e347b15e5d5c6a2)
- [CodedSorting.CommonRecordProgram.Program](../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram](SemanticCost.definitions.md#def-6eb0883ed396c784)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `letFun`, `instHMul`

<a id="def-f26dec5f36f23e44"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.program_charge_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean#L116)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ) (he : 2 ≤ q.exponent)
  (source buffer limit : ℕ) (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonMSDChunks.space q hnormal n ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hshape : 3 * CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n < (2 ^ q.w) ^ q.digits),
  (CodedSorting.Construction.Sorting.CommonMSDChunks.program q reader hnormal n he source buffer limit hs hw hl
        hshape).charge ≤
    CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.operation](SemanticCost.definitions.md#def-40ef24b228c13800)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.charge](SemanticCost.definitions.md#def-b2f906314e475a2f)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.space](SemanticCost.definitions.md#def-ca744a79f4318f82)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.program](SemanticCost.definitions.md#def-ce459c3458041f1e)
- [CodedSorting.CommonRecordProgram.Program.charge](../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-8cf2e684ca90057a"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  0 < CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q)
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-6a6dc946519a8719"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (C buffer : ℕ),
  0 < CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) →
    ∀ (c : Fin C),
      CodedSorting.CommonSlabBatch.recordBase q (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) buffer
            ↑c +
          max 1
            (CodedSorting.CommonRecordProgram.recordBlocks q
              (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q)) ≤
        buffer +
          C *
            CodedSorting.CommonRecordProgram.recordBlocks q
              (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q)
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-e192f85de221fbac)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-509934d35bc4d01e"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (C buffer : ℕ),
  buffer +
      C * CodedSorting.CommonSlabBatch.stride q (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q * 3) ≤
    buffer +
      C *
        CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q)
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.stride](../../Interchange/Framework/Memory/SlabBatchAllocation.definitions.md#def-94b29694418488f5)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-dc805df6de6541e0"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.batchProgram._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (C : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer +
              C *
                CodedSorting.CommonRecordProgram.recordBlocks q
                  (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) +
            CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3
              (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) ≤
          limit →
        buffer +
            C *
              CodedSorting.CommonRecordProgram.recordBlocks q
                (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) ≤
          limit
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-d67f84ac718799ad"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.program._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Construction.RecursiveParameters.Normalized q →
    ∀ (n : ℕ),
      ℕ →
        ∀ (buffer : ℕ),
          ℕ →
            buffer +
                CodedSorting.CommonRecordProgram.recordBlocks q
                  (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount q n *
                    CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) ≤
              buffer +
                max 1
                  (CodedSorting.CommonRecordProgram.recordBlocks q
                    (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n))
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount](SemanticCost.definitions.md#def-da6bf909e65853b7)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-6d2329b4e7ff37e2"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.program._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n buffer : ℕ),
  buffer +
      max 1
        (CodedSorting.CommonRecordProgram.recordBlocks q
          (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n)) ≤
    buffer +
      max 1
        (CodedSorting.CommonRecordProgram.recordBlocks q
          (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n))
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)

**基础库名称**

`Preorder.toLE`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-287a70160bb62cb0"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.program._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer +
                max 1
                  (CodedSorting.CommonRecordProgram.recordBlocks q
                    (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n)) +
              CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount q n *
                CodedSorting.CommonRecordProgram.recordBlocks q
                  (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) +
            CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3
              (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) ≤
          limit →
        buffer +
            max 1
              (CodedSorting.CommonRecordProgram.recordBlocks q
                (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n)) ≤
          limit
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount](SemanticCost.definitions.md#def-da6bf909e65853b7)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-ffa866ed30c82488"></a>
## `CodedSorting.Construction.Sorting.CommonMSDChunks.program._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticCost.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) (n buffer limit : ℕ),
  buffer + CodedSorting.Construction.Sorting.CommonMSDChunks.space q hnormal n ≤ limit →
    buffer +
            max 1
              (CodedSorting.CommonRecordProgram.recordBlocks q
                (CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize q n)) +
          CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount q n *
            CodedSorting.CommonRecordProgram.recordBlocks q
              (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) +
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3
          (CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize q) ≤
      limit
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space](../Local/Program.definitions.md#def-6e019908a7c3b3ef)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkSize](SemanticCost.definitions.md#def-b34e4ae62fdb9563)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.paddedSize](SemanticCost.definitions.md#def-fc62f3f8104981a7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.chunkCount](SemanticCost.definitions.md#def-da6bf909e65853b7)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.space](SemanticCost.definitions.md#def-ca744a79f4318f82)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`
