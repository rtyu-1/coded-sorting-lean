# ChunkRows 的定义

[源码](ChunkRows.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-22045c2145d573a7"></a>
## `CodedSorting.CommonMSDRowDirectoryBatch.Row`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ChunkRows.lean#L15)

**类型**

```lean
ℕ → Type
```

**继续展开**

- [CodedSorting.CommonMSDRowDirectoryBatch.Row.mk](ChunkRows.definitions.md#def-5d0c0512b83d6d16)

**基础库名称**

`Nat`

<a id="def-5d0c0512b83d6d16"></a>
## `CodedSorting.CommonMSDRowDirectoryBatch.Row.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ChunkRows.lean#L15)

**类型**

```lean
{n : ℕ} → (offset length : ℕ) → offset + length ≤ n → CodedSorting.CommonMSDRowDirectoryBatch.Row n
```

**继续展开**

- [CodedSorting.CommonMSDRowDirectoryBatch.Row](ChunkRows.definitions.md#def-22045c2145d573a7)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-ba762cd50d4f77e1"></a>
## `CodedSorting.CommonMSDRowDirectoryBatch.Row.offset`

读取 `CodedSorting.CommonMSDRowDirectoryBatch.Row` 的 `offset` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ChunkRows.lean#L16)

**类型**

```lean
{n : ℕ} → CodedSorting.CommonMSDRowDirectoryBatch.Row n → ℕ
```

**定义**

```lean
fun n self => self.1
```

**继续展开**

- [CodedSorting.CommonMSDRowDirectoryBatch.Row](ChunkRows.definitions.md#def-22045c2145d573a7)

**基础库名称**

`Nat`

<a id="def-ef72a6010c1334f8"></a>
## `CodedSorting.CommonMSDRowDirectoryBatch.Row.length`

读取 `CodedSorting.CommonMSDRowDirectoryBatch.Row` 的 `length` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ChunkRows.lean#L17)

**类型**

```lean
{n : ℕ} → CodedSorting.CommonMSDRowDirectoryBatch.Row n → ℕ
```

**定义**

```lean
fun n self => self.2
```

**继续展开**

- [CodedSorting.CommonMSDRowDirectoryBatch.Row](ChunkRows.definitions.md#def-22045c2145d573a7)

**基础库名称**

`Nat`

<a id="def-75bc861f3912fc86"></a>
## `CodedSorting.CommonMSDRowDirectoryBatch.target`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ChunkRows.lean#L20)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q K base c => base + c * CodedSorting.CommonMSDDirectory.blocks q K
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDDirectory.blocks](Directory.definitions.md#def-2a36fe66dfedd827)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-d2d3b105572c444c"></a>
## `CodedSorting.CommonMSDRowDirectoryBatch.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ChunkRows.lean#L77)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    {K C n : ℕ} →
      K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
        (CodedSorting.WordControl.Word q.w → Fin K) →
          (Fin C → CodedSorting.CommonMSDRowDirectoryBatch.Row n) →
            ℕ → ℕ → ℕ → List (Fin C) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader {K C n} hfit key rows source scratch directory cs =>
  List.flatMap
    (fun c =>
      CodedSorting.CommonMSDRowDirectory.code q reader hfit key (rows c).offset (rows c).length source scratch
        (CodedSorting.CommonMSDRowDirectoryBatch.target q K directory ↑c))
    cs
```

**继续展开**

- [CodedSorting.CommonMSDRowDirectoryBatch.target](ChunkRows.definitions.md#def-75bc861f3912fc86)
- [CodedSorting.CommonMSDRowDirectoryBatch.Row.length](ChunkRows.definitions.md#def-ef72a6010c1334f8)
- [CodedSorting.CommonMSDRowDirectoryBatch.Row.offset](ChunkRows.definitions.md#def-ba762cd50d4f77e1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonMSDRowDirectory.code](RadixCost.definitions.md#def-49653fc97a33c8a2)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMSDRowDirectoryBatch.Row](ChunkRows.definitions.md#def-22045c2145d573a7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `List.flatMap`, `instHMul`

<a id="def-663dba53ac045c88"></a>
## `CodedSorting.CommonMSDChunkRows.row`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ChunkRows.lean#L297)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) → Fin (CodedSorting.CommonMSDChunks.chunkCount q n) → CodedSorting.CommonMSDRowDirectoryBatch.Row n
```

**定义**

```lean
fun q n j =>
  { offset := ↑j * CodedSorting.CommonMSDChunks.chunkSize q,
    length := min (CodedSorting.CommonMSDChunks.chunkSize q) (n - ↑j * CodedSorting.CommonMSDChunks.chunkSize q),
    fits := ⋯ }
```

**继续展开**

- [CodedSorting.CommonMSDRowDirectoryBatch.Row.mk](ChunkRows.definitions.md#def-5d0c0512b83d6d16)
- [CodedSorting.CommonMSDRowDirectoryBatch.Row](ChunkRows.definitions.md#def-22045c2145d573a7)
- [CodedSorting.CommonMSDChunks.chunkSize](Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.CommonMSDChunks.chunkCount](Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDChunkRows.row._proof_2](ChunkRows.definitions.md#def-98b1b1f22452d7f4)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `Fin.val`, `instHSub`, `Nat`, `Nat.instMin_mathlib`, `Fin`, `Min.min`, `instHMul`

<a id="def-98b1b1f22452d7f4"></a>
## `CodedSorting.CommonMSDChunkRows.row._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ChunkRows.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ)
  (j : Fin (CodedSorting.CommonMSDChunks.chunkCount q n)),
  ↑j * CodedSorting.CommonMSDChunks.chunkSize q +
      min (CodedSorting.CommonMSDChunks.chunkSize q) (n - ↑j * CodedSorting.CommonMSDChunks.chunkSize q) ≤
    n
```

**继续展开**

- [CodedSorting.CommonMSDChunks.chunkSize](Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.CommonMSDChunks.chunkCount](Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instMin_mathlib`, `instAddNat`, `Fin`, `Min.min`, `instHMul`
