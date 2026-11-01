# Semantic 的定义

[源码](Semantic.lean) · [主定理导读](../../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-dd873ceba2e4d5f9"></a>
## `CodedSorting.CommonMSDNodeLayout.slot`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L29)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n K : ℕ) →
    Fin (K * CodedSorting.CommonMSDChunks.chunkCount q n) → Fin K × Fin (CodedSorting.CommonMSDChunks.chunkCount q n)
```

**定义**

```lean
fun q n K i => finProdFinEquiv.symm i
```

**继续展开**

- [CodedSorting.CommonMSDChunks.chunkCount](../../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-4512f8319d2ae7a2"></a>
## `CodedSorting.CommonMSDNodeLayout.layout`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L32)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n K : ℕ) →
    ℕ → ℕ → ℕ → CodedSorting.CommonMSDGatherController.Layout (K * CodedSorting.CommonMSDChunks.chunkCount q n)
```

**定义**

```lean
fun q n K source directory target =>
  { source := fun x => source,
    offset := fun i =>
      3 * (CodedSorting.CommonMSDChunkRows.row q n (CodedSorting.CommonMSDNodeLayout.slot q n K i).2).offset,
    directory := fun i =>
      CodedSorting.CommonMSDRowDirectoryBatch.target q K directory ↑(CodedSorting.CommonMSDNodeLayout.slot q n K i).2,
    entry := fun i => ↑(CodedSorting.CommonMSDNodeLayout.slot q n K i).1, target := target }
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout.mk](../../Framework/GatherController.definitions.md#def-13df2c0a5ba23091)
- [CodedSorting.CommonMSDRowDirectoryBatch.target](../../Framework/ChunkRows.definitions.md#def-75bc861f3912fc86)
- [CodedSorting.CommonMSDGatherController.Layout](../../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonMSDRowDirectoryBatch.Row.offset](../../Framework/ChunkRows.definitions.md#def-ba762cd50d4f77e1)
- [CodedSorting.CommonMSDChunkRows.row](../../Framework/ChunkRows.definitions.md#def-663dba53ac045c88)
- [CodedSorting.CommonMSDChunks.chunkCount](../../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDNodeLayout.slot](Semantic.definitions.md#def-dd873ceba2e4d5f9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `Nat`, `OfNat.ofNat`, `Fin`, `Prod.snd`, `instHMul`
