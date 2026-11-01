# SemanticSwaps 的定义

[源码](SemanticSwaps.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-9b2a03acf57a38bc"></a>
## `CodedSorting.CommonSortingSemanticSwaps.rowsVolume`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticSwaps.lean#L498)

**类型**

```lean
∀ (s : ℕ), s * CodedSorting.PhysicalLocalSortNode.rows s = s * (s * (s ^ 2 * 1))
```

**继续展开**

- [CodedSorting.PhysicalLocalSortNode.rows](../../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-8003b18e12811d84"></a>
## `CodedSorting.CommonSortingSemanticSwaps.forwardAtRows`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticSwaps.lean#L501)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (s : ℕ) →
    CodedSorting.CommonRecordProgram.Records q (s * CodedSorting.PhysicalLocalSortNode.rows s) →
      CodedSorting.CommonRecordProgram.Records q (s * CodedSorting.PhysicalLocalSortNode.rows s)
```

**定义**

```lean
fun q s f => CodedSorting.CommonRecordReindex.castRecords ⋯ (CodedSorting.CommonLocalSemantic.forward s f)
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.forward](../../Local/Framework/Semantic.definitions.md#def-73fbf5cf9a4e2cae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows._proof_30](SemanticSwaps.definitions.md#def-f7d014d468bc5671)
- [CodedSorting.PhysicalLocalSortNode.rows](../../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-869b338825e3fc26"></a>
## `CodedSorting.CommonSortingSemanticSwaps.backwardAtRows`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SemanticSwaps.lean#L505)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (s : ℕ) →
    CodedSorting.CommonRecordProgram.Records q (s * CodedSorting.PhysicalLocalSortNode.rows s) →
      CodedSorting.CommonRecordProgram.Records q (s * CodedSorting.PhysicalLocalSortNode.rows s)
```

**定义**

```lean
fun q s f => CodedSorting.CommonLocalSemantic.backward s (CodedSorting.CommonRecordReindex.castRecords ⋯ f)
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalSemantic.backward](../../Local/Framework/Semantic.definitions.md#def-7cfe465cda0e4774)
- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.PhysicalLocalSortNode.rows](../../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingSemanticSwaps.rowsVolume](SemanticSwaps.definitions.md#def-9b2a03acf57a38bc)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-f7d014d468bc5671"></a>
## `CodedSorting.CommonSortingSemanticSwaps.forwardAtRows._proof_30`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SemanticSwaps.lean)

**类型**

```lean
∀ (s : ℕ), s * (s * (s ^ 2 * 1)) = s * CodedSorting.PhysicalLocalSortNode.rows s
```

**继续展开**

- [CodedSorting.PhysicalLocalSortNode.rows](../../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`
