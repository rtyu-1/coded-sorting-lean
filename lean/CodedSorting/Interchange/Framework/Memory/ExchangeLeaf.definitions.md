# ExchangeLeaf 的定义

[源码](ExchangeLeaf.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-aaad4ca0dd979eae"></a>
## `CodedSorting.CommonExchangeLeaf.bankWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeLeaf.lean#L14)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => 512 * q.height * 3
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-88582f6aa0de40db"></a>
## `CodedSorting.CommonExchangeLeaf.bankBits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeLeaf.lean#L15)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.CommonExchangeLeaf.bankWords q * q.w
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-7376b1fc157bd35c"></a>
## `CodedSorting.CommonExchangeLeaf.payload`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeLeaf.lean#L17)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonLeafTransform.Bank q → Fin (CodedSorting.CommonExchangeLeaf.bankBits q) → CodedSorting.Circuit.Bit
```

**定义**

```lean
fun q bank =>
  (CodedSorting.BitWordPacking.blockBits (CodedSorting.CommonExchangeLeaf.bankWords q) q.w)
    (CodedSorting.ResidentLeafBank.raw bank)
```

**继续展开**

- [CodedSorting.ResidentLeafBank.raw](../../../Shared/Memory/ResidentLeafBank.definitions.md#def-d1d4a603610970b9)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.BitWordPacking.blockBits](../../../Shared/Words/WordConvention.definitions.md#def-a9a13aad90fdf19b)
- [CodedSorting.CommonExchangeLeaf.bankWords](ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLeafTransform.Bank](../../../Shared/Memory/Leaf/Correctness.definitions.md#def-46cd46b2aa6cdd76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonExchangeLeaf.bankBits](ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-d0d5c9a55366a7cd"></a>
## `CodedSorting.CommonExchangeLeaf.cpu`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeLeaf.lean#L30)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (V : ℕ) →
    V ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
      Equiv.Perm (Fin V) → CodedSorting.CommonLeafTransform.Bank q → CodedSorting.CommonLeafTransform.Bank q
```

**定义**

```lean
fun q V hV π bank =>
  Fin.append (CodedSorting.ResidentLeafSort.header bank)
    ((CodedSorting.BitWordPacking.blockBits (CodedSorting.CommonExchangeLeaf.bankWords q) q.w).symm fun i =>
      if h : ↑i < V then CodedSorting.CommonExchangeLeaf.payload q bank (Fin.castLE hV (π ⟨↑i, h⟩))
      else CodedSorting.CommonExchangeLeaf.payload q bank i)
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.payload](ExchangeLeaf.definitions.md#def-7376b1fc157bd35c)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.BitWordPacking.blockBits](../../../Shared/Words/WordConvention.definitions.md#def-a9a13aad90fdf19b)
- [CodedSorting.CommonExchangeLeaf.bankWords](ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLeafTransform.Bank](../../../Shared/Memory/Leaf/Correctness.definitions.md#def-46cd46b2aa6cdd76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ResidentLeafSort.header](../../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-8e5c767d09c080c6)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonExchangeLeaf.bankBits](ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Fin.castLE`, `Fin.mk`, `Equiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `dite`, `Equiv.Perm`, `Nat`, `LT.lt`, `Nat.decLt`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `Not`, `Fin.append`, `instHMul`

<a id="def-45a7ea9ade5bc038"></a>
## `CodedSorting.CommonExchangeLeaf.roundedCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeLeaf.lean#L150)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (V : ℕ) → V ≤ CodedSorting.CommonExchangeLeaf.bankBits q → Fin (512 * q.height + 1)
```

**定义**

```lean
fun q V hV => ⟨CodedSorting.PhysicalStreamCursor.blockCount (3 * q.w) V, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonExchangeLeaf.bankBits](ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.CommonExchangeLeaf.roundedCount._proof_3](ExchangeLeaf.definitions.md#def-d33beb1b202be3ba)

**基础库名称**

`HMul.hMul`, `Fin.mk`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-d33beb1b202be3ba"></a>
## `CodedSorting.CommonExchangeLeaf.roundedCount._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeLeaf.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ∀ V ≤ CodedSorting.CommonExchangeLeaf.bankBits q,
    CodedSorting.PhysicalStreamCursor.blockCount (3 * q.w) V < 512 * q.height + 1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonExchangeLeaf.bankBits](ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `instHMul`
