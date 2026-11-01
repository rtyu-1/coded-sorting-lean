# SpaceBudget 的定义

[源码](SpaceBudget.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-1e0a2a921a3a1ef0"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSpaceBudget.coefficient`

从已证明的存在性命题中选取一个满足条件的对象。下面链接的命题列出选取条件；阅读时需要看清先选取对象、后允许哪些参数变化。

[源码位置](SpaceBudget.lean#L41)

**类型**

```lean
ℕ
```

**定义**

```lean
Classical.choose CodedSorting.Construction.Sorting.CommonSortingSpaceBudget.coefficient._proof_1
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpace.spaceCoefficient](../../Interchange/Bounds/ExchangeSpace.definitions.md#def-1d0a16090339cc34)
- [CodedSorting.Construction.Sorting.CommonSortingSpaceBudget.coefficient._proof_1](SpaceBudget.definitions.md#def-3f2dacaec34b0b17)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `Classical.choose`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-3f2dacaec34b0b17"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSpaceBudget.coefficient._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SpaceBudget.lean)

**类型**

```lean
∃ K, K = 49 * CodedSorting.Construction.ExchangeSpace.spaceCoefficient
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpace.spaceCoefficient](../../Interchange/Bounds/ExchangeSpace.definitions.md#def-1d0a16090339cc34)

**基础库名称**

`HMul.hMul`, `Exists`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Eq`, `instHMul`
