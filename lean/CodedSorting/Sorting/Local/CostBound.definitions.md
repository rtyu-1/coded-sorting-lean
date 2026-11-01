# CostBound 的定义

[源码](CostBound.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-b1cf14663ae7df26"></a>
## `CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CostBound.lean#L17)

**类型**

```lean
ℝ
```

**定义**

```lean
1 - ↑CodedSorting.Construction.epsilon
```

**继续展开**

- [CodedSorting.Construction.epsilon](../../Circuit/Parameters/Exponent.definitions.md#def-38e0b13c0209d8a9)

**基础库名称**

`Real`, `Real.instSub`, `Real.instRatCast`, `HSub.hSub`, `Rat.cast`, `Real.instOne`, `instHSub`, `One.toOfNat1`, `OfNat.ofNat`

<a id="def-5fb3aac9f5fefeed"></a>
## `CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CostBound.lean#L18)

**类型**

```lean
ℝ
```

**定义**

```lean
CodedSorting.Construction.Sorting.CommonSortingExchangeRate.rateConstant 3
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingExchangeRate.rateConstant](../Resources/Swaps.definitions.md#def-df165fe088b61cab)

**基础库名称**

`Real`, `instOfNatNat`, `Nat`, `OfNat.ofNat`
