# CodePolynomial 的定义

[源码](CodePolynomial.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-3b0f3a964330bad7"></a>
## `CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.rateConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CodePolynomial.lean#L17)

**类型**

```lean
ℕ
```

**定义**

```lean
⌈22194000000 *
      CodedSorting.GlobalSortingBound.rateConstant CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K
        CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau⌉₊ +
  1
```

**继续展开**

- [CodedSorting.GlobalSortingBound.rateConstant](../Bounds/GlobalSortingBound.definitions.md#def-62c2c2bf2fffe5cf)
- [CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K](../Local/CostBound.definitions.md#def-5fb3aac9f5fefeed)
- [CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau](../Local/CostBound.definitions.md#def-b1cf14663ae7df26)
- [CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.rateConstant._proof_1](CodePolynomial.definitions.md#def-bf1bea184578ab16)

**基础库名称**

`Real.partialOrder`, `Real`, `HMul.hMul`, `FloorRing.toFloorSemiring`, `Real.semiring`, `Real.instFloorRing`, `Real.instRing`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `Nat.ceil`, `instAddNat`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `Real.linearOrder`, `instHMul`, `Real.instNatCast`, `Real.instIsStrictOrderedRing`

<a id="def-8381e32da2a6e08e"></a>
## `CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.leafConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CodePolynomial.lean#L19)

**类型**

```lean
ℕ
```

**定义**

```lean
2 * CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.rateConstant + 60
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.rateConstant](CodePolynomial.definitions.md#def-3b0f3a964330bad7)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-0300e71df7b4911d"></a>
## `CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.nodeConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CodePolynomial.lean#L20)

**类型**

```lean
ℕ
```

**定义**

```lean
2 * CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.rateConstant + 200
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.rateConstant](CodePolynomial.definitions.md#def-3b0f3a964330bad7)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-bf1bea184578ab16"></a>
## `CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.rateConstant._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CodePolynomial.lean)

**类型**

```lean
(22193999998 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`
