# GlobalSortingBound 的定义

[源码](GlobalSortingBound.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-82c139647b2d2e4e"></a>
## `CodedSorting.GlobalSortingBound.depth`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GlobalSortingBound.lean#L14)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun H w => Nat.clog H (2 ^ w)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Nat.clog`

<a id="def-62c2c2bf2fffe5cf"></a>
## `CodedSorting.GlobalSortingBound.rateConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GlobalSortingBound.lean#L71)

**类型**

```lean
ℝ → ℝ → ℝ
```

**定义**

```lean
fun K τ => K * (1 + (1 / Real.log 2 + 3) ^ τ) + 3
```

**继续展开**

- [CodedSorting.GlobalSortingBound.rateConstant._proof_2](GlobalSortingBound.definitions.md#def-266237d305644d2b)
- [CodedSorting.GlobalSortingBound.rateConstant._proof_1](GlobalSortingBound.definitions.md#def-8ee07e80d6167c47)

**基础库名称**

`Real.instPow`, `Real`, `instHDiv`, `HMul.hMul`, `Real.instDivInvMonoid`, `HDiv.hDiv`, `Real.log`, `Real.instAdd`, `Real.instOne`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Real.instMul`, `DivInvMonoid.toDiv`, `One.toOfNat1`, `instHPow`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-8ee07e80d6167c47"></a>
## `CodedSorting.GlobalSortingBound.rateConstant._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GlobalSortingBound.lean)

**类型**

```lean
(0 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-266237d305644d2b"></a>
## `CodedSorting.GlobalSortingBound.rateConstant._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GlobalSortingBound.lean)

**类型**

```lean
(1 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`
