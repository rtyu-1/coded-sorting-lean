# SmallMemoryPhysicalRate 的定义

[源码](SmallMemoryPhysicalRate.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-3ce136832ceec971"></a>
## `CodedSorting.SmallMemorySortingRate.wordFactor`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallMemoryPhysicalRate.lean#L15)

**类型**

```lean
ℝ → ℕ
```

**定义**

```lean
fun κ => max 1 ⌈κ⌉₊
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Real.partialOrder`, `Real`, `FloorRing.toFloorSemiring`, `Real.semiring`, `Nat.instMax_mathlib`, `Real.instFloorRing`, `Real.instRing`, `instOfNatNat`, `Max.max`, `Nat`, `Nat.ceil`, `OfNat.ofNat`, `Real.linearOrder`, `Real.instIsStrictOrderedRing`

<a id="def-5af158548a3f45f0"></a>
## `CodedSorting.SmallMemorySortingRate.paperFactor`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallMemoryPhysicalRate.lean#L70)

**类型**

```lean
ℕ → ℕ → ℕ → ℝ → ℝ → ℝ
```

**定义**

```lean
fun N M B τ ε => 1 + Real.log ↑N / (Real.log (↑M / ↑B) ^ τ * Real.log ↑M ^ ε)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Real.instPow`, `Real`, `instHDiv`, `HMul.hMul`, `Real.instDivInvMonoid`, `HDiv.hDiv`, `Nat.cast`, `Real.log`, `Real.instAdd`, `Real.instOne`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `DivInvMonoid.toDiv`, `One.toOfNat1`, `instHPow`, `OfNat.ofNat`, `instHMul`, `Real.instNatCast`
