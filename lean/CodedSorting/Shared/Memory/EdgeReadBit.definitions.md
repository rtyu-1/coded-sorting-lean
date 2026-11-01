# EdgeReadBit 的定义

[源码](EdgeReadBit.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-29658209027b4034"></a>
## `CodedSorting.PhysicalLeafParameters.widthLimit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](EdgeReadBit.lean#L265)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun q ratio => Nat.log q ratio / 8
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `instOfNatNat`, `Nat`, `Nat.instDiv`, `Nat.log`, `OfNat.ofNat`

<a id="def-2fe8d8e0ff0a0b3b"></a>
## `CodedSorting.PhysicalLeafParameters.baseWidth`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](EdgeReadBit.lean#L267)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun m q ratio => m ^ Nat.log m (CodedSorting.PhysicalLeafParameters.widthLimit q ratio)
```

**继续展开**

- [CodedSorting.PhysicalLeafParameters.widthLimit](EdgeReadBit.definitions.md#def-29658209027b4034)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Nat.log`

<a id="def-5b3ccb2ea10f8cb1"></a>
## `CodedSorting.PhysicalLeafParameters.minimumRatio`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](EdgeReadBit.lean#L269)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q reserve lanes => max (q ^ (8 * (Nat.log q reserve + 1))) (reserve * lanes)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `Nat.log`, `OfNat.ofNat`, `instHMul`
