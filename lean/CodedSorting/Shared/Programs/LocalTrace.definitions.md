# LocalTrace 的定义

[源码](LocalTrace.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-80d9b7cd708ab67c"></a>
## `CodedSorting.LocalShape.sizeExponent`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalTrace.lean#L11)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n => Nat.clog 16 n
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.clog`

<a id="def-e17af2e11cd34d9a"></a>
## `CodedSorting.LocalShape.sizeChoice`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalTrace.lean#L14)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n => 2 ^ CodedSorting.LocalShape.sizeExponent n
```

**继续展开**

- [CodedSorting.LocalShape.sizeExponent](LocalTrace.definitions.md#def-80d9b7cd708ab67c)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-0ba59d4f9543a5be"></a>
## `CodedSorting.LocalShape.columnLength`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalTrace.lean#L16)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n => CodedSorting.LocalShape.sizeChoice n ^ 3
```

**继续展开**

- [CodedSorting.LocalShape.sizeChoice](LocalTrace.definitions.md#def-e17af2e11cd34d9a)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`
