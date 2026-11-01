# Join 的定义

[源码](Join.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-251fd32fca912bc3"></a>
## `CodedSorting.CommonColumnJoin.start`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Join.lean#L28)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun B n k =>
  k / CodedSorting.PhysicalStreamCursor.blockCount B n * n + k % CodedSorting.PhysicalStreamCursor.blockCount B n * B
```

**继续展开**

- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instHMul`

<a id="def-0987e91e181b2328"></a>
## `CodedSorting.CommonColumnJoin.useful`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Join.lean#L29)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun B n k => min B (n - k % CodedSorting.PhysicalStreamCursor.blockCount B n * B)
```

**继续展开**

- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `Nat.instMod`, `instHMod`, `instSubNat`, `instMulNat`, `HMod.hMod`, `instHSub`, `Nat`, `Nat.instMin_mathlib`, `Min.min`, `instHMul`

<a id="def-22fe08bf7f06f79b"></a>
## `CodedSorting.CommonColumnJoin.first`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Join.lean#L30)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun B n k => CodedSorting.CommonColumnJoin.start B n k / B
```

**继续展开**

- [CodedSorting.CommonColumnJoin.start](Join.definitions.md#def-251fd32fca912bc3)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `Nat`, `Nat.instDiv`

<a id="def-20711c68bc03c466"></a>
## `CodedSorting.CommonColumnJoin.last`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Join.lean#L31)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun B n k => (CodedSorting.CommonColumnJoin.start B n k + CodedSorting.CommonColumnJoin.useful B n k - 1) / B
```

**继续展开**

- [CodedSorting.CommonColumnJoin.start](Join.definitions.md#def-251fd32fca912bc3)
- [CodedSorting.CommonColumnJoin.useful](Join.definitions.md#def-0987e91e181b2328)

**基础库名称**

`instHDiv`, `HSub.hSub`, `HDiv.hDiv`, `instSubNat`, `instOfNatNat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`
