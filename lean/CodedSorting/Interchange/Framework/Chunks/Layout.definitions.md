# Layout 的定义

[源码](Layout.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e901e0d94d622ec2"></a>
## `CodedSorting.CommonChunkLayout.Volume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Layout.lean#L14)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
CodedSorting.BaseExchangeProgram.Volume
```

**继续展开**

- [CodedSorting.BaseExchangeProgram.Volume](../Memory/BaseExchangeProgram.definitions.md#def-1a2dfaef9959ff0a)

**基础库名称**

`Nat`

<a id="def-6f5402999737c1c7"></a>
## `CodedSorting.CommonChunkLayout.swap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Layout.lean#L16)

**类型**

```lean
(P Q G S : ℕ) → Equiv.Perm (Fin (CodedSorting.CommonChunkLayout.Volume P Q G S))
```

**定义**

```lean
fun P Q G S => Equiv.symm CodedSorting.BaseExchangeProgram.permutation
```

**继续展开**

- [CodedSorting.BaseExchangeProgram.permutation](../Memory/BaseExchangeProgram.definitions.md#def-c68cf3aa9259828f)
- [CodedSorting.CommonChunkLayout.Volume](Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BaseExchangeProgram.Volume](../Memory/BaseExchangeProgram.definitions.md#def-1a2dfaef9959ff0a)

**基础库名称**

`Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`
