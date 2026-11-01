# BaseExchangeProgram 的定义

[源码](BaseExchangeProgram.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-1a2dfaef9959ff0a"></a>
## `CodedSorting.BaseExchangeProgram.Volume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BaseExchangeProgram.lean#L234)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun P Q G S => P * (Q * G) * (Q * S)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-c68cf3aa9259828f"></a>
## `CodedSorting.BaseExchangeProgram.permutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BaseExchangeProgram.lean#L236)

**类型**

```lean
{P Q G S : ℕ} → Equiv.Perm (Fin (CodedSorting.BaseExchangeProgram.Volume P Q G S))
```

**定义**

```lean
fun {P Q G S} =>
  CodedSorting.CoordinateScans.lowLayout.symm.trans
    (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CoordinateScans.lowLayout)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.BaseExchangeProgram.Volume](BaseExchangeProgram.definitions.md#def-1a2dfaef9959ff0a)
- [CodedSorting.CoordinateScans.lowLayout](../Fields/BinaryPaddingScan.definitions.md#def-27613a35b25c74be)
- [CodedSorting.Address.exchangeEquiv](../../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `instMulNat`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `instHMul`
