# ColumnsortParameters 的定义

[源码](ColumnsortParameters.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-c3695925ec3092f4"></a>
## `CodedSorting.Columnsort.inputEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortParameters.lean#L271)

**类型**

```lean
(q s g : ℕ) → Fin (s * q * (s * g)) ≃ Fin s × Fin (q * s * g)
```

**定义**

```lean
fun q s g => (finCongr ⋯).trans finProdFinEquiv.symm
```

**继续展开**

- [CodedSorting.Columnsort.inputEquiv._proof_5](ColumnsortParameters.definitions.md#def-06eaf59ec4fca9e5)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `finCongr`, `Equiv`, `instMulNat`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `instHMul`

<a id="def-06eaf59ec4fca9e5"></a>
## `CodedSorting.Columnsort.inputEquiv._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ColumnsortParameters.lean)

**类型**

```lean
∀ (q s g : ℕ), s * q * (s * g) = s * (q * s * g)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`
