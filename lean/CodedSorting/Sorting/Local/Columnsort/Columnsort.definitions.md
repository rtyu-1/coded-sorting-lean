# Columnsort 的定义

[源码](Columnsort.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-96b08db6c27899aa"></a>
## `CodedSorting.Columnsort.sortColumn`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Columnsort.lean#L27)

**类型**

```lean
{n : ℕ} → {α : Type u_1} → [inst : LinearOrder α] → (Fin n → α) → Fin n → α
```

**定义**

```lean
fun {n} {α} [LinearOrder α] f => f ∘ ⇑(Tuple.sort f)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Equiv.instFunLike`, `LinearOrder`, `Function.comp`, `Equiv.Perm`, `Nat`, `Fin`, `DFunLike.coe`, `Tuple.sort`

<a id="def-02d0c9816dc97387"></a>
## `CodedSorting.Columnsort.stripeIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Columnsort.lean#L88)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun s g c i => (i / g * s + c) * g + i % g
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instHMul`
