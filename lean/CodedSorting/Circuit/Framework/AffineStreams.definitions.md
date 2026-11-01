# AffineStreams 的定义

[源码](AffineStreams.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-03a3a779aefd1efc"></a>
## `CodedSorting.AffineStreams.inverse_increasing_streams`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AffineStreams.lean#L76)

**类型**

```lean
∀ {Q K : ℕ} (e : Equiv.Perm (Fin Q)) (key : Fin Q → Fin K),
  (∀ (x y : Fin Q), x < y → key x = key y → e x < e y) →
    ∀ (x y : Fin Q), x < y → key ((Equiv.symm e) x) = key ((Equiv.symm e) y) → (Equiv.symm e) x < (Equiv.symm e) y
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-7c94b054256195c1"></a>
## `CodedSorting.AffineStreams.additionEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AffineStreams.lean#L115)

**类型**

```lean
{Q : ℕ} → Fin Q → Equiv.Perm (Fin Q)
```

**定义**

```lean
fun {Q} c => Equiv.ofBijective (CodedSorting.SequentialArithmetic.addOffset c) ⋯
```

**继续展开**

- [CodedSorting.AffineStreams.additionEquiv._proof_1](AffineStreams.definitions.md#def-45aa4db1260cbc31)
- [CodedSorting.SequentialArithmetic.addOffset](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-1af292012b811a2b)

**基础库名称**

`Equiv.Perm`, `Nat`, `Equiv.ofBijective`, `Fin`

<a id="def-45aa4db1260cbc31"></a>
## `CodedSorting.AffineStreams.additionEquiv._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AffineStreams.lean)

**类型**

```lean
∀ {Q : ℕ} (c : Fin Q), Function.Bijective (CodedSorting.SequentialArithmetic.addOffset c)
```

**继续展开**

- [CodedSorting.SequentialArithmetic.addOffset](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-1af292012b811a2b)

**基础库名称**

`Nat`, `Function.Bijective`, `Fin`
