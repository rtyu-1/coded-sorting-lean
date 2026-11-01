# LexBlocks 的定义

[源码](LexBlocks.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-3bfb2af662c69a76"></a>
## `CodedSorting.LexBlocks.subvectorEncode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LexBlocks.lean#L16)

**类型**

```lean
{Q : ℕ} →
  {J : Type u_1} →
    [inst : Fintype J] → [inst_1 : LinearOrder J] → [inst_2 : WellFoundedLT J] → (J → Fin Q) ≃ Fin (Q ^ Fintype.card J)
```

**定义**

```lean
fun {Q} {J} [Fintype J] [LinearOrder J] [WellFoundedLT J] =>
  toLex.trans (Fintype.orderIsoFinOfCardEq (Lex (J → Fin Q)) ⋯).symm.toEquiv
```

**继续展开**

- [CodedSorting.LexBlocks.subvectorEncode._proof_1](LexBlocks.definitions.md#def-2d692a31962f5a2c)

**基础库名称**

`Lex.fintype`, `Preorder.toLT`, `Pi.instLinearOrderLexForallOfWellFoundedLT`, `LinearOrder.toDecidableEq`, `Equiv.trans`, `Lex`, `Nat.instMonoid`, `LinearOrder`, `WellFoundedLT`, `PartialOrder.toPreorder`, `Pi.instFintype`, `Fintype.orderIsoFinOfCardEq`, `Preorder.toLE`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fintype.card`, `Equiv`, `LE.le`, `OrderIso.symm`, `instLEFin`, `Fin.fintype`, `Fin.instLinearOrder`, `Fintype`, `HPow.hPow`, `Nat`, `instHPow`, `RelIso.toEquiv`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `toLex`

<a id="def-b5dc0c1da80a1119"></a>
## `CodedSorting.LexBlocks.PrefixCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LexBlocks.lean#L25)

**类型**

```lean
{m : ℕ} → ℕ → Fin m → ℕ
```

**定义**

```lean
fun {m} Q i => Q ^ Fintype.card (CodedSorting.SingleCoordinate.Before i)
```

**继续展开**

- [CodedSorting.SingleCoordinate.Before](../../Interchange/Framework/Fields/BinaryPaddingScan.definitions.md#def-c8fa626af923b445)

**基础库名称**

`Preorder.toLT`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `Subtype.fintype`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fintype.card`, `Fin.fintype`, `Fin.instLinearOrder`, `Fin.decLt`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-b586bdb106d39599"></a>
## `CodedSorting.LexBlocks.SuffixCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LexBlocks.lean#L26)

**类型**

```lean
{m : ℕ} → ℕ → Fin m → ℕ
```

**定义**

```lean
fun {m} Q i => Q ^ Fintype.card (CodedSorting.SingleCoordinate.After i)
```

**继续展开**

- [CodedSorting.SingleCoordinate.After](../../Interchange/Framework/Fields/BinaryPaddingScan.definitions.md#def-61b672af3baaa6b5)

**基础库名称**

`Preorder.toLT`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `Subtype.fintype`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fintype.card`, `Fin.fintype`, `Fin.instLinearOrder`, `Fin.decLt`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-26d7d10a5c2062e8"></a>
## `CodedSorting.LexBlocks.blockCard`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LexBlocks.lean#L43)

**类型**

```lean
∀ {m Q : ℕ} (i : Fin m), CodedSorting.LexBlocks.PrefixCount Q i * (Q * CodedSorting.LexBlocks.SuffixCount Q i) = Q ^ m
```

**继续展开**

- [CodedSorting.LexBlocks.PrefixCount](LexBlocks.definitions.md#def-b5dc0c1da80a1119)
- [CodedSorting.LexBlocks.SuffixCount](LexBlocks.definitions.md#def-b586bdb106d39599)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`, `instHMul`

<a id="def-2d692a31962f5a2c"></a>
## `CodedSorting.LexBlocks.subvectorEncode._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LexBlocks.lean)

**类型**

```lean
∀ {Q : ℕ} {J : Type u_1} [inst : Fintype J] [inst_1 : LinearOrder J], Fintype.card (J → Fin Q) = Q ^ Fintype.card J
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`LinearOrder.toDecidableEq`, `Nat.instMonoid`, `LinearOrder`, `Pi.instFintype`, `Monoid.toNatPow`, `Fintype.card`, `Fin.fintype`, `Fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`
