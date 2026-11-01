# ProjectionRankDecomposition 的定义

[源码](ProjectionRankDecomposition.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-6ea5d5b2ab62988e"></a>
## `CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ProjectionRankDecomposition.lean#L214)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → Matrix I I ℚ → Type u_1
```

**继续展开**

- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.mk](ProjectionRankDecomposition.definitions.md#def-1efe8cc2990521d9)

**基础库名称**

`Matrix`, `Rat`, `Fintype`

<a id="def-1efe8cc2990521d9"></a>
## `CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ProjectionRankDecomposition.lean#L216)

**类型**

```lean
{I : Type u_1} →
  [inst : Fintype I] →
    {P : Matrix I I ℚ} →
      (vectors : Fin P.rank → I → ℚ) →
        (∀ (i : Fin P.rank), vectors i ≠ 0) →
          (∀ (i j : Fin P.rank), i ≠ j → vectors i ⬝ᵥ vectors j = 0) →
            ∑ i, CodedSorting.Construction.TriangularConjugacy.lineProjection (vectors i) = P →
              CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.lineProjection](../Local/TriangularConjugacy.definitions.md#def-56ff2fa744d2ab0a)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)

**基础库名称**

`Rat.addCommMonoid`, `Rat.instOfNat`, `NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Rat.instMul`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `Finset.univ`, `dotProduct`, `Matrix`, `Rat`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Matrix.rank`, `Pi.instZero`, `Ne`, `Matrix.addCommMonoid`, `Fin.fintype`, `Fintype`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Zero.toOfNat0`, `OfNat.ofNat`, `Fin`, `Eq`, `Finset.sum`, `Rat.commRing`, `MulZeroClass.toZero`

<a id="def-b5c5757d55a96708"></a>
## `CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors`

读取 `CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition` 的 `vectors` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ProjectionRankDecomposition.lean#L217)

**类型**

```lean
{I : Type u_1} →
  [inst : Fintype I] →
    {P : Matrix I I ℚ} → CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P → Fin P.rank → I → ℚ
```

**定义**

```lean
fun I [Fintype I] P self => self.1
```

**继续展开**

- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)

**基础库名称**

`Matrix`, `Rat`, `Matrix.rank`, `Fintype`, `Fin`, `Rat.commRing`
