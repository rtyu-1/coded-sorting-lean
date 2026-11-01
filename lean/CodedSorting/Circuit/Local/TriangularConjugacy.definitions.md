# TriangularConjugacy 的定义

[源码](TriangularConjugacy.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-20302155c99d1d0f"></a>
## `CodedSorting.Construction.TriangularConjugacy.basis`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L32)

**类型**

```lean
{I : Type u_1} → [inst : LinearOrder I] → I → I → ℚ
```

**定义**

```lean
fun {I} [LinearOrder I] j r => if r = j then 1 else 0
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Rat.instOfNat`, `LinearOrder.toDecidableEq`, `LinearOrder`, `Rat`, `OfNat.ofNat`, `Eq`, `ite`

<a id="def-4c8c100ff257ad64"></a>
## `CodedSorting.Construction.TriangularConjugacy.normSq`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L45)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → (I → ℚ) → ℚ
```

**定义**

```lean
fun {I} [Fintype I] w => w ⬝ᵥ w
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Rat.addCommMonoid`, `Rat.instMul`, `dotProduct`, `Rat`, `Fintype`

<a id="def-911b7387755a92e8"></a>
## `CodedSorting.Construction.TriangularConjugacy.alpha`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L52)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → (I → ℚ) → I → ℚ
```

**定义**

```lean
fun {I} [Fintype I] w j => -CodedSorting.Construction.TriangularConjugacy.normSq w / (2 * w j)
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.normSq](TriangularConjugacy.definitions.md#def-4c8c100ff257ad64)

**基础库名称**

`Rat.instOfNat`, `Rat.instMul`, `instHDiv`, `HMul.hMul`, `Rat`, `HDiv.hDiv`, `Fintype`, `OfNat.ofNat`, `Rat.instDiv`, `Neg.neg`, `Rat.instNeg`, `instHMul`

<a id="def-63d2678b906f76fa"></a>
## `CodedSorting.Construction.TriangularConjugacy.factorColumn`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L55)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → (I → ℚ) → I → I → I → I → ℚ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] w i j c =>
  if c = i then
    w + CodedSorting.Construction.TriangularConjugacy.alpha w j • CodedSorting.Construction.TriangularConjugacy.basis j
  else
    if c = j then
      CodedSorting.Construction.TriangularConjugacy.alpha w j • CodedSorting.Construction.TriangularConjugacy.basis j
    else
      CodedSorting.Construction.TriangularConjugacy.basis c -
        (w c / w j) • CodedSorting.Construction.TriangularConjugacy.basis j
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.alpha](TriangularConjugacy.definitions.md#def-911b7387755a92e8)
- [CodedSorting.Construction.TriangularConjugacy.basis](TriangularConjugacy.definitions.md#def-20302155c99d1d0f)

**基础库名称**

`Rat.instSub`, `instHSMul`, `instHDiv`, `LinearOrder.toDecidableEq`, `CommSemiring.toSemiring`, `LinearOrder`, `Rat`, `HSub.hSub`, `Rat.commSemiring`, `Algebra.toSMul`, `Algebra.id`, `HDiv.hDiv`, `Function.hasSMul`, `instHAdd`, `Pi.instAdd`, `instHSub`, `Fintype`, `HAdd.hAdd`, `Rat.instAdd`, `Pi.instSub`, `HSMul.hSMul`, `Eq`, `Rat.instDiv`, `ite`

<a id="def-dfa2b1c860991762"></a>
## `CodedSorting.Construction.TriangularConjugacy.factor`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L62)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → (I → ℚ) → I → I → Matrix I I ℚ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] w i j r c => CodedSorting.Construction.TriangularConjugacy.factorColumn w i j c r
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.factorColumn](TriangularConjugacy.definitions.md#def-63d2678b906f76fa)

**基础库名称**

`Matrix`, `LinearOrder`, `Rat`, `Fintype`

<a id="def-b9e629dd477b8571"></a>
## `CodedSorting.Construction.TriangularConjugacy.swapMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L65)

**类型**

```lean
{I : Type u_1} → [inst : LinearOrder I] → I → I → Matrix I I ℚ
```

**定义**

```lean
fun {I} [LinearOrder I] i j r c => 1 r ((Equiv.swap i j) c)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Equiv.instFunLike`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `LinearOrder.toDecidableEq`, `Matrix`, `LinearOrder`, `Rat`, `Equiv.swap`, `AddGroupWithOne.toAddMonoidWithOne`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Rat.instDivisionRing`, `DivisionRing.toRing`, `AddMonoidWithOne.toOne`, `Equiv.Perm`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `OfNat.ofNat`, `DFunLike.coe`, `Ring.toAddGroupWithOne`, `Rat.commRing`, `MulZeroClass.toZero`

<a id="def-01d2ddb2f4fb32f9"></a>
## `CodedSorting.Construction.TriangularConjugacy.LowerTriangular`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L149)

**类型**

```lean
{I : Type u_1} → [inst : LinearOrder I] → Matrix I I ℚ → Prop
```

**定义**

```lean
fun {I} [LinearOrder I] A => ∀ (r c : I), r < c → A r c = 0
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Rat.instOfNat`, `Preorder.toLT`, `Matrix`, `LinearOrder`, `Rat`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `LT.lt`, `OfNat.ofNat`, `Eq`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-2729b8a2a2991d4c"></a>
## `CodedSorting.Construction.TriangularConjugacy.doubleVec`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L237)

**类型**

```lean
{I : Type u_1} → (I → ℚ) → Lex (I ⊕ I) → ℚ
```

**定义**

```lean
fun {I} u => Sum.elim u fun k => -u k
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Lex`, `Rat`, `Sum`, `Neg.neg`, `Rat.instNeg`, `Sum.elim`

<a id="def-56ff2fa744d2ab0a"></a>
## `CodedSorting.Construction.TriangularConjugacy.lineProjection`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L251)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → (I → ℚ) → Matrix I I ℚ
```

**定义**

```lean
fun {I} [Fintype I] u => (CodedSorting.Construction.TriangularConjugacy.normSq u)⁻¹ • Matrix.vecMulVec u u
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.normSq](TriangularConjugacy.definitions.md#def-4c8c100ff257ad64)

**基础库名称**

`Matrix.smul`, `Rat.instMul`, `instHSMul`, `CommSemiring.toSemiring`, `Matrix`, `Rat`, `Rat.commSemiring`, `Algebra.toSMul`, `Algebra.id`, `Inv.inv`, `Fintype`, `Rat.instInv`, `HSMul.hSMul`, `Matrix.vecMulVec`

<a id="def-d19b70aac67a1997"></a>
## `CodedSorting.Construction.TriangularConjugacy.partialSwap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L260)

**类型**

```lean
{I : Type u_1} → [inst : LinearOrder I] → Matrix I I ℚ → Matrix (Lex (I ⊕ I)) (Lex (I ⊕ I)) ℚ
```

**定义**

```lean
fun {I} [LinearOrder I] P => Matrix.fromBlocks (1 - P) P P (1 - P)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Rat.instSub`, `Matrix.fromBlocks`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `LinearOrder.toDecidableEq`, `Matrix`, `Lex`, `LinearOrder`, `Rat`, `AddGroupWithOne.toAddMonoidWithOne`, `HSub.hSub`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Sum`, `Rat.instDivisionRing`, `DivisionRing.toRing`, `AddMonoidWithOne.toOne`, `instHSub`, `Matrix.sub`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `OfNat.ofNat`, `Ring.toAddGroupWithOne`, `Rat.commRing`, `MulZeroClass.toZero`

<a id="def-13d5a5e633c1a11d"></a>
## `CodedSorting.Construction.TriangularConjugacy.highBlock`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L400)

**类型**

```lean
{I : Type u_1} → Matrix (Lex (I ⊕ I)) (Lex (I ⊕ I)) ℚ → Matrix I I ℚ
```

**定义**

```lean
fun {I} A => A.submatrix (fun k => toLex (Sum.inl k)) fun k => toLex (Sum.inl k)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Equiv.instFunLike`, `Matrix.submatrix`, `Matrix`, `Lex`, `Rat`, `Sum`, `Equiv`, `Sum.inl`, `DFunLike.coe`, `toLex`

<a id="def-d23ebe8dba4d6e83"></a>
## `CodedSorting.Construction.TriangularConjugacy.lowBlock`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularConjugacy.lean#L403)

**类型**

```lean
{I : Type u_1} → Matrix (Lex (I ⊕ I)) (Lex (I ⊕ I)) ℚ → Matrix I I ℚ
```

**定义**

```lean
fun {I} A => A.submatrix (fun k => toLex (Sum.inr k)) fun k => toLex (Sum.inr k)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Equiv.instFunLike`, `Matrix.submatrix`, `Matrix`, `Lex`, `Rat`, `Sum`, `Equiv`, `Sum.inr`, `DFunLike.coe`, `toLex`
