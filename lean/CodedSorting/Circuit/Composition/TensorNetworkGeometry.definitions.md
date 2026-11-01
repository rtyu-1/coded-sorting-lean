# TensorNetworkGeometry 的定义

[源码](TensorNetworkGeometry.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-3417bb4efc8c8579"></a>
## `CodedSorting.Construction.TensorFrameGeometry.integerLine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L28)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.Line → Fin 8 → ℤ
```

**定义**

```lean
fun a k => CodedSorting.Construction.FiniteCertificate.lines[↑a]![↑k]!
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.FiniteCertificate.lines](../../Generated/FiniteCircuit/Data.definitions.md#def-b85746934906bd4e)

**基础库名称**

`Int.instInhabited`, `instOfNatNat`, `Int`, `Fin.val`, `Array`, `Array.instInhabited`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `GetElem?.getElem!`, `Array.size`, `Array.instGetElem?NatLtSize`

<a id="def-4ca7ea125588b297"></a>
## `CodedSorting.Construction.TensorFrameGeometry.partner_bound`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorNetworkGeometry.lean#L35)

**类型**

```lean
∀ (a : CodedSorting.Construction.ThreeCopySchedule.Line),
  CodedSorting.Construction.FiniteCertificate.orthogonalPartner[↑a]! < 111
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.FiniteCertificate.orthogonalPartner](../../Generated/FiniteCircuit/Data.definitions.md#def-e0d946baae644aca)

**基础库名称**

`instInhabitedNat`, `instOfNatNat`, `Fin.val`, `Array`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `GetElem?.getElem!`, `Array.size`, `Array.instGetElem?NatLtSize`

<a id="def-ff9f624903a3e90f"></a>
## `CodedSorting.Construction.TensorFrameGeometry.partnerFunction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L39)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.Line → CodedSorting.Construction.ThreeCopySchedule.Line
```

**定义**

```lean
fun a => ⟨CodedSorting.Construction.FiniteCertificate.orthogonalPartner[↑a]!, ⋯⟩
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.partner_bound](TensorNetworkGeometry.definitions.md#def-4ca7ea125588b297)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.FiniteCertificate.orthogonalPartner](../../Generated/FiniteCircuit/Data.definitions.md#def-e0d946baae644aca)

**基础库名称**

`instInhabitedNat`, `Fin.mk`, `instOfNatNat`, `Fin.val`, `Array`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `GetElem?.getElem!`, `Array.size`, `Array.instGetElem?NatLtSize`

<a id="def-ca5aadd79aa1f96a"></a>
## `CodedSorting.Construction.TensorFrameGeometry.partner_bijective`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorNetworkGeometry.lean#L42)

**类型**

```lean
Function.Bijective CodedSorting.Construction.TensorFrameGeometry.partnerFunction
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameGeometry.partnerFunction](TensorNetworkGeometry.definitions.md#def-ff9f624903a3e90f)

**基础库名称**

`Function.Bijective`

<a id="def-455da91fe23df598"></a>
## `CodedSorting.Construction.TensorFrameGeometry.partner`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L45)

**类型**

```lean
Equiv.Perm CodedSorting.Construction.ThreeCopySchedule.Line
```

**定义**

```lean
Equiv.ofBijective CodedSorting.Construction.TensorFrameGeometry.partnerFunction
  CodedSorting.Construction.TensorFrameGeometry.partner_bijective
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.partner_bijective](TensorNetworkGeometry.definitions.md#def-ca5aadd79aa1f96a)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameGeometry.partnerFunction](TensorNetworkGeometry.definitions.md#def-ff9f624903a3e90f)

**基础库名称**

`Equiv.Perm`, `Equiv.ofBijective`

<a id="def-e8ced2908a315b18"></a>
## `CodedSorting.Construction.TensorFrameGeometry.lineVector`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L51)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.Line → Fin 8 → ℚ
```

**定义**

```lean
fun a =>
  CodedSorting.Construction.IntegerProjection.vectorOfInts (CodedSorting.Construction.TensorFrameGeometry.integerLine a)
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.integerLine](TensorNetworkGeometry.definitions.md#def-3417bb4efc8c8579)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.IntegerProjection.vectorOfInts](../Labels/FiniteInterpretation.definitions.md#def-1d9f5849aecb194d)

**基础库名称**

`Rat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-2acb357ca4da07e1"></a>
## `CodedSorting.Construction.TensorFrameGeometry.lineProjector`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L69)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.Line → Matrix (Fin 8) (Fin 8) ℚ
```

**定义**

```lean
fun a =>
  CodedSorting.Construction.TriangularConjugacy.lineProjection
    (CodedSorting.Construction.TensorFrameGeometry.lineVector a)
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.lineProjection](../Local/TriangularConjugacy.definitions.md#def-56ff2fa744d2ab0a)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameGeometry.lineVector](TensorNetworkGeometry.definitions.md#def-e8ced2908a315b18)

**基础库名称**

`Matrix`, `Rat`, `instOfNatNat`, `Fin.fintype`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-182cf0f7cfe7330f"></a>
## `CodedSorting.Construction.TensorFrameGeometry.Coordinates`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L90)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.TensorLiftProgram.Coordinates
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Coordinates](TensorLiftProgram.definitions.md#def-b93298813069e8c3)

<a id="def-cc6ac375b6fa11c4"></a>
## `CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L91)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.TensorLabels.Label 8
```

**继续展开**

- [CodedSorting.TensorLabels.Label](../Labels/Framework/TensorLabels.definitions.md#def-43a4598c9218b5b2)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-24fd3f061d543855"></a>
## `CodedSorting.Construction.TensorFrameGeometry.tensorLine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L93)

**类型**

```lean
CodedSorting.Construction.TensorFrameGeometry.Coordinates → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun a =>
  CodedSorting.TensorLabels.tensor3 (CodedSorting.Construction.TensorFrameGeometry.lineProjector a.1)
    (CodedSorting.Construction.TensorFrameGeometry.lineProjector a.2.1)
    (CodedSorting.Construction.TensorFrameGeometry.lineProjector a.2.2)
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameGeometry.Coordinates](TensorNetworkGeometry.definitions.md#def-182cf0f7cfe7330f)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameGeometry.lineProjector](TensorNetworkGeometry.definitions.md#def-2acb357ca4da07e1)
- [CodedSorting.TensorLabels.tensor3](../Labels/Framework/TensorLabels.definitions.md#def-a5a55f5aababa4ea)

**基础库名称**

`instOfNatNat`, `Prod.fst`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`

<a id="def-5fcd2eaa4a5943e5"></a>
## `CodedSorting.Construction.TensorFrameGeometry.copyView`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L117)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.Copy → CodedSorting.TensorLabels.H 8 ≃ CodedSorting.TensorLabels.H 8
```

**定义**

```lean
fun i =>
  if ↑i = 0 then Equiv.refl (CodedSorting.TensorLabels.H 8)
  else
    if ↑i = 1 then
      { toFun := fun p => (p.2.1, p.2.2, p.1), invFun := fun p => (p.2.2, p.1, p.2.1),
        left_inv := CodedSorting.Construction.TensorFrameGeometry.copyView._proof_1,
        right_inv := CodedSorting.Construction.TensorFrameGeometry.copyView._proof_2 }
    else
      { toFun := fun p => (p.2.2, p.1, p.2.1), invFun := fun p => (p.2.1, p.2.2, p.1),
        left_inv := CodedSorting.Construction.TensorFrameGeometry.copyView._proof_2,
        right_inv := CodedSorting.Construction.TensorFrameGeometry.copyView._proof_1 }
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.copyView._proof_1](TensorNetworkGeometry.definitions.md#def-3a3ec0dd73a83a01)
- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)
- [CodedSorting.Construction.TensorFrameGeometry.copyView._proof_2](TensorNetworkGeometry.definitions.md#def-37459933ef3beddd)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Equiv.mk`, `Equiv`, `Prod.mk`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `Nat`, `instDecidableEqNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `Eq`, `Prod.snd`, `ite`

<a id="def-2e38ffdde752fb31"></a>
## `CodedSorting.Construction.TensorFrameGeometry.globalize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L131)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.Copy →
  CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix →
    CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun i P =>
  Matrix.submatrix P ⇑(CodedSorting.Construction.TensorFrameGeometry.copyView i)
    ⇑(CodedSorting.Construction.TensorFrameGeometry.copyView i)
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.TensorFrameGeometry.copyView](TensorNetworkGeometry.definitions.md#def-5fcd2eaa4a5943e5)

**基础库名称**

`Equiv.instFunLike`, `Matrix.submatrix`, `Rat`, `Equiv`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `DFunLike.coe`

<a id="def-22a69c1f253e89f3"></a>
## `CodedSorting.Construction.TensorFrameGeometry.dataProjector`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L141)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.DataStream → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun a =>
  CodedSorting.Construction.TensorFrameGeometry.globalize a.1
    (CodedSorting.Construction.TensorFrameGeometry.tensorLine a.2.2)
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameGeometry.tensorLine](TensorNetworkGeometry.definitions.md#def-24fd3f061d543855)
- [CodedSorting.Construction.TensorFrameGeometry.globalize](TensorNetworkGeometry.definitions.md#def-2e38ffdde752fb31)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`instOfNatNat`, `Prod.fst`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`

<a id="def-3228215a919ab085"></a>
## `CodedSorting.Construction.TensorFrameGeometry.dataSource`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L154)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.DataStream → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun a => if a.2.1 = 0 then CodedSorting.Construction.TensorFrameGeometry.dataProjector a else 0
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.dataProjector](TensorNetworkGeometry.definitions.md#def-22a69c1f253e89f3)
- [CodedSorting.Construction.TensorFrameGeometry.dataSource._proof_3](TensorNetworkGeometry.definitions.md#def-b1279b9e88a15fd3)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `Rat`, `instDecidableEqFin`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Fin.instOfNat`, `instOfNatNat`, `Prod.fst`, `Nat`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Zero.toOfNat0`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `Matrix.zero`, `Rat.commRing`, `MulZeroClass.toZero`, `ite`

<a id="def-6c5ce1afce05402e"></a>
## `CodedSorting.Construction.TensorFrameGeometry.dataTerminal`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L158)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.DataStream → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun a => if a.2.1 = 0 then 1 else 1 - CodedSorting.Construction.TensorFrameGeometry.dataProjector a
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.dataProjector](TensorNetworkGeometry.definitions.md#def-22a69c1f253e89f3)
- [CodedSorting.Construction.TensorFrameGeometry.dataSource._proof_3](TensorNetworkGeometry.definitions.md#def-b1279b9e88a15fd3)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Rat.instSub`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `instDecidableEqProd`, `Rat`, `instDecidableEqFin`, `AddGroupWithOne.toAddMonoidWithOne`, `HSub.hSub`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Fin.instOfNat`, `Rat.instDivisionRing`, `DivisionRing.toRing`, `instOfNatNat`, `Prod.fst`, `AddMonoidWithOne.toOne`, `instHSub`, `Matrix.sub`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `Ring.toAddGroupWithOne`, `Rat.commRing`, `MulZeroClass.toZero`, `ite`

<a id="def-0fe1dc52244b418a"></a>
## `CodedSorting.Construction.TensorFrameGeometry.sourceLabel`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L187)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.IndependentStream →
  CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun x =>
  match x with
  | Sum.inl a => CodedSorting.Construction.TensorFrameGeometry.dataSource a
  | Sum.inr val => 0
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.dataSource](TensorNetworkGeometry.definitions.md#def-3228215a919ab085)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)
- [CodedSorting.Construction.TensorFrameGeometry.sourceLabel.match_1](TensorNetworkGeometry.definitions.md#def-eafa2d6a2a8e92c6)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `Rat`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `instOfNatNat`, `Nat`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Zero.toOfNat0`, `OfNat.ofNat`, `Matrix.zero`, `Rat.commRing`, `MulZeroClass.toZero`

<a id="def-8e1334570fa7a637"></a>
## `CodedSorting.Construction.TensorFrameGeometry.terminalLabel`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L191)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.IndependentStream →
  CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun x =>
  match x with
  | Sum.inl a => CodedSorting.Construction.TensorFrameGeometry.dataTerminal a
  | Sum.inr val => 1
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.dataTerminal](TensorNetworkGeometry.definitions.md#def-6c5ce1afce05402e)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)
- [CodedSorting.Construction.TensorFrameGeometry.sourceLabel.match_1](TensorNetworkGeometry.definitions.md#def-eafa2d6a2a8e92c6)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `instDecidableEqProd`, `Rat`, `instDecidableEqFin`, `AddGroupWithOne.toAddMonoidWithOne`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Rat.instDivisionRing`, `DivisionRing.toRing`, `instOfNatNat`, `AddMonoidWithOne.toOne`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Prod`, `OfNat.ofNat`, `Fin`, `Ring.toAddGroupWithOne`, `Rat.commRing`, `MulZeroClass.toZero`

<a id="def-f8d9daee937e759b"></a>
## `CodedSorting.Construction.TensorNetwork.certificateForward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L314)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg) →
  List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg) →
    List
        (CodedSorting.Construction.ScatterCopies.ScatterRow CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg
          CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg) →
      List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg)
```

**定义**

```lean
fun before after rows =>
  CodedSorting.Construction.LocalPhysicalContract.structuredProgram
    (CodedSorting.Construction.LocalPhysicalSemantics.localPhysicalProgram before after rows)
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](../Local/LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.registerCount](../Local/FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.LocalPhysicalContract.structuredProgram](../Local/ReverseLocalProgram.definitions.md#def-0b0d122e208fe53a)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.LocalPhysicalSemantics.localPhysicalProgram](../Local/LocalPhysicalSemantics.definitions.md#def-83343efdd06b3465)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `List`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-b520642c4f48b26f"></a>
## `CodedSorting.Construction.TensorNetwork.certificateMiddle`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorNetworkGeometry.lean#L320)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg) →
  List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg) →
    List
        (CodedSorting.Construction.ScatterCopies.ScatterRow CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg
          CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg) →
      List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg)
```

**定义**

```lean
fun before after rows =>
  CodedSorting.Construction.LocalPhysicalContract.structuredProgram
    (CodedSorting.Construction.ReverseLocalProgram.reverseLocalPhysicalProgram before after rows)
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](../Local/LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.registerCount](../Local/FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.ReverseLocalProgram.reverseLocalPhysicalProgram](../Local/ReverseLocalProgram.definitions.md#def-f1a0c58e317a1b44)
- [CodedSorting.Construction.LocalPhysicalContract.structuredProgram](../Local/ReverseLocalProgram.definitions.md#def-0b0d122e208fe53a)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `List`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-3a3ec0dd73a83a01"></a>
## `CodedSorting.Construction.TensorFrameGeometry.copyView._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorNetworkGeometry.lean)

**类型**

```lean
∀ (x : CodedSorting.TensorLabels.H 8), ((x.2.1, x.2.2, x.1).2.2, (x.2.1, x.2.2, x.1).1, (x.2.1, x.2.2, x.1).2.1) = x
```

**继续展开**

- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)

**基础库名称**

`Prod.mk`, `instOfNatNat`, `Prod.fst`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`

<a id="def-37459933ef3beddd"></a>
## `CodedSorting.Construction.TensorFrameGeometry.copyView._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorNetworkGeometry.lean)

**类型**

```lean
∀ (x : CodedSorting.TensorLabels.H 8), ((x.2.2, x.1, x.2.1).2.1, (x.2.2, x.1, x.2.1).2.2, (x.2.2, x.1, x.2.1).1) = x
```

**继续展开**

- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)

**基础库名称**

`Prod.mk`, `instOfNatNat`, `Prod.fst`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`

<a id="def-b1279b9e88a15fd3"></a>
## `CodedSorting.Construction.TensorFrameGeometry.dataSource._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorNetworkGeometry.lean)

**类型**

```lean
NeZero (1 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-eafa2d6a2a8e92c6"></a>
## `CodedSorting.Construction.TensorFrameGeometry.sourceLabel.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TensorNetworkGeometry.lean)

**类型**

```lean
(motive : CodedSorting.Construction.ThreeCopySchedule.IndependentStream → Sort u_1) →
  (x : CodedSorting.Construction.ThreeCopySchedule.IndependentStream) →
    ((a : CodedSorting.Construction.ThreeCopySchedule.DataStream) → motive (Sum.inl a)) →
      ((val : CodedSorting.Construction.ThreeCopySchedule.HelperStream) → motive (Sum.inr val)) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 => Sum.casesOn x (fun val => h_1 val) fun val => h_2 val
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)

**基础库名称**

`Sum.casesOn`, `Sum.inl`, `Sum.inr`
