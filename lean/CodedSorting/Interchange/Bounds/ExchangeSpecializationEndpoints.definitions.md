# ExchangeSpecializationEndpoints 的定义

[源码](ExchangeSpecializationEndpoints.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2b2a59c88aa39ade"></a>
## `CodedSorting.Construction.ExchangeSpecialization.Node`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L26)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
  CodedSorting.Construction.TensorFrameNetwork.program.length
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`List.length`

<a id="def-351dc46d999e8472"></a>
## `CodedSorting.Construction.ExchangeSpecialization.Mat`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L27)

**类型**

```lean
Type
```

**定义**

```lean
Matrix (Fin 512) (Fin 512) ℚ
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Matrix`, `Rat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-cb2ea7b499ebf923"></a>
## `CodedSorting.Construction.ExchangeSpecialization.DoubleMat`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L28)

**类型**

```lean
Type
```

**定义**

```lean
Matrix (Lex (Fin 512 ⊕ Fin 512)) (Lex (Fin 512 ⊕ Fin 512)) ℚ
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Matrix`, `Lex`, `Rat`, `Sum`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-bec6ecadb64b1ab9"></a>
## `CodedSorting.Construction.ExchangeSpecialization.doubledDecEq`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L30)

**类型**

```lean
DecidableEq (Lex (Fin 512 ⊕ Fin 512))
```

**定义**

```lean
LinearOrder.toDecidableEq
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`LinearOrder.toDecidableEq`, `Lex`, `LinearOrder`, `inferInstance`, `Sum`, `instOfNatNat`, `Fin.instLinearOrder`, `Nat`, `Sum.Lex.linearOrder`, `OfNat.ofNat`, `Fin`, `DecidableEq`

<a id="def-94151648ab83fde3"></a>
## `CodedSorting.Construction.ExchangeSpecialization.coordinateEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L33)

**类型**

```lean
Fin 512 ≃ CodedSorting.TensorLabels.H 8
```

**定义**

```lean
(finCongr CodedSorting.Construction.ExchangeSpecialization.coordinateEquiv._proof_1).trans
  (Fintype.equivFin (CodedSorting.TensorLabels.H 8)).symm
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.coordinateEquiv._proof_1](ExchangeSpecializationEndpoints.definitions.md#def-8f9b5fa9270d1546)
- [CodedSorting.TensorLabels.H](../../Circuit/Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)

**基础库名称**

`Equiv.trans`, `finCongr`, `Fintype.card`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `Fintype.equivFin`, `Nat`, `instFintypeProd`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-49fcbe979a3665d5"></a>
## `CodedSorting.Construction.ExchangeSpecialization.label`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L38)

**类型**

```lean
CodedSorting.Construction.ExchangeSpecialization.Node → CodedSorting.Construction.ExchangeSpecialization.Mat
```

**定义**

```lean
fun v =>
  Matrix.submatrix (CodedSorting.Construction.TensorFrameNetwork.actualLabel v)
    ⇑CodedSorting.Construction.ExchangeSpecialization.coordinateEquiv
    ⇑CodedSorting.Construction.ExchangeSpecialization.coordinateEquiv
```

**继续展开**

- [CodedSorting.Construction.TensorFrameNetwork.actualLabel](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-c62aefbdfe1c4740)
- [CodedSorting.Construction.ExchangeSpecialization.coordinateEquiv](ExchangeSpecializationEndpoints.definitions.md#def-94151648ab83fde3)
- [CodedSorting.Construction.ExchangeSpecialization.Mat](ExchangeSpecializationEndpoints.definitions.md#def-351dc46d999e8472)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.TensorLabels.H](../../Circuit/Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)

**基础库名称**

`Equiv.instFunLike`, `Matrix.submatrix`, `Rat`, `Equiv`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-5d2a2c893152e568"></a>
## `CodedSorting.Construction.ExchangeSpecialization.edgeProjection`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L72)

**类型**

```lean
CodedSorting.Construction.OneLevelChildren.Edge → CodedSorting.Construction.ExchangeSpecialization.Mat
```

**定义**

```lean
fun e =>
  if
      CodedSorting.Construction.ExchangeFrameAlgebra.Nested
        (CodedSorting.Construction.ExchangeSpecialization.label
          (CodedSorting.ProgramNetwork.wireTail CodedSorting.Construction.TensorFrameNetwork.program e))
        (CodedSorting.Construction.ExchangeSpecialization.label
          (CodedSorting.ProgramNetwork.wireHead CodedSorting.Construction.TensorFrameNetwork.program e)) then
    CodedSorting.Construction.ExchangeSpecialization.label
        (CodedSorting.ProgramNetwork.wireHead CodedSorting.Construction.TensorFrameNetwork.program e) -
      CodedSorting.Construction.ExchangeSpecialization.label
        (CodedSorting.ProgramNetwork.wireTail CodedSorting.Construction.TensorFrameNetwork.program e)
  else
    CodedSorting.Construction.ExchangeSpecialization.label
        (CodedSorting.ProgramNetwork.wireTail CodedSorting.Construction.TensorFrameNetwork.program e) -
      CodedSorting.Construction.ExchangeSpecialization.label
        (CodedSorting.ProgramNetwork.wireHead CodedSorting.Construction.TensorFrameNetwork.program e)
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.Mat](ExchangeSpecializationEndpoints.definitions.md#def-351dc46d999e8472)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.ProgramNetwork.wireHead](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.wireTail](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.ExchangeFrameAlgebra.Nested](../Local/ExchangeFramePaths.definitions.md#def-3a3d8d6b4a222070)
- [CodedSorting.Construction.ExchangeSpecialization.label](ExchangeSpecializationEndpoints.definitions.md#def-49fcbe979a3665d5)

**基础库名称**

`Rat.instSub`, `Rat`, `HSub.hSub`, `Classical.propDecidable`, `instOfNatNat`, `Fin.fintype`, `instHSub`, `Matrix.sub`, `Nat`, `OfNat.ofNat`, `Fin`, `ite`

<a id="def-7252e547679ccb86"></a>
## `CodedSorting.Construction.ExchangeSpecialization.edgeProjection_rank`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeSpecializationEndpoints.lean#L84)

**类型**

```lean
∀ (e : CodedSorting.Construction.OneLevelChildren.Edge),
  Matrix.rank (CodedSorting.Construction.ExchangeSpecialization.edgeProjection e) =
    CodedSorting.Construction.OneLevelChildren.edgeRank e
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](../OneLevel/Children.definitions.md#def-30d83915a3eba2c8)

**基础库名称**

`Rat`, `Matrix.rank`, `instOfNatNat`, `Fin.fintype`, `Nat`, `OfNat.ofNat`, `Fin`, `Eq`, `Rat.commRing`

<a id="def-cb79f0bb8a242ac3"></a>
## `CodedSorting.Construction.ExchangeSpecialization.decomposition`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L98)

**类型**

```lean
(e : CodedSorting.Construction.OneLevelChildren.Edge) →
  CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition
    (CodedSorting.Construction.ExchangeSpecialization.edgeProjection e)
```

**定义**

```lean
fun e => Classical.choice ⋯
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition._proof_2](ExchangeSpecializationEndpoints.definitions.md#def-55db969e06ce7aaa)

**基础库名称**

`Classical.choice`, `instOfNatNat`, `Fin.fintype`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-c207797430c73a26"></a>
## `CodedSorting.Construction.ExchangeSpecialization.childIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L102)

**类型**

```lean
(e : CodedSorting.Construction.OneLevelChildren.Edge) →
  Fin (Matrix.rank (CodedSorting.Construction.ExchangeSpecialization.edgeProjection e)) ≃
    Fin (CodedSorting.Construction.OneLevelChildren.edgeRank e)
```

**定义**

```lean
fun e => finCongr ⋯
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection_rank](ExchangeSpecializationEndpoints.definitions.md#def-7252e547679ccb86)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](../OneLevel/Children.definitions.md#def-30d83915a3eba2c8)

**基础库名称**

`Rat`, `finCongr`, `Matrix.rank`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `Nat`, `OfNat.ofNat`, `Fin`, `Rat.commRing`

<a id="def-a79378b5d5c5d461"></a>
## `CodedSorting.Construction.ExchangeSpecialization.FamilyIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L121)

**类型**

```lean
Type
```

**定义**

```lean
Option
  (CodedSorting.Construction.ExchangeSpecialization.Node ⊕
    (e : CodedSorting.Construction.OneLevelChildren.Edge) ×
      CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex
        (CodedSorting.Construction.ExchangeSpecialization.edgeProjection e))
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)

**基础库名称**

`Sum`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Sigma`, `Option`

<a id="def-78bf95f0832b39f8"></a>
## `CodedSorting.Construction.ExchangeSpecialization.family`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L123)

**类型**

```lean
CodedSorting.Construction.ExchangeSpecialization.FamilyIndex →
  CodedSorting.Construction.ExchangeSpecialization.DoubleMat
```

**定义**

```lean
fun x =>
  match x with
  | none => CodedSorting.Construction.TriangularConjugacy.partialSwap 1
  | some (Sum.inl v) =>
    CodedSorting.Construction.TriangularConjugacy.partialSwap (CodedSorting.Construction.ExchangeSpecialization.label v)
  | some (Sum.inr ⟨e, k⟩) =>
    CodedSorting.Construction.RankPartialSwapExecution.family
      (CodedSorting.Construction.ExchangeSpecialization.decomposition e) k
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](../Local/ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.ExchangeSpecialization.FamilyIndex](ExchangeSpecializationEndpoints.definitions.md#def-a79378b5d5c5d461)
- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.family.match_1](ExchangeSpecializationEndpoints.definitions.md#def-fb481be6768f2dbf)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.DoubleMat](ExchangeSpecializationEndpoints.definitions.md#def-cb2ea7b499ebf923)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.Construction.TriangularConjugacy.partialSwap](../../Circuit/Local/TriangularConjugacy.definitions.md#def-d19b70aac67a1997)
- [CodedSorting.Construction.ExchangeSpecialization.label](ExchangeSpecializationEndpoints.definitions.md#def-49fcbe979a3665d5)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`NormedCommRing.toNormedRing`, `NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `NormedRing.toRing`, `Matrix`, `Rat`, `instDecidableEqFin`, `AddGroupWithOne.toAddMonoidWithOne`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `instOfNatNat`, `NormedCommRing.toNonUnitalNormedCommRing`, `AddMonoidWithOne.toOne`, `Fin.instLinearOrder`, `Unit`, `Rat.instNormedField`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `NonUnitalNormedCommRing.toNonUnitalCommRing`, `NormedField.toNormedCommRing`, `OfNat.ofNat`, `Fin`, `Ring.toAddGroupWithOne`, `MulZeroClass.toZero`

<a id="def-187fdef53c805022"></a>
## `CodedSorting.Construction.ExchangeSpecialization.uniform`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L130)

**类型**

```lean
CodedSorting.MatrixFactorization.SpecializedFamily CodedSorting.Construction.ExchangeSpecialization.family
```

**定义**

```lean
CodedSorting.MatrixFactorization.specializeFamily CodedSorting.Construction.ExchangeSpecialization.family
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ExchangeSpecialization.FamilyIndex](ExchangeSpecializationEndpoints.definitions.md#def-a79378b5d5c5d461)
- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.ThreeCopySchedule.Block](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.MatrixFactorization.specializeFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-6501610d878a69b1)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.ProgramNetwork.instFintypeVertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-c8f35892a045d1f9)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.ExchangeSpecialization.family](ExchangeSpecializationEndpoints.definitions.md#def-78bf95f0832b39f8)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.TensorLiftProgram.instFintypeRound](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-9d47e1f47feb55c7)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.ExchangeSpecialization.doubledDecEq](ExchangeSpecializationEndpoints.definitions.md#def-bec6ecadb64b1ab9)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Bool.fintype`, `Lex`, `Rat`, `Matrix.rank`, `Sum`, `instOfNatNat`, `Fin.fintype`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Sigma.instFintype`, `Bool`, `instFintypeOption`, `instAddNat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`, `List.length`, `Rat.commRing`, `Sigma`

<a id="def-b02b8b98752b35b8"></a>
## `CodedSorting.Construction.ExchangeSpecialization.radix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L134)

**类型**

```lean
ℕ
```

**定义**

```lean
CodedSorting.Construction.ExchangeSpecialization.uniform.prime
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.FamilyIndex](ExchangeSpecializationEndpoints.definitions.md#def-a79378b5d5c5d461)
- [CodedSorting.Construction.ExchangeSpecialization.uniform](ExchangeSpecializationEndpoints.definitions.md#def-187fdef53c805022)
- [CodedSorting.Construction.ExchangeSpecialization.family](ExchangeSpecializationEndpoints.definitions.md#def-78bf95f0832b39f8)
- [CodedSorting.Construction.ExchangeSpecialization.doubledDecEq](ExchangeSpecializationEndpoints.definitions.md#def-bec6ecadb64b1ab9)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Lex`, `Sum`, `instOfNatNat`, `Fin.fintype`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-2580b898498e1f35"></a>
## `CodedSorting.Construction.ExchangeSpecialization.edgeFamily`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L139)

**类型**

```lean
(e : CodedSorting.Construction.OneLevelChildren.Edge) →
  CodedSorting.MatrixFactorization.SpecializedFamily
    (CodedSorting.Construction.RankPartialSwapExecution.family
      (CodedSorting.Construction.ExchangeSpecialization.decomposition e))
```

**定义**

```lean
fun e =>
  CodedSorting.Construction.PartialSwapExecution.restrictFamily CodedSorting.Construction.ExchangeSpecialization.uniform
    (fun k => some (Sum.inr ⟨e, k⟩)) (fun x => id) fun x => id
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](../Local/ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.TensorLiftProgram.Round](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ExchangeSpecialization.FamilyIndex](ExchangeSpecializationEndpoints.definitions.md#def-a79378b5d5c5d461)
- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.ThreeCopySchedule.Block](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ExchangeSpecialization.uniform](ExchangeSpecializationEndpoints.definitions.md#def-187fdef53c805022)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.ProgramNetwork.instFintypeVertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-c8f35892a045d1f9)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.ExchangeSpecialization.family](ExchangeSpecializationEndpoints.definitions.md#def-78bf95f0832b39f8)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.TensorLiftProgram.instFintypeRound](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-9d47e1f47feb55c7)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.PartialSwapExecution.restrictFamily](../Local/PartialSwapExecution.definitions.md#def-d9dcea7b7c12220f)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.ExchangeSpecialization.doubledDecEq](ExchangeSpecializationEndpoints.definitions.md#def-bec6ecadb64b1ab9)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Bool.fintype`, `Lex`, `Rat`, `Option.some`, `Matrix.rank`, `Sum`, `id`, `instOfNatNat`, `Fin.fintype`, `instHAdd`, `HAdd.hAdd`, `Sum.inr`, `Nat`, `Sigma.instFintype`, `Bool`, `instFintypeOption`, `instAddNat`, `instFintypeProd`, `Sigma.mk`, `Prod`, `OfNat.ofNat`, `Fin`, `List.length`, `Rat.commRing`, `Sigma`

<a id="def-238a7d902cdc531a"></a>
## `CodedSorting.Construction.ExchangeSpecialization.instNeZeroNatHPowRadix`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeSpecializationEndpoints.lean#L146)

**类型**

```lean
∀ (f : ℕ), NeZero (CodedSorting.Construction.ExchangeSpecialization.radix ^ f)
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.radix](ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `MulZeroClass.toZero`

<a id="def-1ac5781123eaec83"></a>
## `CodedSorting.Construction.ExchangeSpecialization.frameMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L148)

**类型**

```lean
(f : ℕ) →
  CodedSorting.Construction.ExchangeSpecialization.Node →
    Matrix (Lex (Fin 512 ⊕ Fin 512)) (Lex (Fin 512 ⊕ Fin 512))
      (Fin (CodedSorting.Construction.ExchangeSpecialization.uniform.prime ^ f))
```

**定义**

```lean
fun f v =>
  CodedSorting.Construction.PartialSwapExecution.fullFinMatrix CodedSorting.Construction.ExchangeSpecialization.uniform
    f (some (Sum.inl v))
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.FamilyIndex](ExchangeSpecializationEndpoints.definitions.md#def-a79378b5d5c5d461)
- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](../Local/PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.PartialSwapExecution.fullFinMatrix](../Local/PartialSwapExecution.definitions.md#def-dc198e292b23529a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.uniform](ExchangeSpecializationEndpoints.definitions.md#def-187fdef53c805022)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.Construction.ExchangeSpecialization.family](ExchangeSpecializationEndpoints.definitions.md#def-78bf95f0832b39f8)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Option.some`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Sum.inl`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Sigma`

<a id="def-4d30def71e49611e"></a>
## `CodedSorting.Construction.ExchangeSpecialization.edgeMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L149)

**类型**

```lean
(f : ℕ) →
  (e : CodedSorting.Construction.OneLevelChildren.Edge) →
    Matrix (Lex (Fin 512 ⊕ Fin 512)) (Lex (Fin 512 ⊕ Fin 512))
      (Fin ((CodedSorting.Construction.ExchangeSpecialization.edgeFamily e).prime ^ f))
```

**定义**

```lean
fun f e =>
  CodedSorting.Construction.PartialSwapExecution.fullFinMatrix
    (CodedSorting.Construction.ExchangeSpecialization.edgeFamily e) f none
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](../Local/ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](../Local/PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.PartialSwapExecution.fullFinMatrix](../Local/PartialSwapExecution.definitions.md#def-dc198e292b23529a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.edgeFamily](ExchangeSpecializationEndpoints.definitions.md#def-2580b898498e1f35)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.fintype`, `Option.none`, `HPow.hPow`, `Nat`, `Bool`, `instHPow`, `Prod`, `OfNat.ofNat`, `Fin`, `Rat.commRing`

<a id="def-433c895725f6e331"></a>
## `CodedSorting.Construction.ExchangeSpecialization.frameMatrix_square`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeSpecializationEndpoints.lean#L164)

**类型**

```lean
∀ (f : ℕ) (v : CodedSorting.Construction.ExchangeSpecialization.Node),
  CodedSorting.Construction.ExchangeSpecialization.frameMatrix f v *
      CodedSorting.Construction.ExchangeSpecialization.frameMatrix f v =
    1
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.FamilyIndex](ExchangeSpecializationEndpoints.definitions.md#def-a79378b5d5c5d461)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](../Local/PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.ExchangeSpecialization.instNeZeroNatHPowRadix](ExchangeSpecializationEndpoints.definitions.md#def-238a7d902cdc531a)
- [CodedSorting.Construction.ExchangeSpecialization.uniform](ExchangeSpecializationEndpoints.definitions.md#def-187fdef53c805022)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.Construction.ExchangeSpecialization.frameMatrix](ExchangeSpecializationEndpoints.definitions.md#def-1ac5781123eaec83)
- [CodedSorting.Construction.ExchangeSpecialization.family](ExchangeSpecializationEndpoints.definitions.md#def-78bf95f0832b39f8)
- [CodedSorting.Construction.ExchangeSpecialization.doubledDecEq](ExchangeSpecializationEndpoints.definitions.md#def-bec6ecadb64b1ab9)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Lex.fintype`, `instFintypeSum`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `CommRing.toNonUnitalCommRing`, `Fin.instCommRing`, `Matrix`, `Lex`, `Nat.instMonoid`, `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.instAddMonoidWithOne`, `Fin.fintype`, `AddMonoidWithOne.toOne`, `HPow.hPow`, `Fin.instMul`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Fin.addCommMonoid`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `MulZeroClass.toZero`

<a id="def-99b116eb0a9223e8"></a>
## `CodedSorting.Construction.ExchangeSpecialization.edgeMatrix_square`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeSpecializationEndpoints.lean#L167)

**类型**

```lean
∀ (f : ℕ) (e : CodedSorting.Construction.OneLevelChildren.Edge),
  CodedSorting.Construction.ExchangeSpecialization.edgeMatrix f e *
      CodedSorting.Construction.ExchangeSpecialization.edgeMatrix f e =
    1
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](../Local/ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](../Local/PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.instNeZeroNatHPowRadix](ExchangeSpecializationEndpoints.definitions.md#def-238a7d902cdc531a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeMatrix](ExchangeSpecializationEndpoints.definitions.md#def-4d30def71e49611e)
- [CodedSorting.Construction.ExchangeSpecialization.edgeFamily](ExchangeSpecializationEndpoints.definitions.md#def-2580b898498e1f35)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.ExchangeSpecialization.doubledDecEq](ExchangeSpecializationEndpoints.definitions.md#def-bec6ecadb64b1ab9)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Lex.fintype`, `instFintypeSum`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `CommRing.toNonUnitalCommRing`, `Fin.instCommRing`, `Matrix`, `Lex`, `Nat.instMonoid`, `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.instAddMonoidWithOne`, `Fin.fintype`, `AddMonoidWithOne.toOne`, `HPow.hPow`, `Fin.instMul`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Fin.addCommMonoid`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `MulZeroClass.toZero`

<a id="def-ccfe084da8739a92"></a>
## `CodedSorting.Construction.ExchangeSpecialization.location`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L273)

**类型**

```lean
(f Pref G S : ℕ) →
  CodedSorting.Construction.ExchangeSpecialization.Node →
    Equiv.Perm
      (Fin
        (CodedSorting.CommonAddressLayout.Volume (Fin 512) Pref
          (CodedSorting.Construction.ExchangeSpecialization.radix ^ f) G S))
```

**定义**

```lean
fun f Pref G S v =>
  CodedSorting.Construction.ExchangeFramePermutation.numericPerm
    (CodedSorting.Construction.ExchangeSpecialization.frameMatrix f v) ⋯ Pref G S
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.frameMatrix_square](ExchangeSpecializationEndpoints.definitions.md#def-433c895725f6e331)
- [CodedSorting.Construction.ExchangeSpecialization.FamilyIndex](ExchangeSpecializationEndpoints.definitions.md#def-a79378b5d5c5d461)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](../Local/PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.ExchangeSpecialization.instNeZeroNatHPowRadix](ExchangeSpecializationEndpoints.definitions.md#def-238a7d902cdc531a)
- [CodedSorting.Construction.ExchangeSpecialization.uniform](ExchangeSpecializationEndpoints.definitions.md#def-187fdef53c805022)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.Construction.ExchangeSpecialization.frameMatrix](ExchangeSpecializationEndpoints.definitions.md#def-1ac5781123eaec83)
- [CodedSorting.Construction.ExchangeFramePermutation.numericPerm](../Local/ExchangeFramePermutation.definitions.md#def-d5b41a60c5233f49)
- [CodedSorting.Construction.ExchangeSpecialization.family](ExchangeSpecializationEndpoints.definitions.md#def-78bf95f0832b39f8)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.Construction.ExchangeSpecialization.radix](ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Lex`, `Nat.instMonoid`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.fintype`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-f505d6f449c2b2be"></a>
## `CodedSorting.Construction.ExchangeSpecialization.edgePermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeSpecializationEndpoints.lean#L277)

**类型**

```lean
(f Pref G S : ℕ) →
  CodedSorting.Construction.OneLevelChildren.Edge →
    Equiv.Perm
      (Fin
        (CodedSorting.CommonAddressLayout.Volume (Fin 512) Pref
          (CodedSorting.Construction.ExchangeSpecialization.radix ^ f) G S))
```

**定义**

```lean
fun f Pref G S e =>
  CodedSorting.Construction.ExchangeFramePermutation.numericPerm
    (CodedSorting.Construction.ExchangeSpecialization.edgeMatrix f e) ⋯ Pref G S
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](../Local/ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](../Local/PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.instNeZeroNatHPowRadix](ExchangeSpecializationEndpoints.definitions.md#def-238a7d902cdc531a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeMatrix](ExchangeSpecializationEndpoints.definitions.md#def-4d30def71e49611e)
- [CodedSorting.Construction.ExchangeFramePermutation.numericPerm](../Local/ExchangeFramePermutation.definitions.md#def-d5b41a60c5233f49)
- [CodedSorting.Construction.ExchangeSpecialization.edgeFamily](ExchangeSpecializationEndpoints.definitions.md#def-2580b898498e1f35)
- [CodedSorting.Construction.ExchangeSpecialization.edgeMatrix_square](ExchangeSpecializationEndpoints.definitions.md#def-99b116eb0a9223e8)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.Construction.ExchangeSpecialization.radix](ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Lex`, `Nat.instMonoid`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.fintype`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-8f9b5fa9270d1546"></a>
## `CodedSorting.Construction.ExchangeSpecialization.coordinateEquiv._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeSpecializationEndpoints.lean)

**类型**

```lean
512 = Fintype.card (Fin 8 × Fin 8 × Fin 8)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Fintype.card`, `instOfNatNat`, `Fin.fintype`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-55db969e06ce7aaa"></a>
## `CodedSorting.Construction.ExchangeSpecialization.decomposition._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeSpecializationEndpoints.lean)

**类型**

```lean
∀ (e : CodedSorting.Construction.OneLevelChildren.Edge),
  Nonempty
    (CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition
      (CodedSorting.Construction.ExchangeSpecialization.edgeProjection e))
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)

**基础库名称**

`instOfNatNat`, `Fin.fintype`, `Nat`, `Nonempty`, `OfNat.ofNat`, `Fin`

<a id="def-fb481be6768f2dbf"></a>
## `CodedSorting.Construction.ExchangeSpecialization.family.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ExchangeSpecializationEndpoints.lean)

**类型**

```lean
(motive : CodedSorting.Construction.ExchangeSpecialization.FamilyIndex → Sort u_1) →
  (x : CodedSorting.Construction.ExchangeSpecialization.FamilyIndex) →
    (Unit → motive none) →
      ((v : CodedSorting.Construction.ExchangeSpecialization.Node) → motive (some (Sum.inl v))) →
        ((e : CodedSorting.Construction.OneLevelChildren.Edge) →
            (k :
                CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex
                  (CodedSorting.Construction.ExchangeSpecialization.edgeProjection e)) →
              motive (some (Sum.inr ⟨e, k⟩))) →
          motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 =>
  Option.casesOn x (h_1 ()) fun val =>
    Sum.casesOn val (fun val => h_2 val) fun val => Sigma.casesOn val fun fst snd => h_3 fst snd
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.FamilyIndex](ExchangeSpecializationEndpoints.definitions.md#def-a79378b5d5c5d461)
- [CodedSorting.Construction.OneLevelChildren.Edge](../OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.Node](ExchangeSpecializationEndpoints.definitions.md#def-2b2a59c88aa39ade)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)

**基础库名称**

`Unit.unit`, `Option.casesOn`, `Option.some`, `Sum.casesOn`, `Sum`, `instOfNatNat`, `Sum.inl`, `Option.none`, `Unit`, `Sum.inr`, `Nat`, `Sigma.mk`, `Sigma.casesOn`, `OfNat.ofNat`, `Sigma`
