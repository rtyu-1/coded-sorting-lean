# PhysicalFrameWord 的定义

[源码](PhysicalFrameWord.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-f7e566db2f6fdb43"></a>
## `CodedSorting.Construction.PhysicalFramePaths.annotatePhysical`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWord.lean#L214)

**类型**

```lean
CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg →
  CodedSorting.Construction.TensorFrameGeometry.LocalMatrix → CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**定义**

```lean
fun g P =>
  {
    gate :=
      CodedSorting.CircuitProgram.XorGate.lift
        CodedSorting.Construction.TensorLiftProgram.localPhysicalIndex.symm.toEmbedding g,
    frame := P }
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](../Local/LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg](../Local/LocalPhysicalSemantics.definitions.md#def-8ab4657853f928aa)
- [CodedSorting.CircuitProgram.XorGate.lift](../Framework/CircuitProgram.definitions.md#def-797ff3f834dbecd3)
- [CodedSorting.Construction.FiniteCertificate.registerCount](../Local/FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](../Composition/TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorLiftProgram.localPhysicalIndex](../Composition/TensorLiftProgram.definitions.md#def-3f174a6e4eb935de)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate.mk](../Composition/TensorFrameProgram.definitions.md#def-eb6722fef0706796)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](../Composition/TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instFintypeSum`, `instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `Fin.fintype`, `Equiv.toEmbedding`, `Nat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-4186e611df60ae2c"></a>
## `CodedSorting.Construction.PhysicalFramePaths.framedOrdinary`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWord.lean#L217)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Gate → CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**定义**

```lean
fun g =>
  CodedSorting.Construction.PhysicalFramePaths.annotatePhysical
    (CodedSorting.CircuitProgram.XorGate.lift CodedSorting.Construction.ExplicitCopies.originalEmbedding
      (CodedSorting.Construction.SymbolicXor.compileGate CodedSorting.Construction.FiniteCertificate.registerCount g))
    (CodedSorting.Construction.PhysicalFramePaths.frameMatrix g.frame)
```

**继续展开**

- [CodedSorting.Construction.ExplicitCopies.originalEmbedding](../Composition/ScatterCopies.definitions.md#def-e9d75cf5c51fb139)
- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](../Local/LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.Gate.frame](../Local/FiniteTypes.definitions.md#def-bb43c3add3b6fb8d)
- [CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg](../Local/LocalPhysicalSemantics.definitions.md#def-8ab4657853f928aa)
- [CodedSorting.CircuitProgram.XorGate.lift](../Framework/CircuitProgram.definitions.md#def-797ff3f834dbecd3)
- [CodedSorting.Construction.FiniteCertificate.registerCount](../Local/FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.FiniteCertificate.Gate](../Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.PhysicalFramePaths.frameMatrix](PhysicalFramePaths.definitions.md#def-c985f0fda5be0bcd)
- [CodedSorting.Construction.SymbolicXor.compileGate](../Local/FiniteSemantics.definitions.md#def-d677975eff07740c)
- [CodedSorting.Construction.PhysicalFramePaths.annotatePhysical](PhysicalFrameWord.definitions.md#def-f7e566db2f6fdb43)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](../Composition/TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instDecidableEqFin`, `Sum.instDecidableEq`, `instOfNatNat`, `Fin.fintype`, `Nat`, `OfNat.ofNat`

<a id="def-7cc10c162975bbad"></a>
## `CodedSorting.Construction.PhysicalFramePaths.framedCopy`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWord.lean#L220)

**类型**

```lean
CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg → CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**定义**

```lean
fun t =>
  CodedSorting.Construction.PhysicalFramePaths.annotatePhysical
    (CodedSorting.Construction.ExplicitCopies.copyGate
      (⇑CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper) t)
    (CodedSorting.Construction.PhysicalFramePaths.frameMatrix (510 + ↑t))
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](../Local/LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.registerCount](../Local/FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.ExplicitCopies.copyGate](../Composition/ScatterCopies.definitions.md#def-a03389164991af4f)
- [CodedSorting.Construction.PhysicalFramePaths.frameMatrix](PhysicalFramePaths.definitions.md#def-c985f0fda5be0bcd)
- [CodedSorting.Construction.PhysicalFramePaths.annotatePhysical](PhysicalFrameWord.definitions.md#def-f7e566db2f6fdb43)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](../Composition/TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)
- [CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper](../Local/LocalPhysicalSemantics.definitions.md#def-88033a59012feb72)

**基础库名称**

`instDecidableEqFin`, `instOfNatNat`, `Fin.val`, `Function.Embedding`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Function.instFunLikeEmbedding`, `OfNat.ofNat`, `DFunLike.coe`

<a id="def-5e7b44ec1fffc324"></a>
## `CodedSorting.Construction.PhysicalFramePaths.framedScatter`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWord.lean#L223)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Gate → CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**定义**

```lean
fun g =>
  CodedSorting.Construction.PhysicalFramePaths.annotatePhysical
    (CodedSorting.Construction.ScatterCopies.copiedScatter
      (CodedSorting.Construction.ConcreteLocalProgram.scatterRow g))
    (CodedSorting.Construction.PhysicalFramePaths.frameMatrix 0)
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](../Local/LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.registerCount](../Local/FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.ConcreteLocalProgram.scatterRow](../Local/ConcreteLocalProgram.definitions.md#def-6f5e42443e179678)
- [CodedSorting.Construction.ScatterCopies.copiedScatter](../Composition/ScatterCopies.definitions.md#def-8b2995aef7915972)
- [CodedSorting.Construction.FiniteCertificate.Gate](../Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.PhysicalFramePaths.frameMatrix](PhysicalFramePaths.definitions.md#def-c985f0fda5be0bcd)
- [CodedSorting.Construction.PhysicalFramePaths.annotatePhysical](PhysicalFrameWord.definitions.md#def-f7e566db2f6fdb43)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](../Composition/TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instDecidableEqFin`, `instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-f0828bdca9d3f0c2"></a>
## `CodedSorting.Construction.PhysicalFramePaths.complementFrame`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWord.lean#L226)

**类型**

```lean
CodedSorting.Construction.TensorFrameProgram.FramedGate → CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**定义**

```lean
fun g => { gate := g.gate, frame := 1 - g.frame }
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate.gate](../Composition/TensorFrameProgram.definitions.md#def-add1e37e387d9654)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate.mk](../Composition/TensorFrameProgram.definitions.md#def-eb6722fef0706796)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](../Composition/TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate.frame](../Composition/TensorFrameProgram.definitions.md#def-a4bce6ec320b2b60)

**基础库名称**

`NormedCommRing.toNormedRing`, `NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Rat.instSub`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `NormedRing.toRing`, `Rat`, `instDecidableEqFin`, `AddGroupWithOne.toAddMonoidWithOne`, `HSub.hSub`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `instOfNatNat`, `NormedCommRing.toNonUnitalNormedCommRing`, `AddMonoidWithOne.toOne`, `instHSub`, `Rat.instNormedField`, `Matrix.sub`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `NonUnitalNormedCommRing.toNonUnitalCommRing`, `NormedField.toNormedCommRing`, `OfNat.ofNat`, `Fin`, `Ring.toAddGroupWithOne`, `MulZeroClass.toZero`

<a id="def-a51d92cc3db97e1a"></a>
## `CodedSorting.Construction.PhysicalFramePaths.forwardWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWord.lean#L228)

**类型**

```lean
List CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**定义**

```lean
List.map CodedSorting.Construction.PhysicalFramePaths.framedOrdinary
        CodedSorting.Construction.PhysicalFramePaths.physicalPrefix ++
      List.map CodedSorting.Construction.PhysicalFramePaths.framedCopy
        CodedSorting.Construction.LocalPhysicalSemantics.allTemporaries ++
    List.map CodedSorting.Construction.PhysicalFramePaths.framedScatter
      CodedSorting.Construction.PhysicalFramePaths.physicalScatter ++
  List.map CodedSorting.Construction.PhysicalFramePaths.framedOrdinary
    CodedSorting.Construction.PhysicalFramePaths.physicalSuffix
```

**继续展开**

- [CodedSorting.Construction.PhysicalFramePaths.physicalPrefix](PhysicalFrameWordData.definitions.md#def-447407dc57ac7037)
- [CodedSorting.Construction.PhysicalFramePaths.framedScatter](PhysicalFrameWord.definitions.md#def-5e7b44ec1fffc324)
- [CodedSorting.Construction.PhysicalFramePaths.physicalSuffix](PhysicalFrameWordData.definitions.md#def-da276d2c2da84939)
- [CodedSorting.Construction.FiniteCertificate.Gate](../Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.PhysicalFramePaths.physicalScatter](PhysicalFrameWordData.definitions.md#def-d1f8f6b329be583a)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](../Composition/TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.PhysicalFramePaths.framedOrdinary](PhysicalFrameWord.definitions.md#def-4186e611df60ae2c)
- [CodedSorting.Construction.LocalPhysicalSemantics.allTemporaries](../Local/LocalPhysicalSemantics.definitions.md#def-f0a6e00641a5b0fc)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)
- [CodedSorting.Construction.PhysicalFramePaths.framedCopy](PhysicalFrameWord.definitions.md#def-7cc10c162975bbad)

**基础库名称**

`List.map`, `instHAppendOfAppend`, `List`, `List.instAppend`, `HAppend.hAppend`

<a id="def-ba5708087d7e245a"></a>
## `CodedSorting.Construction.PhysicalFramePaths.middleRawWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWord.lean#L232)

**类型**

```lean
List CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**定义**

```lean
List.map CodedSorting.Construction.PhysicalFramePaths.framedOrdinary
        CodedSorting.Construction.PhysicalFramePaths.physicalSuffix.reverse ++
      List.map CodedSorting.Construction.PhysicalFramePaths.framedCopy
        CodedSorting.Construction.LocalPhysicalSemantics.allTemporaries ++
    List.map CodedSorting.Construction.PhysicalFramePaths.framedScatter
      CodedSorting.Construction.PhysicalFramePaths.physicalScatter.reverse ++
  List.map CodedSorting.Construction.PhysicalFramePaths.framedOrdinary
    CodedSorting.Construction.PhysicalFramePaths.physicalPrefix.reverse
```

**继续展开**

- [CodedSorting.Construction.PhysicalFramePaths.physicalPrefix](PhysicalFrameWordData.definitions.md#def-447407dc57ac7037)
- [CodedSorting.Construction.PhysicalFramePaths.framedScatter](PhysicalFrameWord.definitions.md#def-5e7b44ec1fffc324)
- [CodedSorting.Construction.PhysicalFramePaths.physicalSuffix](PhysicalFrameWordData.definitions.md#def-da276d2c2da84939)
- [CodedSorting.Construction.FiniteCertificate.Gate](../Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.PhysicalFramePaths.physicalScatter](PhysicalFrameWordData.definitions.md#def-d1f8f6b329be583a)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](../Composition/TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.PhysicalFramePaths.framedOrdinary](PhysicalFrameWord.definitions.md#def-4186e611df60ae2c)
- [CodedSorting.Construction.LocalPhysicalSemantics.allTemporaries](../Local/LocalPhysicalSemantics.definitions.md#def-f0a6e00641a5b0fc)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)
- [CodedSorting.Construction.PhysicalFramePaths.framedCopy](PhysicalFrameWord.definitions.md#def-7cc10c162975bbad)

**基础库名称**

`List.map`, `instHAppendOfAppend`, `List`, `List.reverse`, `List.instAppend`, `HAppend.hAppend`

<a id="def-775e708c2bdaaaaf"></a>
## `CodedSorting.Construction.PhysicalFramePaths.middleWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWord.lean#L236)

**类型**

```lean
List CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**定义**

```lean
List.map CodedSorting.Construction.PhysicalFramePaths.complementFrame
  CodedSorting.Construction.PhysicalFramePaths.middleRawWord
```

**继续展开**

- [CodedSorting.Construction.PhysicalFramePaths.complementFrame](PhysicalFrameWord.definitions.md#def-f0828bdca9d3f0c2)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](../Composition/TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.PhysicalFramePaths.middleRawWord](PhysicalFrameWord.definitions.md#def-ba5708087d7e245a)

**基础库名称**

`List.map`, `List`
