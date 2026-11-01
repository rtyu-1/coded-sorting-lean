# TensorFrameNetwork 的定义

[源码](TensorFrameNetwork.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-48fc94b7a3b7e000"></a>
## `CodedSorting.Construction.TensorFrameNetwork.annotatedStages`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameNetwork.lean#L441)

**类型**

```lean
List CodedSorting.Construction.TensorFrameProgram.Stage
```

**定义**

```lean
CodedSorting.Construction.TensorFrameProgram.stages CodedSorting.Construction.PhysicalFramePaths.forwardWord
  CodedSorting.Construction.PhysicalFramePaths.middleWord CodedSorting.Construction.PhysicalFramePaths.forwardWord
```

**继续展开**

- [CodedSorting.Construction.TensorFrameProgram.Stage](TensorFrameProgram.definitions.md#def-594c907edead5734)
- [CodedSorting.Construction.TensorFrameProgram.stages](TensorFrameProgram.definitions.md#def-1bdd968c524ea98e)
- [CodedSorting.Construction.PhysicalFramePaths.forwardWord](../MemoryAccess/PhysicalFrameWord.definitions.md#def-a51d92cc3db97e1a)
- [CodedSorting.Construction.PhysicalFramePaths.middleWord](../MemoryAccess/PhysicalFrameWord.definitions.md#def-775e708c2bdaaaaf)

**基础库名称**

`List`

<a id="def-831c8f924acdba89"></a>
## `CodedSorting.Construction.TensorFrameNetwork.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameNetwork.lean#L443)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.GlobalReg)
```

**定义**

```lean
CodedSorting.Construction.TensorThreeRound.threeRoundProgram CodedSorting.Construction.ConcreteLocalProgram.forward
  CodedSorting.Construction.ConcreteLocalProgram.middle CodedSorting.Construction.ConcreteLocalProgram.forward
  CodedSorting.Construction.TensorFrameGeometry.partner
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorFrameGeometry.partner](TensorNetworkGeometry.definitions.md#def-455da91fe23df598)
- [CodedSorting.Construction.ConcreteLocalProgram.forward](../Local/ConcreteLocalProgram.definitions.md#def-c2d12f93764101cb)
- [CodedSorting.Construction.ConcreteLocalProgram.middle](../Local/ConcreteLocalProgram.definitions.md#def-26f32c601224e3e7)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorThreeRound.threeRoundProgram](TensorThreeRound.definitions.md#def-ca4a87271cd10a88)

**基础库名称**

`List`

<a id="def-0e846a45c5538a95"></a>
## `CodedSorting.Construction.TensorFrameNetwork.annotatedStages_program`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorFrameNetwork.lean#L448)

**类型**

```lean
List.map (CodedSorting.Construction.TensorFrameProgram.stageGate CodedSorting.Construction.TensorFrameGeometry.partner)
    CodedSorting.Construction.TensorFrameNetwork.annotatedStages =
  CodedSorting.Construction.TensorFrameNetwork.program
```

**继续展开**

- [CodedSorting.Construction.TensorFrameProgram.Stage](TensorFrameProgram.definitions.md#def-594c907edead5734)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorFrameGeometry.partner](TensorNetworkGeometry.definitions.md#def-455da91fe23df598)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorFrameProgram.stageGate](TensorFrameProgram.definitions.md#def-8a55e8bf73004b38)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.TensorFrameNetwork.annotatedStages](TensorFrameNetwork.definitions.md#def-48fc94b7a3b7e000)

**基础库名称**

`List.map`, `List`, `Eq`

<a id="def-ea107afd0ba63df8"></a>
## `CodedSorting.Construction.TensorFrameNetwork.tempSource`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameNetwork.lean#L452)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Block → Fin 9 → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun r block t =>
  CodedSorting.Construction.TensorFrameGeometry.globalFrame r block
    (if r = CodedSorting.Construction.TensorLiftProgram.Round.second then
      1 - CodedSorting.Construction.PhysicalFramePaths.frameMatrix (510 + ↑t)
    else CodedSorting.Construction.PhysicalFramePaths.frameMatrix (510 + ↑t))
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameGeometry.globalFrame](TensorFrameProgram.definitions.md#def-a9278272af3581a4)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](../MemoryAccess/PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.PhysicalFramePaths.frameMatrix](../MemoryAccess/PhysicalFramePaths.definitions.md#def-c985f0fda5be0bcd)
- [CodedSorting.Construction.TensorLiftProgram.instDecidableEqRound](TensorLiftProgram.definitions.md#def-4e29313a6d76909b)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

**基础库名称**

`NormedCommRing.toNormedRing`, `NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Rat.instSub`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `NormedRing.toRing`, `Rat`, `instDecidableEqFin`, `AddGroupWithOne.toAddMonoidWithOne`, `HSub.hSub`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `instOfNatNat`, `NormedCommRing.toNonUnitalNormedCommRing`, `Fin.val`, `AddMonoidWithOne.toOne`, `instHAdd`, `instHSub`, `Rat.instNormedField`, `HAdd.hAdd`, `Matrix.sub`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `instAddNat`, `NonUnitalNormedCommRing.toNonUnitalCommRing`, `NormedField.toNormedCommRing`, `OfNat.ofNat`, `Fin`, `Eq`, `Ring.toAddGroupWithOne`, `MulZeroClass.toZero`, `ite`

<a id="def-836ebc5829774fa5"></a>
## `CodedSorting.Construction.TensorFrameNetwork.tempTerminal`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameNetwork.lean#L456)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Block → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun r block =>
  CodedSorting.Construction.TensorFrameGeometry.globalFrame r block
    (if r = CodedSorting.Construction.TensorLiftProgram.Round.second then 1 else 0)
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameGeometry.globalFrame](TensorFrameProgram.definitions.md#def-a9278272af3581a4)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](../MemoryAccess/PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.TensorLiftProgram.instDecidableEqRound](TensorLiftProgram.definitions.md#def-4e29313a6d76909b)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

**基础库名称**

`NormedCommRing.toNormedRing`, `NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `NormedRing.toRing`, `Rat`, `instDecidableEqFin`, `AddGroupWithOne.toAddMonoidWithOne`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `instOfNatNat`, `NormedCommRing.toNonUnitalNormedCommRing`, `AddMonoidWithOne.toOne`, `Rat.instNormedField`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Zero.toOfNat0`, `NonUnitalNormedCommRing.toNonUnitalCommRing`, `NormedField.toNormedCommRing`, `OfNat.ofNat`, `Fin`, `Eq`, `Matrix.zero`, `Ring.toAddGroupWithOne`, `MulZeroClass.toZero`, `ite`

<a id="def-02b33ffdb0500a29"></a>
## `CodedSorting.Construction.TensorFrameNetwork.physicalSource`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameNetwork.lean#L459)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.GlobalReg → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun x =>
  match x with
  | Sum.inl r => CodedSorting.Construction.TensorFrameGeometry.sourceLabel r
  | Sum.inr (r, block, t) => CodedSorting.Construction.TensorFrameNetwork.tempSource r block t
```

**继续展开**

- [CodedSorting.Construction.TensorFrameNetwork.physicalSource.match_1](TensorFrameNetwork.definitions.md#def-ec8d7b3c8213978c)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameGeometry.sourceLabel](TensorNetworkGeometry.definitions.md#def-0fe1dc52244b418a)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameNetwork.tempSource](TensorFrameNetwork.definitions.md#def-ea107afd0ba63df8)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-37251dee3e9cc851"></a>
## `CodedSorting.Construction.TensorFrameNetwork.physicalTerminal`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameNetwork.lean#L463)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.GlobalReg → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun x =>
  match x with
  | Sum.inl r => CodedSorting.Construction.TensorFrameGeometry.terminalLabel r
  | Sum.inr (r, block, snd) => CodedSorting.Construction.TensorFrameNetwork.tempTerminal r block
```

**继续展开**

- [CodedSorting.Construction.TensorFrameNetwork.physicalSource.match_1](TensorFrameNetwork.definitions.md#def-ec8d7b3c8213978c)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameGeometry.terminalLabel](TensorNetworkGeometry.definitions.md#def-8e1334570fa7a637)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorFrameNetwork.tempTerminal](TensorFrameNetwork.definitions.md#def-836ebc5829774fa5)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-f3854ebe6ee75662"></a>
## `CodedSorting.Construction.TensorFrameNetwork.rawLabel`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameNetwork.lean#L467)

**类型**

```lean
CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
    (List.map
        (CodedSorting.Construction.TensorFrameProgram.stageGate CodedSorting.Construction.TensorFrameGeometry.partner)
        CodedSorting.Construction.TensorFrameNetwork.annotatedStages).length →
  CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
CodedSorting.StageLabels.vertexLabel CodedSorting.Construction.TensorFrameNetwork.annotatedStages
  (CodedSorting.Construction.TensorFrameProgram.stageGate CodedSorting.Construction.TensorFrameGeometry.partner)
  CodedSorting.Construction.TensorFrameProgram.stageLabel CodedSorting.Construction.TensorFrameNetwork.physicalSource
  CodedSorting.Construction.TensorFrameNetwork.physicalTerminal
```

**继续展开**

- [CodedSorting.Construction.TensorFrameProgram.Stage](TensorFrameProgram.definitions.md#def-594c907edead5734)
- [CodedSorting.Construction.TensorFrameNetwork.physicalTerminal](TensorFrameNetwork.definitions.md#def-37251dee3e9cc851)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorFrameGeometry.partner](TensorNetworkGeometry.definitions.md#def-455da91fe23df598)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameProgram.stageLabel](TensorFrameProgram.definitions.md#def-2cfb0a75f2837b12)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorFrameProgram.stageGate](TensorFrameProgram.definitions.md#def-8a55e8bf73004b38)
- [CodedSorting.Construction.TensorFrameNetwork.physicalSource](TensorFrameNetwork.definitions.md#def-02b33ffdb0500a29)
- [CodedSorting.StageLabels.vertexLabel](../Labels/Framework/StageLabels.definitions.md#def-fce87c300b941dbd)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.ProgramNetwork.Vertex](../NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)
- [CodedSorting.Construction.TensorFrameNetwork.annotatedStages](TensorFrameNetwork.definitions.md#def-48fc94b7a3b7e000)

**基础库名称**

`List.map`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `List.length`

<a id="def-c62aefbdfe1c4740"></a>
## `CodedSorting.Construction.TensorFrameNetwork.actualLabel`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameNetwork.lean#L470)

**类型**

```lean
CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
    CodedSorting.Construction.TensorFrameNetwork.program.length →
  CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
CodedSorting.StageLabels.transportLabel CodedSorting.Construction.TensorFrameNetwork.annotatedStages_program
  CodedSorting.Construction.TensorFrameNetwork.rawLabel
```

**继续展开**

- [CodedSorting.Construction.TensorFrameProgram.Stage](TensorFrameProgram.definitions.md#def-594c907edead5734)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorFrameGeometry.partner](TensorNetworkGeometry.definitions.md#def-455da91fe23df598)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameNetwork.annotatedStages_program](TensorFrameNetwork.definitions.md#def-0e846a45c5538a95)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorFrameProgram.stageGate](TensorFrameProgram.definitions.md#def-8a55e8bf73004b38)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.StageLabels.transportLabel](../Labels/Framework/StageLabels.definitions.md#def-3069156944b597d9)
- [CodedSorting.Construction.TensorFrameNetwork.rawLabel](TensorFrameNetwork.definitions.md#def-f3854ebe6ee75662)
- [CodedSorting.ProgramNetwork.Vertex](../NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)
- [CodedSorting.Construction.TensorFrameNetwork.annotatedStages](TensorFrameNetwork.definitions.md#def-48fc94b7a3b7e000)

**基础库名称**

`List.map`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `List.length`

<a id="def-9d1847a336b60ba6"></a>
## `CodedSorting.Construction.TensorFrameNetwork.temporary_stream_count`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorFrameNetwork.lean#L501)

**类型**

```lean
Fintype.card CodedSorting.Construction.TensorLiftProgram.TemporaryStream = 998001
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorLiftProgram.instFintypeRound](TensorLiftProgram.definitions.md#def-9d47e1f47feb55c7)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Fintype.card`, `instOfNatNat`, `Fin.fintype`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-ec8d7b3c8213978c"></a>
## `CodedSorting.Construction.TensorFrameNetwork.physicalSource.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TensorFrameNetwork.lean)

**类型**

```lean
(motive : CodedSorting.Construction.TensorLiftProgram.GlobalReg → Sort u_1) →
  (x : CodedSorting.Construction.TensorLiftProgram.GlobalReg) →
    ((r : CodedSorting.Construction.ThreeCopySchedule.IndependentStream) → motive (Sum.inl r)) →
      ((r : CodedSorting.Construction.TensorLiftProgram.Round) →
          (block : CodedSorting.Construction.ThreeCopySchedule.Block) → (t : Fin 9) → motive (Sum.inr (r, block, t))) →
        motive x
```

**定义**

```lean
fun motive x h_1 h_2 =>
  Sum.casesOn x (fun val => h_1 val) fun val =>
    Prod.casesOn val fun fst snd => Prod.casesOn snd fun fst_1 snd => h_2 fst fst_1 snd
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)

**基础库名称**

`Sum.casesOn`, `Prod.mk`, `instOfNatNat`, `Sum.inl`, `Sum.inr`, `Nat`, `Prod`, `Prod.casesOn`, `OfNat.ofNat`, `Fin`
