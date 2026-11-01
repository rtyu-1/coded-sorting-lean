# TensorFrameProgram 的定义

[源码](TensorFrameProgram.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-4110f618451d8172"></a>
## `CodedSorting.Construction.TensorFrameGeometry.liftLinear`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L245)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Line →
    CodedSorting.Construction.ThreeCopySchedule.Line →
      CodedSorting.Construction.TensorFrameGeometry.LocalMatrix →
        CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun r b c P =>
  match r with
  | CodedSorting.Construction.TensorLiftProgram.Round.first =>
    CodedSorting.TensorLabels.tensor3 P (CodedSorting.Construction.TensorFrameGeometry.lineProjector b)
      (CodedSorting.Construction.TensorFrameGeometry.lineProjector c)
  | CodedSorting.Construction.TensorLiftProgram.Round.second =>
    CodedSorting.TensorLabels.tensor3 (CodedSorting.Construction.TensorFrameGeometry.lineProjector c) P
      (CodedSorting.Construction.TensorFrameGeometry.lineProjector b)
  | CodedSorting.Construction.TensorLiftProgram.Round.third =>
    CodedSorting.TensorLabels.tensor3 (CodedSorting.Construction.TensorFrameGeometry.lineProjector b)
      (CodedSorting.Construction.TensorFrameGeometry.lineProjector c) P
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](../MemoryAccess/PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameGeometry.liftLinear.match_1](TensorFrameProgram.definitions.md#def-ae7759d51cde43ee)
- [CodedSorting.Construction.TensorFrameGeometry.lineProjector](TensorNetworkGeometry.definitions.md#def-2acb357ca4da07e1)
- [CodedSorting.TensorLabels.tensor3](../Labels/Framework/TensorLabels.definitions.md#def-a5a55f5aababa4ea)

**基础库名称**

`instOfNatNat`, `Unit`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-1f73f9570deee029"></a>
## `CodedSorting.Construction.TensorFrameGeometry.liftBase`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L254)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Line →
    CodedSorting.Construction.ThreeCopySchedule.Line → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun r b c =>
  match r with
  | CodedSorting.Construction.TensorLiftProgram.Round.first => 0
  | CodedSorting.Construction.TensorLiftProgram.Round.second =>
    CodedSorting.TensorLabels.tensor3 (1 - CodedSorting.Construction.TensorFrameGeometry.lineProjector c) 1
      (CodedSorting.Construction.TensorFrameGeometry.lineProjector b)
  | CodedSorting.Construction.TensorLiftProgram.Round.third =>
    1 -
      CodedSorting.TensorLabels.tensor3 (CodedSorting.Construction.TensorFrameGeometry.lineProjector b)
        (CodedSorting.Construction.TensorFrameGeometry.lineProjector c) 1
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameGeometry.liftLinear.match_1](TensorFrameProgram.definitions.md#def-ae7759d51cde43ee)
- [CodedSorting.Construction.TensorFrameGeometry.lineProjector](TensorNetworkGeometry.definitions.md#def-2acb357ca4da07e1)
- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)
- [CodedSorting.TensorLabels.tensor3](../Labels/Framework/TensorLabels.definitions.md#def-a5a55f5aababa4ea)

**基础库名称**

`NormedCommRing.toNormedRing`, `NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Rat.instSub`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `NormedRing.toRing`, `instDecidableEqProd`, `Matrix`, `Rat`, `instDecidableEqFin`, `AddGroupWithOne.toAddMonoidWithOne`, `HSub.hSub`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `instOfNatNat`, `NormedCommRing.toNonUnitalNormedCommRing`, `AddMonoidWithOne.toOne`, `Unit`, `instHSub`, `Rat.instNormedField`, `Matrix.sub`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Zero.toOfNat0`, `NonUnitalNormedCommRing.toNonUnitalCommRing`, `NormedField.toNormedCommRing`, `Prod`, `OfNat.ofNat`, `Fin`, `Matrix.zero`, `Ring.toAddGroupWithOne`, `MulZeroClass.toZero`

<a id="def-dcb86c0afbe74b3c"></a>
## `CodedSorting.Construction.TensorFrameGeometry.liftFrame`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L260)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Line →
    CodedSorting.Construction.ThreeCopySchedule.Line →
      CodedSorting.Construction.TensorFrameGeometry.LocalMatrix →
        CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun r b c P =>
  CodedSorting.Construction.TensorFrameGeometry.liftBase r b c +
    CodedSorting.Construction.TensorFrameGeometry.liftLinear r b c P
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](../MemoryAccess/PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.TensorFrameGeometry.liftBase](TensorFrameProgram.definitions.md#def-1f73f9570deee029)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.TensorLabels.H](../Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)
- [CodedSorting.Construction.TensorFrameGeometry.liftLinear](TensorFrameProgram.definitions.md#def-4110f618451d8172)

**基础库名称**

`Matrix.add`, `Rat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Rat.instAdd`, `OfNat.ofNat`

<a id="def-a9278272af3581a4"></a>
## `CodedSorting.Construction.TensorFrameGeometry.globalFrame`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L347)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Block →
    CodedSorting.Construction.TensorFrameGeometry.LocalMatrix →
      CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun r block P =>
  CodedSorting.Construction.TensorFrameGeometry.globalize block.1
    (CodedSorting.Construction.TensorFrameGeometry.liftFrame r block.2.1 block.2.2 P)
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](../MemoryAccess/PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.TensorFrameGeometry.liftFrame](TensorFrameProgram.definitions.md#def-dcb86c0afbe74b3c)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameGeometry.globalize](TensorNetworkGeometry.definitions.md#def-2e38ffdde752fb31)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Prod.fst`, `Prod`, `Prod.snd`

<a id="def-1d2e6468e1769ac5"></a>
## `CodedSorting.Construction.TensorFrameProgram.FramedGate`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](TensorFrameProgram.lean#L505)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.Construction.TensorFrameProgram.FramedGate.mk](TensorFrameProgram.definitions.md#def-eb6722fef0706796)

<a id="def-eb6722fef0706796"></a>
## `CodedSorting.Construction.TensorFrameProgram.FramedGate.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](TensorFrameProgram.lean#L505)

**类型**

```lean
CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg →
  CodedSorting.Construction.TensorFrameGeometry.LocalMatrix → CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](../MemoryAccess/PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)

**基础库名称**

`instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-add1e37e387d9654"></a>
## `CodedSorting.Construction.TensorFrameProgram.FramedGate.gate`

读取 `CodedSorting.Construction.TensorFrameProgram.FramedGate` 的 `gate` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](TensorFrameProgram.lean#L506)

**类型**

```lean
CodedSorting.Construction.TensorFrameProgram.FramedGate →
  CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg
```

**定义**

```lean
fun self => self.1
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)

**基础库名称**

`instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-a4bce6ec320b2b60"></a>
## `CodedSorting.Construction.TensorFrameProgram.FramedGate.frame`

读取 `CodedSorting.Construction.TensorFrameProgram.FramedGate` 的 `frame` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](TensorFrameProgram.lean#L507)

**类型**

```lean
CodedSorting.Construction.TensorFrameProgram.FramedGate → CodedSorting.Construction.TensorFrameGeometry.LocalMatrix
```

**定义**

```lean
fun self => self.2
```

**继续展开**

- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](../MemoryAccess/PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)

<a id="def-594c907edead5734"></a>
## `CodedSorting.Construction.TensorFrameProgram.Stage`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L509)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.TensorLiftProgram.Round ×
  CodedSorting.Construction.ThreeCopySchedule.Block × CodedSorting.Construction.TensorFrameProgram.FramedGate
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)

**基础库名称**

`Prod`

<a id="def-8a55e8bf73004b38"></a>
## `CodedSorting.Construction.TensorFrameProgram.stageGate`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L511)

**类型**

```lean
Equiv.Perm CodedSorting.Construction.ThreeCopySchedule.Line →
  CodedSorting.Construction.TensorFrameProgram.Stage →
    CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.GlobalReg
```

**定义**

```lean
fun pi s =>
  CodedSorting.CircuitProgram.XorGate.lift
    (CodedSorting.Construction.TensorLiftProgram.fiberEmbedding s.1
      (CodedSorting.Construction.TensorThreeRound.roundAssignment pi s.1) s.2.1)
    s.2.2.gate
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.fiberEmbedding](TensorLiftProgram.definitions.md#def-d4e1275444897c04)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.CircuitProgram.XorGate.lift](../Framework/CircuitProgram.definitions.md#def-797ff3f834dbecd3)
- [CodedSorting.Construction.TensorFrameProgram.Stage](TensorFrameProgram.definitions.md#def-594c907edead5734)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate.gate](TensorFrameProgram.definitions.md#def-add1e37e387d9654)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.TensorThreeRound.roundAssignment](TensorThreeRound.definitions.md#def-83372085a1b0abcf)

**基础库名称**

`instFintypeSum`, `instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `Prod.fst`, `Fin.fintype`, `Equiv.Perm`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`

<a id="def-2cfb0a75f2837b12"></a>
## `CodedSorting.Construction.TensorFrameProgram.stageLabel`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L514)

**类型**

```lean
CodedSorting.Construction.TensorFrameProgram.Stage → CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix
```

**定义**

```lean
fun s => CodedSorting.Construction.TensorFrameGeometry.globalFrame s.1 s.2.1 s.2.2.frame
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameGeometry.globalFrame](TensorFrameProgram.definitions.md#def-a9278272af3581a4)
- [CodedSorting.Construction.TensorFrameProgram.Stage](TensorFrameProgram.definitions.md#def-594c907edead5734)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate.frame](TensorFrameProgram.definitions.md#def-a4bce6ec320b2b60)

**基础库名称**

`Prod.fst`, `Prod`, `Prod.snd`

<a id="def-79a0c53ddcfccf78"></a>
## `CodedSorting.Construction.TensorFrameProgram.roundStages`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L517)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  List CodedSorting.Construction.TensorFrameProgram.FramedGate → List CodedSorting.Construction.TensorFrameProgram.Stage
```

**定义**

```lean
fun r word => List.flatMap (fun block => List.map (fun g => (r, block, g)) word) Finset.univ.toList
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorFrameProgram.Stage](TensorFrameProgram.definitions.md#def-594c907edead5734)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Finset.univ`, `List.map`, `Prod.mk`, `instOfNatNat`, `Finset.toList`, `Fin.fintype`, `List`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `List.flatMap`

<a id="def-1bdd968c524ea98e"></a>
## `CodedSorting.Construction.TensorFrameProgram.stages`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorFrameProgram.lean#L520)

**类型**

```lean
List CodedSorting.Construction.TensorFrameProgram.FramedGate →
  List CodedSorting.Construction.TensorFrameProgram.FramedGate →
    List CodedSorting.Construction.TensorFrameProgram.FramedGate →
      List CodedSorting.Construction.TensorFrameProgram.Stage
```

**定义**

```lean
fun one two three =>
  CodedSorting.Construction.TensorFrameProgram.roundStages CodedSorting.Construction.TensorLiftProgram.Round.first
        one ++
      CodedSorting.Construction.TensorFrameProgram.roundStages CodedSorting.Construction.TensorLiftProgram.Round.second
        two ++
    CodedSorting.Construction.TensorFrameProgram.roundStages CodedSorting.Construction.TensorLiftProgram.Round.third
      three
```

**继续展开**

- [CodedSorting.Construction.TensorFrameProgram.Stage](TensorFrameProgram.definitions.md#def-594c907edead5734)
- [CodedSorting.Construction.TensorFrameProgram.roundStages](TensorFrameProgram.definitions.md#def-79a0c53ddcfccf78)
- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorFrameProgram.FramedGate](TensorFrameProgram.definitions.md#def-1d2e6468e1769ac5)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

**基础库名称**

`instHAppendOfAppend`, `List`, `List.instAppend`, `HAppend.hAppend`

<a id="def-ae7759d51cde43ee"></a>
## `CodedSorting.Construction.TensorFrameGeometry.liftLinear.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TensorFrameProgram.lean)

**类型**

```lean
(motive : CodedSorting.Construction.TensorLiftProgram.Round → Sort u_1) →
  (r : CodedSorting.Construction.TensorLiftProgram.Round) →
    (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.first) →
      (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.second) →
        (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.third) → motive r
```

**定义**

```lean
fun motive r h_1 h_2 h_3 => CodedSorting.Construction.TensorLiftProgram.Round.casesOn r (h_1 ()) (h_2 ()) (h_3 ())
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.casesOn](TensorLiftProgram.definitions.md#def-81b2db8aedad1210)
- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

**基础库名称**

`Unit.unit`, `Unit`
