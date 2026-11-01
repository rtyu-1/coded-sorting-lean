# Children 的定义

[源码](Children.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-299c106d65a6a02a"></a>
## `CodedSorting.Construction.OneLevelChildren.Edge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Children.lean#L21)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.ProgramNetwork.Wire CodedSorting.Construction.TensorLiftProgram.GlobalReg
  CodedSorting.Construction.TensorFrameNetwork.program.length
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.ProgramNetwork.Wire](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`List.length`

<a id="def-30d83915a3eba2c8"></a>
## `CodedSorting.Construction.OneLevelChildren.edgeRank`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Children.lean#L23)

**类型**

```lean
CodedSorting.Construction.OneLevelChildren.Edge → ℕ
```

**定义**

```lean
fun e =>
  Matrix.rank
    (CodedSorting.Construction.TensorFrameNetwork.actualLabel
        (CodedSorting.ProgramNetwork.wireHead CodedSorting.Construction.TensorFrameNetwork.program e) -
      CodedSorting.Construction.TensorFrameNetwork.actualLabel
        (CodedSorting.ProgramNetwork.wireTail CodedSorting.Construction.TensorFrameNetwork.program e))
```

**继续展开**

- [CodedSorting.Construction.TensorFrameNetwork.actualLabel](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-c62aefbdfe1c4740)
- [CodedSorting.Construction.OneLevelChildren.Edge](Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.ProgramNetwork.wireHead](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.Construction.TensorFrameGeometry.GlobalMatrix](../../Circuit/Composition/TensorNetworkGeometry.definitions.md#def-cc6ac375b6fa11c4)
- [CodedSorting.ProgramNetwork.wireTail](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.TensorLabels.H](../../Circuit/Labels/Framework/TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)

**基础库名称**

`Rat.instSub`, `Rat`, `HSub.hSub`, `Matrix.rank`, `instOfNatNat`, `Fin.fintype`, `instHSub`, `Matrix.sub`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`, `Rat.commRing`

<a id="def-e64350cb13f8e2d9"></a>
## `CodedSorting.Construction.OneLevelChildren.Child`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Children.lean#L26)

**类型**

```lean
Type
```

**定义**

```lean
(e : CodedSorting.Construction.OneLevelChildren.Edge) × Fin (CodedSorting.Construction.OneLevelChildren.edgeRank e)
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](Children.definitions.md#def-30d83915a3eba2c8)

**基础库名称**

`Fin`, `Sigma`
