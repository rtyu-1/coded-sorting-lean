# ReverseLocalProgram 的定义

[源码](ReverseLocalProgram.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-0b0d122e208fe53a"></a>
## `CodedSorting.Construction.LocalPhysicalContract.structuredProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ReverseLocalProgram.lean#L85)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg) →
  List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg)
```

**定义**

```lean
fun word =>
  List.map
    (CodedSorting.CircuitProgram.XorGate.lift
      CodedSorting.Construction.TensorLiftProgram.localPhysicalIndex.symm.toEmbedding)
    word
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg](LocalPhysicalSemantics.definitions.md#def-8ab4657853f928aa)
- [CodedSorting.CircuitProgram.XorGate.lift](../Framework/CircuitProgram.definitions.md#def-797ff3f834dbecd3)
- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](../Composition/TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorLiftProgram.localPhysicalIndex](../Composition/TensorLiftProgram.definitions.md#def-3f174a6e4eb935de)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instFintypeSum`, `instDecidableEqProd`, `List.map`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `Fin.fintype`, `List`, `Equiv.toEmbedding`, `Nat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-f1a0c58e317a1b44"></a>
## `CodedSorting.Construction.ReverseLocalProgram.reverseLocalPhysicalProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ReverseLocalProgram.lean#L235)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg) →
  List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg) →
    List
        (CodedSorting.Construction.ScatterCopies.ScatterRow CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg
          CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg) →
      List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg)
```

**定义**

```lean
fun before after rows =>
  CodedSorting.Construction.LocalPhysicalSemantics.localPhysicalProgram after.reverse before.reverse rows.reverse
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg](LocalPhysicalSemantics.definitions.md#def-8ab4657853f928aa)
- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.LocalPhysicalSemantics.localPhysicalProgram](LocalPhysicalSemantics.definitions.md#def-83343efdd06b3465)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](../Composition/ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instDecidableEqFin`, `Sum.instDecidableEq`, `instOfNatNat`, `List`, `Nat`, `List.reverse`, `OfNat.ofNat`
