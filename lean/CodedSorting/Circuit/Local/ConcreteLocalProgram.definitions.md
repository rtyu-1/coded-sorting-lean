# ConcreteLocalProgram 的定义

[源码](ConcreteLocalProgram.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-ad7f07d56a291ef3"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.prefixGates`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L26)

**类型**

```lean
List CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
List.take CodedSorting.Construction.FiniteCertificate.beforeScatterCount
  CodedSorting.Construction.FiniteCertificate.gates.toList
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.gates](../../Generated/FiniteCircuit/Data.definitions.md#def-1b8de7a898d28b81)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.FiniteCertificate.beforeScatterCount](../../Generated/FiniteCircuit/Data.definitions.md#def-8594ece3c1c04e1b)

**基础库名称**

`Array.toList`, `List`, `List.take`

<a id="def-71c633127a0a21ef"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.scatterGates`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L27)

**类型**

```lean
List CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
List.take CodedSorting.Construction.FiniteCertificate.portCount
  (List.drop CodedSorting.Construction.FiniteCertificate.beforeScatterCount
    CodedSorting.Construction.FiniteCertificate.gates.toList)
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.gates](../../Generated/FiniteCircuit/Data.definitions.md#def-1b8de7a898d28b81)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.FiniteCertificate.portCount](FiniteTypes.definitions.md#def-be4c1d670d56138f)
- [CodedSorting.Construction.FiniteCertificate.beforeScatterCount](../../Generated/FiniteCircuit/Data.definitions.md#def-8594ece3c1c04e1b)

**基础库名称**

`Array.toList`, `List`, `List.drop`, `List.take`

<a id="def-ff59e12bb4aa024d"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.suffixGates`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L28)

**类型**

```lean
List CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
List.drop
  (CodedSorting.Construction.FiniteCertificate.beforeScatterCount +
    CodedSorting.Construction.FiniteCertificate.portCount)
  CodedSorting.Construction.FiniteCertificate.gates.toList
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.gates](../../Generated/FiniteCircuit/Data.definitions.md#def-1b8de7a898d28b81)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.FiniteCertificate.portCount](FiniteTypes.definitions.md#def-be4c1d670d56138f)
- [CodedSorting.Construction.FiniteCertificate.beforeScatterCount](../../Generated/FiniteCircuit/Data.definitions.md#def-8594ece3c1c04e1b)

**基础库名称**

`Array.toList`, `List`, `instHAdd`, `List.drop`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-e6a41341590be761"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.before`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L30)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg)
```

**定义**

```lean
List.map (CodedSorting.Construction.SymbolicXor.compileGate CodedSorting.Construction.FiniteCertificate.registerCount)
  CodedSorting.Construction.ConcreteLocalProgram.prefixGates
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.ConcreteLocalProgram.prefixGates](ConcreteLocalProgram.definitions.md#def-ad7f07d56a291ef3)
- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.SymbolicXor.compileGate](FiniteSemantics.definitions.md#def-d677975eff07740c)

**基础库名称**

`List.map`, `instDecidableEqFin`, `List`

<a id="def-51b09fe4ff08e72f"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.after`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L31)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg)
```

**定义**

```lean
List.map (CodedSorting.Construction.SymbolicXor.compileGate CodedSorting.Construction.FiniteCertificate.registerCount)
  CodedSorting.Construction.ConcreteLocalProgram.suffixGates
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.SymbolicXor.compileGate](FiniteSemantics.definitions.md#def-d677975eff07740c)
- [CodedSorting.Construction.ConcreteLocalProgram.suffixGates](ConcreteLocalProgram.definitions.md#def-ff59e12bb4aa024d)

**基础库名称**

`List.map`, `instDecidableEqFin`, `List`

<a id="def-6f5e42443e179678"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.scatterRow`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L33)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Gate →
  CodedSorting.Construction.ScatterCopies.ScatterRow CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg
    CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg
```

**定义**

```lean
fun g =>
  { destination := ⟨g.destination % CodedSorting.Construction.FiniteCertificate.registerCount, ⋯⟩,
    sources := {t | ↑(CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper t) ∈ g.sources} }
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.FiniteCertificate.Gate.destination](FiniteTypes.definitions.md#def-b03234f707cb6726)
- [CodedSorting.Construction.FiniteCertificate.Gate.sources](FiniteTypes.definitions.md#def-516947edde89b6d1)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](../Composition/ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)
- [CodedSorting.Construction.ScatterCopies.ScatterRow.mk](../Composition/ScatterCopies.definitions.md#def-ca957c76c103117c)
- [CodedSorting.Construction.ConcreteLocalProgram.scatterRow._proof_1](ConcreteLocalProgram.definitions.md#def-2187014308a3393d)
- [CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper](LocalPhysicalSemantics.definitions.md#def-88033a59012feb72)

**基础库名称**

`Finset.univ`, `Membership.mem`, `Fin.mk`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `instBEqOfDecidableEq`, `Fin.val`, `Fin.fintype`, `Function.Embedding`, `List`, `HMod.hMod`, `List.instMembership`, `Nat`, `instDecidableEqNat`, `Nat.instLawfulBEq`, `Function.instFunLikeEmbedding`, `List.instDecidableMemOfLawfulBEq`, `OfNat.ofNat`, `Finset.filter`, `DFunLike.coe`

<a id="def-2791af97268ae335"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.rows`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L37)

**类型**

```lean
List
  (CodedSorting.Construction.ScatterCopies.ScatterRow CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg
    CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg)
```

**定义**

```lean
List.map CodedSorting.Construction.ConcreteLocalProgram.scatterRow
  CodedSorting.Construction.ConcreteLocalProgram.scatterGates
```

**继续展开**

- [CodedSorting.Construction.ConcreteLocalProgram.scatterGates](ConcreteLocalProgram.definitions.md#def-71c633127a0a21ef)
- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.ConcreteLocalProgram.scatterRow](ConcreteLocalProgram.definitions.md#def-6f5e42443e179678)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](../Composition/ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`List.map`, `List`

<a id="def-c2d12f93764101cb"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.forward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L39)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg)
```

**定义**

```lean
CodedSorting.Construction.TensorNetwork.certificateForward CodedSorting.Construction.ConcreteLocalProgram.before
  CodedSorting.Construction.ConcreteLocalProgram.after CodedSorting.Construction.ConcreteLocalProgram.rows
```

**继续展开**

- [CodedSorting.Construction.ConcreteLocalProgram.rows](ConcreteLocalProgram.definitions.md#def-2791af97268ae335)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](../Composition/TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.ConcreteLocalProgram.before](ConcreteLocalProgram.definitions.md#def-e6a41341590be761)
- [CodedSorting.Construction.TensorNetwork.certificateForward](../Composition/TensorNetworkGeometry.definitions.md#def-f8d9daee937e759b)
- [CodedSorting.Construction.ConcreteLocalProgram.after](ConcreteLocalProgram.definitions.md#def-51b09fe4ff08e72f)

**基础库名称**

`instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `List`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-26f32c601224e3e7"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.middle`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteLocalProgram.lean#L40)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg)
```

**定义**

```lean
CodedSorting.Construction.TensorNetwork.certificateMiddle CodedSorting.Construction.ConcreteLocalProgram.before
  CodedSorting.Construction.ConcreteLocalProgram.after CodedSorting.Construction.ConcreteLocalProgram.rows
```

**继续展开**

- [CodedSorting.Construction.ConcreteLocalProgram.rows](ConcreteLocalProgram.definitions.md#def-2791af97268ae335)
- [CodedSorting.Construction.TensorNetwork.certificateMiddle](../Composition/TensorNetworkGeometry.definitions.md#def-b520642c4f48b26f)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](../Composition/TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.ConcreteLocalProgram.before](ConcreteLocalProgram.definitions.md#def-e6a41341590be761)
- [CodedSorting.Construction.ConcreteLocalProgram.after](ConcreteLocalProgram.definitions.md#def-51b09fe4ff08e72f)

**基础库名称**

`instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `List`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-2187014308a3393d"></a>
## `CodedSorting.Construction.ConcreteLocalProgram.scatterRow._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ConcreteLocalProgram.lean)

**类型**

```lean
∀ (g : CodedSorting.Construction.FiniteCertificate.Gate),
  g.destination % CodedSorting.Construction.FiniteCertificate.registerCount <
    CodedSorting.Construction.FiniteCertificate.registerCount
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.FiniteCertificate.Gate.destination](FiniteTypes.definitions.md#def-b03234f707cb6726)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`
