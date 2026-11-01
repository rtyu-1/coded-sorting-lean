# LocalPhysicalSemantics 的定义

[源码](LocalPhysicalSemantics.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-9d780c699bf6c5ab"></a>
## `CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalPhysicalSemantics.lean#L27)

**类型**

```lean
Type
```

**定义**

```lean
Fin CodedSorting.Construction.FiniteCertificate.registerCount
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)

**基础库名称**

`Fin`

<a id="def-b31f6a3a15f6fe7a"></a>
## `CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalPhysicalSemantics.lean#L28)

**类型**

```lean
Type
```

**定义**

```lean
Fin 9
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-8ab4657853f928aa"></a>
## `CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalPhysicalSemantics.lean#L29)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg ⊕
  CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`Sum`

<a id="def-88033a59012feb72"></a>
## `CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalPhysicalSemantics.lean#L49)

**类型**

```lean
CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg ↪
  CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg
```

**定义**

```lean
{ toFun := fun t => ⟨472 + ↑t, ⋯⟩, inj' := CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper._proof_4 }
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper._proof_3](LocalPhysicalSemantics.definitions.md#def-db68005bd180229a)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)
- [CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper._proof_4](LocalPhysicalSemantics.definitions.md#def-16040d6a6a8269c9)

**基础库名称**

`Function.Embedding.mk`, `Fin.mk`, `instOfNatNat`, `Fin.val`, `Function.Embedding`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-f0a6e00641a5b0fc"></a>
## `CodedSorting.Construction.LocalPhysicalSemantics.allTemporaries`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalPhysicalSemantics.lean#L63)

**类型**

```lean
List CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg
```

**定义**

```lean
List.finRange 9
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `List.finRange`

<a id="def-83343efdd06b3465"></a>
## `CodedSorting.Construction.LocalPhysicalSemantics.localPhysicalProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalPhysicalSemantics.lean#L68)

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
  CodedSorting.Construction.ScatterCopies.expandedProgram
    CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper
    CodedSorting.Construction.LocalPhysicalSemantics.allTemporaries before after rows
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg](LocalPhysicalSemantics.definitions.md#def-8ab4657853f928aa)
- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.ScatterCopies.expandedProgram](../Composition/ScatterCopies.definitions.md#def-6b5504d1a6afa918)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](../Composition/ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.LocalPhysicalSemantics.allTemporaries](LocalPhysicalSemantics.definitions.md#def-f0a6e00641a5b0fc)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)
- [CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper](LocalPhysicalSemantics.definitions.md#def-88033a59012feb72)

**基础库名称**

`instDecidableEqFin`, `Sum.instDecidableEq`, `instOfNatNat`, `Fin.fintype`, `List`, `Nat`, `OfNat.ofNat`

<a id="def-db68005bd180229a"></a>
## `CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LocalPhysicalSemantics.lean)

**类型**

```lean
∀ (t : CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg),
  472 + ↑t < CodedSorting.Construction.FiniteCertificate.registerCount
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-16040d6a6a8269c9"></a>
## `CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LocalPhysicalSemantics.lean)

**类型**

```lean
∀ ⦃a b : CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg⦄, ⟨472 + ↑a, ⋯⟩ = ⟨472 + ↑b, ⋯⟩ → a = b
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.FiniteCertificate.registerCount](FiniteTypes.definitions.md#def-6410b1b9a0cf1a12)
- [CodedSorting.Construction.LocalPhysicalSemantics.retainedHelper._proof_3](LocalPhysicalSemantics.definitions.md#def-db68005bd180229a)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`
