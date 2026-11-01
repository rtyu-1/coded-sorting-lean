# FiniteSemantics 的定义

[源码](FiniteSemantics.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-bde62b0f7325694d"></a>
## `CodedSorting.Construction.SymbolicXor.sourceRegisters`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteSemantics.lean#L136)

**类型**

```lean
(n : ℕ) → CodedSorting.Construction.FiniteCertificate.Gate → Finset (Fin n)
```

**定义**

```lean
fun n g => {r | ↑r ∈ g.sources}
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.sources](FiniteTypes.definitions.md#def-516947edde89b6d1)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`Finset.univ`, `Finset`, `Membership.mem`, `instBEqOfDecidableEq`, `Fin.val`, `Fin.fintype`, `List`, `List.instMembership`, `Nat`, `instDecidableEqNat`, `Nat.instLawfulBEq`, `List.instDecidableMemOfLawfulBEq`, `Fin`, `Finset.filter`

<a id="def-d677975eff07740c"></a>
## `CodedSorting.Construction.SymbolicXor.compileGate`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteSemantics.lean#L139)

**类型**

```lean
(n : ℕ) → CodedSorting.Construction.FiniteCertificate.Gate → CodedSorting.CircuitProgram.XorGate (Fin n)
```

**定义**

```lean
fun n g =>
  { ports := {r | ↑r = g.destination ∨ ↑r ∈ g.sources}, targets := {r | ↑r = g.destination},
    controls := fun x => CodedSorting.Construction.SymbolicXor.sourceRegisters n g, targets_subset := ⋯,
    controls_subset := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.SymbolicXor.compileGate._proof_4](FiniteSemantics.definitions.md#def-331f8721ec1b31b5)
- [CodedSorting.Construction.FiniteCertificate.Gate.destination](FiniteTypes.definitions.md#def-b03234f707cb6726)
- [CodedSorting.CircuitProgram.XorGate.mk](../Framework/CircuitProgram.definitions.md#def-a958dc84c6bc445e)
- [CodedSorting.Construction.FiniteCertificate.Gate.sources](FiniteTypes.definitions.md#def-516947edde89b6d1)
- [CodedSorting.Construction.SymbolicXor.sourceRegisters](FiniteSemantics.definitions.md#def-bde62b0f7325694d)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.SymbolicXor.compileGate._proof_3](FiniteSemantics.definitions.md#def-f0b34843dda7c290)

**基础库名称**

`Finset.univ`, `instDecidableEqFin`, `Membership.mem`, `instBEqOfDecidableEq`, `Fin.val`, `Fin.fintype`, `List`, `List.instMembership`, `Nat`, `instDecidableEqNat`, `Or`, `Nat.instLawfulBEq`, `List.instDecidableMemOfLawfulBEq`, `Fin`, `Finset.filter`, `Eq`, `instDecidableOr`

<a id="def-f0b34843dda7c290"></a>
## `CodedSorting.Construction.SymbolicXor.compileGate._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](FiniteSemantics.lean)

**类型**

```lean
∀ (n : ℕ) (g : CodedSorting.Construction.FiniteCertificate.Gate) ⦃r : Fin n⦄,
  r ∈ {r | ↑r = g.destination} → r ∈ {r | ↑r = g.destination ∨ ↑r ∈ g.sources}
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.destination](FiniteTypes.definitions.md#def-b03234f707cb6726)
- [CodedSorting.Construction.FiniteCertificate.Gate.sources](FiniteTypes.definitions.md#def-516947edde89b6d1)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`Finset.univ`, `Finset`, `Membership.mem`, `Finset.instMembership`, `instBEqOfDecidableEq`, `Fin.val`, `Fin.fintype`, `List`, `List.instMembership`, `Nat`, `instDecidableEqNat`, `Or`, `Nat.instLawfulBEq`, `List.instDecidableMemOfLawfulBEq`, `Fin`, `Finset.filter`, `Eq`, `instDecidableOr`

<a id="def-331f8721ec1b31b5"></a>
## `CodedSorting.Construction.SymbolicXor.compileGate._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](FiniteSemantics.lean)

**类型**

```lean
∀ (n : ℕ) (g : CodedSorting.Construction.FiniteCertificate.Gate),
  ∀ r ∈ {r | ↑r = g.destination},
    ∀ ⦃c : Fin n⦄,
      c ∈ CodedSorting.Construction.SymbolicXor.sourceRegisters n g → c ∈ {r | ↑r = g.destination ∨ ↑r ∈ g.sources}
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.destination](FiniteTypes.definitions.md#def-b03234f707cb6726)
- [CodedSorting.Construction.FiniteCertificate.Gate.sources](FiniteTypes.definitions.md#def-516947edde89b6d1)
- [CodedSorting.Construction.SymbolicXor.sourceRegisters](FiniteSemantics.definitions.md#def-bde62b0f7325694d)
- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`Finset.univ`, `Finset`, `Membership.mem`, `Finset.instMembership`, `instBEqOfDecidableEq`, `Fin.val`, `Fin.fintype`, `List`, `List.instMembership`, `Nat`, `instDecidableEqNat`, `Or`, `Nat.instLawfulBEq`, `List.instDecidableMemOfLawfulBEq`, `Fin`, `Finset.filter`, `Eq`, `instDecidableOr`
