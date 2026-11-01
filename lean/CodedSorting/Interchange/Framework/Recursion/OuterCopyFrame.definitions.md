# OuterCopyFrame 的定义

[源码](OuterCopyFrame.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-654a82544fb518ba"></a>
## `CodedSorting.CommonRecursiveExchange.copyCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](OuterCopyFrame.lean#L150)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader V source target =>
  CodedSorting.CommonPermutationScan.program q reader (Equiv.refl (Fin V)) (fun x => 0) source target
```

**继续展开**

- [CodedSorting.CommonPermutationScan.program](../Memory/Reflection.definitions.md#def-40c5a71a42c86359)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecursiveExchange.copyCode._proof_1](OuterCopyFrame.definitions.md#def-f2400fc2343a8478)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `Equiv.refl`

<a id="def-f2400fc2343a8478"></a>
## `CodedSorting.CommonRecursiveExchange.copyCode._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](OuterCopyFrame.lean)

**类型**

```lean
NeZero (0 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`
