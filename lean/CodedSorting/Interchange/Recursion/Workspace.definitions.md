# Workspace 的定义

[源码](Workspace.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-167360864504c5b9"></a>
## `CodedSorting.Construction.RecursiveWorkspaceBudget.buckets`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Workspace.lean#L104)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun base => (CodedSorting.Construction.ExchangeSpecialization.radix ^ base) ^ 2
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-ccdb4faa2250afa6"></a>
## `CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Workspace.lean#L109)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → Prop
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters.mk](Workspace.definitions.md#def-83977d55880218b0)

**基础库名称**

`Nat`

<a id="def-83977d55880218b0"></a>
## `CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Workspace.lean#L110)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff base : ℕ},
  cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
        CodedSorting.CommonExchangeLeaf.bankWords q →
      CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * CodedSorting.CommonPermutationPairs.width q ≤
          cutoff + CodedSorting.CommonPermutationPairs.width q →
        CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters q cutoff base
```

**继续展开**

- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters](Workspace.definitions.md#def-ccdb4faa2250afa6)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-a58d60b2c1651e18"></a>
## `CodedSorting.Construction.RecursiveParameters.ratio`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Workspace.lean#L514)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.CommonExchangeLeaf.bankWords q / q.block
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `Nat`, `Nat.instDiv`

<a id="def-a2c8269bde8615b2"></a>
## `CodedSorting.Construction.RecursiveParameters.cutoff`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Workspace.lean#L516)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.CommonExchangeLeaf.bankBits q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`Nat`

<a id="def-99c1453727e16831"></a>
## `CodedSorting.Construction.RecursiveParameters.chosenBase`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Workspace.lean#L518)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q =>
  CodedSorting.PhysicalLeafParameters.baseWidth CodedSorting.Construction.ambientDimension
    CodedSorting.Construction.ExchangeSpecialization.radix (CodedSorting.Construction.RecursiveParameters.ratio q)
```

**继续展开**

- [CodedSorting.Construction.RecursiveParameters.ratio](Workspace.definitions.md#def-a58d60b2c1651e18)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.PhysicalLeafParameters.baseWidth](../../Shared/Memory/EdgeReadBit.definitions.md#def-2fe8d8e0ff0a0b3b)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`Nat`

<a id="def-28a0e406b8961cb8"></a>
## `CodedSorting.Construction.RecursiveParameters.Normalized`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Workspace.lean#L521)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Prop
```

**定义**

```lean
fun q =>
  CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount ≤
    CodedSorting.Construction.RecursiveParameters.ratio q
```

**继续展开**

- [CodedSorting.PhysicalLeafParameters.minimumRatio](../../Shared/Memory/EdgeReadBit.definitions.md#def-5b3ccb2ea10f8cb1)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.RecursiveParameters.ratio](Workspace.definitions.md#def-a58d60b2c1651e18)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-54a649e90622840f"></a>
## `CodedSorting.Construction.RecursiveParameters.chosenBase_pos`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Workspace.lean#L537)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Construction.RecursiveParameters.Normalized q →
    0 < CodedSorting.Construction.RecursiveParameters.chosenBase q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.RecursiveParameters.chosenBase](Workspace.definitions.md#def-99c1453727e16831)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-a0428caeb13dd230"></a>
## `CodedSorting.Construction.RecursiveParameters.chosenBase_fit`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Workspace.lean#L555)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Construction.RecursiveParameters.Normalized q →
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets
          (CodedSorting.Construction.RecursiveParameters.chosenBase q) *
        q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q
```

**继续展开**

- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.RecursiveParameters.chosenBase](Workspace.definitions.md#def-99c1453727e16831)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Nat`, `instHMul`

<a id="def-03f8fdc6d5092bf3"></a>
## `CodedSorting.Construction.RecursiveParameters.chosenBase_startup`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Workspace.lean#L566)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Construction.RecursiveParameters.Normalized q →
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets
          (CodedSorting.Construction.RecursiveParameters.chosenBase q) *
        CodedSorting.CommonPermutationPairs.width q ≤
      CodedSorting.Construction.RecursiveParameters.cutoff q + CodedSorting.CommonPermutationPairs.width q
```

**继续展开**

- [CodedSorting.Construction.RecursiveParameters.cutoff](Workspace.definitions.md#def-a2c8269bde8615b2)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.RecursiveParameters.chosenBase](Workspace.definitions.md#def-99c1453727e16831)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-26fe83f7876f95ec"></a>
## `CodedSorting.Construction.RecursiveParameters.normalized_of_inventory`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Workspace.lean#L587)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
        CodedSorting.Construction.streamCount ≤
      q.inventory.ratio →
    CodedSorting.Construction.RecursiveParameters.Normalized q
```

**继续展开**

- [CodedSorting.PhysicalLeafParameters.minimumRatio](../../Shared/Memory/EdgeReadBit.definitions.md#def-5b3ccb2ea10f8cb1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.ratio](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-197343a4949f7653)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`
