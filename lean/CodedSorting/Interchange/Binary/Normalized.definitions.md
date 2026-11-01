# Normalized 的定义

[源码](Normalized.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-93d11072655d9856"></a>
## `CodedSorting.Construction.BinaryNormalized.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalized.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → (G S : ℕ) → 0 < G → 0 < S → CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ
```

**定义**

```lean
fun q P u G S hG hS hnormal =>
  CodedSorting.Construction.BinaryMachine.space q (CodedSorting.Construction.RecursiveParameters.chosenBase q)
    (CodedSorting.Construction.RecursiveParameters.cutoff q) P u G S ⋯ hG hS ⋯ ⋯ ⋯ ⋯
```

**继续展开**

- [CodedSorting.Construction.RecursiveParameters.cutoff](../Recursion/Workspace.definitions.md#def-a2c8269bde8615b2)
- [CodedSorting.Construction.BinaryMachine.space](Machine.definitions.md#def-71c20450b6ab5991)
- [CodedSorting.Construction.RecursiveParameters.chosenBase_fit](../Recursion/Workspace.definitions.md#def-a0428caeb13dd230)
- [CodedSorting.Construction.BinaryNormalized.space._proof_1](Normalized.definitions.md#def-74e172c571df4abb)
- [CodedSorting.Construction.BinaryNormalized.space._proof_2](Normalized.definitions.md#def-d3132be6e1f66696)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.RecursiveParameters.chosenBase_pos](../Recursion/Workspace.definitions.md#def-54a649e90622840f)
- [CodedSorting.Construction.RecursiveParameters.chosenBase](../Recursion/Workspace.definitions.md#def-99c1453727e16831)
- [CodedSorting.Construction.RecursiveParameters.chosenBase_startup](../Recursion/Workspace.definitions.md#def-03f8fdc6d5092bf3)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-5e24c8408dd8706c"></a>
## `CodedSorting.Construction.BinaryNormalized.normalizedProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalized.lean#L29)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (P u G S source buffer limit : ℕ) →
      (hG : 0 < G) →
        (hS : 0 < S) →
          (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
            source +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.CommonChunkLayout.Volume P (2 ^ u) G (S * q.w)) ≤
                buffer →
              buffer + CodedSorting.Construction.BinaryNormalized.space q P u G S hG hS hnormal ≤ limit →
                limit ≤ q.N ^ q.exponent →
                  CodedSorting.CommonFinitePermutation.Program q
                    (CodedSorting.CommonChunkLayout.Volume P (2 ^ u) G (S * q.w)) source buffer limit
                    (CodedSorting.CommonChunkLayout.swap P (2 ^ u) G (S * q.w))
```

**定义**

```lean
fun q reader P u G S source buffer limit hG hS hnormal hs hw hl =>
  CodedSorting.Construction.BinaryMachine.program q reader (CodedSorting.Construction.RecursiveParameters.chosenBase q)
    (CodedSorting.Construction.RecursiveParameters.cutoff q) P u G S source buffer limit ⋯ hG hS ⋯ ⋯ ⋯ ⋯ hs hw hl
```

**继续展开**

- [CodedSorting.Construction.RecursiveParameters.cutoff](../Recursion/Workspace.definitions.md#def-a2c8269bde8615b2)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.BinaryMachine.program](Machine.definitions.md#def-545d61c28b3a3406)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.RecursiveParameters.chosenBase_fit](../Recursion/Workspace.definitions.md#def-a0428caeb13dd230)
- [CodedSorting.Construction.BinaryNormalized.space._proof_1](Normalized.definitions.md#def-74e172c571df4abb)
- [CodedSorting.Construction.BinaryNormalized.space._proof_2](Normalized.definitions.md#def-d3132be6e1f66696)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.BinaryNormalized.space](Normalized.definitions.md#def-93d11072655d9856)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.RecursiveParameters.chosenBase_pos](../Recursion/Workspace.definitions.md#def-54a649e90622840f)
- [CodedSorting.Construction.RecursiveParameters.chosenBase](../Recursion/Workspace.definitions.md#def-99c1453727e16831)
- [CodedSorting.Construction.RecursiveParameters.chosenBase_startup](../Recursion/Workspace.definitions.md#def-03f8fdc6d5092bf3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-74e172c571df4abb"></a>
## `CodedSorting.Construction.BinaryNormalized.space._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Normalized.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Construction.RecursiveParameters.cutoff q ≤ CodedSorting.Construction.RecursiveParameters.cutoff q
```

**继续展开**

- [CodedSorting.Construction.RecursiveParameters.cutoff](../Recursion/Workspace.definitions.md#def-a2c8269bde8615b2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Preorder.toLE`, `LE.le`, `Nat.instPreorder`, `Nat`

<a id="def-d3132be6e1f66696"></a>
## `CodedSorting.Construction.BinaryNormalized.space._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Normalized.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Construction.RecursiveParameters.Normalized q →
    CodedSorting.CommonPermutationPairs.width q ≤ CodedSorting.Construction.RecursiveParameters.cutoff q
```

**继续展开**

- [CodedSorting.Construction.RecursiveParameters.cutoff](../Recursion/Workspace.definitions.md#def-a2c8269bde8615b2)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`LE.le`, `instLENat`, `Nat`
