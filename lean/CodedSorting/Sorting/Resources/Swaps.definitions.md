# Swaps 的定义

[源码](Swaps.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e33de77481a74b63"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L23)

**类型**

```lean
(s w : ℕ) → Equiv.Perm (CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w) → Equiv.Perm (Fin (s ^ 4 * w))
```

**定义**

```lean
fun s w e =>
  (CodedSorting.PhysicalSortingExchangeLayout.recordLayout s w).symm.trans
    ((Equiv.symm e).trans (CodedSorting.PhysicalSortingExchangeLayout.recordLayout s w))
```

**继续展开**

- [CodedSorting.PhysicalSortingExchangeLayout.recordLayout](../Bounds/PhysicalSortingExchange.definitions.md#def-7783105b9f1f848c)
- [CodedSorting.PhysicalSortingExchangeLayout.RecordAddress](../Bounds/PhysicalSortingExchange.definitions.md#def-5b3c18cc48f5db74)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-1f600f177b291891"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.suffix_pos`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean#L43)

**类型**

```lean
∀ (t r : ℕ),
  0 < r → ∀ (j : CodedSorting.PhysicalSortingExchange.Swap), 0 < CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-2e0efe3574c60ce8"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L64)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ →
    (r : ℕ) →
      0 < r → CodedSorting.Construction.RecursiveParameters.Normalized q → CodedSorting.PhysicalSortingExchange.Swap → ℕ
```

**定义**

```lean
fun q t r hr hnormal j =>
  CodedSorting.Construction.BinaryNormalized.space q (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
    (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) ⋯ ⋯ hnormal
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace._proof_2](Swaps.definitions.md#def-fb4076306aa38a88)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.BinaryNormalized.space](../../Interchange/Binary/Normalized.definitions.md#def-93d11072655d9856)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.suffix_pos](Swaps.definitions.md#def-1f600f177b291891)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-ff3643bfef900f6d"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageCost`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L69)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → CodedSorting.PhysicalSortingExchange.Swap → ℕ
```

**定义**

```lean
fun q t r j =>
  CodedSorting.Construction.BinaryMachine.bound q (CodedSorting.Construction.RecursiveParameters.chosenBase q)
    (CodedSorting.Construction.RecursiveParameters.cutoff q) (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j)
    t 1 (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j)
```

**继续展开**

- [CodedSorting.Construction.RecursiveParameters.cutoff](../../Interchange/Recursion/Workspace.definitions.md#def-a2c8269bde8615b2)
- [CodedSorting.Construction.BinaryMachine.bound](../../Interchange/Binary/Machine.definitions.md#def-5e8573e662b67b1b)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.Construction.RecursiveParameters.chosenBase](../../Interchange/Recursion/Workspace.definitions.md#def-99c1453727e16831)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-2bccee7b1067b7a4"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L73)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (t r source buffer limit : ℕ) →
      (hr : 0 < r) →
        (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
          (j : CodedSorting.PhysicalSortingExchange.Swap) →
            source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer →
              buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal j ≤ limit →
                limit ≤ q.N ^ q.exponent →
                  CodedSorting.CommonFinitePermutation.Program q ((2 ^ t) ^ 4 * (r * q.w)) source buffer limit
                    (CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
                      (CodedSorting.PhysicalSortingExchange.move (2 ^ t) (r * q.w) j))
```

**定义**

```lean
fun q reader t r source buffer limit hr hnormal j hs hw hl =>
  let p :=
    CodedSorting.Construction.BinaryNormalized.normalizedProgram q reader
      (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
      (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) source buffer limit ⋯ ⋯ hnormal ⋯ hw hl;
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_10](Swaps.definitions.md#def-a7cbfbad6d5ad614)
- [CodedSorting.CommonChunkLayout.swap](../../Interchange/Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.PhysicalSortingExchange.move](../Bounds/PhysicalSortingExchange.definitions.md#def-506e1e347102234e)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_8](Swaps.definitions.md#def-0be34cbac6302838)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../../Interchange/Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.BinaryNormalized.normalizedProgram](../../Interchange/Binary/Normalized.definitions.md#def-5e24c8408dd8706c)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_9](Swaps.definitions.md#def-c3b676d28c26d1ac)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_5](Swaps.definitions.md#def-3f77b5a06745bf18)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_4](Swaps.definitions.md#def-42fd8966c0008ab8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_7](Swaps.definitions.md#def-75ad281cbffc6366)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace](Swaps.definitions.md#def-2e0efe3574c60ce8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.suffix_pos](Swaps.definitions.md#def-1f600f177b291891)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_6](Swaps.definitions.md#def-7b1bddefb8d01db6)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.mk](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-1fc95a6a93b22a39"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L118)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → (r : ℕ) → 0 < r → CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ
```

**定义**

```lean
fun q t r hr hnormal =>
  max
    (CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal
      CodedSorting.PhysicalSortingExchange.Swap.last)
    (max
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal
        CodedSorting.PhysicalSortingExchange.Swap.middle)
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal
        CodedSorting.PhysicalSortingExchange.Swap.first))
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap.first](../Bounds/PhysicalSortingExchange.definitions.md#def-6b3f2a8759a1c396)
- [CodedSorting.PhysicalSortingExchange.Swap.middle](../Bounds/PhysicalSortingExchange.definitions.md#def-a171b37e47af8ac3)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace](Swaps.definitions.md#def-2e0efe3574c60ce8)
- [CodedSorting.PhysicalSortingExchange.Swap.last](../Bounds/PhysicalSortingExchange.definitions.md#def-63a8e508e0d11430)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `Max.max`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-0d77f1963d4cbd11"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L130)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q t r =>
  max
    (CodedSorting.Construction.Sorting.CommonSortingSwaps.stageCost q t r
      CodedSorting.PhysicalSortingExchange.Swap.last)
    (max
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.stageCost q t r
        CodedSorting.PhysicalSortingExchange.Swap.middle)
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.stageCost q t r
        CodedSorting.PhysicalSortingExchange.Swap.first))
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap.first](../Bounds/PhysicalSortingExchange.definitions.md#def-6b3f2a8759a1c396)
- [CodedSorting.PhysicalSortingExchange.Swap.middle](../Bounds/PhysicalSortingExchange.definitions.md#def-a171b37e47af8ac3)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageCost](Swaps.definitions.md#def-ff3643bfef900f6d)
- [CodedSorting.PhysicalSortingExchange.Swap.last](../Bounds/PhysicalSortingExchange.definitions.md#def-63a8e508e0d11430)

**基础库名称**

`Nat.instMax_mathlib`, `Max.max`, `Nat`

<a id="def-923665fdead91628"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L146)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (t r source buffer limit : ℕ) →
      (hr : 0 < r) →
        (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
          source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer →
            buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t r hr hnormal ≤ limit →
              limit ≤ q.N ^ q.exponent →
                (js : List CodedSorting.PhysicalSortingExchange.Swap) →
                  CodedSorting.CommonFinitePermutation.Program q ((2 ^ t) ^ 4 * (r * q.w)) source buffer limit
                    (CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
                      (CodedSorting.PhysicalSortingExchange.permute (2 ^ t) (r * q.w) js))
```

**定义**

```lean
fun q reader t r source buffer limit hr hnormal hs hw hl x =>
  List.brecOn x fun x f =>
    (match (motive :=
        (x : List CodedSorting.PhysicalSortingExchange.Swap) →
          List.below x →
            CodedSorting.CommonFinitePermutation.Program q ((2 ^ t) ^ 4 * (r * q.w)) source buffer limit
              (CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
                (CodedSorting.PhysicalSortingExchange.permute (2 ^ t) (r * q.w) x)))
        x with
      | [] => fun x =>
        (CodedSorting.CommonFinitePermutation.Program.identity q ((2 ^ t) ^ 4 * (r * q.w)) source buffer
              limit).changePermutation
          ⋯
      | j :: js => fun x =>
        ((CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram q reader t r source buffer limit hr hnormal
                  j hs ⋯ hl).append
              x.1).changePermutation
          ⋯)
      f
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram._proof_13](Swaps.definitions.md#def-02b750043111243a)
- [CodedSorting.CommonFinitePermutation.Program.changePermutation](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-abb56e7c683c1f81)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram](Swaps.definitions.md#def-2bccee7b1067b7a4)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram._proof_11](Swaps.definitions.md#def-43d040720b14b51e)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram._proof_12](Swaps.definitions.md#def-ede730d56b300fa3)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.PhysicalSortingExchange.move](../Bounds/PhysicalSortingExchange.definitions.md#def-506e1e347102234e)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.PhysicalSortingExchange.permute](../Bounds/PhysicalSortingExchange.definitions.md#def-5f47d2c3d2727164)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.append](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-91ea532bb04faf9e)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram.match_1](Swaps.definitions.md#def-15c19cd116076612)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonFinitePermutation.Program.identity](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-3c75e77e76e9a63a)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`List.brecOn`, `HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `instHAdd`, `Unit`, `PProd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `List.below`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `instHMul`, `List.nil`

<a id="def-f963af66802c178a"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L178)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (t r source buffer limit : ℕ) →
      (hr : 0 < r) →
        (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
          source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer →
            buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t r hr hnormal ≤ limit →
              limit ≤ q.N ^ q.exponent →
                CodedSorting.CommonFinitePermutation.Program q ((2 ^ t) ^ 4 * (r * q.w)) source buffer limit
                  (CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
                    (CodedSorting.ColumnsortExchange.forwardRecord (2 ^ t) (Fin (r * q.w))))
```

**定义**

```lean
fun q reader t r source buffer limit hr hnormal hs hw hl =>
  (CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram q reader t r source buffer limit hr hnormal hs
        hw hl CodedSorting.PhysicalSortingExchange.forwardSwaps).changePermutation
    ⋯
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.changePermutation](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-abb56e7c683c1f81)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram](Swaps.definitions.md#def-923665fdead91628)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram._proof_14](Swaps.definitions.md#def-2ef7aeaa884a7871)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.PhysicalSortingExchange.permute](../Bounds/PhysicalSortingExchange.definitions.md#def-5f47d2c3d2727164)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.PhysicalSortingExchange.forwardSwaps](../Bounds/PhysicalSortingExchange.definitions.md#def-ca7c18c6bcc67751)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-80dda9a11963a867"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L187)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (t r source buffer limit : ℕ) →
      (hr : 0 < r) →
        (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
          source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer →
            buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t r hr hnormal ≤ limit →
              limit ≤ q.N ^ q.exponent →
                CodedSorting.CommonFinitePermutation.Program q ((2 ^ t) ^ 4 * (r * q.w)) source buffer limit
                  (CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
                    (CodedSorting.ColumnsortExchange.forwardRecord (2 ^ t) (Fin (r * q.w))).symm)
```

**定义**

```lean
fun q reader t r source buffer limit hr hnormal hs hw hl =>
  (CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram q reader t r source buffer limit hr hnormal hs
        hw hl CodedSorting.PhysicalSortingExchange.backwardSwaps).changePermutation
    ⋯
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.changePermutation](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-abb56e7c683c1f81)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram._proof_15](Swaps.definitions.md#def-ff303448da7d46d8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram](Swaps.definitions.md#def-923665fdead91628)
- [CodedSorting.PhysicalSortingExchange.backwardSwaps](../Bounds/PhysicalSortingExchange.definitions.md#def-e8260471144a5190)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.PhysicalSortingExchange.permute](../Bounds/PhysicalSortingExchange.definitions.md#def-5f47d2c3d2727164)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-1881dd130b457bbf"></a>
## `CodedSorting.Construction.Sorting.CommonSortingExchangeRate.machineConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L285)

**类型**

```lean
ℝ
```

**定义**

```lean
CodedSorting.Construction.BinaryCost.binaryConstant 24 27
  (6 * (2 * CodedSorting.Construction.ExchangeSpecialization.radix + 6))
```

**继续展开**

- [CodedSorting.Construction.BinaryCost.binaryConstant](../../Interchange/Binary/Machine.definitions.md#def-020c37b6c349c263)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Real`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-df165fe088b61cab"></a>
## `CodedSorting.Construction.Sorting.CommonSortingExchangeRate.rateConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L290)

**类型**

```lean
ℕ → ℝ
```

**定义**

```lean
fun r =>
  CodedSorting.Construction.Sorting.CommonSortingExchangeRate.machineConstant * ↑r *
    (1 + CodedSorting.Construction.ArbitraryLogRate.baseLogConstant ^ (1 - ↑CodedSorting.Construction.epsilon))
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingExchangeRate.machineConstant](Swaps.definitions.md#def-1881dd130b457bbf)
- [CodedSorting.Construction.ArbitraryLogRate.baseLogConstant](../../Interchange/Fields/LogRate.definitions.md#def-585857d4b90c0ed0)
- [CodedSorting.Construction.epsilon](../../Circuit/Parameters/Exponent.definitions.md#def-38e0b13c0209d8a9)

**基础库名称**

`Real.instPow`, `Real`, `HMul.hMul`, `Real.instSub`, `Real.instRatCast`, `HSub.hSub`, `Rat.cast`, `Nat.cast`, `Real.instAdd`, `Real.instOne`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `One.toOfNat1`, `instHPow`, `OfNat.ofNat`, `instHMul`, `Real.instNatCast`

<a id="def-fa7ade4a62ba0c11"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L414)

**类型**

```lean
(s : ℕ) → {α : Type u_1} → (Fin (s ^ 4) → α) → Fin (s ^ 4) → α
```

**定义**

```lean
fun s {α} f i => f ((CodedSorting.ColumnsortExchange.transpose s).symm i)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.transpose](../Local/Columnsort/ColumnsortExchange.definitions.md#def-f00041a50c5b2acc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-4b669c1ec0718612"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L418)

**类型**

```lean
(s : ℕ) → {α : Type u_1} → (Fin (s ^ 4) → α) → Fin (s ^ 4) → α
```

**定义**

```lean
fun s {α} f i => f ((CodedSorting.ColumnsortExchange.transpose s) i)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.transpose](../Local/Columnsort/ColumnsortExchange.definitions.md#def-f00041a50c5b2acc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-284c801521045b10"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L421)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (t source buffer limit : ℕ) →
      (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
        source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer →
          buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit →
            limit ≤ q.N ^ q.exponent →
              CodedSorting.CommonRecordProgram.Program q ((2 ^ t) ^ 4) source buffer limit
                (CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forward (2 ^ t))
```

**定义**

```lean
fun q reader t source buffer limit hnormal hs hw hl =>
  let p :=
    CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit ⋯ hnormal hs hw
      hl;
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordProgram.Program.mk](../../Shared/Records/RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forward](Swaps.definitions.md#def-fa7ade4a62ba0c11)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_22](Swaps.definitions.md#def-c37a1b1161cbee59)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_23](Swaps.definitions.md#def-bf6849d7a6bca3d2)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_24](Swaps.definitions.md#def-6fd97a669873232e)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_21](Swaps.definitions.md#def-de9ba0353f8b0186)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_16](Swaps.definitions.md#def-1d72ac4b290a7a8d)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_20](Swaps.definitions.md#def-63964a253a8b2a4d)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram](Swaps.definitions.md#def-f963af66802c178a)
- [CodedSorting.CommonRecordProgram.Program](../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Decidable.byContradiction`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-95464506dbf054b2"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L435)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (t source buffer limit : ℕ) →
      (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
        source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer →
          buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit →
            limit ≤ q.N ^ q.exponent →
              CodedSorting.CommonRecordProgram.Program q ((2 ^ t) ^ 4) source buffer limit
                (CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backward (2 ^ t))
```

**定义**

```lean
fun q reader t source buffer limit hnormal hs hw hl =>
  let p :=
    CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit ⋯ hnormal hs
      hw hl;
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_27](Swaps.definitions.md#def-16938c0f7e192332)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordProgram.Program.mk](../../Shared/Records/RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_26](Swaps.definitions.md#def-162dddb51e2709fb)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram](Swaps.definitions.md#def-80dda9a11963a867)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_16](Swaps.definitions.md#def-1d72ac4b290a7a8d)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backward](Swaps.definitions.md#def-4b669c1ec0718612)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_28](Swaps.definitions.md#def-8065628627025846)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_29](Swaps.definitions.md#def-ff432ed97fadf0f0)
- [CodedSorting.CommonRecordProgram.Program](../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_25](Swaps.definitions.md#def-476ec1c73989b59e)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Decidable.byContradiction`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-daca8efda4d14df3"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.rowsVolume`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean#L493)

**类型**

```lean
∀ (s : ℕ), s * CodedSorting.PhysicalLocalSortNode.rows s = s * (s * (s ^ 2 * 1))
```

**继续展开**

- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-30a2bb86019ae6e0"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardAtRows`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L496)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (s : ℕ) →
    CodedSorting.CommonRecordProgram.Records q (s * CodedSorting.PhysicalLocalSortNode.rows s) →
      CodedSorting.CommonRecordProgram.Records q (s * CodedSorting.PhysicalLocalSortNode.rows s)
```

**定义**

```lean
fun q s f => CodedSorting.CommonRecordReindex.castRecords ⋯ (CodedSorting.CommonLocalSemantic.forward s f)
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.forward](../Local/Framework/Semantic.definitions.md#def-73fbf5cf9a4e2cae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordReindex.castRecords](../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardAtRows._proof_30](Swaps.definitions.md#def-623231adbac02659)
- [CodedSorting.CommonRecordProgram.Records](../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-9b9055335e3f3253"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardAtRows`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L500)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (s : ℕ) →
    CodedSorting.CommonRecordProgram.Records q (s * CodedSorting.PhysicalLocalSortNode.rows s) →
      CodedSorting.CommonRecordProgram.Records q (s * CodedSorting.PhysicalLocalSortNode.rows s)
```

**定义**

```lean
fun q s f => CodedSorting.CommonLocalSemantic.backward s (CodedSorting.CommonRecordReindex.castRecords ⋯ f)
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordBot](../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalSemantic.backward](../Local/Framework/Semantic.definitions.md#def-7cfe465cda0e4774)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.rowsVolume](Swaps.definitions.md#def-daca8efda4d14df3)
- [CodedSorting.CommonRecordReindex.castRecords](../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.KeyRecordBits.recordTop](../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-f6741e55f82db402"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L520)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (t source buffer limit : ℕ) →
      (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
        source +
              CodedSorting.CommonRecordProgram.recordBlocks q
                (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
            buffer →
          buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit →
            limit ≤ q.N ^ q.exponent →
              CodedSorting.CommonRecordProgram.Program q (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t))
                source buffer limit
                (CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardAtRows q (2 ^ t))
```

**定义**

```lean
fun q reader t source buffer limit hnormal hs hw hl =>
  (CodedSorting.CommonRecordReindex.castProgram
        (CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram q reader t source buffer limit
          hnormal ⋯ hw hl)
        ⋯).changeFunction
    ⋯
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_32](Swaps.definitions.md#def-c56c5a6d7759d9a0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordReindex.castProgram](../../Shared/Records/RecordOperations.definitions.md#def-2ef3a997d0144ffd)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_31](Swaps.definitions.md#def-1f7e1ea911065895)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forward](Swaps.definitions.md#def-fa7ade4a62ba0c11)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram](Swaps.definitions.md#def-284c801521045b10)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardAtRows](Swaps.definitions.md#def-30a2bb86019ae6e0)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_16](Swaps.definitions.md#def-1d72ac4b290a7a8d)
- [CodedSorting.CommonRecordReindex.castFunction](../../Shared/Records/RecordOperations.definitions.md#def-5d0de92d31fd312b)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_33](Swaps.definitions.md#def-cd72b36e6c179e41)
- [CodedSorting.CommonRecordProgram.Program](../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Decidable.byContradiction`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-50d584f0d5984b76"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Swaps.lean#L530)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (t source buffer limit : ℕ) →
      (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
        source +
              CodedSorting.CommonRecordProgram.recordBlocks q
                (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
            buffer →
          buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit →
            limit ≤ q.N ^ q.exponent →
              CodedSorting.CommonRecordProgram.Program q (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t))
                source buffer limit
                (CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardAtRows q (2 ^ t))
```

**定义**

```lean
fun q reader t source buffer limit hnormal hs hw hl =>
  (CodedSorting.CommonRecordReindex.castProgram
        (CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram q reader t source buffer limit
          hnormal ⋯ hw hl)
        ⋯).changeFunction
    ⋯
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_32](Swaps.definitions.md#def-c56c5a6d7759d9a0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordReindex.castProgram](../../Shared/Records/RecordOperations.definitions.md#def-2ef3a997d0144ffd)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_31](Swaps.definitions.md#def-1f7e1ea911065895)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardAtRows](Swaps.definitions.md#def-9b9055335e3f3253)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram](Swaps.definitions.md#def-95464506dbf054b2)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_16](Swaps.definitions.md#def-1d72ac4b290a7a8d)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backward](Swaps.definitions.md#def-4b669c1ec0718612)
- [CodedSorting.CommonRecordReindex.castFunction](../../Shared/Records/RecordOperations.definitions.md#def-5d0de92d31fd312b)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardProgram._proof_34](Swaps.definitions.md#def-d0b7bade6a9769a6)
- [CodedSorting.CommonRecordProgram.Program](../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Decidable.byContradiction`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-fe7c4f3f3377374f"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forward_charge_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean#L542)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs :
    source + CodedSorting.CommonRecordProgram.recordBlocks q (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
      buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  (CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram q reader t source buffer limit hnormal hs
        hw hl).charge ≤
    3 * CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q t 3
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost](Swaps.definitions.md#def-0d77f1963d4cbd11)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardAtRows](Swaps.definitions.md#def-30a2bb86019ae6e0)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram](Swaps.definitions.md#def-f6741e55f82db402)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_16](Swaps.definitions.md#def-1d72ac4b290a7a8d)
- [CodedSorting.CommonRecordProgram.Program.charge](../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Decidable.byContradiction`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-a912b0575f77e47a"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backward_charge_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean#L553)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs :
    source + CodedSorting.CommonRecordProgram.recordBlocks q (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
      buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  (CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardProgram q reader t source buffer limit hnormal
        hs hw hl).charge ≤
    3 * CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q t 3
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardAtRows](Swaps.definitions.md#def-9b9055335e3f3253)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost](Swaps.definitions.md#def-0d77f1963d4cbd11)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_16](Swaps.definitions.md#def-1d72ac4b290a7a8d)
- [CodedSorting.CommonRecordProgram.Program.charge](../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardProgram](Swaps.definitions.md#def-50d584f0d5984b76)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Decidable.byContradiction`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-476ec1c73989b59e"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_25`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q)
  (f : CodedSorting.CommonRecordProgram.Records q ((2 ^ t) ^ 4)),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    ∀ (y : Fin ((2 ^ t) ^ 4 * (3 * q.w))),
      CodedSorting.CommonPermutationPairs.readBit q
          (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit ⋯
                    hnormal hs hw hl).instructions
                s).1.disk
          source ↑y =
        CodedSorting.CommonRecordProgram.bits q
          (CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backward (2 ^ t) f) y
```

**继续展开**

- [CodedSorting.CommonRecordProgram.bits](../../Shared/Records/RecordOperations.definitions.md#def-82da314eef6ab4d1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](../../Shared/Records/RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram](Swaps.definitions.md#def-80dda9a11963a867)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonPermutationPairs.readBit](../../Interchange/Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backward](Swaps.definitions.md#def-4b669c1ec0718612)
- [CodedSorting.CommonRecordProgram.Records](../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-162dddb51e2709fb"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_26`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (3 * q.w)) ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit ⋯
                    hnormal hs hw hl).instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram](Swaps.definitions.md#def-80dda9a11963a867)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-16938c0f7e192332"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_27`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  ∀
    i ∈
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit ⋯ hnormal
          hs hw hl).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram](Swaps.definitions.md#def-80dda9a11963a867)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-8065628627025846"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_28`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  CodedSorting.CommonStaticSchedule.cost q
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit ⋯ hnormal
          hs hw hl).instructions ≤
    (CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit ⋯ hnormal hs
        hw hl).charge
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram](Swaps.definitions.md#def-80dda9a11963a867)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-ff432ed97fadf0f0"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backwardProgram._proof_29`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  (CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit ⋯ hnormal hs hw
          hl).instructions.length ≤
    (CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram q reader t 3 source buffer limit ⋯ hnormal hs
        hw hl).charge
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram](Swaps.definitions.md#def-80dda9a11963a867)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`

<a id="def-1d72ac4b290a7a8d"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_16`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ¬0 < 3 → False
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`False`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Not`

<a id="def-69ed1ee431f0e831"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → 0 < 3
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-1fdce6623325494b"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ℕ → ℕ → ℕ → ℕ → CodedSorting.Construction.RecursiveParameters.Normalized q → 0 < 3
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-63964a253a8b2a4d"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_20`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q)
  (f : CodedSorting.CommonRecordProgram.Records q ((2 ^ t) ^ 4)),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    ∀ (y : Fin ((2 ^ t) ^ 4 * (3 * q.w))),
      CodedSorting.CommonPermutationPairs.readBit q
          (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit ⋯
                    hnormal hs hw hl).instructions
                s).1.disk
          source ↑y =
        CodedSorting.CommonRecordProgram.bits q
          (CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forward (2 ^ t) f) y
```

**继续展开**

- [CodedSorting.CommonRecordProgram.bits](../../Shared/Records/RecordOperations.definitions.md#def-82da314eef6ab4d1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forward](Swaps.definitions.md#def-fa7ade4a62ba0c11)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](../../Shared/Records/RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonPermutationPairs.readBit](../../Interchange/Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram](Swaps.definitions.md#def-f963af66802c178a)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-de9ba0353f8b0186"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_21`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (3 * q.w)) ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit ⋯
                    hnormal hs hw hl).instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram](Swaps.definitions.md#def-f963af66802c178a)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-c37a1b1161cbee59"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_22`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  ∀
    i ∈
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit ⋯ hnormal hs
          hw hl).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram](Swaps.definitions.md#def-f963af66802c178a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-bf6849d7a6bca3d2"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_23`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  CodedSorting.CommonStaticSchedule.cost q
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit ⋯ hnormal hs
          hw hl).instructions ≤
    (CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit ⋯ hnormal hs
        hw hl).charge
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram](Swaps.definitions.md#def-f963af66802c178a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-6fd97a669873232e"></a>
## `CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_24`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t source buffer limit : ℕ) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 ⋯ hnormal ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  (CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit ⋯ hnormal hs hw
          hl).instructions.length ≤
    (CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram q reader t 3 source buffer limit ⋯ hnormal hs
        hw hl).charge
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_18](Swaps.definitions.md#def-69ed1ee431f0e831)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forwardProgram._proof_19](Swaps.definitions.md#def-1fdce6623325494b)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram](Swaps.definitions.md#def-f963af66802c178a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`

<a id="def-d0b7bade6a9769a6"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardProgram._proof_34`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t : ℕ),
  CodedSorting.CommonRecordReindex.castFunction q ⋯
      (CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backward (2 ^ t)) =
    CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardAtRows q (2 ^ t)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_31](Swaps.definitions.md#def-1f7e1ea911065895)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardAtRows](Swaps.definitions.md#def-9b9055335e3f3253)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.backward](Swaps.definitions.md#def-4b669c1ec0718612)
- [CodedSorting.CommonRecordProgram.Records](../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordReindex.castFunction](../../Shared/Records/RecordOperations.definitions.md#def-5d0de92d31fd312b)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-623231adbac02659"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardAtRows._proof_30`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (s : ℕ), s * (s * (s ^ 2 * 1)) = s * CodedSorting.PhysicalLocalSortNode.rows s
```

**继续展开**

- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-1f7e1ea911065895"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_31`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (t : ℕ), (2 ^ t) ^ 4 = 2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)
```

**继续展开**

- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-c56c5a6d7759d9a0"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_32`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t source buffer : ℕ),
  source + CodedSorting.CommonRecordProgram.recordBlocks q (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
      buffer →
    source + CodedSorting.CommonRecordProgram.recordBlocks q ((2 ^ t) ^ 4) ≤ buffer
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-cd72b36e6c179e41"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_33`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t : ℕ),
  CodedSorting.CommonRecordReindex.castFunction q ⋯
      (CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forward (2 ^ t)) =
    CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardAtRows q (2 ^ t)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram._proof_31](Swaps.definitions.md#def-1f7e1ea911065895)
- [CodedSorting.Construction.Sorting.CommonSortingRecordSwaps.forward](Swaps.definitions.md#def-fa7ade4a62ba0c11)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.PhysicalLocalSortNode.rows](../Local/Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardAtRows](Swaps.definitions.md#def-30a2bb86019ae6e0)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordReindex.castFunction](../../Shared/Records/RecordOperations.definitions.md#def-5d0de92d31fd312b)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-ff303448da7d46d8"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.backwardProgram._proof_15`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t r : ℕ),
  CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
      (CodedSorting.PhysicalSortingExchange.permute (2 ^ t) (r * q.w)
        CodedSorting.PhysicalSortingExchange.backwardSwaps) =
    CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
      (CodedSorting.ColumnsortExchange.forwardRecord (2 ^ t) (Fin (r * q.w))).symm
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.backwardSwaps](../Bounds/PhysicalSortingExchange.definitions.md#def-e8260471144a5190)
- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.PhysicalSortingExchange.permute](../Bounds/PhysicalSortingExchange.definitions.md#def-5f47d2c3d2727164)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-2ef7aeaa884a7871"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.forwardProgram._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t r : ℕ),
  CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
      (CodedSorting.PhysicalSortingExchange.permute (2 ^ t) (r * q.w)
        CodedSorting.PhysicalSortingExchange.forwardSwaps) =
    CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
      (CodedSorting.ColumnsortExchange.forwardRecord (2 ^ t) (Fin (r * q.w)))
```

**继续展开**

- [CodedSorting.ColumnsortExchange.forwardRecord](../Local/Columnsort/ColumnsortExchange.definitions.md#def-37af7200b313ff9a)
- [CodedSorting.PhysicalSortingExchange.permute](../Bounds/PhysicalSortingExchange.definitions.md#def-5f47d2c3d2727164)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.PhysicalSortingExchange.forwardSwaps](../Bounds/PhysicalSortingExchange.definitions.md#def-ca7c18c6bcc67751)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-43d040720b14b51e"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t r : ℕ),
  Equiv.refl (Fin ((2 ^ t) ^ 4 * (r * q.w))) =
    CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
      (CodedSorting.PhysicalSortingExchange.permute (2 ^ t) (r * q.w) [])
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.permute](../Bounds/PhysicalSortingExchange.definitions.md#def-5f47d2c3d2727164)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `Eq`, `instHMul`, `List.nil`

<a id="def-ede730d56b300fa3"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t r buffer limit : ℕ) (hr : 0 < r)
  (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q),
  buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t r hr hnormal ≤ limit →
    ∀ (j : CodedSorting.PhysicalSortingExchange.Swap),
      buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal j ≤ limit
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace](Swaps.definitions.md#def-2e0efe3574c60ce8)

**基础库名称**

`Preorder.toLE`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-02b750043111243a"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t r : ℕ) (j : CodedSorting.PhysicalSortingExchange.Swap)
  (js : List CodedSorting.PhysicalSortingExchange.Swap),
  Equiv.trans
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
        (CodedSorting.PhysicalSortingExchange.permute (2 ^ t) (r * q.w) js))
      (CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
        (CodedSorting.PhysicalSortingExchange.move (2 ^ t) (r * q.w) j)) =
    CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
      ((CodedSorting.PhysicalSortingExchange.move (2 ^ t) (r * q.w) j).trans
        (CodedSorting.PhysicalSortingExchange.permute (2 ^ t) (r * q.w) js))
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.move](../Bounds/PhysicalSortingExchange.definitions.md#def-506e1e347102234e)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.permute](../Bounds/PhysicalSortingExchange.definitions.md#def-5f47d2c3d2727164)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.PhysicalSortingExchangeLayout.RecordAddress](../Bounds/PhysicalSortingExchange.definitions.md#def-5b3c18cc48f5db74)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `List`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-15c19cd116076612"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.sequenceProgram.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Swaps.lean)

**类型**

```lean
(motive : List CodedSorting.PhysicalSortingExchange.Swap → Sort u_1) →
  (x : List CodedSorting.PhysicalSortingExchange.Swap) →
    (Unit → motive []) →
      ((j : CodedSorting.PhysicalSortingExchange.Swap) →
          (js : List CodedSorting.PhysicalSortingExchange.Swap) → motive (j :: js)) →
        motive x
```

**定义**

```lean
fun motive x h_1 h_2 => List.casesOn x (h_1 ()) fun head tail => h_2 head tail
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `List.casesOn`, `List.nil`

<a id="def-a7cbfbad6d5ad614"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t r source buffer limit : ℕ) (hr : 0 < r) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (j : CodedSorting.PhysicalSortingExchange.Swap)
  (hs : source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal j ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  (CodedSorting.Construction.BinaryNormalized.normalizedProgram q reader
          (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
          (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) source buffer limit ⋯ ⋯ hnormal ⋯ hw
          hl).instructions.length ≤
    (CodedSorting.Construction.BinaryNormalized.normalizedProgram q reader
        (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
        (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) source buffer limit ⋯ ⋯ hnormal ⋯ hw hl).charge
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../../Interchange/Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../../Interchange/Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.BinaryNormalized.normalizedProgram](../../Interchange/Binary/Normalized.definitions.md#def-5e24c8408dd8706c)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_5](Swaps.definitions.md#def-3f77b5a06745bf18)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_4](Swaps.definitions.md#def-42fd8966c0008ab8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace](Swaps.definitions.md#def-2e0efe3574c60ce8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.suffix_pos](Swaps.definitions.md#def-1f600f177b291891)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`

<a id="def-42fd8966c0008ab8"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ℕ →
    ∀ (r : ℕ),
      ℕ →
        ℕ →
          ℕ →
            0 < r →
              CodedSorting.Construction.RecursiveParameters.Normalized q →
                CodedSorting.PhysicalSortingExchange.Swap → 0 < 1
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-3f77b5a06745bf18"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (t r source buffer : ℕ)
  (j : CodedSorting.PhysicalSortingExchange.Swap),
  source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer →
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) (2 ^ t) 1
            (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j * q.w)) ≤
      buffer
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../../Interchange/Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-7b1bddefb8d01db6"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t r source buffer limit : ℕ) (hr : 0 < r) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (j : CodedSorting.PhysicalSortingExchange.Swap)
  (hs : source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal j ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin ((2 ^ t) ^ 4 * (r * q.w))),
  CodedSorting.CommonPermutationPairs.readBit q
      (CodedSorting.CommonStaticSchedule.executeRaw q
            (CodedSorting.Construction.BinaryNormalized.normalizedProgram q reader
                (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
                (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) source buffer limit ⋯ ⋯ hnormal ⋯ hw
                hl).instructions
            s).1.disk
      source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q s.disk source
      ↑((CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation (2 ^ t) (r * q.w)
            (CodedSorting.PhysicalSortingExchange.move (2 ^ t) (r * q.w) j))
          y)
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../../Interchange/Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalSortingExchange.move](../Bounds/PhysicalSortingExchange.definitions.md#def-506e1e347102234e)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../../Interchange/Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.BinaryNormalized.normalizedProgram](../../Interchange/Binary/Normalized.definitions.md#def-5e24c8408dd8706c)
- [CodedSorting.CommonPermutationPairs.readBit](../../Interchange/Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.bitPermutation](Swaps.definitions.md#def-e33de77481a74b63)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_5](Swaps.definitions.md#def-3f77b5a06745bf18)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_4](Swaps.definitions.md#def-42fd8966c0008ab8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace](Swaps.definitions.md#def-2e0efe3574c60ce8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.suffix_pos](Swaps.definitions.md#def-1f600f177b291891)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-75ad281cbffc6366"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t r source buffer limit : ℕ) (hr : 0 < r) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (j : CodedSorting.PhysicalSortingExchange.Swap)
  (hs : source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal j ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.Construction.BinaryNormalized.normalizedProgram q reader
                    (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
                    (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) source buffer limit ⋯ ⋯ hnormal ⋯ hw
                    hl).instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../../Interchange/Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../../Interchange/Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.BinaryNormalized.normalizedProgram](../../Interchange/Binary/Normalized.definitions.md#def-5e24c8408dd8706c)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_5](Swaps.definitions.md#def-3f77b5a06745bf18)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_4](Swaps.definitions.md#def-42fd8966c0008ab8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace](Swaps.definitions.md#def-2e0efe3574c60ce8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.suffix_pos](Swaps.definitions.md#def-1f600f177b291891)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-0be34cbac6302838"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t r source buffer limit : ℕ) (hr : 0 < r) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (j : CodedSorting.PhysicalSortingExchange.Swap)
  (hs : source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal j ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  ∀
    i ∈
      (CodedSorting.Construction.BinaryNormalized.normalizedProgram q reader
          (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
          (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) source buffer limit ⋯ ⋯ hnormal ⋯ hw
          hl).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../../Interchange/Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../../Interchange/Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.BinaryNormalized.normalizedProgram](../../Interchange/Binary/Normalized.definitions.md#def-5e24c8408dd8706c)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_5](Swaps.definitions.md#def-3f77b5a06745bf18)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_4](Swaps.definitions.md#def-42fd8966c0008ab8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace](Swaps.definitions.md#def-2e0efe3574c60ce8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.suffix_pos](Swaps.definitions.md#def-1f600f177b291891)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-c3b676d28c26d1ac"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (t r source buffer limit : ℕ) (hr : 0 < r) (hnormal : CodedSorting.Construction.RecursiveParameters.Normalized q)
  (j : CodedSorting.PhysicalSortingExchange.Swap)
  (hs : source + CodedSorting.CommonPermutationPairs.count q ((2 ^ t) ^ 4 * (r * q.w)) ≤ buffer)
  (hw : buffer + CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace q t r hr hnormal j ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent),
  CodedSorting.CommonStaticSchedule.cost q
      (CodedSorting.Construction.BinaryNormalized.normalizedProgram q reader
          (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
          (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) source buffer limit ⋯ ⋯ hnormal ⋯ hw
          hl).instructions ≤
    (CodedSorting.Construction.BinaryNormalized.normalizedProgram q reader
        (CodedSorting.PhysicalSortingExchange.prefixSize (2 ^ t) j) t 1
        (CodedSorting.PhysicalSortingExchange.suffix (2 ^ t) r j) source buffer limit ⋯ ⋯ hnormal ⋯ hw hl).charge
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../../Interchange/Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.PhysicalSortingExchange.Swap](../Bounds/PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../../Interchange/Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.BinaryNormalized.normalizedProgram](../../Interchange/Binary/Normalized.definitions.md#def-5e24c8408dd8706c)
- [CodedSorting.CommonSortingNormalization.Configuration](Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.PhysicalSortingExchange.suffix](../Bounds/PhysicalSortingExchange.definitions.md#def-72944fee1cb2bbcf)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_5](Swaps.definitions.md#def-3f77b5a06745bf18)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageProgram._proof_4](Swaps.definitions.md#def-42fd8966c0008ab8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace](Swaps.definitions.md#def-2e0efe3574c60ce8)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.suffix_pos](Swaps.definitions.md#def-1f600f177b291891)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.PhysicalSortingExchange.prefixSize](../Bounds/PhysicalSortingExchange.definitions.md#def-5f1887d78e8d6fa1)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-fb4076306aa38a88"></a>
## `CodedSorting.Construction.Sorting.CommonSortingSwaps.stageSpace._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Swaps.lean)

**类型**

```lean
ℕ → 0 < 1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`
