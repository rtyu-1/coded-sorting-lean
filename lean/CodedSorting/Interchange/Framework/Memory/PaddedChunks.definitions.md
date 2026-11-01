# PaddedChunks 的定义

[源码](PaddedChunks.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-9ec0c3411839713f"></a>
## `CodedSorting.CommonFinitePadding.zeroCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PaddedChunks.lean#L75)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader M target => CodedSorting.CommonXorAccumulator.code q reader M target []
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonXorAccumulator.code](../../../Shared/Memory/XorAccumulator.definitions.md#def-0b3750a8a06a174e)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List`, `Nat`, `Fin`, `List.nil`

<a id="def-5437562fd5b33739"></a>
## `CodedSorting.CommonFinitePadding.prefixCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PaddedChunks.lean#L103)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader V M source target =>
  CodedSorting.CommonFinitePadding.zeroCode q reader M target ++
    CodedSorting.CommonRecursiveExchange.copyCode q reader V source target
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRecursiveExchange.copyCode](../Recursion/OuterCopyFrame.definitions.md#def-654a82544fb518ba)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePadding.zeroCode](PaddedChunks.definitions.md#def-9ec0c3411839713f)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-10f123792cd1770e"></a>
## `CodedSorting.CommonFinitePadding.insertCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PaddedChunks.lean#L178)

**类型**

```lean
{V M : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin q.inventory.readers →
      V ≤ M → (e : Fin V → Fin M) → StrictMono e → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V M} q reader h e he source scratch target =>
  CodedSorting.CommonFinitePadding.prefixCode q reader V M source scratch ++
    CodedSorting.CommonPermutationScan.program q reader (CodedSorting.CommonMonotoneExtension.permutation h e he)
      (CodedSorting.CommonMonotoneExtension.colour V) scratch target
```

**继续展开**

- [CodedSorting.CommonMonotoneExtension.colour](../../../Shared/Memory/MonotoneExtension.definitions.md#def-ef8ff90a35dea536)
- [CodedSorting.CommonPermutationScan.program](Reflection.definitions.md#def-40c5a71a42c86359)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMonotoneExtension.permutation](../../../Shared/Memory/MonotoneExtension.definitions.md#def-dc652367a7659577)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePadding.prefixCode](PaddedChunks.definitions.md#def-5437562fd5b33739)

**基础库名称**

`StrictMono`, `PartialOrder.toPreorder`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `Fin.instPartialOrder`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`

<a id="def-6a70a00139c2578b"></a>
## `CodedSorting.CommonFinitePadding.eraseCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PaddedChunks.lean#L184)

**类型**

```lean
{V M : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin q.inventory.readers →
      V ≤ M → (e : Fin V → Fin M) → StrictMono e → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {V M} q reader h e he source scratch target =>
  CodedSorting.CommonPermutationScan.program q reader
      (Equiv.symm (CodedSorting.CommonMonotoneExtension.permutation h e he))
      (CodedSorting.CommonMonotoneExtension.inverseColour h e he) source scratch ++
    CodedSorting.CommonRecursiveExchange.copyCode q reader V scratch target
```

**继续展开**

- [CodedSorting.CommonPermutationScan.program](Reflection.definitions.md#def-40c5a71a42c86359)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMonotoneExtension.permutation](../../../Shared/Memory/MonotoneExtension.definitions.md#def-dc652367a7659577)
- [CodedSorting.CommonRecursiveExchange.copyCode](../Recursion/OuterCopyFrame.definitions.md#def-654a82544fb518ba)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMonotoneExtension.inverseColour](../../../Shared/Memory/MonotoneExtension.definitions.md#def-98ba883de6bb98d6)

**基础库名称**

`StrictMono`, `PartialOrder.toPreorder`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `Fin.instPartialOrder`, `Nat`, `List.instAppend`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`

<a id="def-80d15f0f10ae859a"></a>
## `CodedSorting.CommonPaddedPermutation.wrap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PaddedChunks.lean#L332)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    {V M : ℕ} →
      V ≤ M →
        (e : Fin V → Fin M) →
          StrictMono e →
            (smallπ : Equiv.Perm (Fin V)) →
              (largeπ : Equiv.Perm (Fin M)) →
                (∀ (y : Fin V), largeπ (e y) = e (smallπ y)) →
                  (source buffer limit : ℕ) →
                    CodedSorting.CommonFinitePermutation.Program q M
                        (buffer + CodedSorting.CommonPermutationPairs.count q M)
                        (buffer + CodedSorting.CommonPermutationPairs.count q M +
                          CodedSorting.CommonPermutationPairs.count q M)
                        limit largeπ →
                      source + CodedSorting.CommonPermutationPairs.count q V ≤ buffer →
                        buffer + CodedSorting.CommonPermutationPairs.count q M +
                              CodedSorting.CommonPermutationPairs.count q M ≤
                            limit →
                          limit ≤ q.N ^ q.exponent →
                            CodedSorting.CommonFinitePermutation.Program q V source buffer limit smallπ
```

**定义**

```lean
fun q reader {V M} h e he smallπ largeπ hcomm source buffer limit child hs hw hl =>
  {
    instructions :=
      CodedSorting.CommonFinitePadding.insertCode q reader h e he source buffer
            (buffer + CodedSorting.CommonPermutationPairs.count q M) ++
          child.instructions ++
        CodedSorting.CommonFinitePadding.eraseCode q reader h e he
          (buffer + CodedSorting.CommonPermutationPairs.count q M) buffer source,
    charge :=
      child.charge + 12 * CodedSorting.CommonPermutationPairs.count q V +
        27 * CodedSorting.CommonPermutationPairs.count q M,
    correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonPaddedPermutation.wrap._proof_10](PaddedChunks.definitions.md#def-e95c1b24ac3ffda0)
- [CodedSorting.CommonPaddedPermutation.wrap._proof_13](PaddedChunks.definitions.md#def-d159c79b704bdbae)
- [CodedSorting.CommonPaddedPermutation.wrap._proof_12](PaddedChunks.definitions.md#def-515a61b7d80cf0c1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonFinitePadding.eraseCode](PaddedChunks.definitions.md#def-6a70a00139c2578b)
- [CodedSorting.CommonPaddedPermutation.wrap._proof_11](PaddedChunks.definitions.md#def-9213f8ff435857ea)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePadding.insertCode](PaddedChunks.definitions.md#def-10f123792cd1770e)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonPaddedPermutation.wrap._proof_9](PaddedChunks.definitions.md#def-71f7821e509ab07e)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.mk](ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `StrictMono`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `Fin.instPartialOrder`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `instHPow`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `HAppend.hAppend`, `instHMul`

<a id="def-d8c2300d94e17845"></a>
## `CodedSorting.CommonPaddedPermutation.prefix_swap_commutes`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PaddedChunks.lean#L405)

**类型**

```lean
∀ (P P' Q G S : ℕ) (h : P ≤ P') (y : Fin (CodedSorting.CommonChunkLayout.Volume P Q G S)),
  (CodedSorting.CommonChunkLayout.swap P' Q G S) (Fin.castLE ⋯ y) =
    Fin.castLE ⋯ ((CodedSorting.CommonChunkLayout.swap P Q G S) y)
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.PhysicalPrefixPadding.volume_mono](PhysicalBorrowedChunks.definitions.md#def-d759513570ef8f00)
- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`Equiv.instFunLike`, `Fin.castLE`, `LE.le`, `instLENat`, `Equiv.Perm`, `Nat`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-aec2c3eefc2875d7"></a>
## `CodedSorting.CommonPaddedPermutation.prefixProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PaddedChunks.lean#L414)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (P P' Q G S : ℕ) →
      P ≤ P' →
        (source buffer limit : ℕ) →
          CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P' Q G S)
              (buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P' Q G S))
              (buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P' Q G S) +
                CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P' Q G S))
              limit (CodedSorting.CommonChunkLayout.swap P' Q G S) →
            source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P Q G S) ≤
                buffer →
              buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P' Q G S) +
                    CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P' Q G S) ≤
                  limit →
                limit ≤ q.N ^ q.exponent →
                  CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q G S) source
                    buffer limit (CodedSorting.CommonChunkLayout.swap P Q G S)
```

**定义**

```lean
fun q reader P P' Q G S h source buffer limit child hs hw hl =>
  CodedSorting.CommonPaddedPermutation.wrap q reader ⋯ (Fin.castLE ⋯) ⋯ (CodedSorting.CommonChunkLayout.swap P Q G S)
    (CodedSorting.CommonChunkLayout.swap P' Q G S) ⋯ source buffer limit child hs hw hl
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPaddedPermutation.wrap](PaddedChunks.definitions.md#def-80d15f0f10ae859a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.PhysicalPrefixPadding.volume_mono](PhysicalBorrowedChunks.definitions.md#def-d759513570ef8f00)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonPaddedPermutation.prefix_swap_commutes](PaddedChunks.definitions.md#def-d8c2300d94e17845)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Preorder.toLT`, `Fin.castLE`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `instHAdd`, `Fin.instPartialOrder`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `Fin`

<a id="def-8e73ee09e5a29046"></a>
## `CodedSorting.CommonPaddedPermutation.binary_volume_mono`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PaddedChunks.lean#L427)

**类型**

```lean
∀ (P Q Q' G S : ℕ),
  Q ≤ Q' → CodedSorting.CommonChunkLayout.Volume P Q G S ≤ CodedSorting.CommonChunkLayout.Volume P Q' G S
```

**继续展开**

- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-ffbf687ef5c22e8d"></a>
## `CodedSorting.CommonPaddedPermutation.binary_swap_commutes`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PaddedChunks.lean#L432)

**类型**

```lean
∀ (P Q Q' G S : ℕ) (h : Q ≤ Q') (y : Fin (CodedSorting.CommonChunkLayout.Volume P Q G S)),
  (CodedSorting.CommonChunkLayout.swap P Q' G S) (CodedSorting.BinaryPadding.physicalEmbed h y) =
    CodedSorting.BinaryPadding.physicalEmbed h ((CodedSorting.CommonChunkLayout.swap P Q G S) y)
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.BinaryPadding.physicalEmbed](../Fields/BinaryPaddingScan.definitions.md#def-55a103c70c916359)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)

**基础库名称**

`Equiv.instFunLike`, `LE.le`, `instLENat`, `Equiv.Perm`, `Nat`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-a69ad54d00ab06e8"></a>
## `CodedSorting.CommonPaddedPermutation.binaryProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PaddedChunks.lean#L440)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (P Q Q' G S : ℕ) →
      Q ≤ Q' →
        (source buffer limit : ℕ) →
          CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q' G S)
              (buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P Q' G S))
              (buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P Q' G S) +
                CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P Q' G S))
              limit (CodedSorting.CommonChunkLayout.swap P Q' G S) →
            source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P Q G S) ≤
                buffer →
              buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P Q' G S) +
                    CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P Q' G S) ≤
                  limit →
                limit ≤ q.N ^ q.exponent →
                  CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q G S) source
                    buffer limit (CodedSorting.CommonChunkLayout.swap P Q G S)
```

**定义**

```lean
fun q reader P Q Q' G S h source buffer limit child hs hw hl =>
  CodedSorting.CommonPaddedPermutation.wrap q reader ⋯ (CodedSorting.BinaryPadding.physicalEmbed h) ⋯
    (CodedSorting.CommonChunkLayout.swap P Q G S) (CodedSorting.CommonChunkLayout.swap P Q' G S) ⋯ source buffer limit
    child hs hw hl
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.BinaryPadding.physicalEmbed](../Fields/BinaryPaddingScan.definitions.md#def-55a103c70c916359)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonPaddedPermutation.binary_volume_mono](PaddedChunks.definitions.md#def-8e73ee09e5a29046)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonPaddedPermutation.binary_swap_commutes](PaddedChunks.definitions.md#def-ffbf687ef5c22e8d)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPaddedPermutation.wrap](PaddedChunks.definitions.md#def-80d15f0f10ae859a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.BinaryPadding.physicalEmbed_strictMono](../Fields/BinaryPaddingScan.definitions.md#def-910a2c4f95254734)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Fin`

<a id="def-e95c1b24ac3ffda0"></a>
## `CodedSorting.CommonPaddedPermutation.wrap._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PaddedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) {V M : ℕ} (h : V ≤ M)
  (e : Fin V → Fin M) (he : StrictMono e) (largeπ : Equiv.Perm (Fin M)) (source buffer limit : ℕ)
  (child :
    CodedSorting.CommonFinitePermutation.Program q M (buffer + CodedSorting.CommonPermutationPairs.count q M)
      (buffer + CodedSorting.CommonPermutationPairs.count q M + CodedSorting.CommonPermutationPairs.count q M) limit
      largeπ),
  source + CodedSorting.CommonPermutationPairs.count q V ≤ buffer →
    buffer + CodedSorting.CommonPermutationPairs.count q M + CodedSorting.CommonPermutationPairs.count q M ≤ limit →
      limit ≤ q.N ^ q.exponent →
        ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
          ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q V ≤ ↑a →
            ↑a < buffer ∨ limit ≤ ↑a →
              (CodedSorting.CommonStaticSchedule.executeRaw q
                        (CodedSorting.CommonFinitePadding.insertCode q reader h e he source buffer
                              (buffer + CodedSorting.CommonPermutationPairs.count q M) ++
                            child.instructions ++
                          CodedSorting.CommonFinitePadding.eraseCode q reader h e he
                            (buffer + CodedSorting.CommonPermutationPairs.count q M) buffer source)
                        s).1.disk
                  a =
                s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePadding.eraseCode](PaddedChunks.definitions.md#def-6a70a00139c2578b)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonFinitePadding.insertCode](PaddedChunks.definitions.md#def-10f123792cd1770e)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`StrictMono`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAppendOfAppend`, `List`, `instHAdd`, `Fin.instPartialOrder`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `List.instAppend`, `Fin`, `Eq`, `HAppend.hAppend`

<a id="def-9213f8ff435857ea"></a>
## `CodedSorting.CommonPaddedPermutation.wrap._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PaddedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) {V M : ℕ} (h : V ≤ M)
  (e : Fin V → Fin M) (he : StrictMono e) (largeπ : Equiv.Perm (Fin M)) (source buffer limit : ℕ)
  (child :
    CodedSorting.CommonFinitePermutation.Program q M (buffer + CodedSorting.CommonPermutationPairs.count q M)
      (buffer + CodedSorting.CommonPermutationPairs.count q M + CodedSorting.CommonPermutationPairs.count q M) limit
      largeπ),
  ∀
    i ∈
      CodedSorting.CommonFinitePadding.insertCode q reader h e he source buffer
            (buffer + CodedSorting.CommonPermutationPairs.count q M) ++
          child.instructions ++
        CodedSorting.CommonFinitePadding.eraseCode q reader h e he
          (buffer + CodedSorting.CommonPermutationPairs.count q M) buffer source,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonFinitePadding.eraseCode](PaddedChunks.definitions.md#def-6a70a00139c2578b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePadding.insertCode](PaddedChunks.definitions.md#def-10f123792cd1770e)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`StrictMono`, `PartialOrder.toPreorder`, `Membership.mem`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `Fin.instPartialOrder`, `List.instMembership`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-515a61b7d80cf0c1"></a>
## `CodedSorting.CommonPaddedPermutation.wrap._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PaddedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) {V M : ℕ} (h : V ≤ M)
  (e : Fin V → Fin M) (he : StrictMono e) (largeπ : Equiv.Perm (Fin M)) (source buffer limit : ℕ)
  (child :
    CodedSorting.CommonFinitePermutation.Program q M (buffer + CodedSorting.CommonPermutationPairs.count q M)
      (buffer + CodedSorting.CommonPermutationPairs.count q M + CodedSorting.CommonPermutationPairs.count q M) limit
      largeπ),
  CodedSorting.CommonStaticSchedule.cost q
      (CodedSorting.CommonFinitePadding.insertCode q reader h e he source buffer
            (buffer + CodedSorting.CommonPermutationPairs.count q M) ++
          child.instructions ++
        CodedSorting.CommonFinitePadding.eraseCode q reader h e he
          (buffer + CodedSorting.CommonPermutationPairs.count q M) buffer source) ≤
    child.charge + 12 * CodedSorting.CommonPermutationPairs.count q V +
      27 * CodedSorting.CommonPermutationPairs.count q M
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonFinitePadding.eraseCode](PaddedChunks.definitions.md#def-6a70a00139c2578b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePadding.insertCode](PaddedChunks.definitions.md#def-10f123792cd1770e)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `StrictMono`, `PartialOrder.toPreorder`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `Fin.instPartialOrder`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `instHMul`

<a id="def-d159c79b704bdbae"></a>
## `CodedSorting.CommonPaddedPermutation.wrap._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PaddedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) {V M : ℕ} (h : V ≤ M)
  (e : Fin V → Fin M) (he : StrictMono e) (largeπ : Equiv.Perm (Fin M)) (source buffer limit : ℕ)
  (child :
    CodedSorting.CommonFinitePermutation.Program q M (buffer + CodedSorting.CommonPermutationPairs.count q M)
      (buffer + CodedSorting.CommonPermutationPairs.count q M + CodedSorting.CommonPermutationPairs.count q M) limit
      largeπ),
  (CodedSorting.CommonFinitePadding.insertCode q reader h e he source buffer
            (buffer + CodedSorting.CommonPermutationPairs.count q M) ++
          child.instructions ++
        CodedSorting.CommonFinitePadding.eraseCode q reader h e he
          (buffer + CodedSorting.CommonPermutationPairs.count q M) buffer source).length ≤
    child.charge + 12 * CodedSorting.CommonPermutationPairs.count q V +
      27 * CodedSorting.CommonPermutationPairs.count q M
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonFinitePadding.eraseCode](PaddedChunks.definitions.md#def-6a70a00139c2578b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePadding.insertCode](PaddedChunks.definitions.md#def-10f123792cd1770e)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `StrictMono`, `PartialOrder.toPreorder`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `Fin.instPartialOrder`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `List.length`, `HAppend.hAppend`, `instHMul`

<a id="def-71f7821e509ab07e"></a>
## `CodedSorting.CommonPaddedPermutation.wrap._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PaddedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) {V M : ℕ} (h : V ≤ M)
  (e : Fin V → Fin M) (he : StrictMono e) (smallπ : Equiv.Perm (Fin V)) (largeπ : Equiv.Perm (Fin M)),
  (∀ (y : Fin V), largeπ (e y) = e (smallπ y)) →
    ∀ (source buffer limit : ℕ)
      (child :
        CodedSorting.CommonFinitePermutation.Program q M (buffer + CodedSorting.CommonPermutationPairs.count q M)
          (buffer + CodedSorting.CommonPermutationPairs.count q M + CodedSorting.CommonPermutationPairs.count q M) limit
          largeπ),
      source + CodedSorting.CommonPermutationPairs.count q V ≤ buffer →
        buffer + CodedSorting.CommonPermutationPairs.count q M + CodedSorting.CommonPermutationPairs.count q M ≤ limit →
          limit ≤ q.N ^ q.exponent →
            ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin V),
              CodedSorting.CommonPermutationPairs.readBit q
                  (CodedSorting.CommonStaticSchedule.executeRaw q
                        (CodedSorting.CommonFinitePadding.insertCode q reader h e he source buffer
                              (buffer + CodedSorting.CommonPermutationPairs.count q M) ++
                            child.instructions ++
                          CodedSorting.CommonFinitePadding.eraseCode q reader h e he
                            (buffer + CodedSorting.CommonPermutationPairs.count q M) buffer source)
                        s).1.disk
                  source ↑y =
                CodedSorting.CommonPermutationPairs.readBit q s.disk source ↑(smallπ y)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePadding.eraseCode](PaddedChunks.definitions.md#def-6a70a00139c2578b)
- [CodedSorting.CommonPermutationPairs.readBit](Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePadding.insertCode](PaddedChunks.definitions.md#def-10f123792cd1770e)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `StrictMono`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAppendOfAppend`, `List`, `instHAdd`, `Fin.instPartialOrder`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `instHPow`, `List.instAppend`, `Fin`, `Eq`, `DFunLike.coe`, `HAppend.hAppend`
