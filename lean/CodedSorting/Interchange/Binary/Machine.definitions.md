# Machine 的定义

[源码](Machine.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-46ff5d34f45b4c56"></a>
## `CodedSorting.Construction.BinaryCost.growth`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L15)

**类型**

```lean
ℝ
```

**定义**

```lean
↑CodedSorting.Construction.ExchangeSpecialization.radix ^ 2
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Real`, `Monoid.toNatPow`, `instOfNatNat`, `Nat.cast`, `Real.instMonoid`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Real.instNatCast`

<a id="def-4c61436c9e7a9e0d"></a>
## `CodedSorting.Construction.BinaryCost.bound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L46)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun base cutoff b P u G S A D F =>
  CodedSorting.Construction.ArbitraryCostRate.bound base cutoff b P
        (CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u) G S A D F +
      12 * (CodedSorting.BinaryPadding.Volume P (2 ^ u) G S / b + 1) +
    27 *
      (CodedSorting.BinaryPadding.Volume P
            (CodedSorting.Construction.ExchangeSpecialization.radix ^
              CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
            G S /
          b +
        1)
```

**继续展开**

- [CodedSorting.BinaryPadding.exponent](../Framework/Fields/BinaryPaddingScan.definitions.md#def-2592e6a8b528ee13)
- [CodedSorting.Construction.ArbitraryCostRate.bound](../Fields/LogRate.definitions.md#def-30367d5004946d77)
- [CodedSorting.BinaryPadding.Volume](../Framework/Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-020c37b6c349c263"></a>
## `CodedSorting.Construction.BinaryCost.binaryConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L50)

**类型**

```lean
ℕ → ℕ → ℕ → ℝ
```

**定义**

```lean
fun A D F =>
  CodedSorting.Construction.ArbitraryCostRate.finalConstant A D F * CodedSorting.Construction.BinaryCost.growth + 12 +
    27 * CodedSorting.Construction.BinaryCost.growth
```

**继续展开**

- [CodedSorting.Construction.BinaryCost.binaryConstant._proof_1](Machine.definitions.md#def-7d46635bd4d32d33)
- [CodedSorting.Construction.ArbitraryCostRate.finalConstant](../Fields/LogRate.definitions.md#def-dee17484e25629d3)
- [CodedSorting.Construction.BinaryCost.growth](Machine.definitions.md#def-46ff5d34f45b4c56)
- [CodedSorting.Construction.BinaryCost.binaryConstant._proof_2](Machine.definitions.md#def-6a2e1c528615219d)

**基础库名称**

`Real`, `HMul.hMul`, `Real.instAdd`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-71c20450b6ab5991"></a>
## `CodedSorting.Construction.BinaryMachine.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L146)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (base cutoff : ℕ) →
    ℕ →
      ℕ →
        (G S : ℕ) →
          0 < base →
            0 < G →
              0 < S →
                cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
                  CodedSorting.CommonPermutationPairs.width q ≤ cutoff →
                    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
                        CodedSorting.CommonExchangeLeaf.bankWords q →
                      CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base *
                            CodedSorting.CommonPermutationPairs.width q ≤
                          cutoff + CodedSorting.CommonPermutationPairs.width q →
                        ℕ
```

**定义**

```lean
fun q base cutoff P u G S hb hG hS hresident hblock hfit hstartup =>
  2 *
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.CommonChunkLayout.Volume P
          (CodedSorting.Construction.ExchangeSpecialization.radix ^
            CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
          G (S * q.w)) +
    CodedSorting.Construction.ArbitraryMachine.space q base cutoff P
      (CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u) G S hb hG hS
      hresident hblock hfit hstartup
```

**继续展开**

- [CodedSorting.BinaryPadding.exponent](../Framework/Fields/BinaryPaddingScan.definitions.md#def-2592e6a8b528ee13)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ArbitraryMachine.space](../Fields/Machine.definitions.md#def-520a6476c2a49ad5)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-5e8573e662b67b1b"></a>
## `CodedSorting.Construction.BinaryMachine.bound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L155)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q base cutoff P u G S =>
  CodedSorting.Construction.BinaryCost.bound base cutoff (CodedSorting.CommonPermutationPairs.width q) P u G (S * q.w)
    24 27 (6 * (2 * CodedSorting.Construction.ExchangeSpecialization.radix + 6))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.BinaryCost.bound](Machine.definitions.md#def-4c61436c9e7a9e0d)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-545d61c28b3a3406"></a>
## `CodedSorting.Construction.BinaryMachine.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L158)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (base cutoff P u G S source buffer limit : ℕ) →
      (hb : 0 < base) →
        (hG : 0 < G) →
          (hS : 0 < S) →
            (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q) →
              (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff) →
                (hfit :
                    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
                      CodedSorting.CommonExchangeLeaf.bankWords q) →
                  (hstartup :
                      CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base *
                          CodedSorting.CommonPermutationPairs.width q ≤
                        cutoff + CodedSorting.CommonPermutationPairs.width q) →
                    source +
                          CodedSorting.CommonPermutationPairs.count q
                            (CodedSorting.CommonChunkLayout.Volume P (2 ^ u) G (S * q.w)) ≤
                        buffer →
                      buffer +
                            CodedSorting.Construction.BinaryMachine.space q base cutoff P u G S hb hG hS hresident
                              hblock hfit hstartup ≤
                          limit →
                        limit ≤ q.N ^ q.exponent →
                          CodedSorting.CommonFinitePermutation.Program q
                            (CodedSorting.CommonChunkLayout.Volume P (2 ^ u) G (S * q.w)) source buffer limit
                            (CodedSorting.CommonChunkLayout.swap P (2 ^ u) G (S * q.w))
```

**定义**

```lean
fun q reader base cutoff P u G S source buffer limit hb hG hS hresident hblock hfit hstartup hs hw hl =>
  let C :=
    CodedSorting.CommonPermutationPairs.count q
      (CodedSorting.CommonChunkLayout.Volume P
        (CodedSorting.Construction.ExchangeSpecialization.radix ^
          CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
        G (S * q.w));
  let_fun hw' := ⋯;
  let child :=
    CodedSorting.Construction.ArbitraryMachine.program q reader base cutoff P
      (CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u) G S (buffer + C)
      (buffer + C + C) limit hb hG hS hresident hblock hfit hstartup ⋯ hw' hl;
  CodedSorting.CommonPaddedPermutation.binaryProgram q reader P (2 ^ u)
    (CodedSorting.Construction.ExchangeSpecialization.radix ^
      CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
    G (S * q.w) ⋯ source buffer limit child hs ⋯ hl
```

**继续展开**

- [CodedSorting.Construction.ArbitraryMachine.program](../Fields/Machine.definitions.md#def-a271a1f2620822b0)
- [CodedSorting.BinaryPadding.exponent](../Framework/Fields/BinaryPaddingScan.definitions.md#def-2592e6a8b528ee13)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.BinaryMachine.program._proof_5](Machine.definitions.md#def-69e74b5090c6a308)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.BinaryMachine.space](Machine.definitions.md#def-71c20450b6ab5991)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPaddedPermutation.binaryProgram](../Framework/Memory/PaddedChunks.definitions.md#def-a69ad54d00ab06e8)
- [CodedSorting.Construction.BinaryMachine.program._proof_6](Machine.definitions.md#def-7b3902eb83f3ecad)
- [CodedSorting.Construction.BinaryMachine.program._proof_8](Machine.definitions.md#def-de87a9c826de2a23)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.BinaryMachine.program._proof_7](Machine.definitions.md#def-1c246b7e53a6e091)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ArbitraryMachine.space](../Fields/Machine.definitions.md#def-520a6476c2a49ad5)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `letFun`, `instHMul`

<a id="def-7d46635bd4d32d33"></a>
## `CodedSorting.Construction.BinaryCost.binaryConstant._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
(10 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-6a2e1c528615219d"></a>
## `CodedSorting.Construction.BinaryCost.binaryConstant._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
(25 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-69e74b5090c6a308"></a>
## `CodedSorting.Construction.BinaryMachine.program._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base cutoff P u G S : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ) (hb : 0 < base) (hG : 0 < G) (hS : 0 < S)
      (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
      (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
      (hfit :
        CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
          CodedSorting.CommonExchangeLeaf.bankWords q)
      (hstartup :
        CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * CodedSorting.CommonPermutationPairs.width q ≤
          cutoff + CodedSorting.CommonPermutationPairs.width q),
      buffer +
            CodedSorting.Construction.BinaryMachine.space q base cutoff P u G S hb hG hS hresident hblock hfit
              hstartup ≤
          limit →
        buffer +
                CodedSorting.CommonPermutationPairs.count q
                  (CodedSorting.CommonChunkLayout.Volume P
                    (CodedSorting.Construction.ExchangeSpecialization.radix ^
                      CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
                    G (S * q.w)) +
              CodedSorting.CommonPermutationPairs.count q
                (CodedSorting.CommonChunkLayout.Volume P
                  (CodedSorting.Construction.ExchangeSpecialization.radix ^
                    CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
                  G (S * q.w)) +
            CodedSorting.Construction.ArbitraryMachine.space q base cutoff P
              (CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u) G S hb hG
              hS hresident hblock hfit hstartup ≤
          limit
```

**继续展开**

- [CodedSorting.BinaryPadding.exponent](../Framework/Fields/BinaryPaddingScan.definitions.md#def-2592e6a8b528ee13)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.BinaryMachine.space](Machine.definitions.md#def-71c20450b6ab5991)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ArbitraryMachine.space](../Fields/Machine.definitions.md#def-520a6476c2a49ad5)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-7b3902eb83f3ecad"></a>
## `CodedSorting.Construction.BinaryMachine.program._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (P u G S buffer : ℕ),
  buffer +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P
            (CodedSorting.Construction.ExchangeSpecialization.radix ^
              CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
            G (S * q.w)) +
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.CommonChunkLayout.Volume P
          (CodedSorting.Construction.ExchangeSpecialization.radix ^
            CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
          G (S * q.w)) ≤
    buffer +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P
            (CodedSorting.Construction.ExchangeSpecialization.radix ^
              CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
            G (S * q.w)) +
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.CommonChunkLayout.Volume P
          (CodedSorting.Construction.ExchangeSpecialization.radix ^
            CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
          G (S * q.w))
```

**继续展开**

- [CodedSorting.BinaryPadding.exponent](../Framework/Fields/BinaryPaddingScan.definitions.md#def-2592e6a8b528ee13)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `instHMul`

<a id="def-1c246b7e53a6e091"></a>
## `CodedSorting.Construction.BinaryMachine.program._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (u : ℕ),
  2 ^ u ≤
    CodedSorting.Construction.ExchangeSpecialization.radix ^
      CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u
```

**继续展开**

- [CodedSorting.BinaryPadding.exponent](../Framework/Fields/BinaryPaddingScan.definitions.md#def-2592e6a8b528ee13)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-de87a9c826de2a23"></a>
## `CodedSorting.Construction.BinaryMachine.program._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base cutoff P u G S : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ) (hb : 0 < base) (hG : 0 < G) (hS : 0 < S)
      (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
      (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
      (hfit :
        CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
          CodedSorting.CommonExchangeLeaf.bankWords q)
      (hstartup :
        CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * CodedSorting.CommonPermutationPairs.width q ≤
          cutoff + CodedSorting.CommonPermutationPairs.width q),
      buffer +
                CodedSorting.CommonPermutationPairs.count q
                  (CodedSorting.CommonChunkLayout.Volume P
                    (CodedSorting.Construction.ExchangeSpecialization.radix ^
                      CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
                    G (S * q.w)) +
              CodedSorting.CommonPermutationPairs.count q
                (CodedSorting.CommonChunkLayout.Volume P
                  (CodedSorting.Construction.ExchangeSpecialization.radix ^
                    CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
                  G (S * q.w)) +
            CodedSorting.Construction.ArbitraryMachine.space q base cutoff P
              (CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u) G S hb hG
              hS hresident hblock hfit hstartup ≤
          limit →
        buffer +
              CodedSorting.CommonPermutationPairs.count q
                (CodedSorting.CommonChunkLayout.Volume P
                  (CodedSorting.Construction.ExchangeSpecialization.radix ^
                    CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
                  G (S * q.w)) +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.CommonChunkLayout.Volume P
                (CodedSorting.Construction.ExchangeSpecialization.radix ^
                  CodedSorting.BinaryPadding.exponent CodedSorting.Construction.ExchangeSpecialization.radix u)
                G (S * q.w)) ≤
          limit
```

**继续展开**

- [CodedSorting.BinaryPadding.exponent](../Framework/Fields/BinaryPaddingScan.definitions.md#def-2592e6a8b528ee13)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ArbitraryMachine.space](../Fields/Machine.definitions.md#def-520a6476c2a49ad5)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`
