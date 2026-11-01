# Build 的定义

[源码](Build.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-fd6d02cee6665828"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.buckets`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L30)

**类型**

```lean
ℕ → CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun radix c => radix ^ c.fieldWidth * radix ^ c.fieldWidth
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `HPow.hPow`, `Nat`, `instHPow`, `instHMul`

<a id="def-2fa61f2d9f4e0cb8"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L34)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (radix : ℕ) →
    Fin q.inventory.readers →
      (c : CodedSorting.Construction.ExchangeInterface.Call) →
        CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c * q.block ≤
            CodedSorting.CommonExchangeLeaf.bankWords q →
          List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q radix reader c hfit =>
  CodedSorting.CommonBufferedCosts.code q hfit reader
    (CodedSorting.CommonBufferedBaseLayout.indexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
    (CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
    c.source c.buffer
```

**继续展开**

- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.ExchangeInterface.Call.prefixCount](../Bounds/ExchangeInterface.definitions.md#def-c6970b08eef740c9)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](../../Shared/Memory/Buffered/Schedule.definitions.md#def-94a32c197b95bcbc)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBufferedBaseLayout.indexEquiv](../../Shared/Memory/Buffered/Schedule.definitions.md#def-d2a7034dd8a02f65)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.ExchangeInterface.Call.suffix](../Bounds/ExchangeInterface.definitions.md#def-f885a54e84cd2206)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv](../../Shared/Memory/Buffered/Schedule.definitions.md#def-274883a4b214c632)
- [CodedSorting.CommonBufferedBaseLayout.Volume](../../Shared/Memory/Buffered/Schedule.definitions.md#def-ab652a1f6edc68d1)
- [CodedSorting.CommonBufferedCosts.code](../../Shared/Memory/Buffered/Permutation.definitions.md#def-c705e7b426b934c0)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `instHMul`

<a id="def-47b9b66be010d3ec"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L44)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun q radix c =>
  4 * CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.ExchangeInterface.volume radix c) +
      2 * CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c +
    1
```

**继续展开**

- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-d8a6bf0cd7cc94f2"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L101)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (radix : ℕ) →
    Fin q.inventory.readers →
      (c : CodedSorting.Construction.ExchangeInterface.Call) →
        CodedSorting.Construction.ExchangeInterface.Allocation q radix c →
          CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c * q.block ≤
              CodedSorting.CommonExchangeLeaf.bankWords q →
            c.buffer +
                    CodedSorting.CommonPermutationPairs.count q
                      (CodedSorting.Construction.ExchangeInterface.volume radix c) +
                  CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c ≤
                c.limit →
              CodedSorting.Construction.ExchangeInterface.Program q radix c
```

**定义**

```lean
fun q radix reader c a hfit hwork =>
  { instructions := CodedSorting.Construction.RecursiveBufferedLeaf.code q radix reader c hfit,
    charge := CodedSorting.Construction.RecursiveBufferedLeaf.charge q radix c, correct := ⋯, frame := ⋯, safe := ⋯,
    cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.Construction.RecursiveBufferedLeaf.code](Build.definitions.md#def-2fa61f2d9f4e0cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_4](Build.definitions.md#def-d7f7262f0b845ef2)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_2](Build.definitions.md#def-9a419c4e606d4003)
- [CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_3](Build.definitions.md#def-0506f0d13adbb8c2)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_5](Build.definitions.md#def-f0cbb9c671f5aac5)
- [CodedSorting.Construction.RecursiveBufferedLeaf.charge](Build.definitions.md#def-47b9b66be010d3ec)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_1](Build.definitions.md#def-f286a5df4a6223d8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `instHMul`

<a id="def-b8507927370d8d64"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.leafCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L229)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (c : CodedSorting.Construction.ExchangeInterface.Call) →
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
        CodedSorting.CommonExchangeLeaf.bankBits q →
      List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q c hV =>
  CodedSorting.CommonStaticLeaf.code q
    (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c) hV
    (CodedSorting.Construction.ExchangeInterface.permutation CodedSorting.Construction.ExchangeSpecialization.radix c)
    c.source c.buffer
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticLeaf.code](../../Shared/Programs/Static/Leaf.definitions.md#def-c4f24073a5ed5287)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`LE.le`, `instLENat`, `List`, `Nat`

<a id="def-f85ba4ceac3c04d0"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L235)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (c : CodedSorting.Construction.ExchangeInterface.Call) →
      CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
          CodedSorting.CommonExchangeLeaf.bankBits q →
        List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader c hV =>
  CodedSorting.Construction.RecursiveResidentLeaf.leafCode q c hV ++
    CodedSorting.CommonRecursiveExchange.copyCode q reader
      (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c)
      c.buffer c.source
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRecursiveExchange.copyCode](../Framework/Recursion/OuterCopyFrame.definitions.md#def-654a82544fb518ba)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.RecursiveResidentLeaf.leafCode](Build.definitions.md#def-b8507927370d8d64)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-118df22df70eaa8e"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L241)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun q c =>
  20 *
    (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c /
        CodedSorting.CommonPermutationPairs.width q +
      1)
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-ac5636a3a11d420b"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.code_safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L300)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (hV :
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
      CodedSorting.CommonExchangeLeaf.bankBits q),
  ∀ i ∈ CodedSorting.Construction.RecursiveResidentLeaf.code q reader c hV,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.Construction.RecursiveResidentLeaf.code](Build.definitions.md#def-f85ba4ceac3c04d0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Membership.mem`, `LE.le`, `instLENat`, `List`, `List.instMembership`, `Nat`, `Fin`

<a id="def-207defdf6a1281b4"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.code_length`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L314)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (hV :
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
      CodedSorting.CommonExchangeLeaf.bankBits q),
  (CodedSorting.Construction.RecursiveResidentLeaf.code q reader c hV).length ≤
    CodedSorting.Construction.RecursiveResidentLeaf.charge q c
```

**继续展开**

- [CodedSorting.Construction.RecursiveResidentLeaf.code](Build.definitions.md#def-f85ba4ceac3c04d0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.RecursiveResidentLeaf.charge](Build.definitions.md#def-118df22df70eaa8e)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`LE.le`, `instLENat`, `Nat`, `Fin`, `List.length`

<a id="def-5cb21d4bb49811af"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.code_cost`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L328)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (hV :
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
      CodedSorting.CommonExchangeLeaf.bankBits q),
  CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c →
    c.buffer +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
                c) +
          3 ≤
        c.limit →
      CodedSorting.CommonStaticSchedule.cost q (CodedSorting.Construction.RecursiveResidentLeaf.code q reader c hV) ≤
        CodedSorting.Construction.RecursiveResidentLeaf.charge q c
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveResidentLeaf.code](Build.definitions.md#def-f85ba4ceac3c04d0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.Construction.RecursiveResidentLeaf.charge](Build.definitions.md#def-118df22df70eaa8e)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-1ae8264c7cf19dfb"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L348)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (c : CodedSorting.Construction.ExchangeInterface.Call) →
      CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
          CodedSorting.CommonExchangeLeaf.bankBits q →
        CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix
            c →
          c.buffer +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.Construction.ExchangeInterface.volume
                      CodedSorting.Construction.ExchangeSpecialization.radix c) +
                3 ≤
              c.limit →
            CodedSorting.Construction.ExchangeInterface.Program q CodedSorting.Construction.ExchangeSpecialization.radix
              c
```

**定义**

```lean
fun q reader c hV a hpadding =>
  { instructions := CodedSorting.Construction.RecursiveResidentLeaf.code q reader c hV,
    charge := CodedSorting.Construction.RecursiveResidentLeaf.charge q c, correct := ⋯, frame := ⋯, safe := ⋯,
    cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveResidentLeaf.code](Build.definitions.md#def-f85ba4ceac3c04d0)
- [CodedSorting.Construction.RecursiveResidentLeaf.program._proof_8](Build.definitions.md#def-af5e13795eaa0715)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.RecursiveResidentLeaf.code_length](Build.definitions.md#def-207defdf6a1281b4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RecursiveResidentLeaf.program._proof_7](Build.definitions.md#def-9f89beedf6c69638)
- [CodedSorting.Construction.RecursiveResidentLeaf.code_safe](Build.definitions.md#def-ac5636a3a11d420b)
- [CodedSorting.Construction.RecursiveResidentLeaf.code_cost](Build.definitions.md#def-5cb21d4bb49811af)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveResidentLeaf.charge](Build.definitions.md#def-118df22df70eaa8e)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-5243f314a89f5144"></a>
## `CodedSorting.Construction.RecursiveLeafProgram.padding`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L404)

**类型**

```lean
ℕ → CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun cutoff c =>
  if
      CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
        cutoff then
    3
  else CodedSorting.Construction.RecursiveBufferedLeaf.buckets CodedSorting.Construction.ExchangeSpecialization.radix c
```

**继续展开**

- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `Nat.decLe`, `ite`

<a id="def-3465f12ff96845b8"></a>
## `CodedSorting.Construction.RecursiveLeafProgram.Workspace`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L407)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → CodedSorting.Construction.ExchangeInterface.Call → Prop
```

**定义**

```lean
fun q cutoff c =>
  c.buffer +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
            c) +
      CodedSorting.Construction.RecursiveLeafProgram.padding cutoff c ≤
    c.limit
```

**继续展开**

- [CodedSorting.Construction.RecursiveLeafProgram.padding](Build.definitions.md#def-5243f314a89f5144)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-11ef51af866789d9"></a>
## `CodedSorting.Construction.RecursiveLeafProgram.resident_fit`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L413)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.ExchangeInterface.LeafFits q CodedSorting.Construction.ExchangeSpecialization.radix cutoff k
      c →
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
        cutoff →
      CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
        CodedSorting.CommonExchangeLeaf.bankBits q
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.LeafFits](../Bounds/ExchangeInterface.definitions.md#def-968c9a7921183848)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-cc4823e8634888f3"></a>
## `CodedSorting.Construction.RecursiveLeafProgram.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L425)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff k : ℕ) →
      (c : CodedSorting.Construction.ExchangeInterface.Call) →
        CodedSorting.Construction.ExchangeInterface.LeafFits q CodedSorting.Construction.ExchangeSpecialization.radix
            cutoff k c →
          CodedSorting.Construction.ExchangeInterface.Allocation q
              CodedSorting.Construction.ExchangeSpecialization.radix c →
            CodedSorting.Construction.RecursiveLeafProgram.Workspace q cutoff c →
              CodedSorting.Construction.ExchangeInterface.Program q
                CodedSorting.Construction.ExchangeSpecialization.radix c
```

**定义**

```lean
fun q reader cutoff k c hf a hw =>
  if hs :
      CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
        cutoff then
    CodedSorting.Construction.RecursiveResidentLeaf.program q reader c ⋯ a ⋯
  else
    CodedSorting.Construction.RecursiveBufferedLeaf.program q CodedSorting.Construction.ExchangeSpecialization.radix
      reader c a ⋯ ⋯
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveLeafProgram.program._proof_10](Build.definitions.md#def-ec137255ca32b54a)
- [CodedSorting.Construction.RecursiveLeafProgram.Workspace](Build.definitions.md#def-3465f12ff96845b8)
- [CodedSorting.Construction.RecursiveBufferedLeaf.program](Build.definitions.md#def-d8a6bf0cd7cc94f2)
- [CodedSorting.Construction.RecursiveLeafProgram.program._proof_11](Build.definitions.md#def-163cd363141dbae8)
- [CodedSorting.Construction.RecursiveLeafProgram.program._proof_9](Build.definitions.md#def-00d3b6e28e8dcfbc)
- [CodedSorting.Construction.RecursiveLeafProgram.resident_fit](Build.definitions.md#def-11ef51af866789d9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.LeafFits](../Bounds/ExchangeInterface.definitions.md#def-968c9a7921183848)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.RecursiveResidentLeaf.program](Build.definitions.md#def-1ae8264c7cf19dfb)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`LE.le`, `instLENat`, `dite`, `Nat`, `Fin`, `Not`, `Nat.decLe`

<a id="def-360840da586786ab"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.LeafReady`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Build.lean#L537)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → CodedSorting.Construction.ExchangeInterface.Call → Prop
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady.mk](Build.definitions.md#def-e0355da98f03b743)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-e0355da98f03b743"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.LeafReady.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Build.lean#L538)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c →
    CodedSorting.Construction.ExchangeInterface.LeafFits q CodedSorting.Construction.ExchangeSpecialization.radix cutoff
        k c →
      CodedSorting.Construction.RecursiveLeafProgram.Workspace q cutoff c →
        CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff k c
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveLeafProgram.Workspace](Build.definitions.md#def-3465f12ff96845b8)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.LeafFits](../Bounds/ExchangeInterface.definitions.md#def-968c9a7921183848)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady](Build.definitions.md#def-360840da586786ab)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat`

<a id="def-3672bacd592f7879"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.LeafReady.allocation`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L539)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff k c →
    CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady](Build.definitions.md#def-360840da586786ab)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat`

<a id="def-114c07a5968aa003"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.LeafReady.fits`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L540)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff k c →
    CodedSorting.Construction.ExchangeInterface.LeafFits q CodedSorting.Construction.ExchangeSpecialization.radix cutoff
      k c
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.LeafFits](../Bounds/ExchangeInterface.definitions.md#def-968c9a7921183848)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady](Build.definitions.md#def-360840da586786ab)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat`

<a id="def-edb577a57b37468a"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.LeafReady.workspace`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L541)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff k c →
    CodedSorting.Construction.RecursiveLeafProgram.Workspace q cutoff c
```

**继续展开**

- [CodedSorting.Construction.RecursiveLeafProgram.Workspace](Build.definitions.md#def-3465f12ff96845b8)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady](Build.definitions.md#def-360840da586786ab)

**基础库名称**

`Nat`

<a id="def-36bd195f966d5594"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.NodeReady`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Build.lean#L543)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ℕ →
    CodedSorting.Construction.ExchangeInterface.Call → (CodedSorting.Construction.ExchangeInterface.Call → Prop) → Prop
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.NodeReady.mk](Build.definitions.md#def-4caa778541667225)

**基础库名称**

`Nat`

<a id="def-4caa778541667225"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.NodeReady.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Build.lean#L546)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call}
  {childReady : CodedSorting.Construction.ExchangeInterface.Call → Prop}
  (shape : CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c)
  (allocation :
    CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c)
  (reserve : CodedSorting.Construction.RecursiveCallBridge.requiredLimit q c ≤ c.limit),
  (∀ (child : CodedSorting.Construction.OneLevelChildren.Child),
      childReady
        (CodedSorting.Construction.OneLevelExchange.childCall
          (CodedSorting.Construction.RecursiveCallBridge.nextSetup shape allocation reserve) child)) →
    CodedSorting.Construction.RecursiveBuildConditions.NodeReady q k c childReady
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.RecursiveCallBridge.requiredLimit](CallBridge.definitions.md#def-6e22cf5475ac82d9)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.OneLevelExchange.childCall](../OneLevel/Exchange.definitions.md#def-3343cdc150a25701)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.RecursiveCallBridge.nextSetup](CallBridge.definitions.md#def-cee33bf01bfa59c7)
- [CodedSorting.Construction.OneLevelChildren.Child](../OneLevel/Children.definitions.md#def-e64350cb13f8e2d9)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.RecursiveBuildConditions.NodeReady](Build.definitions.md#def-36bd195f966d5594)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-ec5a8673d7f93825"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.Ready`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L554)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → CodedSorting.Construction.ExchangeInterface.Call → Prop
```

**定义**

```lean
fun q cutoff x x_1 =>
  Nat.brecOn (motive := fun x => CodedSorting.Construction.ExchangeInterface.Call → Prop) x
    (fun x f x_2 =>
      (match (motive :=
          (x : ℕ) →
            CodedSorting.Construction.ExchangeInterface.Call →
              Nat.below (motive := fun x => CodedSorting.Construction.ExchangeInterface.Call → Prop) x → Prop)
          x, x_2 with
        | 0, c => fun x => CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff 0 c
        | k.succ, c => fun x =>
          if
              CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
                  c ≤
                cutoff then
            CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff (k + 1) c
          else CodedSorting.Construction.RecursiveBuildConditions.NodeReady q k c x.1)
        f)
    x_1
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady](Build.definitions.md#def-360840da586786ab)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.RecursiveBuildConditions.Ready.match_1](Build.definitions.md#def-971a087799b82b32)
- [CodedSorting.Construction.RecursiveBuildConditions.NodeReady](Build.definitions.md#def-36bd195f966d5594)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat.brecOn`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.succ`, `Nat.decLe`, `ite`

<a id="def-45bf1c337c8b01dd"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.zero_leaf`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L562)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff 0 c →
    CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff 0 c
```

**继续展开**

- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady](Build.definitions.md#def-360840da586786ab)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-730dacf360896838"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.large_node`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean#L572)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff (k + 1) c →
    ¬CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
          cutoff →
      CodedSorting.Construction.RecursiveBuildConditions.NodeReady q k c
        (CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff k)
```

**继续展开**

- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.RecursiveBuildConditions.NodeReady](Build.definitions.md#def-36bd195f966d5594)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`

<a id="def-dd2634413366742e"></a>
## `CodedSorting.Construction.RecursiveBuild.leaf`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L624)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff k : ℕ) →
      (c : CodedSorting.Construction.ExchangeInterface.Call) →
        CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff k c →
          CodedSorting.Construction.ExchangeInterface.Program q CodedSorting.Construction.ExchangeSpecialization.radix c
```

**定义**

```lean
fun q reader cutoff k c h => CodedSorting.Construction.RecursiveLeafProgram.program q reader cutoff k c ⋯ ⋯ ⋯
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady.fits](Build.definitions.md#def-114c07a5968aa003)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady.workspace](Build.definitions.md#def-edb577a57b37468a)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady.allocation](Build.definitions.md#def-3672bacd592f7879)
- [CodedSorting.Construction.RecursiveLeafProgram.program](Build.definitions.md#def-cc4823e8634888f3)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady](Build.definitions.md#def-360840da586786ab)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat`, `Fin`

<a id="def-6eaefa37259d3a83"></a>
## `CodedSorting.Construction.RecursiveBuild.build`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Build.lean#L629)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff k : ℕ) →
      (c : CodedSorting.Construction.ExchangeInterface.Call) →
        CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff k c →
          CodedSorting.Construction.ExchangeInterface.Program q CodedSorting.Construction.ExchangeSpecialization.radix c
```

**定义**

```lean
fun q reader cutoff x x_1 x_2 =>
  Nat.brecOn (motive := fun x =>
    (x_3 : CodedSorting.Construction.ExchangeInterface.Call) →
      CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff x x_3 →
        CodedSorting.Construction.ExchangeInterface.Program q CodedSorting.Construction.ExchangeSpecialization.radix
          x_3)
    x
    (fun x f x_3 x_4 =>
      (match (motive :=
          (x : ℕ) →
            (x_5 : CodedSorting.Construction.ExchangeInterface.Call) →
              CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff x x_5 →
                Nat.below (motive := fun x =>
                    (x_7 : CodedSorting.Construction.ExchangeInterface.Call) →
                      CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff x x_7 →
                        CodedSorting.Construction.ExchangeInterface.Program q
                          CodedSorting.Construction.ExchangeSpecialization.radix x_7)
                    x →
                  CodedSorting.Construction.ExchangeInterface.Program q
                    CodedSorting.Construction.ExchangeSpecialization.radix x_5)
          x, x_3, x_4 with
        | 0, c, h => fun x => CodedSorting.Construction.RecursiveBuild.leaf q reader cutoff 0 c ⋯
        | k.succ, c, h => fun x =>
          if hs :
              CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
                  c ≤
                cutoff then
            CodedSorting.Construction.RecursiveBuild.leaf q reader cutoff (k + 1) c ⋯
          else
            let hn := ⋯;
            CodedSorting.Construction.RecursiveCallBridge.nextProgram reader ⋯ ⋯ ⋯ fun child =>
              x.1
                (CodedSorting.Construction.OneLevelExchange.childCall
                  (CodedSorting.Construction.RecursiveCallBridge.nextSetup ⋯ ⋯ ⋯) child)
                ⋯)
        f)
    x_1 x_2
```

**继续展开**

- [CodedSorting.Construction.RecursiveBuild.build._proof_15](Build.definitions.md#def-3c05e18a8393c610)
- [CodedSorting.Construction.RecursiveCallBridge.nextProgram](CallBridge.definitions.md#def-5537eed977da1c36)
- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.OneLevelExchange.childCall](../OneLevel/Exchange.definitions.md#def-3343cdc150a25701)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.RecursiveBuild.build._proof_12](Build.definitions.md#def-74bbcfb7ec2fbad2)
- [CodedSorting.Construction.RecursiveBuild.build._proof_13](Build.definitions.md#def-beb96623485f0604)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RecursiveCallBridge.nextSetup](CallBridge.definitions.md#def-cee33bf01bfa59c7)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.OneLevelChildren.Child](../OneLevel/Children.definitions.md#def-e64350cb13f8e2d9)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveBuild.build._proof_16](Build.definitions.md#def-f73cff3b1c898824)
- [CodedSorting.Construction.RecursiveBuild.leaf](Build.definitions.md#def-dd2634413366742e)
- [CodedSorting.Construction.RecursiveBuildConditions.zero_leaf](Build.definitions.md#def-45bf1c337c8b01dd)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.RecursiveBuild.build.match_1](Build.definitions.md#def-16e38f16ee224969)
- [CodedSorting.Construction.RecursiveBuild.build._proof_14](Build.definitions.md#def-8df88019cae4aa97)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.RecursiveBuildConditions.NodeReady](Build.definitions.md#def-36bd195f966d5594)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.RecursiveBuildConditions.large_node](Build.definitions.md#def-730dacf360896838)

**基础库名称**

`Nat.brecOn`, `instOfNatNat`, `LE.le`, `instLENat`, `dite`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `Not`, `Nat.decLe`

<a id="def-f286a5df4a6223d8"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix : ℕ) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.ExchangeInterface.Allocation q radix c →
    ∀
      (hfit :
        CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c * q.block ≤
          CodedSorting.CommonExchangeLeaf.bankWords q),
      c.buffer +
              CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.ExchangeInterface.volume radix c) +
            CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c ≤
          c.limit →
        ∀ (s : CodedSorting.CommonLeafProgram.Machine q)
          (i : Fin (CodedSorting.Construction.ExchangeInterface.volume radix c)),
          CodedSorting.CommonPermutationPairs.readBit q
              (CodedSorting.CommonStaticSchedule.executeRaw q
                    (CodedSorting.Construction.RecursiveBufferedLeaf.code q radix reader c hfit) s).1.disk
              c.source ↑i =
            CodedSorting.CommonPermutationPairs.readBit q s.disk c.source
              ↑((CodedSorting.Construction.ExchangeInterface.permutation radix c) i)
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.Construction.RecursiveBufferedLeaf.code](Build.definitions.md#def-2fa61f2d9f4e0cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `instHPow`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-9a419c4e606d4003"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix : ℕ) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.ExchangeInterface.Allocation q radix c →
    ∀
      (hfit :
        CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c * q.block ≤
          CodedSorting.CommonExchangeLeaf.bankWords q),
      c.buffer +
              CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.ExchangeInterface.volume radix c) +
            CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c ≤
          c.limit →
        ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (z : Fin (q.N ^ q.exponent)),
          ↑z < c.source ∨
              c.source +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.Construction.ExchangeInterface.volume radix c) ≤
                ↑z →
            ↑z < c.buffer ∨ c.limit ≤ ↑z →
              (CodedSorting.CommonStaticSchedule.executeRaw q
                        (CodedSorting.Construction.RecursiveBufferedLeaf.code q radix reader c hfit) s).1.disk
                  z =
                s.disk z
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.Construction.RecursiveBufferedLeaf.code](Build.definitions.md#def-2fa61f2d9f4e0cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `instHMul`

<a id="def-0506f0d13adbb8c2"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix : ℕ) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (hfit :
    CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q),
  ∀
    i ∈
      CodedSorting.CommonBufferedCosts.code q hfit reader
        (CodedSorting.CommonBufferedBaseLayout.indexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
        (CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
        c.source c.buffer,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.ExchangeInterface.Call.prefixCount](../Bounds/ExchangeInterface.definitions.md#def-c6970b08eef740c9)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](../../Shared/Memory/Buffered/Schedule.definitions.md#def-94a32c197b95bcbc)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBufferedBaseLayout.indexEquiv](../../Shared/Memory/Buffered/Schedule.definitions.md#def-d2a7034dd8a02f65)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.ExchangeInterface.Call.suffix](../Bounds/ExchangeInterface.definitions.md#def-f885a54e84cd2206)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv](../../Shared/Memory/Buffered/Schedule.definitions.md#def-274883a4b214c632)
- [CodedSorting.CommonBufferedBaseLayout.Volume](../../Shared/Memory/Buffered/Schedule.definitions.md#def-ab652a1f6edc68d1)
- [CodedSorting.CommonBufferedCosts.code](../../Shared/Memory/Buffered/Permutation.definitions.md#def-c705e7b426b934c0)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `List`, `HPow.hPow`, `List.instMembership`, `Nat`, `instHPow`, `Fin`, `instHMul`

<a id="def-d7f7262f0b845ef2"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix : ℕ) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (hfit :
    CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q),
  CodedSorting.CommonStaticSchedule.cost q
      (CodedSorting.CommonBufferedCosts.code q hfit reader
        (CodedSorting.CommonBufferedBaseLayout.indexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
        (CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
        c.source c.buffer) ≤
    CodedSorting.Construction.RecursiveBufferedLeaf.charge q radix c
```

**继续展开**

- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.ExchangeInterface.Call.prefixCount](../Bounds/ExchangeInterface.definitions.md#def-c6970b08eef740c9)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](../../Shared/Memory/Buffered/Schedule.definitions.md#def-94a32c197b95bcbc)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBufferedBaseLayout.indexEquiv](../../Shared/Memory/Buffered/Schedule.definitions.md#def-d2a7034dd8a02f65)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.ExchangeInterface.Call.suffix](../Bounds/ExchangeInterface.definitions.md#def-f885a54e84cd2206)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv](../../Shared/Memory/Buffered/Schedule.definitions.md#def-274883a4b214c632)
- [CodedSorting.CommonBufferedBaseLayout.Volume](../../Shared/Memory/Buffered/Schedule.definitions.md#def-ab652a1f6edc68d1)
- [CodedSorting.CommonBufferedCosts.code](../../Shared/Memory/Buffered/Permutation.definitions.md#def-c705e7b426b934c0)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.RecursiveBufferedLeaf.charge](Build.definitions.md#def-47b9b66be010d3ec)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat.instPreorder`, `Nat`, `instHPow`, `Fin`, `instHMul`

<a id="def-f0cbb9c671f5aac5"></a>
## `CodedSorting.Construction.RecursiveBufferedLeaf.program._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix : ℕ) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (hfit :
    CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q),
  (CodedSorting.CommonBufferedCosts.code q hfit reader
        (CodedSorting.CommonBufferedBaseLayout.indexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
        (CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
        c.source c.buffer).length ≤
    4 *
          CodedSorting.CommonPermutationPairs.count q
            (CodedSorting.CommonBufferedBaseLayout.Volume c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix) +
        2 * CodedSorting.Construction.RecursiveBufferedLeaf.buckets radix c +
      1
```

**继续展开**

- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.ExchangeInterface.Call.prefixCount](../Bounds/ExchangeInterface.definitions.md#def-c6970b08eef740c9)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](../../Shared/Memory/Buffered/Schedule.definitions.md#def-94a32c197b95bcbc)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBufferedBaseLayout.indexEquiv](../../Shared/Memory/Buffered/Schedule.definitions.md#def-d2a7034dd8a02f65)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.ExchangeInterface.Call.suffix](../Bounds/ExchangeInterface.definitions.md#def-f885a54e84cd2206)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv](../../Shared/Memory/Buffered/Schedule.definitions.md#def-274883a4b214c632)
- [CodedSorting.CommonBufferedBaseLayout.Volume](../../Shared/Memory/Buffered/Schedule.definitions.md#def-ab652a1f6edc68d1)
- [CodedSorting.CommonBufferedCosts.code](../../Shared/Memory/Buffered/Permutation.definitions.md#def-c705e7b426b934c0)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`

<a id="def-74bbcfb7ec2fbad2"></a>
## `CodedSorting.Construction.RecursiveBuild.build._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff k : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff (k + 1) c →
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
        cutoff →
      CodedSorting.Construction.RecursiveBuildConditions.LeafReady q cutoff (k + 1) c
```

**继续展开**

- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveBuildConditions.LeafReady](Build.definitions.md#def-360840da586786ab)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-beb96623485f0604"></a>
## `CodedSorting.Construction.RecursiveBuild.build._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff k : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff (k + 1) c →
    ¬CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
          cutoff →
      CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c
```

**继续展开**

- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`

<a id="def-8df88019cae4aa97"></a>
## `CodedSorting.Construction.RecursiveBuild.build._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff k : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff (k + 1) c →
    ¬CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
          cutoff →
      CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`

<a id="def-3c05e18a8393c610"></a>
## `CodedSorting.Construction.RecursiveBuild.build._proof_15`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff k : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff (k + 1) c →
    ¬CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
          cutoff →
      CodedSorting.Construction.RecursiveCallBridge.requiredLimit q c ≤ c.limit
```

**继续展开**

- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.RecursiveCallBridge.requiredLimit](CallBridge.definitions.md#def-6e22cf5475ac82d9)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`

<a id="def-f73cff3b1c898824"></a>
## `CodedSorting.Construction.RecursiveBuild.build._proof_16`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff k : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (h : CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff (k + 1) c)
  (hs :
    ¬CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
        cutoff)
  (child : CodedSorting.Construction.OneLevelChildren.Child),
  CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff k
    (CodedSorting.Construction.OneLevelExchange.childCall
      (CodedSorting.Construction.RecursiveCallBridge.nextSetup ⋯ ⋯ ⋯) child)
```

**继续展开**

- [CodedSorting.Construction.RecursiveBuild.build._proof_15](Build.definitions.md#def-3c05e18a8393c610)
- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.OneLevelExchange.childCall](../OneLevel/Exchange.definitions.md#def-3343cdc150a25701)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.RecursiveBuild.build._proof_13](Build.definitions.md#def-beb96623485f0604)
- [CodedSorting.Construction.RecursiveCallBridge.nextSetup](CallBridge.definitions.md#def-cee33bf01bfa59c7)
- [CodedSorting.Construction.OneLevelChildren.Child](../OneLevel/Children.definitions.md#def-e64350cb13f8e2d9)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.RecursiveBuild.build._proof_14](Build.definitions.md#def-8df88019cae4aa97)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`

<a id="def-16e38f16ee224969"></a>
## `CodedSorting.Construction.RecursiveBuild.build.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Build.lean)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (cutoff : ℕ) →
    (motive :
        (x : ℕ) →
          (x_1 : CodedSorting.Construction.ExchangeInterface.Call) →
            CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff x x_1 → Sort u_1) →
      (x : ℕ) →
        (x_1 : CodedSorting.Construction.ExchangeInterface.Call) →
          (x_2 : CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff x x_1) →
            ((c : CodedSorting.Construction.ExchangeInterface.Call) →
                (h : CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff 0 c) → motive 0 c h) →
              ((k : ℕ) →
                  (c : CodedSorting.Construction.ExchangeInterface.Call) →
                    (h : CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff (k + 1) c) →
                      motive k.succ c h) →
                motive x x_1 x_2
```

**定义**

```lean
fun q cutoff motive x x_1 x_2 h_1 h_2 =>
  Nat.casesOn (motive := fun x =>
    (x_3 : CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff x x_1) → motive x x_1 x_3) x
    (fun x => h_1 x_1 x) (fun n x => h_2 n x_1 x) x_2
```

**继续展开**

- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Nat.zero`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-971a087799b82b32"></a>
## `CodedSorting.Construction.RecursiveBuildConditions.Ready.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Build.lean)

**类型**

```lean
(motive : ℕ → CodedSorting.Construction.ExchangeInterface.Call → Sort u_1) →
  (x : ℕ) →
    (x_1 : CodedSorting.Construction.ExchangeInterface.Call) →
      ((c : CodedSorting.Construction.ExchangeInterface.Call) → motive 0 c) →
        ((k : ℕ) → (c : CodedSorting.Construction.ExchangeInterface.Call) → motive k.succ c) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-ec137255ca32b54a"></a>
## `CodedSorting.Construction.RecursiveLeafProgram.program._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff k : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.ExchangeInterface.LeafFits q CodedSorting.Construction.ExchangeSpecialization.radix cutoff k
      c →
    ¬CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
          cutoff →
      CodedSorting.Construction.RecursiveBufferedLeaf.buckets CodedSorting.Construction.ExchangeSpecialization.radix c *
          q.block ≤
        CodedSorting.CommonExchangeLeaf.bankWords q
```

**继续展开**

- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.LeafFits](../Bounds/ExchangeInterface.definitions.md#def-968c9a7921183848)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Nat`, `Not`, `instHMul`

<a id="def-163cd363141dbae8"></a>
## `CodedSorting.Construction.RecursiveLeafProgram.program._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.RecursiveLeafProgram.Workspace q cutoff c →
    ¬CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
          cutoff →
      c.buffer +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
                c) +
          CodedSorting.Construction.RecursiveBufferedLeaf.buckets CodedSorting.Construction.ExchangeSpecialization.radix
            c ≤
        c.limit
```

**继续展开**

- [CodedSorting.Construction.RecursiveLeafProgram.Workspace](Build.definitions.md#def-3465f12ff96845b8)
- [CodedSorting.Construction.RecursiveBufferedLeaf.buckets](Build.definitions.md#def-fd6d02cee6665828)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Not`

<a id="def-00d3b6e28e8dcfbc"></a>
## `CodedSorting.Construction.RecursiveLeafProgram.program._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.RecursiveLeafProgram.Workspace q cutoff c →
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
        cutoff →
      c.buffer +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
                c) +
          3 ≤
        c.limit
```

**继续展开**

- [CodedSorting.Construction.RecursiveLeafProgram.Workspace](Build.definitions.md#def-3465f12ff96845b8)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-9f89beedf6c69638"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.program._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (hV :
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
      CodedSorting.CommonExchangeLeaf.bankBits q),
  CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c →
    c.buffer +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
                c) +
          3 ≤
        c.limit →
      ∀ (s : CodedSorting.CommonLeafProgram.Machine q)
        (y :
          Fin
            (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
              c)),
        CodedSorting.CommonPermutationPairs.readBit q
            (CodedSorting.CommonStaticSchedule.executeRaw q
                  (CodedSorting.Construction.RecursiveResidentLeaf.code q reader c hV) s).1.disk
            c.source ↑y =
          CodedSorting.CommonPermutationPairs.readBit q s.disk c.source
            ↑((CodedSorting.Construction.ExchangeInterface.permutation
                  CodedSorting.Construction.ExchangeSpecialization.radix c)
                y)
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveResidentLeaf.code](Build.definitions.md#def-f85ba4ceac3c04d0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-af5e13795eaa0715"></a>
## `CodedSorting.Construction.RecursiveResidentLeaf.program._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Build.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c : CodedSorting.Construction.ExchangeInterface.Call)
  (hV :
    CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix c ≤
      CodedSorting.CommonExchangeLeaf.bankBits q),
  CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c →
    c.buffer +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
                c) +
          3 ≤
        c.limit →
      ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (x : Fin (q.N ^ q.exponent)),
        ↑x < c.source ∨
            c.source +
                CodedSorting.CommonPermutationPairs.count q
                  (CodedSorting.Construction.ExchangeInterface.volume
                    CodedSorting.Construction.ExchangeSpecialization.radix c) ≤
              ↑x →
          ↑x < c.buffer ∨ c.limit ≤ ↑x →
            (CodedSorting.CommonStaticSchedule.executeRaw q
                      (CodedSorting.Construction.RecursiveResidentLeaf.code q reader c hV) s).1.disk
                x =
              s.disk x
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveResidentLeaf.code](Build.definitions.md#def-f85ba4ceac3c04d0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`
