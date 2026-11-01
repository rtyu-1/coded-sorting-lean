# BorrowedChunks 的定义

[源码](BorrowedChunks.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-0cc500b7f150481a"></a>
## `CodedSorting.Construction.ChunkCompose.emptyProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L27)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (P G S source buffer limit : ℕ) →
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P 1 G (S * q.w)) source buffer
      limit (CodedSorting.CommonChunkLayout.swap P 1 G (S * q.w))
```

**定义**

```lean
fun q P G S source buffer limit =>
  { instructions := [], charge := 0, correct := ⋯, frame := ⋯, safe := ⋯,
    cost_le := CodedSorting.Construction.ChunkCompose.emptyProgram._proof_4,
    length_le := CodedSorting.Construction.ChunkCompose.emptyProgram._proof_4 }
```

**继续展开**

- [CodedSorting.Construction.ChunkCompose.emptyProgram._proof_3](BorrowedChunks.definitions.md#def-74391b5646a893ea)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.ChunkCompose.emptyProgram._proof_2](BorrowedChunks.definitions.md#def-e60c47085fb96f56)
- [CodedSorting.Construction.ChunkCompose.emptyProgram._proof_4](BorrowedChunks.definitions.md#def-a1cb493d796040f2)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ChunkCompose.emptyProgram._proof_1](BorrowedChunks.definitions.md#def-07b3c888c51eb5f6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`, `List.nil`

<a id="def-1f6373641f597a68"></a>
## `CodedSorting.Construction.ChunkCompose.combine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L38)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (P Q R G S source buffer limit : ℕ) →
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q (R * G) (R * S * q.w))
        source buffer limit (CodedSorting.CommonChunkLayout.swap P Q (R * G) (R * S * q.w)) →
      CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume (P * Q) R (G * Q) (S * q.w))
          source buffer limit (CodedSorting.CommonChunkLayout.swap (P * Q) R (G * Q) (S * q.w)) →
        CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P (Q * R) G (S * q.w))
          source buffer limit (CodedSorting.CommonChunkLayout.swap P (Q * R) G (S * q.w))
```

**定义**

```lean
fun q P Q R G S source buffer limit p₁ p₂ =>
  { instructions := p₁.instructions ++ p₂.instructions, charge := p₁.charge + p₂.charge, correct := ⋯, frame := ⋯,
    safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.ChunkCompose.combine._proof_7](BorrowedChunks.definitions.md#def-0a25c30dc169502d)
- [CodedSorting.Construction.ChunkCompose.combine._proof_8](BorrowedChunks.definitions.md#def-de529d553c31f68c)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ChunkCompose.combine._proof_5](BorrowedChunks.definitions.md#def-c39f487dc51b4730)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.Construction.ChunkCompose.combine._proof_6](BorrowedChunks.definitions.md#def-6f69ec5b1d8a9961)
- [CodedSorting.Construction.ChunkCompose.combine._proof_9](BorrowedChunks.definitions.md#def-7a5239ea9dfae052)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `HAppend.hAppend`, `instHMul`

<a id="def-464508b12f165a08"></a>
## `CodedSorting.Construction.ChunkExchange.Conditions`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](BorrowedChunks.lean#L114)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ℕ → List CodedSorting.Construction.ArbitraryCalls.Call → ℕ → Prop
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions.mk](BorrowedChunks.definitions.md#def-e22f45959df329eb)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`List`, `Nat`

<a id="def-e22f45959df329eb"></a>
## `CodedSorting.Construction.ChunkExchange.Conditions.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](BorrowedChunks.lean#L114)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff : ℕ}
  {cs : List CodedSorting.Construction.ArbitraryCalls.Call} {P : ℕ},
  cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
    CodedSorting.CommonPermutationPairs.width q ≤ cutoff →
      (∀ c ∈ cs, CodedSorting.Construction.streamCount ^ c.depth ∣ P) →
        (∀ c ∈ cs,
            CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
              CodedSorting.CommonExchangeLeaf.bankWords q) →
          (∀ c ∈ cs,
              CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
                  CodedSorting.CommonPermutationPairs.width q ≤
                cutoff + CodedSorting.CommonPermutationPairs.width q) →
            CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `Nat.instDvd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `instHMul`

<a id="def-ccebc2bca7c844ea"></a>
## `CodedSorting.Construction.ChunkExchange.Conditions.resident`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean#L116)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff : ℕ}
  {cs : List CodedSorting.Construction.ArbitraryCalls.Call} {P : ℕ},
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P → cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`LE.le`, `instLENat`, `List`, `Nat`

<a id="def-77993e059f0f8156"></a>
## `CodedSorting.Construction.ChunkExchange.Conditions.block`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean#L117)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff : ℕ}
  {cs : List CodedSorting.Construction.ArbitraryCalls.Call} {P : ℕ},
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P →
    CodedSorting.CommonPermutationPairs.width q ≤ cutoff
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`LE.le`, `instLENat`, `List`, `Nat`

<a id="def-b072f0f5da7600e1"></a>
## `CodedSorting.Construction.ChunkExchange.Conditions.divisible`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean#L118)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff : ℕ}
  {cs : List CodedSorting.Construction.ArbitraryCalls.Call} {P : ℕ},
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P →
    ∀ c ∈ cs, CodedSorting.Construction.streamCount ^ c.depth ∣ P
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Dvd.dvd`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `List`, `HPow.hPow`, `Nat.instDvd`, `List.instMembership`, `Nat`, `instHPow`

<a id="def-70c3df6c3ad07499"></a>
## `CodedSorting.Construction.ChunkExchange.Conditions.buffers`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean#L119)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff : ℕ}
  {cs : List CodedSorting.Construction.ArbitraryCalls.Call} {P : ℕ},
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P →
    ∀ c ∈ cs,
      CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
        CodedSorting.CommonExchangeLeaf.bankWords q
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Membership.mem`, `instMulNat`, `LE.le`, `instLENat`, `List`, `List.instMembership`, `Nat`, `instHMul`

<a id="def-d91509e7fa44f3b2"></a>
## `CodedSorting.Construction.ChunkExchange.Conditions.startup`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean#L120)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {cutoff : ℕ}
  {cs : List CodedSorting.Construction.ArbitraryCalls.Call} {P : ℕ},
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P →
    ∀ c ∈ cs,
      CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
          CodedSorting.CommonPermutationPairs.width q ≤
        cutoff + CodedSorting.CommonPermutationPairs.width q
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `Membership.mem`, `instMulNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-9755ef9d6158e0af"></a>
## `CodedSorting.Construction.ChunkExchange.Conditions.tail`

读取 `CodedSorting.Construction.ChunkExchange.Conditions` 的 `tail` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](BorrowedChunks.lean#L122)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (P : ℕ),
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P →
    CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs
      (P * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
```

**定义**

```lean
fun q cutoff c cs P h =>
  { resident := h.resident, block := h.block,
    divisible := fun d hd =>
      dvd_mul_of_dvd_left
        (h.divisible d
          (of_eq_true
            (Eq.trans Init.Data.List.Lemmas._auxLemma.9
              (Eq.trans (congrArg (Or (d = c)) (eq_true hd)) (or_true (d = c))))))
        (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width),
    buffers := fun d hd =>
      h.buffers d
        (of_eq_true
          (Eq.trans Init.Data.List.Lemmas._auxLemma.9
            (Eq.trans (congrArg (Or (d = c)) (eq_true hd)) (or_true (d = c))))),
    startup := fun d hd =>
      h.startup d
        (of_eq_true
          (Eq.trans Init.Data.List.Lemmas._auxLemma.9
            (Eq.trans (congrArg (Or (d = c)) (eq_true hd)) (or_true (d = c))))) }
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions.resident](BorrowedChunks.definitions.md#def-ccebc2bca7c844ea)
- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ChunkExchange.Conditions.mk](BorrowedChunks.definitions.md#def-e22f45959df329eb)
- [CodedSorting.Construction.ChunkExchange.Conditions.startup](BorrowedChunks.definitions.md#def-d91509e7fa44f3b2)
- [CodedSorting.Construction.ChunkExchange.Conditions.block](BorrowedChunks.definitions.md#def-77993e059f0f8156)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ChunkExchange.Conditions.divisible](BorrowedChunks.definitions.md#def-b072f0f5da7600e1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ChunkExchange.Conditions.buffers](BorrowedChunks.definitions.md#def-70c3df6c3ad07499)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`dvd_mul_of_dvd_left`, `Init.Data.List.Lemmas._auxLemma.9`, `HMul.hMul`, `congrArg`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `Nat.instSemigroup`, `List.cons`, `List`, `HPow.hPow`, `List.instMembership`, `Nat`, `True`, `eq_true`, `of_eq_true`, `Or`, `instHPow`, `or_true`, `Eq`, `Eq.trans`, `instHMul`

<a id="def-021550a3e75cde97"></a>
## `CodedSorting.Construction.ChunkExchange.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L132)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (cutoff : ℕ) →
    (cs : List CodedSorting.Construction.ArbitraryCalls.Call) →
      (P G S : ℕ) → 0 < G → 0 < S → CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P → ℕ
```

**定义**

```lean
fun q cutoff cs P G S _hG _hS _h =>
  CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
    (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w))
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-e43a7871cce415f5"></a>
## `CodedSorting.Construction.ChunkExchange.oneCall`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L137)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  CodedSorting.Construction.ArbitraryCalls.Call →
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → CodedSorting.Construction.ExchangeInterface.Call
```

**定义**

```lean
fun q c P G S source buffer limit =>
  { fieldWidth := c.width, prefixCount := P, gap := G, suffix := S * q.w, source := source, buffer := buffer,
    limit := limit }
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.mk](../Bounds/ExchangeInterface.definitions.md#def-88d363c434138873)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-6a15cca64e14a596"></a>
## `CodedSorting.Construction.ChunkExchange.one_shape`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean#L141)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c : CodedSorting.Construction.ArbitraryCalls.Call)
  (P G S source buffer limit : ℕ),
  0 < c.baseWidth →
    0 < G →
      0 < S →
        CodedSorting.Construction.streamCount ^ c.depth ∣ P →
          CodedSorting.Construction.RecursiveCallShape.ShapeDepth q c.depth
            (CodedSorting.Construction.ChunkExchange.oneCall q c P G S source buffer limit)
```

**继续展开**

- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](../Recursion/CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ChunkExchange.oneCall](BorrowedChunks.definitions.md#def-e43a7871cce415f5)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Dvd.dvd`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat.instDvd`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-a6c93425fe359947"></a>
## `_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L148)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff : ℕ) →
      (c : CodedSorting.Construction.ArbitraryCalls.Call) →
        (P G S source buffer limit : ℕ) →
          0 < G →
            0 < S →
              cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
                CodedSorting.CommonPermutationPairs.width q ≤ cutoff →
                  CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
                      CodedSorting.CommonExchangeLeaf.bankWords q →
                    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
                          CodedSorting.CommonPermutationPairs.width q ≤
                        cutoff + CodedSorting.CommonPermutationPairs.width q →
                      CodedSorting.Construction.streamCount ^ c.depth ∣ P →
                        source +
                              CodedSorting.CommonPermutationPairs.count q
                                (CodedSorting.CommonChunkLayout.Volume P
                                  (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G (S * q.w)) ≤
                            buffer →
                          buffer +
                                CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
                                  (CodedSorting.CommonChunkLayout.Volume P
                                    (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G (S * q.w)) ≤
                              limit →
                            limit ≤ q.N ^ q.exponent →
                              { p //
                                p.charge ≤
                                  CodedSorting.Construction.ExchangeInterface.costBound
                                    (24 * CodedSorting.Construction.streamCount + 36 +
                                      CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
                                    (CodedSorting.CommonPermutationPairs.width q) cutoff c.depth
                                    (CodedSorting.CommonChunkLayout.Volume P
                                      (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G (S * q.w)) }
```

**定义**

```lean
fun q reader cutoff c P G S source buffer limit hG hS hresident hblock hfit hstartup hdiv hs hw hl =>
  if hz : c.baseWidth = 0 then
    let_fun he := ⋯;
    let p := CodedSorting.Construction.ChunkCompose.emptyProgram q P G S source buffer limit;
    ⋯.mpr ⟨p, ⋯⟩
  else
    let_fun hb := ⋯;
    let call := CodedSorting.Construction.ChunkExchange.oneCall q c P G S source buffer limit;
    let hp := ⋯;
    let_fun hshape := ⋯;
    let_fun hwidth := ⋯;
    let p :=
      CodedSorting.Construction.RecursiveWorkspaceProgram.program q reader cutoff c.baseWidth c.depth call hp hblock
        hshape hwidth hs hw hl;
    ⟨p, ⋯⟩
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](../Recursion/CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_16](BorrowedChunks.definitions.md#def-bbe578efe0e946a9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters](../Recursion/Workspace.definitions.md#def-ccdb4faa2250afa6)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.program](../Recursion/Resources.definitions.md#def-ecb93c574fcd450c)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_13](BorrowedChunks.definitions.md#def-9043f8fca9b400c6)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.ChunkExchange.oneCall](BorrowedChunks.definitions.md#def-e43a7871cce415f5)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_11](BorrowedChunks.definitions.md#def-d0e7bae02b2e7ff4)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_15](BorrowedChunks.definitions.md#def-19b89506a5deb054)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ChunkExchange.one_shape](BorrowedChunks.definitions.md#def-6a15cca64e14a596)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_10](BorrowedChunks.definitions.md#def-1c76c93c36e0a667)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_14](BorrowedChunks.definitions.md#def-9a5200b672b22c3c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_12](BorrowedChunks.definitions.md#def-2df922dd150bceaa)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Construction.ChunkCompose.emptyProgram](BorrowedChunks.definitions.md#def-0cc500b7f150481a)

**基础库名称**

`Eq.mpr`, `Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `dite`, `Subtype.mk`, `instHAdd`, `HPow.hPow`, `Nat.instDvd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instDecidableEqNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Not`, `letFun`, `instHMul`

<a id="def-274ab2475a9b08b3"></a>
## `CodedSorting.Construction.ChunkExchange.oneProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L179)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff : ℕ) →
      (c : CodedSorting.Construction.ArbitraryCalls.Call) →
        (P G S source buffer limit : ℕ) →
          0 < G →
            0 < S →
              cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
                CodedSorting.CommonPermutationPairs.width q ≤ cutoff →
                  CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
                      CodedSorting.CommonExchangeLeaf.bankWords q →
                    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
                          CodedSorting.CommonPermutationPairs.width q ≤
                        cutoff + CodedSorting.CommonPermutationPairs.width q →
                      CodedSorting.Construction.streamCount ^ c.depth ∣ P →
                        source +
                              CodedSorting.CommonPermutationPairs.count q
                                (CodedSorting.CommonChunkLayout.Volume P
                                  (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G (S * q.w)) ≤
                            buffer →
                          buffer +
                                CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
                                  (CodedSorting.CommonChunkLayout.Volume P
                                    (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G (S * q.w)) ≤
                              limit →
                            limit ≤ q.N ^ q.exponent →
                              CodedSorting.CommonFinitePermutation.Program q
                                (CodedSorting.CommonChunkLayout.Volume P
                                  (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G (S * q.w))
                                source buffer limit
                                (CodedSorting.CommonChunkLayout.swap P
                                  (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G (S * q.w))
```

**定义**

```lean
fun q reader cutoff c P G S source buffer limit hG hS hresident hblock hfit hstartup hdiv hs hw hl =>
  let t :=
    CodedSorting.Construction.ChunkExchange.generatedOne✝ q reader cutoff c P G S source buffer limit hG hS hresident
      hblock hfit hstartup hdiv hs hw hl;
  let __src := ↑t;
  { instructions := __src.instructions,
    charge :=
      CodedSorting.Construction.ExchangeInterface.costBound
        (24 * CodedSorting.Construction.streamCount + 36 +
          CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
        (CodedSorting.CommonPermutationPairs.width q) cutoff c.depth
        (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
          (S * q.w)),
    correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.ChunkExchange.oneProgram._proof_20](BorrowedChunks.definitions.md#def-4e9fb164025943e1)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ChunkExchange.oneProgram._proof_21](BorrowedChunks.definitions.md#def-c55d667eba0af2e9)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne](BorrowedChunks.definitions.md#def-a6c93425fe359947)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ChunkExchange.oneProgram._proof_19](BorrowedChunks.definitions.md#def-263e84015aaf930a)
- [CodedSorting.Construction.ChunkExchange.oneProgram._proof_18](BorrowedChunks.definitions.md#def-cfcf83ed87cf6e40)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ChunkExchange.oneProgram._proof_17](BorrowedChunks.definitions.md#def-205f86bce0bd3910)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `Nat.instDvd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `instHMul`

<a id="def-480dcc7effcef751"></a>
## `CodedSorting.Construction.ChunkExchange.generated`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L241)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff : ℕ) →
      (cs : List CodedSorting.Construction.ArbitraryCalls.Call) →
        (P G S source buffer limit : ℕ) →
          (hG : 0 < G) →
            (hS : 0 < S) →
              (h : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P) →
                source +
                      CodedSorting.CommonPermutationPairs.count q
                        (CodedSorting.CommonChunkLayout.Volume P
                          (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w)) ≤
                    buffer →
                  buffer + CodedSorting.Construction.ChunkExchange.space q cutoff cs P G S hG hS h ≤ limit →
                    limit ≤ q.N ^ q.exponent →
                      { p //
                        p.charge =
                          CodedSorting.Construction.ArbitraryCost.totalBound cutoff
                            (CodedSorting.CommonPermutationPairs.width q) cs
                            (CodedSorting.CommonChunkLayout.Volume P
                              (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w)) }
```

**定义**

```lean
fun q reader cutoff cs P G S source buffer limit hG hS h hs hw hl =>
  List.rec (motive := fun cs =>
    (P G S : ℕ) →
      (hG : 0 < G) →
        (hS : 0 < S) →
          (h : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P) →
            source +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
                      (S * q.w)) ≤
                buffer →
              buffer + CodedSorting.Construction.ChunkExchange.space q cutoff cs P G S hG hS h ≤ limit →
                { p //
                  p.charge =
                    CodedSorting.Construction.ArbitraryCost.totalBound cutoff
                      (CodedSorting.CommonPermutationPairs.width q) cs
                      (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
                        G (S * q.w)) })
    (fun P G S hG hS h hs hw => ⟨CodedSorting.Construction.ChunkCompose.emptyProgram q P G S source buffer limit, ⋯⟩)
    (fun c cs ih P G S hG hS h hs hw =>
      let_fun hs₁ := ⋯;
      let_fun hs₂ := ⋯;
      let_fun hw₁ := ⋯;
      let_fun hw₂ := ⋯;
      let p₁ :=
        CodedSorting.Construction.ChunkExchange.oneProgram q reader cutoff c P
          (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * G)
          (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * S) source buffer limit ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ hs₁ hw₁ hl;
      let p₂ :=
        ih (P * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
          (G * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) S ⋯ hS ⋯ hs₂ hw₂;
      ⟨CodedSorting.Construction.ChunkCompose.combine q P
          (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
          (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G S source buffer limit p₁ ↑p₂,
        ⋯⟩)
    cs P G S hG hS h hs hw
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.generated._proof_29](BorrowedChunks.definitions.md#def-d0ac37c8f7369376)
- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.ChunkExchange.generated._proof_27](BorrowedChunks.definitions.md#def-77fa5d5b7dbe2b46)
- [CodedSorting.Construction.ChunkCompose.combine](BorrowedChunks.definitions.md#def-1f6373641f597a68)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ChunkExchange.generated._proof_23](BorrowedChunks.definitions.md#def-cf246785e28b709a)
- [CodedSorting.Construction.ChunkExchange.generated._proof_33](BorrowedChunks.definitions.md#def-d10cd4a2a97c66a9)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.Construction.ChunkExchange.Conditions.tail](BorrowedChunks.definitions.md#def-9755ef9d6158e0af)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ChunkExchange.generated._proof_34](BorrowedChunks.definitions.md#def-0544c761bdd4c90d)
- [CodedSorting.Construction.ChunkExchange.oneProgram](BorrowedChunks.definitions.md#def-274ab2475a9b08b3)
- [CodedSorting.Construction.ArbitraryCost.totalBound](../Fields/LogRate.definitions.md#def-499e7e2cf6508472)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ChunkExchange.generated._proof_32](BorrowedChunks.definitions.md#def-a991cc5cfe0ce0e5)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ChunkExchange.generated._proof_26](BorrowedChunks.definitions.md#def-3e2be4792d7e47a4)
- [CodedSorting.Construction.ChunkExchange.generated._proof_24](BorrowedChunks.definitions.md#def-6d1aeabca4a314a8)
- [CodedSorting.Construction.ChunkExchange.generated._proof_31](BorrowedChunks.definitions.md#def-08209f4831aa4716)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.Construction.ChunkExchange.generated._proof_25](BorrowedChunks.definitions.md#def-f4c1aa7064904443)
- [CodedSorting.Construction.ChunkExchange.generated._proof_30](BorrowedChunks.definitions.md#def-5598f757d09e4f8b)
- [CodedSorting.Construction.ChunkExchange.generated._proof_22](BorrowedChunks.definitions.md#def-bc0b4c26b2141946)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ChunkExchange.generated._proof_28](BorrowedChunks.definitions.md#def-7f5f3b3a6696f2c2)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Construction.ChunkCompose.emptyProgram](BorrowedChunks.definitions.md#def-0cc500b7f150481a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Subtype`, `instMulNat`, `instOfNatNat`, `List.rec`, `LE.le`, `instLENat`, `List.cons`, `Subtype.mk`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `letFun`, `instHMul`, `List.nil`

<a id="def-73c46e787b2eb032"></a>
## `CodedSorting.Construction.ChunkExchange.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L282)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff : ℕ) →
      (cs : List CodedSorting.Construction.ArbitraryCalls.Call) →
        (P G S source buffer limit : ℕ) →
          (hG : 0 < G) →
            (hS : 0 < S) →
              (h : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P) →
                source +
                      CodedSorting.CommonPermutationPairs.count q
                        (CodedSorting.CommonChunkLayout.Volume P
                          (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w)) ≤
                    buffer →
                  buffer + CodedSorting.Construction.ChunkExchange.space q cutoff cs P G S hG hS h ≤ limit →
                    limit ≤ q.N ^ q.exponent →
                      CodedSorting.CommonFinitePermutation.Program q
                        (CodedSorting.CommonChunkLayout.Volume P
                          (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w))
                        source buffer limit
                        (CodedSorting.CommonChunkLayout.swap P (CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
                          G (S * q.w))
```

**定义**

```lean
fun q reader cutoff cs P G S source buffer limit hG hS h hs hw hl =>
  ↑(CodedSorting.Construction.ChunkExchange.generated q reader cutoff cs P G S source buffer limit hG hS h hs hw hl)
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ArbitraryCost.totalBound](../Fields/LogRate.definitions.md#def-499e7e2cf6508472)
- [CodedSorting.Construction.ChunkExchange.generated](BorrowedChunks.definitions.md#def-480dcc7effcef751)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `instHMul`

<a id="def-c51ddc981e74391d"></a>
## `CodedSorting.Construction.PaddedChunks.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L331)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (cutoff : ℕ) →
    (cs : List CodedSorting.Construction.ArbitraryCalls.Call) →
      (P' G S : ℕ) → 0 < G → 0 < S → CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P' → ℕ
```

**定义**

```lean
fun q cutoff cs P' G S hG hS hc =>
  CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
          (S * q.w)) +
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
          (S * q.w)) +
    CodedSorting.Construction.ChunkExchange.space q cutoff cs P' G S hG hS hc
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-7b5ca3125edacd25"></a>
## `CodedSorting.Construction.PaddedChunks.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L358)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff : ℕ) →
      (cs : List CodedSorting.Construction.ArbitraryCalls.Call) →
        (P P' G S source buffer limit : ℕ) →
          (hG : 0 < G) →
            (hS : 0 < S) →
              P ≤ P' →
                (hc : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P') →
                  source +
                        CodedSorting.CommonPermutationPairs.count q
                          (CodedSorting.CommonChunkLayout.Volume P
                            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w)) ≤
                      buffer →
                    buffer + CodedSorting.Construction.PaddedChunks.space q cutoff cs P' G S hG hS hc ≤ limit →
                      limit ≤ q.N ^ q.exponent →
                        CodedSorting.CommonFinitePermutation.Program q
                          (CodedSorting.CommonChunkLayout.Volume P
                            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w))
                          source buffer limit
                          (CodedSorting.CommonChunkLayout.swap P
                            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w))
```

**定义**

```lean
fun q reader cutoff cs P P' G S source buffer limit hG hS hp hc hs hw hl =>
  let C :=
    CodedSorting.CommonPermutationPairs.count q
      (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w));
  let_fun hchild := ⋯;
  let child :=
    CodedSorting.Construction.ChunkExchange.program q reader cutoff cs P' G S (buffer + C) (buffer + C + C) limit hG hS
      hc ⋯ hchild hl;
  CodedSorting.CommonPaddedPermutation.prefixProgram q reader P P'
    (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w) hp source buffer limit child hs ⋯ hl
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.PaddedChunks.program._proof_37](BorrowedChunks.definitions.md#def-4f6f6c2ddb09391c)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ChunkExchange.program](BorrowedChunks.definitions.md#def-73c46e787b2eb032)
- [CodedSorting.Construction.PaddedChunks.program._proof_36](BorrowedChunks.definitions.md#def-992e8d8a8e5aa0ca)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonPaddedPermutation.prefixProgram](../Framework/Memory/PaddedChunks.definitions.md#def-aec2c3eefc2875d7)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.PaddedChunks.space](BorrowedChunks.definitions.md#def-c51ddc981e74391d)
- [CodedSorting.Construction.PaddedChunks.program._proof_38](BorrowedChunks.definitions.md#def-29f36de9f416779a)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `letFun`, `instHMul`

<a id="def-fe66073119deea1a"></a>
## `CodedSorting.Construction.BorrowedChunks.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L415)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (cutoff : ℕ) →
    (cs : List CodedSorting.Construction.ArbitraryCalls.Call) →
      ℕ → ℕ → (P' G S : ℕ) → 0 < G → 0 < S → CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P' → ℕ
```

**定义**

```lean
fun q cutoff cs O ρ P' G S hG hS hc =>
  CodedSorting.CommonPermutationPairs.count q
      (CodedSorting.CommonChunkLayout.Volume O
        (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
          CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
        G (S * q.w)) +
    CodedSorting.Construction.PaddedChunks.space q cutoff cs P' G S hG hS hc
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.PaddedChunks.space](BorrowedChunks.definitions.md#def-c51ddc981e74391d)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-4c3b7d939f1696ba"></a>
## `CodedSorting.Construction.BorrowedChunks.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BorrowedChunks.lean#L430)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff : ℕ) →
      (cs : List CodedSorting.Construction.ArbitraryCalls.Call) →
        (O ρ P' G S source buffer limit : ℕ) →
          (hG : 0 < G) →
            (hS : 0 < S) →
              O *
                    (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
                      CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ) ≤
                  P' →
                (hc : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P') →
                  source +
                        CodedSorting.CommonPermutationPairs.count q
                          (CodedSorting.CommonChunkLayout.Volume O
                            (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
                              CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
                            G (S * q.w)) ≤
                      buffer →
                    buffer + CodedSorting.Construction.BorrowedChunks.space q cutoff cs O ρ P' G S hG hS hc ≤ limit →
                      limit ≤ q.N ^ q.exponent →
                        CodedSorting.CommonFinitePermutation.Program q
                          (CodedSorting.CommonChunkLayout.Volume O
                            (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
                              CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
                            G (S * q.w))
                          source buffer limit
                          (CodedSorting.CommonChunkLayout.swap O
                            (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
                              CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
                            G (S * q.w))
```

**定义**

```lean
fun q reader cutoff cs O ρ P' G S source buffer limit hG hS hp hc hs hw hl =>
  let H := CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ;
  let_fun hsinner := ⋯;
  let_fun hwpadded := ⋯;
  let_fun hwborrow := ⋯;
  let p :=
    CodedSorting.Construction.PaddedChunks.program q reader cutoff cs (O * (H * H)) P' G S source buffer limit hG hS hp
      hc hsinner hwpadded hl;
  CodedSorting.CommonBorrowedCore.program q reader O CodedSorting.Construction.ExchangeSpecialization.radix ρ
    (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w) source buffer limit p hs hwborrow hl
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.BorrowedChunks.program._proof_44](BorrowedChunks.definitions.md#def-2922797f0f1dd7ee)
- [CodedSorting.Construction.BorrowedChunks.program._proof_42](BorrowedChunks.definitions.md#def-1f688187e97eac16)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBorrowedCore.program](../Framework/BorrowedMemory/Machine.definitions.md#def-354b0e5ca8f5d4da)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.PaddedChunks.space](BorrowedChunks.definitions.md#def-c51ddc981e74391d)
- [CodedSorting.Construction.BorrowedChunks.space](BorrowedChunks.definitions.md#def-fe66073119deea1a)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.BorrowedChunks.program._proof_43](BorrowedChunks.definitions.md#def-d0c9b31af482402d)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.PaddedChunks.program](BorrowedChunks.definitions.md#def-7b5ca3125edacd25)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `letFun`, `instHMul`

<a id="def-1f688187e97eac16"></a>
## `CodedSorting.Construction.BorrowedChunks.program._proof_42`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cs : List CodedSorting.Construction.ArbitraryCalls.Call)
  (O ρ G S source buffer : ℕ),
  source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume O
            (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
              CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
            G (S * q.w)) ≤
      buffer →
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume
            (O *
              (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
                CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ))
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w)) ≤
      buffer
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `instHMul`

<a id="def-d0c9b31af482402d"></a>
## `CodedSorting.Construction.BorrowedChunks.program._proof_43`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (O ρ P' G S : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
      (hc : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P'),
      buffer + CodedSorting.Construction.BorrowedChunks.space q cutoff cs O ρ P' G S hG hS hc ≤ limit →
        buffer + CodedSorting.Construction.PaddedChunks.space q cutoff cs P' G S hG hS hc ≤ limit
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.PaddedChunks.space](BorrowedChunks.definitions.md#def-c51ddc981e74391d)
- [CodedSorting.Construction.BorrowedChunks.space](BorrowedChunks.definitions.md#def-fe66073119deea1a)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-2922797f0f1dd7ee"></a>
## `CodedSorting.Construction.BorrowedChunks.program._proof_44`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (O ρ P' G S : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
      (hc : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P'),
      buffer + CodedSorting.Construction.BorrowedChunks.space q cutoff cs O ρ P' G S hG hS hc ≤ limit →
        buffer +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.CommonChunkLayout.Volume O
                (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
                  CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
                G (S * q.w)) ≤
          limit
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.BorrowedChunks.space](BorrowedChunks.definitions.md#def-fe66073119deea1a)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-c39f487dc51b4730"></a>
## `CodedSorting.Construction.ChunkCompose.combine._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (P Q R G S source buffer limit : ℕ)
  (p₁ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q (R * G) (R * S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap P Q (R * G) (R * S * q.w)))
  (p₂ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume (P * Q) R (G * Q) (S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap (P * Q) R (G * Q) (S * q.w)))
  (s : CodedSorting.CommonLeafProgram.Machine q)
  (y : Fin (CodedSorting.CommonChunkLayout.Volume P (Q * R) G (S * q.w))),
  CodedSorting.CommonPermutationPairs.readBit q
      (CodedSorting.CommonStaticSchedule.executeRaw q (p₁.instructions ++ p₂.instructions) s).1.disk source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q s.disk source
      ↑((CodedSorting.CommonChunkLayout.swap P (Q * R) G (S * q.w)) y)
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `Fin.val`, `Prod.fst`, `instHAppendOfAppend`, `List`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `List.instAppend`, `Fin`, `Eq`, `DFunLike.coe`, `HAppend.hAppend`, `instHMul`

<a id="def-6f69ec5b1d8a9961"></a>
## `CodedSorting.Construction.ChunkCompose.combine._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (P Q R G S source buffer limit : ℕ)
  (p₁ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q (R * G) (R * S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap P Q (R * G) (R * S * q.w)))
  (p₂ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume (P * Q) R (G * Q) (S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap (P * Q) R (G * Q) (S * q.w)))
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨
      source +
          CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P (Q * R) G (S * q.w)) ≤
        ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q (p₁.instructions ++ p₂.instructions) s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAppendOfAppend`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `List.instAppend`, `Fin`, `Eq`, `HAppend.hAppend`, `instHMul`

<a id="def-0a25c30dc169502d"></a>
## `CodedSorting.Construction.ChunkCompose.combine._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (P Q R G S source buffer limit : ℕ)
  (p₁ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q (R * G) (R * S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap P Q (R * G) (R * S * q.w)))
  (p₂ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume (P * Q) R (G * Q) (S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap (P * Q) R (G * Q) (S * q.w))),
  ∀ i ∈ p₁.instructions ++ p₂.instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`HMul.hMul`, `Membership.mem`, `instMulNat`, `instHAppendOfAppend`, `List`, `List.instMembership`, `Nat`, `List.instAppend`, `HAppend.hAppend`, `instHMul`

<a id="def-de529d553c31f68c"></a>
## `CodedSorting.Construction.ChunkCompose.combine._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (P Q R G S source buffer limit : ℕ)
  (p₁ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q (R * G) (R * S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap P Q (R * G) (R * S * q.w)))
  (p₂ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume (P * Q) R (G * Q) (S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap (P * Q) R (G * Q) (S * q.w))),
  CodedSorting.CommonStaticSchedule.cost q (p₁.instructions ++ p₂.instructions) ≤ p₁.charge + p₂.charge
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `HAppend.hAppend`, `instHMul`

<a id="def-7a5239ea9dfae052"></a>
## `CodedSorting.Construction.ChunkCompose.combine._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (P Q R G S source buffer limit : ℕ)
  (p₁ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q (R * G) (R * S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap P Q (R * G) (R * S * q.w)))
  (p₂ :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume (P * Q) R (G * Q) (S * q.w))
      source buffer limit (CodedSorting.CommonChunkLayout.swap (P * Q) R (G * Q) (S * q.w))),
  (p₁.instructions ++ p₂.instructions).length ≤ p₁.charge + p₂.charge
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `List.length`, `HAppend.hAppend`, `instHMul`

<a id="def-07b3c888c51eb5f6"></a>
## `CodedSorting.Construction.ChunkCompose.emptyProgram._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (P G S source : ℕ)
  (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin (CodedSorting.CommonChunkLayout.Volume P 1 G (S * q.w))),
  CodedSorting.CommonPermutationPairs.readBit q (CodedSorting.CommonStaticSchedule.executeRaw q [] s).1.disk source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q s.disk source
      ↑((CodedSorting.CommonChunkLayout.swap P 1 G (S * q.w)) y)
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`, `List.nil`

<a id="def-e60c47085fb96f56"></a>
## `CodedSorting.Construction.ChunkCompose.emptyProgram._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (P G S source buffer limit : ℕ)
  (x : CodedSorting.CommonLeafProgram.Machine q) (x_1 : Fin (q.N ^ q.exponent)),
  ↑x_1 < source ∨
      source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P 1 G (S * q.w)) ≤
        ↑x_1 →
    ↑x_1 < buffer ∨ limit ≤ ↑x_1 →
      (CodedSorting.CommonStaticSchedule.executeRaw q [] x).1.disk x_1 =
        (CodedSorting.CommonStaticSchedule.executeRaw q [] x).1.disk x_1
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`, `List.nil`

<a id="def-74391b5646a893ea"></a>
## `CodedSorting.Construction.ChunkCompose.emptyProgram._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ∀ a ∈ [], CodedSorting.CommonStaticSchedule.RespectsPC q a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `List.nil`

<a id="def-a1cb493d796040f2"></a>
## `CodedSorting.Construction.ChunkCompose.emptyProgram._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
0 ≤ 0
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-bc0b4c26b2141946"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_22`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (source buffer limit P G S : ℕ),
  (CodedSorting.Construction.ChunkCompose.emptyProgram q P G S source buffer limit).charge =
    (CodedSorting.Construction.ChunkCompose.emptyProgram q P G S source buffer limit).charge
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ChunkCompose.emptyProgram](BorrowedChunks.definitions.md#def-0cc500b7f150481a)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`, `List.nil`

<a id="def-cf246785e28b709a"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_23`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (source buffer : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call)
  (P G S : ℕ),
  source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ArbitraryCalls.fieldCount (c :: cs)) G
            (S * q.w)) ≤
      buffer →
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * G)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * S * q.w)) ≤
      buffer
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `instHMul`

<a id="def-6d1aeabca4a314a8"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_24`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (source buffer : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call)
  (P G S : ℕ),
  source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ArbitraryCalls.fieldCount (c :: cs)) G
            (S * q.w)) ≤
      buffer →
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume (P * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
            (G * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) (S * q.w)) ≤
      buffer
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `instHMul`

<a id="def-f4c1aa7064904443"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_25`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff buffer limit : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call)
  (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) (h : CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P),
  buffer + CodedSorting.Construction.ChunkExchange.space q cutoff (c :: cs) P G S hG hS h ≤ limit →
    buffer +
        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * G)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * S * q.w)) ≤
      limit
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-3e2be4792d7e47a4"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_26`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (c : CodedSorting.Construction.ArbitraryCalls.Call) (G : ℕ),
  0 < G → G * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width > 0
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `GT.gt`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-77fa5d5b7dbe2b46"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_27`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff buffer limit : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call)
  (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) (h : CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P),
  buffer + CodedSorting.Construction.ChunkExchange.space q cutoff (c :: cs) P G S hG hS h ≤ limit →
    buffer +
        CodedSorting.Construction.ChunkExchange.space q cutoff cs
          (P * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
          (G * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) S ⋯ hS ⋯ ≤
      limit
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ChunkExchange.Conditions.tail](BorrowedChunks.definitions.md#def-9755ef9d6158e0af)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ChunkExchange.generated._proof_26](BorrowedChunks.definitions.md#def-3e2be4792d7e47a4)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-7f5f3b3a6696f2c2"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_28`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (G : ℕ),
  0 < G → CodedSorting.Construction.ArbitraryCalls.fieldCount cs * G > 0
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `GT.gt`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-d0ac37c8f7369376"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_29`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (P : ℕ),
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P →
    cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`LE.le`, `instLENat`, `List.cons`, `List`, `Nat`

<a id="def-5598f757d09e4f8b"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_30`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (P : ℕ),
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P →
    CodedSorting.CommonPermutationPairs.width q ≤ cutoff
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`LE.le`, `instLENat`, `List.cons`, `List`, `Nat`

<a id="def-08209f4831aa4716"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_31`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (P : ℕ),
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P →
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `Nat`, `instHMul`

<a id="def-a991cc5cfe0ce0e5"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_32`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (P : ℕ),
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P →
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
        CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-d10cd4a2a97c66a9"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_33`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (P : ℕ),
  CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P →
    CodedSorting.Construction.streamCount ^ c.depth ∣ P
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Dvd.dvd`, `Nat.instMonoid`, `Monoid.toNatPow`, `List.cons`, `List`, `HPow.hPow`, `Nat.instDvd`, `Nat`, `instHPow`

<a id="def-0544c761bdd4c90d"></a>
## `CodedSorting.Construction.ChunkExchange.generated._proof_34`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (cutoff source buffer limit : ℕ) (hl : limit ≤ q.N ^ q.exponent) (c : CodedSorting.Construction.ArbitraryCalls.Call)
  (cs : List CodedSorting.Construction.ArbitraryCalls.Call)
  (ih :
    (P G S : ℕ) →
      (hG : 0 < G) →
        (hS : 0 < S) →
          (h : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P) →
            source +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
                      (S * q.w)) ≤
                buffer →
              buffer + CodedSorting.Construction.ChunkExchange.space q cutoff cs P G S hG hS h ≤ limit →
                { p //
                  p.charge =
                    CodedSorting.Construction.ArbitraryCost.totalBound cutoff
                      (CodedSorting.CommonPermutationPairs.width q) cs
                      (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
                        G (S * q.w)) })
  (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) (h : CodedSorting.Construction.ChunkExchange.Conditions q cutoff (c :: cs) P)
  (hs₁ :
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * G)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * S * q.w)) ≤
      buffer)
  (hs₂ :
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume (P * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
            (G * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) (S * q.w)) ≤
      buffer)
  (hw₁ :
    buffer +
        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * G)
            (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * S * q.w)) ≤
      limit)
  (hw₂ :
    buffer +
        CodedSorting.Construction.ChunkExchange.space q cutoff cs
          (P * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
          (G * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) S ⋯ hS ⋯ ≤
      limit),
  (CodedSorting.Construction.ChunkCompose.combine q P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
        (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G S source buffer limit
        (CodedSorting.Construction.ChunkExchange.oneProgram q reader cutoff c P
          (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * G)
          (CodedSorting.Construction.ArbitraryCalls.fieldCount cs * S) source buffer limit ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ hs₁ hw₁ hl)
        ↑(ih (P * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
            (G * CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) S ⋯ hS ⋯ hs₂ hw₂)).charge =
    CodedSorting.Construction.ArbitraryCost.totalBound cutoff (CodedSorting.CommonPermutationPairs.width q) (c :: cs)
      (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ArbitraryCalls.fieldCount (c :: cs)) G
        (S * q.w))
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.generated._proof_29](BorrowedChunks.definitions.md#def-d0ac37c8f7369376)
- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.ChunkCompose.combine](BorrowedChunks.definitions.md#def-1f6373641f597a68)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.ChunkExchange.generated._proof_33](BorrowedChunks.definitions.md#def-d10cd4a2a97c66a9)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.Construction.ChunkExchange.Conditions.tail](BorrowedChunks.definitions.md#def-9755ef9d6158e0af)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ChunkExchange.oneProgram](BorrowedChunks.definitions.md#def-274ab2475a9b08b3)
- [CodedSorting.Construction.ArbitraryCost.totalBound](../Fields/LogRate.definitions.md#def-499e7e2cf6508472)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ChunkExchange.generated._proof_32](BorrowedChunks.definitions.md#def-a991cc5cfe0ce0e5)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ChunkExchange.generated._proof_26](BorrowedChunks.definitions.md#def-3e2be4792d7e47a4)
- [CodedSorting.Construction.ChunkExchange.generated._proof_31](BorrowedChunks.definitions.md#def-08209f4831aa4716)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.Construction.ChunkExchange.generated._proof_30](BorrowedChunks.definitions.md#def-5598f757d09e4f8b)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ChunkExchange.generated._proof_28](BorrowedChunks.definitions.md#def-7f5f3b3a6696f2c2)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List.cons`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `instHMul`

<a id="def-205f86bce0bd3910"></a>
## `CodedSorting.Construction.ChunkExchange.oneProgram._proof_17`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (P G S source buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
  (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
  (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
  (hfit :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q)
  (hstartup :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
        CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q)
  (hdiv : CodedSorting.Construction.streamCount ^ c.depth ∣ P)
  (hs :
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      buffer)
  (hw :
    buffer +
        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q)
  (y :
    Fin
      (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
        (S * q.w))),
  CodedSorting.CommonPermutationPairs.readBit q
      (CodedSorting.CommonStaticSchedule.executeRaw q
            (↑(CodedSorting.Construction.ChunkExchange.generatedOne✝ q reader cutoff c P G S source buffer limit hG hS
                  hresident hblock hfit hstartup hdiv hs hw hl)).instructions
            s).1.disk
      source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q s.disk source
      ↑((CodedSorting.CommonChunkLayout.swap P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w))
          y)
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne](BorrowedChunks.definitions.md#def-a6c93425fe359947)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `Nat.instDvd`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-cfcf83ed87cf6e40"></a>
## `CodedSorting.Construction.ChunkExchange.oneProgram._proof_18`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (P G S source buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
  (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
  (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
  (hfit :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q)
  (hstartup :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
        CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q)
  (hdiv : CodedSorting.Construction.streamCount ^ c.depth ∣ P)
  (hs :
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      buffer)
  (hw :
    buffer +
        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨
      source +
          CodedSorting.CommonPermutationPairs.count q
            (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
              G (S * q.w)) ≤
        ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (↑(CodedSorting.Construction.ChunkExchange.generatedOne✝ q reader cutoff c P G S source buffer limit hG
                      hS hresident hblock hfit hstartup hdiv hs hw hl)).instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne](BorrowedChunks.definitions.md#def-a6c93425fe359947)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `Nat.instDvd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `instHMul`

<a id="def-263e84015aaf930a"></a>
## `CodedSorting.Construction.ChunkExchange.oneProgram._proof_19`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (P G S source buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
  (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
  (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
  (hfit :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q)
  (hstartup :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
        CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q)
  (hdiv : CodedSorting.Construction.streamCount ^ c.depth ∣ P)
  (hs :
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      buffer)
  (hw :
    buffer +
        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent),
  ∀
    i ∈
      (↑(CodedSorting.Construction.ChunkExchange.generatedOne✝ q reader cutoff c P G S source buffer limit hG hS
            hresident hblock hfit hstartup hdiv hs hw hl)).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne](BorrowedChunks.definitions.md#def-a6c93425fe359947)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `Nat.instDvd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `instHMul`

<a id="def-4e9fb164025943e1"></a>
## `CodedSorting.Construction.ChunkExchange.oneProgram._proof_20`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (P G S source buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
  (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
  (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
  (hfit :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q)
  (hstartup :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
        CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q)
  (hdiv : CodedSorting.Construction.streamCount ^ c.depth ∣ P)
  (hs :
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      buffer)
  (hw :
    buffer +
        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent),
  CodedSorting.CommonStaticSchedule.cost q
      (↑(CodedSorting.Construction.ChunkExchange.generatedOne✝ q reader cutoff c P G S source buffer limit hG hS
            hresident hblock hfit hstartup hdiv hs hw hl)).instructions ≤
    CodedSorting.Construction.ExchangeInterface.costBound
      (24 * CodedSorting.Construction.streamCount + 36 +
        CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
      (CodedSorting.CommonPermutationPairs.width q) cutoff c.depth
      (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
        (S * q.w))
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne](BorrowedChunks.definitions.md#def-a6c93425fe359947)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `Nat.instDvd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `instHMul`

<a id="def-c55d667eba0af2e9"></a>
## `CodedSorting.Construction.ChunkExchange.oneProgram._proof_21`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (P G S source buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
  (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
  (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
  (hfit :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q)
  (hstartup :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
        CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q)
  (hdiv : CodedSorting.Construction.streamCount ^ c.depth ∣ P)
  (hs :
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      buffer)
  (hw :
    buffer +
        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent),
  (↑(CodedSorting.Construction.ChunkExchange.generatedOne✝ q reader cutoff c P G S source buffer limit hG hS hresident
            hblock hfit hstartup hdiv hs hw hl)).instructions.length ≤
    CodedSorting.Construction.ExchangeInterface.costBound
      (24 * CodedSorting.Construction.streamCount + 36 +
        CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
      (CodedSorting.CommonPermutationPairs.width q) cutoff c.depth
      (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
        (S * q.w))
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne](BorrowedChunks.definitions.md#def-a6c93425fe359947)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `Nat.instDvd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `List.length`, `instHMul`

<a id="def-992e8d8a8e5aa0ca"></a>
## `CodedSorting.Construction.PaddedChunks.program._proof_36`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (cs : List CodedSorting.Construction.ArbitraryCalls.Call) (P' G S buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
  (hc : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P'),
  buffer + CodedSorting.Construction.PaddedChunks.space q cutoff cs P' G S hG hS hc ≤ limit →
    buffer +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
                (S * q.w)) +
          CodedSorting.CommonPermutationPairs.count q
            (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
              (S * q.w)) +
        CodedSorting.Construction.ChunkExchange.space q cutoff cs P' G S hG hS hc ≤
      limit
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.PaddedChunks.space](BorrowedChunks.definitions.md#def-c51ddc981e74391d)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-4f6f6c2ddb09391c"></a>
## `CodedSorting.Construction.PaddedChunks.program._proof_37`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cs : List CodedSorting.Construction.ArbitraryCalls.Call)
  (P' G S buffer : ℕ),
  buffer +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
            (S * q.w)) +
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
          (S * q.w)) ≤
    buffer +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
            (S * q.w)) +
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G (S * q.w))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Preorder.toLE`, `instMulNat`, `LE.le`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHMul`

<a id="def-29f36de9f416779a"></a>
## `CodedSorting.Construction.PaddedChunks.program._proof_38`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (cs : List CodedSorting.Construction.ArbitraryCalls.Call),
  ℕ →
    ∀ (P' G S : ℕ),
      ℕ →
        ∀ (buffer limit : ℕ) (hG : 0 < G) (hS : 0 < S)
          (hc : CodedSorting.Construction.ChunkExchange.Conditions q cutoff cs P'),
          buffer +
                    CodedSorting.CommonPermutationPairs.count q
                      (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
                        G (S * q.w)) +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
                      (S * q.w)) +
                CodedSorting.Construction.ChunkExchange.space q cutoff cs P' G S hG hS hc ≤
              limit →
            buffer +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
                      (S * q.w)) +
                CodedSorting.CommonPermutationPairs.count q
                  (CodedSorting.CommonChunkLayout.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G
                    (S * q.w)) ≤
              limit
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](../Fields/LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ChunkExchange.space](BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-1c76c93c36e0a667"></a>
## `_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (c : CodedSorting.Construction.ArbitraryCalls.Call),
  c.baseWidth = 0 →
    CodedSorting.Construction.ExchangeSpecialization.radix ^
        (c.baseWidth * CodedSorting.Construction.ambientDimension ^ c.depth) =
      1
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-d0e7bae02b2e7ff4"></a>
## `_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (P G S source buffer limit : ℕ),
  CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width = 1 →
    { p //
        p.charge ≤
          CodedSorting.Construction.ExchangeInterface.costBound
            (24 * CodedSorting.Construction.streamCount + 36 +
              CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
            (CodedSorting.CommonPermutationPairs.width q) cutoff c.depth
            (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width)
              G (S * q.w)) } =
      { p //
        p.charge ≤
          CodedSorting.Construction.ExchangeInterface.costBound
            (24 * CodedSorting.Construction.streamCount + 36 +
              CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
            (CodedSorting.CommonPermutationPairs.width q) cutoff c.depth
            (CodedSorting.CommonChunkLayout.Volume P 1 G (S * q.w)) }
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-2df922dd150bceaa"></a>
## `_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (P G S : ℕ),
  0 ≤
    CodedSorting.Construction.ExchangeInterface.costBound
      (24 * CodedSorting.Construction.streamCount + 36 +
        CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
      (CodedSorting.CommonPermutationPairs.width q) cutoff c.depth
      (CodedSorting.CommonChunkLayout.Volume P 1 G (S * q.w))
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-9043f8fca9b400c6"></a>
## `_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (c : CodedSorting.Construction.ArbitraryCalls.Call), ¬c.baseWidth = 0 → 0 < c.baseWidth
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Eq`, `Not`

<a id="def-9a5200b672b22c3c"></a>
## `_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call),
  cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
        CodedSorting.CommonExchangeLeaf.bankWords q →
      CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
            CodedSorting.CommonPermutationPairs.width q ≤
          cutoff + CodedSorting.CommonPermutationPairs.width q →
        CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters q cutoff c.baseWidth
```

**继续展开**

- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters](../Recursion/Workspace.definitions.md#def-ccdb4faa2250afa6)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-19b89506a5deb054"></a>
## `_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_15`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (c : CodedSorting.Construction.ArbitraryCalls.Call),
  c.baseWidth * CodedSorting.Construction.ambientDimension ^ c.depth =
    CodedSorting.Construction.ambientDimension ^ c.depth * c.baseWidth
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `HPow.hPow`, `Nat`, `instHPow`, `Eq`, `instHMul`

<a id="def-bbe578efe0e946a9"></a>
## `_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_16`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BorrowedChunks.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
  (c : CodedSorting.Construction.ArbitraryCalls.Call) (P G S source buffer limit : ℕ)
  (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
  (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
  (hfit :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q)
  (hstartup :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets c.baseWidth *
        CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q)
  (hs :
    source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      buffer)
  (hw :
    buffer +
        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width) G
            (S * q.w)) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hshape :
    CodedSorting.Construction.RecursiveCallShape.ShapeDepth q c.depth
      (CodedSorting.Construction.ChunkExchange.oneCall q c P G S source buffer limit))
  (hwidth :
    (CodedSorting.Construction.ChunkExchange.oneCall q c P G S source buffer limit).fieldWidth =
      CodedSorting.Construction.ambientDimension ^ c.depth * c.baseWidth),
  (CodedSorting.Construction.RecursiveWorkspaceProgram.program q reader cutoff c.baseWidth c.depth
        (CodedSorting.Construction.ChunkExchange.oneCall q c P G S source buffer limit) ⋯ hblock hshape hwidth hs hw
        hl).charge ≤
    CodedSorting.Construction.ExchangeInterface.costBound
      (24 * CodedSorting.Construction.streamCount + 36 +
        CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
      (CodedSorting.CommonPermutationPairs.width q) cutoff c.depth
      (CodedSorting.Construction.ExchangeInterface.volume CodedSorting.Construction.ExchangeSpecialization.radix
        (CodedSorting.Construction.ChunkExchange.oneCall q c P G S source buffer limit))
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](../Recursion/CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](../Fields/LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.program](../Recursion/Resources.definitions.md#def-ecb93c574fcd450c)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](../Fields/LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.ChunkExchange.oneCall](BorrowedChunks.definitions.md#def-e43a7871cce415f5)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.Call](../Fields/LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](../Recursion/Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [_private.CodedSorting.Interchange.Chunks.BorrowedChunks.0.CodedSorting.Construction.ChunkExchange.generatedOne._proof_14](BorrowedChunks.definitions.md#def-9a5200b672b22c3c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](../Fields/LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`
