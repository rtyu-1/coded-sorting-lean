# Machine 的定义

[源码](Machine.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-6a2ac9479d29d19e"></a>
## `CodedSorting.Construction.ArbitraryConditions.buckets_mono`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean#L12)

**类型**

```lean
∀ {a b : ℕ},
  a ≤ b →
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets a ≤
      CodedSorting.Construction.RecursiveWorkspaceBudget.buckets b
```

**继续展开**

- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-dd9eaf09b277dbe2"></a>
## `CodedSorting.Construction.ArbitraryConditions.baseConditions`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L16)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff base e P : ℕ),
  0 < base →
    cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
      CodedSorting.CommonPermutationPairs.width q ≤ cutoff →
        CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
            CodedSorting.CommonExchangeLeaf.bankWords q →
          CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base *
                CodedSorting.CommonPermutationPairs.width q ≤
              cutoff + CodedSorting.CommonPermutationPairs.width q →
            CodedSorting.Construction.ChunkExchange.Conditions q cutoff
              (CodedSorting.Construction.ArbitraryCalls.baseCalls base e) P
```

**定义**

```lean
fun q cutoff base e P hb hresident hblock hfit hstartup =>
  { resident := hresident, block := hblock,
    divisible := CodedSorting.Construction.ArbitraryCalls.baseCalls_fit P base e,
    buffers := fun c hc =>
      LE.le.trans
        (Nat.mul_le_mul_right q.block
          (CodedSorting.Construction.ArbitraryConditions.buckets_mono
            (CodedSorting.Construction.ArbitraryCalls.baseCalls_base base e hb c hc)))
        hfit,
    startup := fun c hc =>
      LE.le.trans
        (Nat.mul_le_mul_right (CodedSorting.CommonPermutationPairs.width q)
          (CodedSorting.Construction.ArbitraryConditions.buckets_mono
            (CodedSorting.Construction.ArbitraryCalls.baseCalls_base base e hb c hc)))
        hstartup }
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](../Chunks/BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.Construction.ChunkExchange.Conditions.mk](../Chunks/BorrowedChunks.definitions.md#def-e22f45959df329eb)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls_fit](LogRate.definitions.md#def-f9bbe89ff5799074)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ArbitraryConditions.buckets_mono](Machine.definitions.md#def-6a2ac9479d29d19e)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls_base](LogRate.definitions.md#def-c7f67aa83650bf20)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`HMul.hMul`, `Nat.mul_le_mul_right`, `Membership.mem`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `LE.le.trans`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-520a6476c2a49ad5"></a>
## `CodedSorting.Construction.ArbitraryMachine.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L62)

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
fun q base cutoff P e G S hb hG hS hresident hblock hfit hstartup =>
  let k := CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e;
  let ρ :=
    CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
      CodedSorting.Construction.streamCount k;
  if ρ < e then
    let cs := CodedSorting.Construction.ArbitraryCalls.calls base k (e - ρ);
    let P' :=
      CodedSorting.Construction.ArbitraryCalls.paddedRows
        (P *
          (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
            CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ))
        k;
    CodedSorting.Construction.BorrowedChunks.space q cutoff cs P ρ P' G S hG hS ⋯
  else
    CodedSorting.Construction.ChunkExchange.space q cutoff (CodedSorting.Construction.ArbitraryCalls.baseCalls base e) P
      G S hG hS ⋯
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.calls](LogRate.definitions.md#def-75983e57bda8a0ed)
- [CodedSorting.Construction.ArbitraryMachine.space._proof_1](Machine.definitions.md#def-2bfe7b2f5ee5af00)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ArbitraryConditions.baseConditions](Machine.definitions.md#def-dd9eaf09b277dbe2)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.Construction.ArbitraryCalls.paddedRows](LogRate.definitions.md#def-f8506f50419e099d)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.BorrowedChunks.space](../Chunks/BorrowedChunks.definitions.md#def-fe66073119deea1a)
- [CodedSorting.Construction.ChunkExchange.space](../Chunks/BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`, `ite`

<a id="def-887ed50202147d3e"></a>
## `CodedSorting.Construction.ArbitraryMachine.base_fields`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean#L82)

**类型**

```lean
∀ (base e : ℕ),
  CodedSorting.Construction.ArbitraryCalls.fieldCount (CodedSorting.Construction.ArbitraryCalls.baseCalls base e) =
    CodedSorting.Construction.ExchangeSpecialization.radix ^ e
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Eq`

<a id="def-a271a1f2620822b0"></a>
## `CodedSorting.Construction.ArbitraryMachine.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L86)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (base cutoff P e G S source buffer limit : ℕ) →
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
                            (CodedSorting.CommonChunkLayout.Volume P
                              (CodedSorting.Construction.ExchangeSpecialization.radix ^ e) G (S * q.w)) ≤
                        buffer →
                      buffer +
                            CodedSorting.Construction.ArbitraryMachine.space q base cutoff P e G S hb hG hS hresident
                              hblock hfit hstartup ≤
                          limit →
                        limit ≤ q.N ^ q.exponent →
                          CodedSorting.CommonFinitePermutation.Program q
                            (CodedSorting.CommonChunkLayout.Volume P
                              (CodedSorting.Construction.ExchangeSpecialization.radix ^ e) G (S * q.w))
                            source buffer limit
                            (CodedSorting.CommonChunkLayout.swap P
                              (CodedSorting.Construction.ExchangeSpecialization.radix ^ e) G (S * q.w))
```

**定义**

```lean
fun q reader base cutoff P e G S source buffer limit hb hG hS hresident hblock hfit hstartup hs hw hl =>
  let k := CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e;
  let ρ :=
    CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
      CodedSorting.Construction.streamCount k;
  if hborrow : ρ < e then
    let cs := CodedSorting.Construction.ArbitraryCalls.calls base k (e - ρ);
    let P' :=
      CodedSorting.Construction.ArbitraryCalls.paddedRows
        (P *
          (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
            CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ))
        k;
    let hc := ⋯;
    let_fun hfields := ⋯;
    let_fun hs' := ⋯;
    let_fun hw' := ⋯;
    CodedSorting.CommonExchangeShapeProgram.reshape q ⋯ hfields ⋯ ⋯
      (CodedSorting.Construction.BorrowedChunks.program q reader cutoff cs P ρ P' G S source buffer limit hG hS ⋯ hc hs'
        hw' hl)
  else
    let hc := ⋯;
    let_fun hfields := ⋯;
    let_fun hs' := ⋯;
    let_fun hw' := ⋯;
    CodedSorting.CommonExchangeShapeProgram.reshape q ⋯ hfields ⋯ ⋯
      (CodedSorting.Construction.ChunkExchange.program q reader cutoff
        (CodedSorting.Construction.ArbitraryCalls.baseCalls base e) P G S source buffer limit hG hS hc hs' hw' hl)
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](../Chunks/BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.calls](LogRate.definitions.md#def-75983e57bda8a0ed)
- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.ArbitraryMachine.space._proof_1](Machine.definitions.md#def-2bfe7b2f5ee5af00)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.Construction.ArbitraryMachine.program._proof_6](Machine.definitions.md#def-e8326629ccfca50c)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ChunkExchange.program](../Chunks/BorrowedChunks.definitions.md#def-73c46e787b2eb032)
- [CodedSorting.Construction.BorrowedChunks.program](../Chunks/BorrowedChunks.definitions.md#def-4c3b7d939f1696ba)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.ArbitraryConditions.baseConditions](Machine.definitions.md#def-dd9eaf09b277dbe2)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryMachine.program._proof_4](Machine.definitions.md#def-c0583235de1ae410)
- [CodedSorting.Construction.ArbitraryMachine.program._proof_2](Machine.definitions.md#def-0913232f8d03745e)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.CommonExchangeShapeProgram.reshape](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-996aff3a413a714f)
- [CodedSorting.Construction.ArbitraryMachine.base_fields](Machine.definitions.md#def-887ed50202147d3e)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.Construction.ArbitraryCalls.paddedRows](LogRate.definitions.md#def-f8506f50419e099d)
- [CodedSorting.Construction.ArbitraryMachine.program._proof_7](Machine.definitions.md#def-80a3abc9fc91dc78)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ArbitraryMachine.program._proof_8](Machine.definitions.md#def-18292d196d10ea95)
- [CodedSorting.Construction.BorrowedChunks.space](../Chunks/BorrowedChunks.definitions.md#def-fe66073119deea1a)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ChunkExchange.space](../Chunks/BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.ArbitraryMachine.program._proof_5](Machine.definitions.md#def-4ac1dfde2136379c)
- [CodedSorting.Construction.ArbitraryMachine.program._proof_3](Machine.definitions.md#def-5001cceaf8e89143)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ArbitraryMachine.space](Machine.definitions.md#def-520a6476c2a49ad5)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `dite`, `List`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Not`, `letFun`, `rfl`, `instHMul`

<a id="def-0913232f8d03745e"></a>
## `CodedSorting.Construction.ArbitraryMachine.program._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (base e : ℕ),
  CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
        CodedSorting.Construction.streamCount
        (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) <
      e →
    CodedSorting.Construction.ExchangeSpecialization.radix ^
          CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
            CodedSorting.Construction.streamCount
            (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) *
        CodedSorting.Construction.ArbitraryCalls.fieldCount
          (CodedSorting.Construction.ArbitraryCalls.calls base
            (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)
            (e -
              CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                CodedSorting.Construction.streamCount
                (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e))) =
      CodedSorting.Construction.ExchangeSpecialization.radix ^ e
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.calls](LogRate.definitions.md#def-75983e57bda8a0ed)
- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instMulNat`, `instHSub`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `Eq`, `instHMul`

<a id="def-5001cceaf8e89143"></a>
## `CodedSorting.Construction.ArbitraryMachine.program._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base P e G S source buffer : ℕ),
  source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ e) G
            (S * q.w)) ≤
      buffer →
    CodedSorting.Construction.ExchangeSpecialization.radix ^
            CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
              CodedSorting.Construction.streamCount
              (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) *
          CodedSorting.Construction.ArbitraryCalls.fieldCount
            (CodedSorting.Construction.ArbitraryCalls.calls base
              (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)
              (e -
                CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                  CodedSorting.Construction.streamCount
                  (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e))) =
        CodedSorting.Construction.ExchangeSpecialization.radix ^ e →
      source +
          CodedSorting.CommonPermutationPairs.count q
            (CodedSorting.CommonChunkLayout.Volume P
              (CodedSorting.Construction.ExchangeSpecialization.radix ^
                  CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                    CodedSorting.Construction.streamCount
                    (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) *
                CodedSorting.Construction.ArbitraryCalls.fieldCount
                  (CodedSorting.Construction.ArbitraryCalls.calls base
                    (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)
                    (e -
                      CodedSorting.ArbitrarySchedule.borrowedWidth
                        CodedSorting.Construction.ExchangeSpecialization.radix CodedSorting.Construction.streamCount
                        (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e))))
              G (S * q.w)) ≤
        buffer
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.calls](LogRate.definitions.md#def-75983e57bda8a0ed)
- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Eq`, `instHMul`

<a id="def-c0583235de1ae410"></a>
## `CodedSorting.Construction.ArbitraryMachine.program._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base cutoff P e G S buffer limit : ℕ) (hb : 0 < base)
  (hG : 0 < G) (hS : 0 < S) (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
  (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
  (hfit :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q)
  (hstartup :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q),
  buffer +
        CodedSorting.Construction.ArbitraryMachine.space q base cutoff P e G S hb hG hS hresident hblock hfit hstartup ≤
      limit →
    CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
          CodedSorting.Construction.streamCount
          (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) <
        e →
      buffer +
          CodedSorting.Construction.BorrowedChunks.space q cutoff
            (CodedSorting.Construction.ArbitraryCalls.calls base
              (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)
              (e -
                CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                  CodedSorting.Construction.streamCount
                  (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)))
            P
            (CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
              CodedSorting.Construction.streamCount
              (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e))
            (CodedSorting.Construction.ArbitraryCalls.paddedRows
              (P *
                (CodedSorting.Construction.ExchangeSpecialization.radix ^
                    CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                      CodedSorting.Construction.streamCount
                      (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) *
                  CodedSorting.Construction.ExchangeSpecialization.radix ^
                    CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                      CodedSorting.Construction.streamCount
                      (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)))
              (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e))
            G S hG hS ⋯ ≤
        limit
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.calls](LogRate.definitions.md#def-75983e57bda8a0ed)
- [CodedSorting.Construction.ArbitraryMachine.space._proof_1](Machine.definitions.md#def-2bfe7b2f5ee5af00)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.Construction.ArbitraryCalls.paddedRows](LogRate.definitions.md#def-f8506f50419e099d)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.BorrowedChunks.space](../Chunks/BorrowedChunks.definitions.md#def-fe66073119deea1a)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ArbitraryMachine.space](Machine.definitions.md#def-520a6476c2a49ad5)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-4ac1dfde2136379c"></a>
## `CodedSorting.Construction.ArbitraryMachine.program._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (S : ℕ), S * q.w = S * q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`

<a id="def-e8326629ccfca50c"></a>
## `CodedSorting.Construction.ArbitraryMachine.program._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (base P e : ℕ),
  P *
      (CodedSorting.Construction.ExchangeSpecialization.radix ^
          CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
            CodedSorting.Construction.streamCount
            (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) *
        CodedSorting.Construction.ExchangeSpecialization.radix ^
          CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
            CodedSorting.Construction.streamCount
            (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)) ≤
    CodedSorting.Construction.ArbitraryCalls.paddedRows
      (P *
        (CodedSorting.Construction.ExchangeSpecialization.radix ^
            CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
              CodedSorting.Construction.streamCount
              (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) *
          CodedSorting.Construction.ExchangeSpecialization.radix ^
            CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
              CodedSorting.Construction.streamCount
              (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)))
      (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)
```

**继续展开**

- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.Construction.ArbitraryCalls.paddedRows](LogRate.definitions.md#def-f8506f50419e099d)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `instHMul`

<a id="def-80a3abc9fc91dc78"></a>
## `CodedSorting.Construction.ArbitraryMachine.program._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base P e G S source buffer : ℕ),
  source +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonChunkLayout.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ e) G
            (S * q.w)) ≤
      buffer →
    CodedSorting.Construction.ArbitraryCalls.fieldCount (CodedSorting.Construction.ArbitraryCalls.baseCalls base e) =
        CodedSorting.Construction.ExchangeSpecialization.radix ^ e →
      source +
          CodedSorting.CommonPermutationPairs.count q
            (CodedSorting.CommonChunkLayout.Volume P
              (CodedSorting.Construction.ArbitraryCalls.fieldCount
                (CodedSorting.Construction.ArbitraryCalls.baseCalls base e))
              G (S * q.w)) ≤
        buffer
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Eq`, `instHMul`

<a id="def-18292d196d10ea95"></a>
## `CodedSorting.Construction.ArbitraryMachine.program._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base cutoff P e G S buffer limit : ℕ) (hb : 0 < base)
  (hG : 0 < G) (hS : 0 < S) (hresident : cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q)
  (hblock : CodedSorting.CommonPermutationPairs.width q ≤ cutoff)
  (hfit :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
      CodedSorting.CommonExchangeLeaf.bankWords q)
  (hstartup :
    CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * CodedSorting.CommonPermutationPairs.width q ≤
      cutoff + CodedSorting.CommonPermutationPairs.width q),
  buffer +
        CodedSorting.Construction.ArbitraryMachine.space q base cutoff P e G S hb hG hS hresident hblock hfit hstartup ≤
      limit →
    ¬CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
            CodedSorting.Construction.streamCount
            (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) <
          e →
      (buffer +
          if False then
            CodedSorting.Construction.BorrowedChunks.space q cutoff
              (CodedSorting.Construction.ArbitraryCalls.calls base
                (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)
                (e -
                  CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                    CodedSorting.Construction.streamCount
                    (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)))
              P
              (CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                CodedSorting.Construction.streamCount
                (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e))
              (CodedSorting.Construction.ArbitraryCalls.paddedRows
                (P *
                  (CodedSorting.Construction.ExchangeSpecialization.radix ^
                      CodedSorting.ArbitrarySchedule.borrowedWidth
                        CodedSorting.Construction.ExchangeSpecialization.radix CodedSorting.Construction.streamCount
                        (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) *
                    CodedSorting.Construction.ExchangeSpecialization.radix ^
                      CodedSorting.ArbitrarySchedule.borrowedWidth
                        CodedSorting.Construction.ExchangeSpecialization.radix CodedSorting.Construction.streamCount
                        (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)))
                (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e))
              G S hG hS ⋯
          else
            CodedSorting.Construction.ChunkExchange.space q cutoff
              (CodedSorting.Construction.ArbitraryCalls.baseCalls base e) P G S hG hS ⋯) ≤
        limit
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.calls](LogRate.definitions.md#def-75983e57bda8a0ed)
- [CodedSorting.Construction.ArbitraryMachine.space._proof_1](Machine.definitions.md#def-2bfe7b2f5ee5af00)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ArbitraryConditions.baseConditions](Machine.definitions.md#def-dd9eaf09b277dbe2)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.Construction.ArbitraryCalls.paddedRows](LogRate.definitions.md#def-f8506f50419e099d)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.BorrowedChunks.space](../Chunks/BorrowedChunks.definitions.md#def-fe66073119deea1a)
- [CodedSorting.Construction.ChunkExchange.space](../Chunks/BorrowedChunks.definitions.md#def-021550a3e75cde97)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ArbitraryMachine.space](Machine.definitions.md#def-520a6476c2a49ad5)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`False`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instDecidableFalse`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Not`, `instHMul`, `ite`

<a id="def-2bfe7b2f5ee5af00"></a>
## `CodedSorting.Construction.ArbitraryMachine.space._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base cutoff P e : ℕ),
  0 < base →
    cutoff ≤ CodedSorting.CommonExchangeLeaf.bankBits q →
      CodedSorting.CommonPermutationPairs.width q ≤ cutoff →
        CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base * q.block ≤
            CodedSorting.CommonExchangeLeaf.bankWords q →
          CodedSorting.Construction.RecursiveWorkspaceBudget.buckets base *
                CodedSorting.CommonPermutationPairs.width q ≤
              cutoff + CodedSorting.CommonPermutationPairs.width q →
            CodedSorting.Construction.ChunkExchange.Conditions q cutoff
              (CodedSorting.Construction.ArbitraryCalls.calls base
                (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)
                (e -
                  CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
                    CodedSorting.Construction.streamCount
                    (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)))
              (CodedSorting.Construction.ArbitraryCalls.paddedRows
                (P *
                  (CodedSorting.Construction.ExchangeSpecialization.radix ^
                      CodedSorting.ArbitrarySchedule.borrowedWidth
                        CodedSorting.Construction.ExchangeSpecialization.radix CodedSorting.Construction.streamCount
                        (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e) *
                    CodedSorting.Construction.ExchangeSpecialization.radix ^
                      CodedSorting.ArbitrarySchedule.borrowedWidth
                        CodedSorting.Construction.ExchangeSpecialization.radix CodedSorting.Construction.streamCount
                        (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e)))
                (CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e))
```

**继续展开**

- [CodedSorting.Construction.ChunkExchange.Conditions](../Chunks/BorrowedChunks.definitions.md#def-464508b12f165a08)
- [CodedSorting.Construction.ArbitraryCalls.calls](LogRate.definitions.md#def-75983e57bda8a0ed)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.buckets](../Recursion/Workspace.definitions.md#def-167360864504c5b9)
- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.Construction.ArbitraryCalls.paddedRows](LogRate.definitions.md#def-f8506f50419e099d)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`
