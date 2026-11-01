# TopPrefix 的定义

[源码](TopPrefix.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-5e06d151a523aeca"></a>
## `CodedSorting.CommonRecordTopPrefix.operation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TopPrefix.lean#L16)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m : ℕ} →
    n ≤ m →
      (CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m) →
        CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n
```

**定义**

```lean
fun {q} {n m} hn F f => CodedSorting.RecursiveColumnsort.trim hn (F (CodedSorting.RecursiveColumnsort.pad f))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-f52d388ddcf14cc3"></a>
## `CodedSorting.CommonRecordTopPrefix.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TopPrefix.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    {n m source buffer work limit : ℕ} →
      {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} →
        (hn : n ≤ m) →
          CodedSorting.CommonRecordProgram.Program q m buffer work limit F →
            source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
              buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work →
                work ≤ limit →
                  limit ≤ q.N ^ q.exponent →
                    3 * m < (2 ^ q.w) ^ q.digits →
                      CodedSorting.CommonRecordProgram.Program q n source buffer limit
                        (CodedSorting.CommonRecordTopPrefix.operation hn F)
```

**定义**

```lean
fun q reader {n m source buffer work limit} {F} hn p hs hw hwl hl hshape =>
  let_fun hc := ⋯;
  let_fun hsc := ⋯;
  let_fun hmc := ⋯;
  let_fun hdesc := ⋯;
  let p0 :=
    CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer limit ⋯ ⋯ hsc ⋯ ⋯ ⋯
      ⋯;
  let padStage := (p0.castOutput ⋯).changeFunction ⋯;
  let middle := CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯;
  let t0 :=
    CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit ⋯ ⋯ hmc ⋯ ⋯ ⋯ ⋯;
  let trimStage := (t0.castOutput ⋯).changeFunction ⋯;
  let all := (padStage.append middle).append trimStage;
  let done := all.toProgram;
  let_fun hcharge := ⋯;
  { instructions := done.instructions,
    charge :=
      3 * CodedSorting.CommonRecordProgram.recordBlocks q m + p.charge +
        3 * CodedSorting.CommonRecordProgram.recordBlocks q n,
    correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.program._proof_21](TopPrefix.definitions.md#def-78f83fc01e5ec633)
- [CodedSorting.CommonRecordTopPrefix.program._proof_24](TopPrefix.definitions.md#def-101451f9ab5eb67f)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_29](TopPrefix.definitions.md#def-3dfc1350a28cd1b9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_30](TopPrefix.definitions.md#def-a47821fcebef89b8)
- [CodedSorting.CommonRecordTopPrefix.program._proof_43](TopPrefix.definitions.md#def-e67b660100bc1f6f)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTopPrefix.operation](TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.CommonRecordTopPrefix.program._proof_42](TopPrefix.definitions.md#def-308dc710a94271cc)
- [CodedSorting.CommonRecordTransform.workspaceProgram](Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_47](TopPrefix.definitions.md#def-0e7f4f12ba68574d)
- [CodedSorting.CommonRecordProgram.Program.mk](RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonRecordTransform.margins](Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonRecordTopPrefix.program._proof_31](TopPrefix.definitions.md#def-37c046239a318417)
- [CodedSorting.CommonRecordTopPrefix.program._proof_28](TopPrefix.definitions.md#def-4d43e0ed34b34c1d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_32](TopPrefix.definitions.md#def-a1e948a754541f4d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_20](TopPrefix.definitions.md#def-ac7c3bf418e0f90a)
- [CodedSorting.CommonRecordTopPrefix.program._proof_26](TopPrefix.definitions.md#def-72b12c132f897510)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTopPrefix.program._proof_36](TopPrefix.definitions.md#def-dc90c65a5b5fa5c5)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonRecordTopPrefix.program._proof_44](TopPrefix.definitions.md#def-c697a6a125b3a966)
- [CodedSorting.CommonRecordTopPrefix.program._proof_34](TopPrefix.definitions.md#def-0cab55e656d744a6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_38](TopPrefix.definitions.md#def-beb01710e5e7b390)
- [CodedSorting.CommonRecordTopPrefix.program._proof_27](TopPrefix.definitions.md#def-1b3aaa68ce32453b)
- [CodedSorting.CommonRecordTopPrefix.program._proof_33](TopPrefix.definitions.md#def-e6c9d9d83930e277)
- [CodedSorting.CommonRecordTopPrefix.program._proof_23](TopPrefix.definitions.md#def-0e89590e3fdeda01)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_39](TopPrefix.definitions.md#def-82b596b3dee075b3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_46](TopPrefix.definitions.md#def-7fc07cd17eed4f57)
- [CodedSorting.CommonRecordTopPrefix.program._proof_37](TopPrefix.definitions.md#def-086516557ef3b782)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordTransform.Stage.append](Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonRecordTopPrefix.program._proof_40](TopPrefix.definitions.md#def-66491f7d820421f7)
- [CodedSorting.CommonRecordTopPrefix.program._proof_45](TopPrefix.definitions.md#def-13d0e423a5256126)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordTopPrefix.program._proof_35](TopPrefix.definitions.md#def-1e94006298d5489a)
- [CodedSorting.CommonRecordTopPrefix.program._proof_41](TopPrefix.definitions.md#def-9ebd364aa59b6ff6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_22](TopPrefix.definitions.md#def-cbc67f0a264c06cb)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordTopPrefix.program._proof_25](TopPrefix.definitions.md#def-d9e69386904b9f93)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_rfl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `letFun`, `instHMul`

<a id="def-ac7c3bf418e0f90a"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_20`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m : ℕ},
  n ≤ m →
    CodedSorting.CommonPermutationPairs.count q (n * (3 * q.w)) ≤
      CodedSorting.CommonPermutationPairs.count q (m * (3 * q.w))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-78f83fc01e5ec633"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_21`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m source buffer work limit : ℕ},
  source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
    buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work →
      work ≤ limit →
        limit ≤ q.N ^ q.exponent →
          CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m →
            source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-cbc67f0a264c06cb"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_22`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n : ℕ} {m : ℕ} {source : ℕ} {buffer work limit : ℕ},
  buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work →
    work ≤ limit →
      limit ≤ q.N ^ q.exponent → buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-0e89590e3fdeda01"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_23`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n : ℕ} {m : ℕ} {source buffer work limit : ℕ},
  3 * m < (2 ^ q.w) ^ q.digits →
    ∀ (L N R O : ℕ),
      L ≤ m →
        N ≤ m →
          R ≤ m →
            O ≤ m →
              3 * L < (2 ^ q.w) ^ q.digits ∧
                3 * N < (2 ^ q.w) ^ q.digits ∧ 3 * R < (2 ^ q.w) ^ q.digits ∧ 3 * O < (2 ^ q.w) ^ q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `And`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-101451f9ab5eb67f"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_24`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ∀ {n : ℕ} {m source buffer work limit : ℕ}, 0 + n ≤ n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-d9e69386904b9f93"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_25`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m : ℕ} {source buffer work limit : ℕ},
  n ≤ m →
    (∀ (L N R O : ℕ),
        L ≤ m → N ≤ m → R ≤ m → O ≤ m → CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)) →
      CodedSorting.CommonStaticMargins.ShapeFits q (3 * 0) (3 * n) (3 * (m - n)) (3 * 0)
```

**继续展开**

- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHSub`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-72b12c132f897510"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_26`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m source buffer : ℕ} {work limit : ℕ},
  source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent →
      source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * n)) ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.PhysicalStreamCursor.blockCount](../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-1b3aaa68ce32453b"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_27`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m : ℕ} {source : ℕ} {buffer : ℕ} {work limit : ℕ},
  n ≤ m →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent →
      buffer + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + (m - n)) ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-4d43e0ed34b34c1d"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_28`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m source buffer : ℕ},
  source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
    source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * n)) ≤ buffer ∨
      buffer + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + (m - n)) ≤ source
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.PhysicalStreamCursor.blockCount](../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `Or`, `OfNat.ofNat`, `instHMul`

<a id="def-3dfc1350a28cd1b9"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_29`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m source buffer work limit : ℕ},
  n ≤ m →
    buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work →
      work ≤ limit →
        ∀ (a : Fin (q.N ^ q.exponent)),
          ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
            ↑a < buffer ∨ limit ≤ ↑a →
              ↑a < buffer ∨ buffer + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + (m - n)) ≤ ↑a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-a47821fcebef89b8"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_30`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ∀ {n m : ℕ} {source buffer work limit : ℕ}, n ≤ m → 0 + n + (m - n) = m
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HSub.hSub`, `instSubNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`

<a id="def-37c046239a318417"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_31`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m source buffer work limit : ℕ} (hn : n ≤ m),
  CodedSorting.CommonRecordReindex.castRecords ⋯ ∘ CodedSorting.CommonStaticMarginsRecords.margin 0 n (m - n) 0 ⋯ =
    CodedSorting.RecursiveColumnsort.pad
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.program._proof_24](TopPrefix.definitions.md#def-101451f9ab5eb67f)
- [CodedSorting.CommonRecordTopPrefix.program._proof_30](TopPrefix.definitions.md#def-a47821fcebef89b8)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`HSub.hSub`, `Function.comp`, `instSubNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-a1e948a754541f4d"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_32`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n : ℕ} {m : ℕ} {source : ℕ} {buffer work limit : ℕ},
  buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work →
    work ≤ limit → buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ limit
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-e6c9d9d83930e277"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_33`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n : ℕ} {m : ℕ} {source : ℕ} {buffer work : ℕ}
  {limit : ℕ}, buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work → buffer ≤ work
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-0cab55e656d744a6"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_34`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ∀ {n m : ℕ} {source buffer work limit : ℕ}, n ≤ m → 0 + n ≤ m
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-1e94006298d5489a"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_35`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m : ℕ} {source buffer work limit : ℕ},
  n ≤ m →
    (∀ (L N R O : ℕ),
        L ≤ m → N ≤ m → R ≤ m → O ≤ m → CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)) →
      CodedSorting.CommonStaticMargins.ShapeFits q (3 * 0) (3 * n) (3 * 0) (3 * 0)
```

**继续展开**

- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-dc90c65a5b5fa5c5"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_36`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m : ℕ} {source : ℕ} {buffer work limit : ℕ},
  buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work →
    work ≤ limit →
      limit ≤ q.N ^ q.exponent →
        CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m →
          buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent →
            buffer + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * n)) ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.PhysicalStreamCursor.blockCount](../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-086516557ef3b782"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_37`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n source : ℕ},
  source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent →
    source + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + 0) ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-beb01710e5e7b390"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_38`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m source buffer : ℕ} {work limit : ℕ},
  source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
    CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m →
      buffer + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * n)) ≤ source ∨
        source + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + 0) ≤ buffer
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.PhysicalStreamCursor.blockCount](../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `Or`, `OfNat.ofNat`, `instHMul`

<a id="def-82b596b3dee075b3"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_39`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n source buffer limit : ℕ} (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a → ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + 0) ≤ ↑a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-66491f7d820421f7"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_40`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ∀ {n : ℕ} {m source buffer work limit : ℕ}, 0 + n + 0 = n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`

<a id="def-9ebd364aa59b6ff6"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_41`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n m source buffer work limit : ℕ} (hn : n ≤ m),
  CodedSorting.CommonRecordReindex.castRecords ⋯ ∘ CodedSorting.CommonStaticMarginsRecords.margin 0 n 0 0 ⋯ =
    CodedSorting.RecursiveColumnsort.trim hn
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTopPrefix.program._proof_34](TopPrefix.definitions.md#def-0cab55e656d744a6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_40](TopPrefix.definitions.md#def-66491f7d820421f7)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)

**基础库名称**

`Function.comp`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-308dc710a94271cc"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_42`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} (hn : n ≤ m)
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F)
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hw : buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hc : CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m)
  (hsc : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hmc : buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent)
  (hdesc :
    ∀ (L N R O : ℕ),
      L ≤ m → N ≤ m → R ≤ m → O ≤ m → CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)),
  (((((CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer limit ⋯ ⋯ hsc ⋯ ⋯
                          ⋯ ⋯).castOutput
                      ⋯).changeFunction
                  ⋯).append
              (CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯)).append
          (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit ⋯ ⋯ hmc ⋯ ⋯
                    ⋯ ⋯).castOutput
                ⋯).changeFunction
            ⋯)).toProgram.charge =
    3 * CodedSorting.CommonRecordProgram.recordBlocks q m + p.charge +
      3 * CodedSorting.CommonRecordProgram.recordBlocks q n
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.program._proof_24](TopPrefix.definitions.md#def-101451f9ab5eb67f)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_29](TopPrefix.definitions.md#def-3dfc1350a28cd1b9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_30](TopPrefix.definitions.md#def-a47821fcebef89b8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTopPrefix.operation](TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.CommonRecordTransform.workspaceProgram](Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonRecordTransform.margins](Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonRecordTopPrefix.program._proof_31](TopPrefix.definitions.md#def-37c046239a318417)
- [CodedSorting.CommonRecordTopPrefix.program._proof_28](TopPrefix.definitions.md#def-4d43e0ed34b34c1d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_32](TopPrefix.definitions.md#def-a1e948a754541f4d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_26](TopPrefix.definitions.md#def-72b12c132f897510)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTopPrefix.program._proof_36](TopPrefix.definitions.md#def-dc90c65a5b5fa5c5)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTopPrefix.program._proof_34](TopPrefix.definitions.md#def-0cab55e656d744a6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_38](TopPrefix.definitions.md#def-beb01710e5e7b390)
- [CodedSorting.CommonRecordTopPrefix.program._proof_27](TopPrefix.definitions.md#def-1b3aaa68ce32453b)
- [CodedSorting.CommonRecordTopPrefix.program._proof_33](TopPrefix.definitions.md#def-e6c9d9d83930e277)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_39](TopPrefix.definitions.md#def-82b596b3dee075b3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_37](TopPrefix.definitions.md#def-086516557ef3b782)
- [CodedSorting.CommonRecordTransform.Stage.append](Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonRecordTopPrefix.program._proof_40](TopPrefix.definitions.md#def-66491f7d820421f7)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordTopPrefix.program._proof_35](TopPrefix.definitions.md#def-1e94006298d5489a)
- [CodedSorting.CommonRecordTopPrefix.program._proof_41](TopPrefix.definitions.md#def-9ebd364aa59b6ff6)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordTopPrefix.program._proof_25](TopPrefix.definitions.md#def-d9e69386904b9f93)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_rfl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-e67b660100bc1f6f"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_43`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} (hn : n ≤ m)
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F)
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hw : buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hc : CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m)
  (hsc : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hmc : buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent)
  (hdesc :
    ∀ (L N R O : ℕ),
      L ≤ m → N ≤ m → R ≤ m → O ≤ m → CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O))
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    CodedSorting.CommonRecordProgram.Encoded q
      (CodedSorting.CommonStaticSchedule.executeRaw q
            (((((CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer limit ⋯
                                  ⋯ hsc ⋯ ⋯ ⋯ ⋯).castOutput
                              ⋯).changeFunction
                          ⋯).append
                      (CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯)).append
                  (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit ⋯ ⋯
                            hmc ⋯ ⋯ ⋯ ⋯).castOutput
                        ⋯).changeFunction
                    ⋯)).toProgram.instructions
            s).1.disk
      source (CodedSorting.CommonRecordTopPrefix.operation hn F f)
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.program._proof_24](TopPrefix.definitions.md#def-101451f9ab5eb67f)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_29](TopPrefix.definitions.md#def-3dfc1350a28cd1b9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_30](TopPrefix.definitions.md#def-a47821fcebef89b8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTopPrefix.operation](TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonRecordTransform.workspaceProgram](Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonRecordTransform.margins](Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonRecordTopPrefix.program._proof_31](TopPrefix.definitions.md#def-37c046239a318417)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordTopPrefix.program._proof_28](TopPrefix.definitions.md#def-4d43e0ed34b34c1d)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonRecordTopPrefix.program._proof_32](TopPrefix.definitions.md#def-a1e948a754541f4d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_26](TopPrefix.definitions.md#def-72b12c132f897510)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTopPrefix.program._proof_36](TopPrefix.definitions.md#def-dc90c65a5b5fa5c5)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTopPrefix.program._proof_34](TopPrefix.definitions.md#def-0cab55e656d744a6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_38](TopPrefix.definitions.md#def-beb01710e5e7b390)
- [CodedSorting.CommonRecordTopPrefix.program._proof_27](TopPrefix.definitions.md#def-1b3aaa68ce32453b)
- [CodedSorting.CommonRecordTopPrefix.program._proof_33](TopPrefix.definitions.md#def-e6c9d9d83930e277)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_39](TopPrefix.definitions.md#def-82b596b3dee075b3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_37](TopPrefix.definitions.md#def-086516557ef3b782)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordTransform.Stage.append](Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonRecordTopPrefix.program._proof_40](TopPrefix.definitions.md#def-66491f7d820421f7)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordTopPrefix.program._proof_35](TopPrefix.definitions.md#def-1e94006298d5489a)
- [CodedSorting.CommonRecordTopPrefix.program._proof_41](TopPrefix.definitions.md#def-9ebd364aa59b6ff6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_25](TopPrefix.definitions.md#def-d9e69386904b9f93)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`le_rfl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-c697a6a125b3a966"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_44`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} (hn : n ≤ m)
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F)
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hw : buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hc : CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m)
  (hsc : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hmc : buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent)
  (hdesc :
    ∀ (L N R O : ℕ),
      L ≤ m → N ≤ m → R ≤ m → O ≤ m → CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O))
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (((((CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer
                                      limit ⋯ ⋯ hsc ⋯ ⋯ ⋯ ⋯).castOutput
                                  ⋯).changeFunction
                              ⋯).append
                          (CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯)).append
                      (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit
                                ⋯ ⋯ hmc ⋯ ⋯ ⋯ ⋯).castOutput
                            ⋯).changeFunction
                        ⋯)).toProgram.instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.program._proof_24](TopPrefix.definitions.md#def-101451f9ab5eb67f)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_29](TopPrefix.definitions.md#def-3dfc1350a28cd1b9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_30](TopPrefix.definitions.md#def-a47821fcebef89b8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTopPrefix.operation](TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonRecordTransform.workspaceProgram](Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonRecordTransform.margins](Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonRecordTopPrefix.program._proof_31](TopPrefix.definitions.md#def-37c046239a318417)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordTopPrefix.program._proof_28](TopPrefix.definitions.md#def-4d43e0ed34b34c1d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_32](TopPrefix.definitions.md#def-a1e948a754541f4d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_26](TopPrefix.definitions.md#def-72b12c132f897510)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTopPrefix.program._proof_36](TopPrefix.definitions.md#def-dc90c65a5b5fa5c5)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTopPrefix.program._proof_34](TopPrefix.definitions.md#def-0cab55e656d744a6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_38](TopPrefix.definitions.md#def-beb01710e5e7b390)
- [CodedSorting.CommonRecordTopPrefix.program._proof_27](TopPrefix.definitions.md#def-1b3aaa68ce32453b)
- [CodedSorting.CommonRecordTopPrefix.program._proof_33](TopPrefix.definitions.md#def-e6c9d9d83930e277)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonRecordTopPrefix.program._proof_39](TopPrefix.definitions.md#def-82b596b3dee075b3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_37](TopPrefix.definitions.md#def-086516557ef3b782)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordTransform.Stage.append](Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonRecordTopPrefix.program._proof_40](TopPrefix.definitions.md#def-66491f7d820421f7)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordTopPrefix.program._proof_35](TopPrefix.definitions.md#def-1e94006298d5489a)
- [CodedSorting.CommonRecordTopPrefix.program._proof_41](TopPrefix.definitions.md#def-9ebd364aa59b6ff6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_25](TopPrefix.definitions.md#def-d9e69386904b9f93)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`le_rfl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-13d0e423a5256126"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_45`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} (hn : n ≤ m)
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F)
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hw : buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hc : CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m)
  (hsc : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hmc : buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent)
  (hdesc :
    ∀ (L N R O : ℕ),
      L ≤ m → N ≤ m → R ≤ m → O ≤ m → CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)),
  ∀
    i ∈
      (((((CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer limit ⋯ ⋯ hsc
                            ⋯ ⋯ ⋯ ⋯).castOutput
                        ⋯).changeFunction
                    ⋯).append
                (CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯)).append
            (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit ⋯ ⋯ hmc ⋯
                      ⋯ ⋯ ⋯).castOutput
                  ⋯).changeFunction
              ⋯)).toProgram.instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.program._proof_24](TopPrefix.definitions.md#def-101451f9ab5eb67f)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_29](TopPrefix.definitions.md#def-3dfc1350a28cd1b9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_30](TopPrefix.definitions.md#def-a47821fcebef89b8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTopPrefix.operation](TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.CommonRecordTransform.workspaceProgram](Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonRecordTransform.margins](Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonRecordTopPrefix.program._proof_31](TopPrefix.definitions.md#def-37c046239a318417)
- [CodedSorting.CommonRecordTopPrefix.program._proof_28](TopPrefix.definitions.md#def-4d43e0ed34b34c1d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_32](TopPrefix.definitions.md#def-a1e948a754541f4d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_26](TopPrefix.definitions.md#def-72b12c132f897510)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTopPrefix.program._proof_36](TopPrefix.definitions.md#def-dc90c65a5b5fa5c5)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTopPrefix.program._proof_34](TopPrefix.definitions.md#def-0cab55e656d744a6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_38](TopPrefix.definitions.md#def-beb01710e5e7b390)
- [CodedSorting.CommonRecordTopPrefix.program._proof_27](TopPrefix.definitions.md#def-1b3aaa68ce32453b)
- [CodedSorting.CommonRecordTopPrefix.program._proof_33](TopPrefix.definitions.md#def-e6c9d9d83930e277)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_39](TopPrefix.definitions.md#def-82b596b3dee075b3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_37](TopPrefix.definitions.md#def-086516557ef3b782)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordTransform.Stage.append](Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonRecordTopPrefix.program._proof_40](TopPrefix.definitions.md#def-66491f7d820421f7)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordTopPrefix.program._proof_35](TopPrefix.definitions.md#def-1e94006298d5489a)
- [CodedSorting.CommonRecordTopPrefix.program._proof_41](TopPrefix.definitions.md#def-9ebd364aa59b6ff6)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonRecordTopPrefix.program._proof_25](TopPrefix.definitions.md#def-d9e69386904b9f93)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_rfl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Membership.mem`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `instHSub`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-7fc07cd17eed4f57"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_46`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} (hn : n ≤ m)
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F)
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hw : buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hc : CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m)
  (hsc : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hmc : buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent)
  (hdesc :
    ∀ (L N R O : ℕ),
      L ≤ m → N ≤ m → R ≤ m → O ≤ m → CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)),
  (((((CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer limit ⋯ ⋯ hsc ⋯ ⋯
                            ⋯ ⋯).castOutput
                        ⋯).changeFunction
                    ⋯).append
                (CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯)).append
            (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit ⋯ ⋯ hmc ⋯
                      ⋯ ⋯ ⋯).castOutput
                  ⋯).changeFunction
              ⋯)).toProgram.charge =
      3 * CodedSorting.CommonRecordProgram.recordBlocks q m + p.charge +
        3 * CodedSorting.CommonRecordProgram.recordBlocks q n →
    CodedSorting.CommonStaticSchedule.cost q
        (((((CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer limit ⋯ ⋯
                              hsc ⋯ ⋯ ⋯ ⋯).castOutput
                          ⋯).changeFunction
                      ⋯).append
                  (CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯)).append
              (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit ⋯ ⋯ hmc
                        ⋯ ⋯ ⋯ ⋯).castOutput
                    ⋯).changeFunction
                ⋯)).toProgram.instructions ≤
      3 * CodedSorting.CommonRecordProgram.recordBlocks q m + p.charge +
        3 * CodedSorting.CommonRecordProgram.recordBlocks q n
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.program._proof_24](TopPrefix.definitions.md#def-101451f9ab5eb67f)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_29](TopPrefix.definitions.md#def-3dfc1350a28cd1b9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_30](TopPrefix.definitions.md#def-a47821fcebef89b8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTopPrefix.operation](TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.CommonRecordTransform.workspaceProgram](Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonRecordTransform.margins](Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonRecordTopPrefix.program._proof_31](TopPrefix.definitions.md#def-37c046239a318417)
- [CodedSorting.CommonRecordTopPrefix.program._proof_28](TopPrefix.definitions.md#def-4d43e0ed34b34c1d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_32](TopPrefix.definitions.md#def-a1e948a754541f4d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_26](TopPrefix.definitions.md#def-72b12c132f897510)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTopPrefix.program._proof_36](TopPrefix.definitions.md#def-dc90c65a5b5fa5c5)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTopPrefix.program._proof_34](TopPrefix.definitions.md#def-0cab55e656d744a6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_38](TopPrefix.definitions.md#def-beb01710e5e7b390)
- [CodedSorting.CommonRecordTopPrefix.program._proof_27](TopPrefix.definitions.md#def-1b3aaa68ce32453b)
- [CodedSorting.CommonRecordTopPrefix.program._proof_33](TopPrefix.definitions.md#def-e6c9d9d83930e277)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_39](TopPrefix.definitions.md#def-82b596b3dee075b3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_37](TopPrefix.definitions.md#def-086516557ef3b782)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordTransform.Stage.append](Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonRecordTopPrefix.program._proof_40](TopPrefix.definitions.md#def-66491f7d820421f7)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordTopPrefix.program._proof_35](TopPrefix.definitions.md#def-1e94006298d5489a)
- [CodedSorting.CommonRecordTopPrefix.program._proof_41](TopPrefix.definitions.md#def-9ebd364aa59b6ff6)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordTopPrefix.program._proof_25](TopPrefix.definitions.md#def-d9e69386904b9f93)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_rfl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-0e7f4f12ba68574d"></a>
## `CodedSorting.CommonRecordTopPrefix.program._proof_47`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TopPrefix.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} (hn : n ≤ m)
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F)
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hw : buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q m) ≤ work) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hc : CodedSorting.CommonRecordProgram.recordBlocks q n ≤ CodedSorting.CommonRecordProgram.recordBlocks q m)
  (hsc : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hmc : buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ q.N ^ q.exponent)
  (hdesc :
    ∀ (L N R O : ℕ),
      L ≤ m → N ≤ m → R ≤ m → O ≤ m → CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)),
  (((((CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer limit ⋯ ⋯ hsc ⋯ ⋯
                            ⋯ ⋯).castOutput
                        ⋯).changeFunction
                    ⋯).append
                (CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯)).append
            (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit ⋯ ⋯ hmc ⋯
                      ⋯ ⋯ ⋯).castOutput
                  ⋯).changeFunction
              ⋯)).toProgram.charge =
      3 * CodedSorting.CommonRecordProgram.recordBlocks q m + p.charge +
        3 * CodedSorting.CommonRecordProgram.recordBlocks q n →
    (((((CodedSorting.CommonRecordTransform.margins q reader 0 n (m - n) 0 source buffer source n buffer limit ⋯ ⋯ hsc ⋯
                              ⋯ ⋯ ⋯).castOutput
                          ⋯).changeFunction
                      ⋯).append
                  (CodedSorting.CommonRecordTransform.workspaceProgram q p ⋯ ⋯ ⋯)).append
              (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 buffer source source n buffer limit ⋯ ⋯ hmc
                        ⋯ ⋯ ⋯ ⋯).castOutput
                    ⋯).changeFunction
                ⋯)).toProgram.instructions.length ≤
      3 * CodedSorting.CommonRecordProgram.recordBlocks q m + p.charge +
        3 * CodedSorting.CommonRecordProgram.recordBlocks q n
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.program._proof_24](TopPrefix.definitions.md#def-101451f9ab5eb67f)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_29](TopPrefix.definitions.md#def-3dfc1350a28cd1b9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_30](TopPrefix.definitions.md#def-a47821fcebef89b8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTopPrefix.operation](TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.CommonRecordTransform.workspaceProgram](Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonRecordTransform.margins](Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonRecordTopPrefix.program._proof_31](TopPrefix.definitions.md#def-37c046239a318417)
- [CodedSorting.CommonRecordTopPrefix.program._proof_28](TopPrefix.definitions.md#def-4d43e0ed34b34c1d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_32](TopPrefix.definitions.md#def-a1e948a754541f4d)
- [CodedSorting.CommonRecordTopPrefix.program._proof_26](TopPrefix.definitions.md#def-72b12c132f897510)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTopPrefix.program._proof_36](TopPrefix.definitions.md#def-dc90c65a5b5fa5c5)
- [CodedSorting.RecursiveColumnsort.pad](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Sorting/Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTopPrefix.program._proof_34](TopPrefix.definitions.md#def-0cab55e656d744a6)
- [CodedSorting.CommonRecordTopPrefix.program._proof_38](TopPrefix.definitions.md#def-beb01710e5e7b390)
- [CodedSorting.CommonRecordTopPrefix.program._proof_27](TopPrefix.definitions.md#def-1b3aaa68ce32453b)
- [CodedSorting.CommonRecordTopPrefix.program._proof_33](TopPrefix.definitions.md#def-e6c9d9d83930e277)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTopPrefix.program._proof_39](TopPrefix.definitions.md#def-82b596b3dee075b3)
- [CodedSorting.CommonRecordTopPrefix.program._proof_37](TopPrefix.definitions.md#def-086516557ef3b782)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordTransform.Stage.append](Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonRecordTopPrefix.program._proof_40](TopPrefix.definitions.md#def-66491f7d820421f7)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordTopPrefix.program._proof_35](TopPrefix.definitions.md#def-1e94006298d5489a)
- [CodedSorting.CommonRecordTopPrefix.program._proof_41](TopPrefix.definitions.md#def-9ebd364aa59b6ff6)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordTopPrefix.program._proof_25](TopPrefix.definitions.md#def-d9e69386904b9f93)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.KeyRecordBits.recordTop](RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_rfl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `List.length`, `instHMul`
