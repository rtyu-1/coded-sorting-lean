# GroupedLeafBatch 的定义

[源码](GroupedLeafBatch.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-8101c426e456898e"></a>
## `CodedSorting.CommonGroupedLeafBatch.gc`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L96)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q r => CodedSorting.CommonLeafGrouping.columns (512 * q.height) r
```

**继续展开**

- [CodedSorting.CommonLeafGrouping.columns](Leaf/Grouping.definitions.md#def-f3d883dd37c94564)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-2e8ff536d0b8cc1f"></a>
## `CodedSorting.CommonGroupedLeafBatch.ng`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L97)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q c r => CodedSorting.CommonLeafGrouping.groups (512 * q.height) r c
```

**继续展开**

- [CodedSorting.CommonLeafGrouping.groups](Leaf/Grouping.definitions.md#def-9472467428d4900c)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-e277e6253b63bf31"></a>
## `CodedSorting.CommonGroupedLeafBatch.groupSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L98)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q r => CodedSorting.CommonGroupedLeafBatch.gc q r * r
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.gc](GroupedLeafBatch.definitions.md#def-8101c426e456898e)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-030422d010c5c00f"></a>
## `CodedSorting.CommonGroupedLeafBatch.paddedSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L99)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q c r => CodedSorting.CommonGroupedLeafBatch.ng q c r * CodedSorting.CommonGroupedLeafBatch.groupSize q r
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-632f8085f3c024ca"></a>
## `CodedSorting.CommonGroupedLeafBatch.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L101)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q c r =>
  if c * r ≤ 512 * q.height then CodedSorting.CommonRecordProgram.recordBlocks q (c * r)
  else
    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
        CodedSorting.CommonGroupedLeafBatch.ng q c r *
          CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) +
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r)
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-a249b8eeae244fe6"></a>
## `CodedSorting.CommonGroupedLeafBatch.sortColumns`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L106)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  (c r : ℕ) → CodedSorting.CommonRecordProgram.Records q (c * r) → CodedSorting.CommonRecordProgram.Records q (c * r)
```

**定义**

```lean
fun {q} c r => CodedSorting.CommonSlabBatch.batchOutput CodedSorting.Columnsort.sortColumn
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Columnsort.sortColumn](../../Sorting/Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonSlabBatch.batchOutput](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-1e347b15e5d5c6a2)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-fd1be21091a07fbc"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L109)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (c r source buffer limit : ℕ) →
      r ≤ 512 * q.height →
        512 * q.height < c * r →
          source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer →
            buffer +
                      CodedSorting.CommonRecordProgram.recordBlocks q
                        (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
                    CodedSorting.CommonGroupedLeafBatch.ng q c r *
                      CodedSorting.CommonRecordProgram.recordBlocks q
                        (CodedSorting.CommonGroupedLeafBatch.groupSize q r) +
                  CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
                limit →
              limit ≤ q.N ^ q.exponent →
                CodedSorting.CommonRecordProgram.Program q (c * r) source buffer limit
                  (CodedSorting.CommonGroupedLeafBatch.sortColumns c r)
```

**定义**

```lean
fun q reader c r source buffer limit hr hlarge hs hw hl =>
  let G := CodedSorting.CommonGroupedLeafBatch.groupSize q r;
  let K := CodedSorting.CommonGroupedLeafBatch.ng q c r;
  let M := CodedSorting.CommonGroupedLeafBatch.paddedSize q c r;
  let slabs := buffer + CodedSorting.CommonRecordProgram.recordBlocks q M;
  let work := slabs + K * CodedSorting.CommonRecordProgram.recordBlocks q G;
  let_fun hG := ⋯;
  let_fun hpos := ⋯;
  let_fun hp := ⋯;
  let_fun hc := ⋯;
  let_fun hwork := ⋯;
  let kids := fun a =>
    CodedSorting.CommonResidentRecordProgram.program q reader G hG
      (CodedSorting.CommonGroupedLeafBatch.sortColumns (CodedSorting.CommonGroupedLeafBatch.gc q r) r)
      (CodedSorting.CommonSlabBatch.recordBase q G slabs ↑a) work limit ⋯ hwork hl;
  let inner := CodedSorting.CommonSlabBatch.program reader kids ⋯ ⋯ ⋯ hl;
  let padded := CodedSorting.CommonRecordPrefix.program reader hp inner hs ⋯ ⋯ hl;
  padded.changeFunction ⋯
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_14](GroupedLeafBatch.definitions.md#def-94da36f018950998)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_9](GroupedLeafBatch.definitions.md#def-ca14514b0e3fbe74)
- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.gc](GroupedLeafBatch.definitions.md#def-8101c426e456898e)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonSlabBatch.Children](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_5](GroupedLeafBatch.definitions.md#def-413de9aec3d869a6)
- [CodedSorting.CommonResidentRecordProgram.program](../../Interchange/Framework/Resident/RecordProgram.definitions.md#def-b98c803ea5f33c23)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.program](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-ae51434b8b1ab7f4)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_8](GroupedLeafBatch.definitions.md#def-f6fce91702d091fd)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_7](GroupedLeafBatch.definitions.md#def-694704fd86b38316)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_4](GroupedLeafBatch.definitions.md#def-d61d96c1725e89fd)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_13](GroupedLeafBatch.definitions.md#def-eb829997e5018c9d)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_12](GroupedLeafBatch.definitions.md#def-f30c823685ce7845)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonRecordPrefix.program](../Records/RecordOperations.definitions.md#def-cf73107deb5a3f9e)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-e192f85de221fbac)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_6](GroupedLeafBatch.definitions.md#def-53c10bb9c537b70e)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_11](GroupedLeafBatch.definitions.md#def-0ed5b43f5c5c46f9)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonRecordPrefix.restrictOutput](../Records/RecordOperations.definitions.md#def-1ff13236813def56)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_10](GroupedLeafBatch.definitions.md#def-ad2b87945ebba04d)
- [CodedSorting.CommonSlabBatch.batchOutput](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-1e347b15e5d5c6a2)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_3](GroupedLeafBatch.definitions.md#def-cb773a8eb7968d73)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `letFun`, `instHMul`

<a id="def-b36448fb5634f1c7"></a>
## `_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L160)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (c r source buffer limit : ℕ) →
      r ≤ 512 * q.height →
        q.block ≤ q.height →
          source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer →
            buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit →
              limit ≤ q.N ^ q.exponent →
                { p // p.charge ≤ 256 * (CodedSorting.CommonRecordProgram.recordBlocks q (c * r) + 1) }
```

**定义**

```lean
fun q reader c r source buffer limit hr hBH hs hw hl =>
  if hn : c * r ≤ 512 * q.height then
    let p :=
      CodedSorting.CommonResidentRecordProgram.program q reader (c * r) hn
        (CodedSorting.CommonGroupedLeafBatch.sortColumns c r) source buffer limit hs ⋯ hl;
    let_fun hc := ⋯;
    ⟨p, hc⟩
  else
    let_fun hg := ⋯;
    let_fun hwork := ⋯;
    let p := CodedSorting.CommonGroupedLeafBatch.largeProgram q reader c r source buffer limit hr hg hs hwork hl;
    let_fun hc := ⋯;
    ⟨p, hc⟩
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.CommonResidentRecordProgram.program](../../Interchange/Framework/Resident/RecordProgram.definitions.md#def-b98c803ea5f33c23)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram](GroupedLeafBatch.definitions.md#def-fd1be21091a07fbc)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_18](GroupedLeafBatch.definitions.md#def-c4b8684d35601b2f)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_20](GroupedLeafBatch.definitions.md#def-76655235ccdfb193)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_21](GroupedLeafBatch.definitions.md#def-b0bb225d8ea3a815)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_19](GroupedLeafBatch.definitions.md#def-2a246d6541aaed20)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_17](GroupedLeafBatch.definitions.md#def-a54869786f5d56f3)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `dite`, `Subtype.mk`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `Nat.decLe`, `letFun`, `instHMul`

<a id="def-b060e8872789c203"></a>
## `CodedSorting.CommonGroupedLeafBatch.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedLeafBatch.lean#L186)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (c r source buffer limit : ℕ) →
      r ≤ 512 * q.height →
        q.block ≤ q.height →
          source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer →
            buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit →
              limit ≤ q.N ^ q.exponent →
                CodedSorting.CommonRecordProgram.Program q (c * r) source buffer limit
                  (CodedSorting.CommonGroupedLeafBatch.sortColumns c r)
```

**定义**

```lean
fun q reader c r source buffer limit hr hBH hs hw hl =>
  let p := CodedSorting.CommonGroupedLeafBatch.construction✝ q reader c r source buffer limit hr hBH hs hw hl;
  { instructions := (↑p).instructions, charge := 256 * (CodedSorting.CommonRecordProgram.recordBlocks q (c * r) + 1),
    correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordProgram.Program.mk](../Records/RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonGroupedLeafBatch.program._proof_26](GroupedLeafBatch.definitions.md#def-a0dd792e9df07e3e)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonGroupedLeafBatch.program._proof_24](GroupedLeafBatch.definitions.md#def-9019ff38f3bf8ad6)
- [CodedSorting.CommonRecordProgram.Program.instructions](../Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonGroupedLeafBatch.program._proof_22](GroupedLeafBatch.definitions.md#def-bf75db4119ffd11a)
- [CodedSorting.CommonGroupedLeafBatch.program._proof_25](GroupedLeafBatch.definitions.md#def-e9f5e9ae6b913e7a)
- [CodedSorting.CommonGroupedLeafBatch.program._proof_23](GroupedLeafBatch.definitions.md#def-8fc91ec2f8881490)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction](GroupedLeafBatch.definitions.md#def-b36448fb5634f1c7)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `instHMul`

<a id="def-ad2b87945ebba04d"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer : ℕ),
  buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
      CodedSorting.CommonGroupedLeafBatch.ng q c r *
        CodedSorting.CommonSlabBatch.stride q (CodedSorting.CommonGroupedLeafBatch.groupSize q r * 3) ≤
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
      CodedSorting.CommonGroupedLeafBatch.ng q c r *
        CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r)
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.stride](../../Interchange/Framework/Memory/SlabBatchAllocation.definitions.md#def-94b29694418488f5)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-0ed5b43f5c5c46f9"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
              CodedSorting.CommonGroupedLeafBatch.ng q c r *
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) +
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
          limit →
        buffer +
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
            CodedSorting.CommonGroupedLeafBatch.ng q c r *
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
          limit
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-f30c823685ce7845"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer : ℕ),
  buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) ≤
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r)
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Preorder.toLE`, `LE.le`, `instHAdd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`

<a id="def-eb829997e5018c9d"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
              CodedSorting.CommonGroupedLeafBatch.ng q c r *
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) +
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
          limit →
        buffer +
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) ≤
          limit
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-94da36f018950998"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r : ℕ)
  (hp : c * r ≤ CodedSorting.CommonGroupedLeafBatch.paddedSize q c r),
  c ≤ CodedSorting.CommonGroupedLeafBatch.ng q c r * CodedSorting.CommonGroupedLeafBatch.gc q r →
    CodedSorting.CommonRecordPrefix.restrictOutput hp
        (CodedSorting.CommonSlabBatch.batchOutput
          (CodedSorting.CommonGroupedLeafBatch.sortColumns (CodedSorting.CommonGroupedLeafBatch.gc q r) r)) =
      CodedSorting.CommonGroupedLeafBatch.sortColumns c r
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.gc](GroupedLeafBatch.definitions.md#def-8101c426e456898e)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordPrefix.restrictOutput](../Records/RecordOperations.definitions.md#def-1ff13236813def56)
- [CodedSorting.CommonSlabBatch.batchOutput](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-1e347b15e5d5c6a2)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Nat`, `Eq`, `instHMul`

<a id="def-cb773a8eb7968d73"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (r : ℕ),
  CodedSorting.CommonLeafGrouping.groupRecords (512 * q.height) r ≤ 512 * q.height
```

**继续展开**

- [CodedSorting.CommonLeafGrouping.groupRecords](Leaf/Grouping.definitions.md#def-6fbb52144658b40e)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-d61d96c1725e89fd"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r : ℕ), 512 * q.height < c * r → 0 < r
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-413de9aec3d869a6"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r : ℕ),
  r ≤ 512 * q.height → 0 < r → c * r ≤ CodedSorting.CommonLeafGrouping.paddedRecords (512 * q.height) r c
```

**继续展开**

- [CodedSorting.CommonLeafGrouping.paddedRecords](Leaf/Grouping.definitions.md#def-cef78037c66d44b3)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-53c10bb9c537b70e"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r : ℕ),
  r ≤ 512 * q.height →
    0 < r →
      c ≤
        CodedSorting.CommonLeafGrouping.groups (512 * q.height) r c *
          CodedSorting.CommonLeafGrouping.columns (512 * q.height) r
```

**继续展开**

- [CodedSorting.CommonLeafGrouping.columns](Leaf/Grouping.definitions.md#def-f3d883dd37c94564)
- [CodedSorting.CommonLeafGrouping.groups](Leaf/Grouping.definitions.md#def-9472467428d4900c)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-694704fd86b38316"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer limit : ℕ),
  buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
          CodedSorting.CommonGroupedLeafBatch.ng q c r *
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) +
        CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
      limit →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
          CodedSorting.CommonGroupedLeafBatch.ng q c r *
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) +
        CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
      limit
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-f6fce91702d091fd"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer : ℕ)
  (a : Fin (CodedSorting.CommonGroupedLeafBatch.ng q c r)),
  CodedSorting.CommonSlabBatch.recordBase q (CodedSorting.CommonGroupedLeafBatch.groupSize q r)
        (buffer +
          CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r))
        ↑a +
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
      CodedSorting.CommonGroupedLeafBatch.ng q c r *
        CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r)
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-e192f85de221fbac)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `instHMul`

<a id="def-ca14514b0e3fbe74"></a>
## `CodedSorting.CommonGroupedLeafBatch.largeProgram._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer : ℕ),
  buffer +
      CodedSorting.CommonRecordProgram.recordBlocks q
        (CodedSorting.CommonGroupedLeafBatch.ng q c r * CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
    buffer +
      CodedSorting.CommonRecordProgram.recordBlocks q
        (CodedSorting.CommonGroupedLeafBatch.ng q c r * CodedSorting.CommonGroupedLeafBatch.groupSize q r)
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `Preorder.toLE`, `instMulNat`, `LE.le`, `instHAdd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHMul`

<a id="def-bf75db4119ffd11a"></a>
## `CodedSorting.CommonGroupedLeafBatch.program._proof_22`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c r source buffer limit : ℕ) (hr : r ≤ 512 * q.height) (hBH : q.block ≤ q.height)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer)
  (hw : buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit) (hl : limit ≤ q.N ^ q.exponent)
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q (c * r)),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    CodedSorting.CommonRecordProgram.Encoded q
      (CodedSorting.CommonStaticSchedule.executeRaw q
            (↑(CodedSorting.CommonGroupedLeafBatch.construction✝ q reader c r source buffer limit hr hBH hs hw
                  hl)).instructions
            s).1.disk
      source (CodedSorting.CommonGroupedLeafBatch.sortColumns c r f)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.CommonRecordProgram.Encoded](../Records/RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonLeafProgram.Machine](Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](../Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](../Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction](GroupedLeafBatch.definitions.md#def-b36448fb5634f1c7)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `instHMul`

<a id="def-8fc91ec2f8881490"></a>
## `CodedSorting.CommonGroupedLeafBatch.program._proof_23`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c r source buffer limit : ℕ) (hr : r ≤ 512 * q.height) (hBH : q.block ≤ q.height)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer)
  (hw : buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit) (hl : limit ≤ q.N ^ q.exponent)
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (↑(CodedSorting.CommonGroupedLeafBatch.construction✝ q reader c r source buffer limit hr hBH hs hw
                      hl)).instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonLeafProgram.Machine](Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](../Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction](GroupedLeafBatch.definitions.md#def-b36448fb5634f1c7)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `instHMul`

<a id="def-9019ff38f3bf8ad6"></a>
## `CodedSorting.CommonGroupedLeafBatch.program._proof_24`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c r source buffer limit : ℕ) (hr : r ≤ 512 * q.height) (hBH : q.block ≤ q.height)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer)
  (hw : buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit) (hl : limit ≤ q.N ^ q.exponent),
  ∀
    i ∈
      (↑(CodedSorting.CommonGroupedLeafBatch.construction✝ q reader c r source buffer limit hr hBH hs hw
            hl)).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](../Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction](GroupedLeafBatch.definitions.md#def-b36448fb5634f1c7)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `instHMul`

<a id="def-e9f5e9ae6b913e7a"></a>
## `CodedSorting.CommonGroupedLeafBatch.program._proof_25`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c r source buffer limit : ℕ) (hr : r ≤ 512 * q.height) (hBH : q.block ≤ q.height)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer)
  (hw : buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit) (hl : limit ≤ q.N ^ q.exponent),
  CodedSorting.CommonStaticSchedule.cost q
      (↑(CodedSorting.CommonGroupedLeafBatch.construction✝ q reader c r source buffer limit hr hBH hs hw
            hl)).instructions ≤
    256 * (CodedSorting.CommonRecordProgram.recordBlocks q (c * r) + 1)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Program.instructions](../Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction](GroupedLeafBatch.definitions.md#def-b36448fb5634f1c7)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `instHMul`

<a id="def-a0dd792e9df07e3e"></a>
## `CodedSorting.CommonGroupedLeafBatch.program._proof_26`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c r source buffer limit : ℕ) (hr : r ≤ 512 * q.height) (hBH : q.block ≤ q.height)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer)
  (hw : buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit) (hl : limit ≤ q.N ^ q.exponent),
  (↑(CodedSorting.CommonGroupedLeafBatch.construction✝ q reader c r source buffer limit hr hBH hs hw
            hl)).instructions.length ≤
    256 * (CodedSorting.CommonRecordProgram.recordBlocks q (c * r) + 1)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](../Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction](GroupedLeafBatch.definitions.md#def-b36448fb5634f1c7)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Preorder.toLE`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `List.length`, `instHMul`

<a id="def-a54869786f5d56f3"></a>
## `_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_17`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer limit : ℕ),
  buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit →
    c * r ≤ 512 * q.height → buffer + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ limit
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-c4b8684d35601b2f"></a>
## `_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_18`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c r source buffer limit : ℕ) (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer)
  (hw : buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit) (hl : limit ≤ q.N ^ q.exponent)
  (hn : c * r ≤ 512 * q.height),
  (CodedSorting.CommonResidentRecordProgram.program q reader (c * r) hn
        (CodedSorting.CommonGroupedLeafBatch.sortColumns c r) source buffer limit hs ⋯ hl).charge ≤
    256 * (CodedSorting.CommonRecordProgram.recordBlocks q (c * r) + 1)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.CommonResidentRecordProgram.program](../../Interchange/Framework/Resident/RecordProgram.definitions.md#def-b98c803ea5f33c23)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_17](GroupedLeafBatch.definitions.md#def-a54869786f5d56f3)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-2a246d6541aaed20"></a>
## `_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_19`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r : ℕ),
  ℕ → ℕ → ℕ → ¬c * r ≤ 512 * q.height → 512 * q.height < c * r
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Not`, `instHMul`

<a id="def-76655235ccdfb193"></a>
## `_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_20`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer limit : ℕ),
  buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit →
    ¬c * r ≤ 512 * q.height →
      buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
            CodedSorting.CommonGroupedLeafBatch.ng q c r *
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) +
          CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
        limit
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.space](GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`, `instHMul`

<a id="def-b0bb225d8ea3a815"></a>
## `_private.CodedSorting.Shared.Memory.GroupedLeafBatch.0.CodedSorting.CommonGroupedLeafBatch.construction._proof_21`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedLeafBatch.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (c r source buffer limit : ℕ) (hr : r ≤ 512 * q.height),
  q.block ≤ q.height →
    ∀ (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer) (hl : limit ≤ q.N ^ q.exponent)
      (hg : 512 * q.height < c * r)
      (hwork :
        buffer +
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.paddedSize q c r) +
              CodedSorting.CommonGroupedLeafBatch.ng q c r *
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) +
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonGroupedLeafBatch.groupSize q r) ≤
          limit),
      (CodedSorting.CommonGroupedLeafBatch.largeProgram q reader c r source buffer limit hr hg hs hwork hl).charge ≤
        256 * (CodedSorting.CommonRecordProgram.recordBlocks q (c * r) + 1)
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.ng](GroupedLeafBatch.definitions.md#def-2e8ff536d0b8cc1f)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonGroupedLeafBatch.groupSize](GroupedLeafBatch.definitions.md#def-e277e6253b63bf31)
- [CodedSorting.CommonGroupedLeafBatch.largeProgram](GroupedLeafBatch.definitions.md#def-fd1be21091a07fbc)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonGroupedLeafBatch.paddedSize](GroupedLeafBatch.definitions.md#def-030422d010c5c00f)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordProgram.Program.charge](../Records/RecordOperations.definitions.md#def-ab509acf69c03316)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`
