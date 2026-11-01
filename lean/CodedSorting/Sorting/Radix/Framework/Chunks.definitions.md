# Chunks 的定义

[源码](Chunks.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-3d2e731029d45a36"></a>
## `CodedSorting.CommonMSDSemantics.digit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Chunks.lean#L21)

**类型**

```lean
{α : Type u_1} → (α → ℕ) → (base : ℕ) → 0 < base → ℕ → α → Fin base
```

**定义**

```lean
fun {α} key base hb fuel x => CodedSorting.MSD.digit base hb fuel (key x)
```

**继续展开**

- [CodedSorting.MSD.digit](../Model/ExternalMSD.definitions.md#def-621d9c0b96834a0d)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-248ff155452c347a"></a>
## `CodedSorting.CommonMSDSemantics.prepare`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Chunks.lean#L24)

**类型**

```lean
{α : Type u_1} → (H : ℕ) → 0 < H → (List α → List α) → List α → List (List α)
```

**定义**

```lean
fun {α} H hH localSort xs => CodedSorting.ExternalMSD.sortedChunks (H ^ 2) ⋯ localSort xs
```

**继续展开**

- [CodedSorting.ExternalMSD.sortedChunks](../Model/ExternalMSD.definitions.md#def-b11efcbd6ec6994e)
- [CodedSorting.CommonMSDSemantics.prepare._proof_1](Chunks.definitions.md#def-ce8882f5d6123403)

**基础库名称**

`instPowNat`, `instOfNatNat`, `instNatPowNat`, `List`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-3a6326bdc285a215"></a>
## `CodedSorting.CommonMSDSemantics.sort`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Chunks.lean#L27)

**类型**

```lean
{α : Type u_1} → (α → ℕ) → (base : ℕ) → 0 < base → (H : ℕ) → 0 < H → (List α → List α) → ℕ → List α → List α
```

**定义**

```lean
fun {α} key base hb H hH localSort x x_1 =>
  Nat.brecOn (motive := fun x => List α → List α) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → List α → Nat.below (motive := fun x => List α → List α) x → List α) x, x_2 with
        | 0, xs => fun x => xs
        | fuel.succ, xs => fun x =>
          if xs.length ≤ H ^ 2 then localSort xs
          else
            List.flatMap
              (fun k =>
                x.1
                  (CodedSorting.ExternalMSD.child (CodedSorting.CommonMSDSemantics.digit key base hb fuel)
                    (CodedSorting.CommonMSDSemantics.prepare H hH localSort xs) k))
              (List.finRange base))
        f)
    x_1
```

**继续展开**

- [CodedSorting.CommonMSDSemantics.digit](Chunks.definitions.md#def-3d2e731029d45a36)
- [CodedSorting.CommonMSDSemantics.sort.match_1](Chunks.definitions.md#def-0b52e9d2b8b039ff)
- [CodedSorting.ExternalMSD.child](../Model/ExternalMSD.definitions.md#def-a8b344a00e5f0985)
- [CodedSorting.CommonMSDSemantics.prepare](Chunks.definitions.md#def-248ff155452c347a)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.brecOn`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `List`, `PProd`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `List.finRange`, `Nat.succ`, `List.length`, `Nat.decLe`, `List.flatMap`, `ite`

<a id="def-1ce5b05bacc178bb"></a>
## `CodedSorting.CommonMSDSemantics.recordSort`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Chunks.lean#L176)

**类型**

```lean
(w base : ℕ) →
  0 < base →
    (H : ℕ) → 0 < H → ℕ → List (CodedSorting.KeyRecordWords.Record w) → List (CodedSorting.KeyRecordWords.Record w)
```

**定义**

```lean
fun w base hb H hH =>
  CodedSorting.CommonMSDSemantics.sort CodedSorting.CommonWordMSD.key base hb H hH CodedSorting.CommonWordMSD.localSort
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonMSDSemantics.sort](Chunks.definitions.md#def-3a6326bdc285a215)
- [CodedSorting.CommonWordMSD.localSort](Words/Definitions.definitions.md#def-ded94dd20cf6d84b)
- [CodedSorting.CommonWordMSD.key](Words/Definitions.definitions.md#def-598ce34cf2b20028)

**基础库名称**

`instOfNatNat`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-35d8fa27ffc0c23b"></a>
## `CodedSorting.CommonMSDChunks.chunkSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Chunks.lean#L206)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => q.height ^ 2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-8b64845cabf0750d"></a>
## `CodedSorting.CommonMSDChunks.chunkCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Chunks.lean#L207)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n => CodedSorting.PhysicalStreamCursor.blockCount (CodedSorting.CommonMSDChunks.chunkSize q) n
```

**继续展开**

- [CodedSorting.CommonMSDChunks.chunkSize](Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-1c4eec1b43cf54c2"></a>
## `CodedSorting.CommonMSDChunks.paddedSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Chunks.lean#L209)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n => CodedSorting.CommonMSDChunks.chunkCount q n * CodedSorting.CommonMSDChunks.chunkSize q
```

**继续展开**

- [CodedSorting.CommonMSDChunks.chunkSize](Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.CommonMSDChunks.chunkCount](Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-5f9b152c18c9ecd8"></a>
## `CodedSorting.CommonMSDChunks.padded_covers`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Chunks.lean#L214)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ), n ≤ CodedSorting.CommonMSDChunks.paddedSize q n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDChunks.paddedSize](Chunks.definitions.md#def-1c4eec1b43cf54c2)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-95900b6568de0791"></a>
## `CodedSorting.CommonMSDChunks.operation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Chunks.lean#L217)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) → CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n
```

**定义**

```lean
fun q n =>
  CodedSorting.CommonRecordTopPrefix.operation ⋯
    (CodedSorting.CommonSlabBatch.batchOutput CodedSorting.Columnsort.sortColumn)
```

**继续展开**

- [CodedSorting.CommonRecordTopPrefix.operation](../../../Shared/Records/TopPrefix.definitions.md#def-5e06d151a523aeca)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonMSDChunks.chunkSize](Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.CommonMSDChunks.chunkCount](Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Columnsort.sortColumn](../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonMSDChunks.paddedSize](Chunks.definitions.md#def-1c4eec1b43cf54c2)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonSlabBatch.batchOutput](../../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-1e347b15e5d5c6a2)
- [CodedSorting.CommonMSDChunks.padded_covers](Chunks.definitions.md#def-5f9b152c18c9ecd8)

**基础库名称**

`Nat`

<a id="def-ce8882f5d6123403"></a>
## `CodedSorting.CommonMSDSemantics.prepare._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Chunks.lean)

**类型**

```lean
∀ (H : ℕ), 0 < H → 0 < H ^ 2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instPowNat`, `instOfNatNat`, `instNatPowNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-0b52e9d2b8b039ff"></a>
## `CodedSorting.CommonMSDSemantics.sort.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Chunks.lean)

**类型**

```lean
{α : Type u_1} →
  (motive : ℕ → List α → Sort u_2) →
    (x : ℕ) →
      (x_1 : List α) → ((xs : List α) → motive 0 xs) → ((fuel : ℕ) → (xs : List α) → motive fuel.succ xs) → motive x x_1
```

**定义**

```lean
fun {α} motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `List`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`
