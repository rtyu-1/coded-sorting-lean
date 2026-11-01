# Program 的定义

[源码](Program.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-c38f6f0224d06ba5"></a>
## `CodedSorting.Construction.Sorting.CommonLocalBudget.batchBound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L12)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q child c r =>
  if r ≤ 512 * q.height then 256 * (CodedSorting.CommonRecordProgram.recordBlocks q (c * r) + 1)
  else c * (child + 12 * CodedSorting.CommonRecordProgram.recordBlocks q r)
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-e7b5e8b778c9f2fd"></a>
## `CodedSorting.Construction.Sorting.CommonLocalBudget.budget`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L16)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → ℕ) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → ℕ → Nat.below (motive := fun x => ℕ → ℕ) x → ℕ) x, x_2 with
        | 0, n => fun x => 8 * CodedSorting.CommonRecordProgram.recordBlocks q n + 1
        | fuel.succ, n => fun x =>
          if n ≤ 512 * q.height then 8 * CodedSorting.CommonRecordProgram.recordBlocks q n + 1
          else
            let s := CodedSorting.LocalShape.sizeChoice n;
            let r := CodedSorting.PhysicalLocalSortNode.rows s;
            3 * CodedSorting.Construction.Sorting.CommonLocalBudget.batchBound q (x.1 r) s r +
                  CodedSorting.Construction.Sorting.CommonLocalBudget.batchBound q (x.1 r) (s + 1) r +
                6 *
                  CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q
                    (CodedSorting.LocalShape.sizeExponent n) 3 +
              3 *
                (2 * CodedSorting.CommonRecordProgram.recordBlocks q (s * r) +
                    CodedSorting.CommonRecordProgram.recordBlocks q ((s + 1) * r) +
                  CodedSorting.CommonRecordProgram.recordBlocks q n))
        f)
    x_1
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonLocalBudget.batchBound](Program.definitions.md#def-c38f6f0224d06ba5)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost](../Resources/Swaps.definitions.md#def-0d77f1963d4cbd11)
- [CodedSorting.LocalShape.sizeChoice](../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalShape.sizeExponent](../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.PhysicalLocalSortNode.rows](Framework/PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonLocalBudget.budget.match_1](Program.definitions.md#def-224b3f47c73827c1)

**基础库名称**

`HMul.hMul`, `Nat.brecOn`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.succ`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-6c28ba39929cd553"></a>
## `CodedSorting.Construction.Sorting.CommonLocalRecursion.batchSpace`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L222)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q c r childSpace =>
  if r ≤ 512 * q.height then CodedSorting.CommonGroupedLeafBatch.space q c r
  else c * CodedSorting.CommonRecordProgram.recordBlocks q r + childSpace
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.space](../../Shared/Memory/GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-6e019908a7c3b3ef"></a>
## `CodedSorting.Construction.Sorting.CommonLocalRecursion.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L226)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q hnormal x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → ℕ) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → ℕ → Nat.below (motive := fun x => ℕ → ℕ) x → ℕ) x, x_2 with
        | 0, n => fun x => CodedSorting.CommonRecordProgram.recordBlocks q n
        | fuel.succ, n => fun x =>
          if n ≤ 512 * q.height then CodedSorting.CommonRecordProgram.recordBlocks q n
          else
            max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
              max
                (CodedSorting.Construction.Sorting.CommonLocalRecursion.batchSpace q
                  (CodedSorting.CommonLocalNode.side n) (CodedSorting.CommonLocalNode.rowCount n)
                  (x.1 (CodedSorting.CommonLocalNode.rowCount n)))
                (max
                  (CodedSorting.Construction.Sorting.CommonLocalRecursion.batchSpace q
                    (CodedSorting.CommonLocalNode.side n + 1) (CodedSorting.CommonLocalNode.rowCount n)
                    (x.1 (CodedSorting.CommonLocalNode.rowCount n)))
                  (CodedSorting.Construction.Sorting.CommonSortingSwaps.space q (CodedSorting.LocalShape.sizeExponent n)
                    3 CodedSorting.Construction.Sorting.CommonLocalRecursion.space._proof_2 hnormal)))
        f)
    x_1
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](../Resources/Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalShape.sizeExponent](../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.CommonLocalNode.small](Framework/Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Framework/Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space._proof_2](Program.definitions.md#def-02ba73dcdda13dba)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Framework/Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonLocalBudget.budget.match_1](Program.definitions.md#def-224b3f47c73827c1)
- [CodedSorting.Construction.Sorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-6c28ba39929cd553)
- [CodedSorting.CommonLocalNode.rowCount](Framework/Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `Nat.brecOn`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.succ`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-d110519bfcd0bb06"></a>
## `CodedSorting.Construction.Sorting.concreteLocalExchange`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L273)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q
```

**定义**

```lean
fun q =>
  { condition := CodedSorting.Construction.RecursiveParameters.Normalized q,
    cost := fun t => CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q t 3,
    space := fun t hnormal =>
      CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3
        CodedSorting.Construction.Sorting.CommonLocalRecursion.space._proof_2 hnormal,
    forward := CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram q,
    backward := CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardProgram q, forward_bound := ⋯,
    backward_bound := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forward_charge_le](../Resources/Swaps.definitions.md#def-fe7c4f3f3377374f)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost](../Resources/Swaps.definitions.md#def-0d77f1963d4cbd11)
- [CodedSorting.Construction.Sorting.CommonSortingSwaps.space](../Resources/Swaps.definitions.md#def-1fc95a6a93b22a39)
- [CodedSorting.LocalSorter.Exchange](Framework/Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.Construction.Sorting.CommonLocalRecursion.space._proof_2](Program.definitions.md#def-02ba73dcdda13dba)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram](../Resources/Swaps.definitions.md#def-f6741e55f82db402)
- [CodedSorting.LocalSorter.Exchange.mk](Framework/Program.definitions.md#def-b25cf5f60a180476)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backward_charge_le](../Resources/Swaps.definitions.md#def-a912b0575f77e47a)
- [CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardProgram](../Resources/Swaps.definitions.md#def-50d584f0d5984b76)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-c56b088bf0286946"></a>
## `CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L300)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (hnormal : (CodedSorting.Construction.Sorting.concreteLocalExchange q).condition) →
      (n : ℕ) →
        n ≤ q.height ^ 2 →
          2 ≤ q.exponent →
            (source buffer limit : ℕ) →
              source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
                buffer +
                      CodedSorting.LocalSorter.space CodedSorting.Construction.Sorting.concreteLocalExchange q hnormal 3
                        n ≤
                    limit →
                  limit ≤ q.N ^ q.exponent →
                    CodedSorting.CommonRecordProgram.Program q n source buffer limit CodedSorting.Columnsort.sortColumn
```

**定义**

```lean
CodedSorting.LocalSorter.Machine.localProgram CodedSorting.Construction.Sorting.concreteLocalExchange
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.concreteLocalExchange](Program.definitions.md#def-d110519bfcd0bb06)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.KeyRecordWords.Record](../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.LocalSorter.Exchange.condition](Framework/Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Columnsort.sortColumn](Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.LocalSorter.space](Framework/Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.ResidentLeafSort.recordOrder](Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.LocalSorter.Machine.localProgram](Framework/Program.definitions.md#def-03f81def84d153b3)
- [CodedSorting.CommonRecordProgram.Program](../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-224b3f47c73827c1"></a>
## `CodedSorting.Construction.Sorting.CommonLocalBudget.budget.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Program.lean)

**类型**

```lean
(motive : ℕ → ℕ → Sort u_1) → (x x_1 : ℕ) → ((n : ℕ) → motive 0 n) → ((fuel n : ℕ) → motive fuel.succ n) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-02ba73dcdda13dba"></a>
## `CodedSorting.Construction.Sorting.CommonLocalRecursion.space._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
0 < 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`
