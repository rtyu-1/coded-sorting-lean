# IntervalCopyBounds 的定义

[源码](IntervalCopyBounds.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-ff70c9345e3a5b86"></a>
## `CodedSorting.CommonIntervalCopy.Block`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L15)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.WordControl.Words q.block q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

<a id="def-13cee856445ebb88"></a>
## `CodedSorting.CommonIntervalCopy.address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L16)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → Fin (q.N ^ q.exponent)
```

**定义**

```lean
CodedSorting.CommonColumnSplit.address
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonColumnSplit.address](../../Interchange/Framework/Columns/ColumnOperations.definitions.md#def-72d3a9464453bd7c)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-2341ee3643386ec8"></a>
## `CodedSorting.CommonIntervalCopy.firstPage`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L18)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q O D k => (O + (k * q.block - D)) / q.block
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HSub.hSub`, `HDiv.hDiv`, `instSubNat`, `instMulNat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instHMul`

<a id="def-88a6002d8d0405a5"></a>
## `CodedSorting.CommonIntervalCopy.selected`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ →
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            CodedSorting.CommonIntervalCopy.Block q →
              CodedSorting.CommonIntervalCopy.Block q → CodedSorting.CommonIntervalCopy.Block q
```

**定义**

```lean
fun q O D N k p a b i =>
  let j := k * q.block + ↑i;
  if D ≤ j ∧ j < D + N ∧ (O + (j - D)) / q.block = p then a ⟨(O + (j - D)) % q.block, ⋯⟩ else b i
```

**继续展开**

- [CodedSorting.CommonIntervalCopy.selected._proof_1](IntervalCopyBounds.definitions.md#def-45e18149d54b257c)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonIntervalCopy.Block](IntervalCopyBounds.definitions.md#def-ff70c9345e3a5b86)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HSub.hSub`, `Fin.mk`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instSubNat`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `instDecidableAnd`, `Fin`, `Eq`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-550f270f5dea9be4"></a>
## `CodedSorting.CommonIntervalCopy.pairCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L26)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader O D N source target k p =>
  [CodedSorting.CommonBlockPair.sourceRead q reader (CodedSorting.CommonIntervalCopy.address q source p),
    CodedSorting.CommonStaticMarginGather.secondRead q reader (CodedSorting.CommonIntervalCopy.address q target k)
      (CodedSorting.CommonIntervalCopy.selected q O D N k p),
    CodedSorting.CommonBlockPair.targetWrite q (CodedSorting.CommonIntervalCopy.address q target k)]
```

**继续展开**

- [CodedSorting.CommonStaticMarginGather.secondRead](../Programs/Static/MarginGather.definitions.md#def-f28024dd78f6b499)
- [CodedSorting.CommonIntervalCopy.address](IntervalCopyBounds.definitions.md#def-13cee856445ebb88)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonBlockPair.sourceRead](BlockPair.definitions.md#def-5dc5b806044bea03)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBlockPair.targetWrite](BlockPair.definitions.md#def-3b05497ae0c5b9b7)
- [CodedSorting.CommonIntervalCopy.selected](IntervalCopyBounds.definitions.md#def-88a6002d8d0405a5)

**基础库名称**

`List.cons`, `List`, `Nat`, `Fin`, `List.nil`

<a id="def-0c35fc3cf9c9abe7"></a>
## `CodedSorting.CommonIntervalCopy.fragment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L43)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader O D N source target k =>
  CodedSorting.CommonIntervalCopy.pairCode q reader O D N source target k
      (CodedSorting.CommonIntervalCopy.firstPage q O D k) ++
    CodedSorting.CommonIntervalCopy.pairCode q reader O D N source target k
      (CodedSorting.CommonIntervalCopy.firstPage q O D k + 1)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonIntervalCopy.pairCode](IntervalCopyBounds.definitions.md#def-550f270f5dea9be4)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonIntervalCopy.firstPage](IntervalCopyBounds.definitions.md#def-2341ee3643386ec8)

**基础库名称**

`instOfNatNat`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`

<a id="def-b5ea9a8ee619ce92"></a>
## `CodedSorting.CommonIntervalCopy.codeFrom`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L104)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader O D N source target x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x_1
    (fun x f x_2 =>
      (match (motive :=
          ℕ →
            (x : ℕ) →
              Nat.below (motive := fun x => ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x →
                List (CodedSorting.CommonStaticSchedule.Instruction q))
          x_2, x with
        | x, 0 => fun x => []
        | k, n.succ => fun x => CodedSorting.CommonIntervalCopy.fragment q reader O D N source target k ++ x.1 (k + 1))
        f)
    x
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonIntervalCopy.codeFrom.match_1](IntervalCopyBounds.definitions.md#def-973bd9228d1812ff)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonIntervalCopy.fragment](IntervalCopyBounds.definitions.md#def-0c35fc3cf9c9abe7)

**基础库名称**

`Nat.brecOn`, `instOfNatNat`, `Nat.below`, `instHAppendOfAppend`, `List`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `HAppend.hAppend`, `List.nil`

<a id="def-2c29f6b867b071a0"></a>
## `CodedSorting.CommonIntervalCopy.pages`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L110)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q D N => CodedSorting.PhysicalStreamCursor.blockCount q.block (D % q.block + N)
```

**继续展开**

- [CodedSorting.PhysicalStreamCursor.blockCount](PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMod`, `instHMod`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-873421a048c5b5e6"></a>
## `CodedSorting.CommonIntervalCopy.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](IntervalCopyBounds.lean#L113)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader O D N source target =>
  CodedSorting.CommonIntervalCopy.codeFrom q reader O D N source target (D / q.block)
    (CodedSorting.CommonIntervalCopy.pages q D N)
```

**继续展开**

- [CodedSorting.CommonIntervalCopy.pages](IntervalCopyBounds.definitions.md#def-2c29f6b867b071a0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonIntervalCopy.codeFrom](IntervalCopyBounds.definitions.md#def-b5ea9a8ee619ce92)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `List`, `Nat`, `Nat.instDiv`, `Fin`

<a id="def-973bd9228d1812ff"></a>
## `CodedSorting.CommonIntervalCopy.codeFrom.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](IntervalCopyBounds.lean)

**类型**

```lean
(motive : ℕ → ℕ → Sort u_1) → (x x_1 : ℕ) → ((x : ℕ) → motive x 0) → ((k n : ℕ) → motive k n.succ) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x_1 (h_1 x) fun n => h_2 x n
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-45e18149d54b257c"></a>
## `CodedSorting.CommonIntervalCopy.selected._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](IntervalCopyBounds.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (O D k : ℕ) (i : Fin q.block),
  (O + (k * q.block + ↑i - D)) % q.block < q.block
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `Nat.instMod`, `instHMod`, `instSubNat`, `instMulNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`, `instHMul`
