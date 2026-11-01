# Program 的定义

[源码](Program.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-7bff9313b1612c55"></a>
## `CodedSorting.CommonLeafWindow.rightWindow`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L13)

**类型**

```lean
(a : ℕ) → {L b : ℕ} → CodedSorting.Normalization.Window L b → CodedSorting.Normalization.Window (a + L) b
```

**定义**

```lean
fun a {L b} win => { base := a + win.base, fits := ⋯ }
```

**继续展开**

- [CodedSorting.CommonLeafWindow.rightWindow._proof_2](Program.definitions.md#def-2aa450cc862e8b7e)
- [CodedSorting.Normalization.Window](../../Programs/Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Window.base](../../Programs/Normalization.definitions.md#def-62b64a40f69e4b5b)
- [CodedSorting.Normalization.Window.mk](../../Programs/Normalization.definitions.md#def-50fd7e7bb45579b5)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-d272acc2ec83dee9"></a>
## `CodedSorting.CommonLeafWindow.firstWindow`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L17)

**类型**

```lean
(b z : ℕ) → CodedSorting.Normalization.Window (b + z) b
```

**定义**

```lean
fun b z => { base := 0, fits := ⋯ }
```

**继续展开**

- [CodedSorting.CommonLeafWindow.firstWindow._proof_4](Program.definitions.md#def-74c17049c98ba38b)
- [CodedSorting.Normalization.Window](../../Programs/Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Window.mk](../../Programs/Normalization.definitions.md#def-50fd7e7bb45579b5)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-e331864fad0a6a8e"></a>
## `CodedSorting.CommonLeafWindow.transferWindow`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L70)

**类型**

```lean
(v : CodedSorting.SortingResourceBudget.Inventory) →
  (H b d : ℕ) → CodedSorting.Normalization.Window (CodedSorting.CommonSortingNormalization.sourceCells v H b d) b
```

**定义**

```lean
fun v H b d =>
  CodedSorting.CommonLeafWindow.rightWindow (CodedSorting.ResidentLeafSort.residentWords (512 * H) d)
    (CodedSorting.CommonLeafWindow.rightWindow (v.readers * CodedSorting.CommonSortingNormalization.inputCells b d)
      (CodedSorting.CommonLeafWindow.rightWindow (v.writers * CodedSorting.CommonSortingNormalization.outputCells b d)
        (CodedSorting.CommonLeafWindow.firstWindow b
          (1 + d + (3 * (2 * v.keys * d) + (3 * (13 * d) + (d + 3 * v.pc)))))))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.inputCells](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-66244596aea2da86)
- [CodedSorting.CommonSortingNormalization.outputCells](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0d3ffcc712372781)
- [CodedSorting.CommonSortingNormalization.tailCells](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-91f4c57732154132)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.ResidentLeafSort.residentWords](../../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-2fda3d29689ad340)
- [CodedSorting.SortingResourceBudget.Inventory.writers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-05f5194f09efb8fc)
- [CodedSorting.Normalization.Window](../../Programs/Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.CommonSortingNormalization.sourceCells](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-ebda39f020ddec43)
- [CodedSorting.SortingResourceBudget.Inventory](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.Inventory.pc](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-42f9d44e4c026d81)
- [CodedSorting.SortingResourceBudget.Inventory.keys](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-b107122480bc6937)
- [CodedSorting.CommonLeafWindow.rightWindow](Program.definitions.md#def-7bff9313b1612c55)
- [CodedSorting.CommonLeafWindow.firstWindow](Program.definitions.md#def-d272acc2ec83dee9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-e3c14c4bd7f3ac1c"></a>
## `CodedSorting.CommonLeafProgram.Store`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L137)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.CommonSortingNormalization.SourceState q.inventory q.height q.block q.digits q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

<a id="def-32e1e07132674e8d"></a>
## `CodedSorting.CommonLeafProgram.RAM`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L139)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.WordControl.Words q.ramWords q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.WordControl.Words](../../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

<a id="def-e343337119cf665f"></a>
## `CodedSorting.CommonLeafProgram.Disk`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L140)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.Normalization.Disk (q.N ^ q.exponent) q.block (CodedSorting.WordControl.Word q.w)
```

**继续展开**

- [CodedSorting.Normalization.Disk](../../Programs/Normalization.definitions.md#def-18f3e234560b5b4a)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-e2ceb047c19cf684"></a>
## `CodedSorting.CommonLeafProgram.Machine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L141)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q =>
  CodedSorting.Normalization.LogicalState q.ramWords q.block (q.N ^ q.exponent) (CodedSorting.WordControl.Word q.w)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.Normalization.LogicalState](../../Programs/Normalization.definitions.md#def-fe5b3999cdd6a29d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-74c17049c98ba38b"></a>
## `CodedSorting.CommonLeafWindow.firstWindow._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (b z : ℕ), 0 + b ≤ b + z
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-2aa450cc862e8b7e"></a>
## `CodedSorting.CommonLeafWindow.rightWindow._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (a : ℕ) {L b : ℕ} (win : CodedSorting.Normalization.Window L b), a + win.base + b ≤ a + L
```

**继续展开**

- [CodedSorting.Normalization.Window](../../Programs/Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Window.base](../../Programs/Normalization.definitions.md#def-62b64a40f69e4b5b)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`
