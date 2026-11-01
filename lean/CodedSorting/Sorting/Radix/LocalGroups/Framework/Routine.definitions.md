# Routine 的定义

[源码](Routine.lean) · [主定理导读](../../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-462240059bcf7402"></a>
## `CodedSorting.CommonMSDIntervalRoutine.embed`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Routine.lean#L17)

**类型**

```lean
{A : ℕ} → Fin A → Fin (A + 3)
```

**定义**

```lean
fun {A} tag => ⟨↑tag, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonMSDIntervalRoutine.embed._proof_2](Routine.definitions.md#def-2a00a33bdb4ee48b)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-5f24b8248fd156de"></a>
## `CodedSorting.CommonMSDIntervalRoutine.extractTag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Routine.lean#L18)

**类型**

```lean
(A : ℕ) → Fin (A + 3)
```

**定义**

```lean
fun A => ⟨A, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonMSDIntervalRoutine.extractTag._proof_4](Routine.definitions.md#def-66be5126876a630b)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-64928273e6b3dc30"></a>
## `CodedSorting.CommonMSDIntervalRoutine.restoreTag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Routine.lean#L19)

**类型**

```lean
(A : ℕ) → Fin (A + 3)
```

**定义**

```lean
fun A => ⟨A + 1, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonMSDIntervalRoutine.restoreTag._proof_6](Routine.definitions.md#def-167ad43bbee52155)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-db4e82e447ca606d"></a>
## `CodedSorting.CommonMSDIntervalRoutine.doneTag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Routine.lean#L20)

**类型**

```lean
(A : ℕ) → Fin (A + 3)
```

**定义**

```lean
fun A => ⟨A + 2, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonMSDIntervalRoutine.doneTag._proof_8](Routine.definitions.md#def-d3e0310b02932192)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-9448d2fdb0ad3d1a"></a>
## `CodedSorting.CommonMSDIntervalRoutine.routine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Routine.lean#L22)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    ℕ →
      ℕ →
        ℕ →
          ℕ → ℕ → {A : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → CodedSorting.CommonMSDRoutine.Routine q (A + 3)
```

**定义**

```lean
fun q reader n base O input target {A} r =>
  { entry := CodedSorting.CommonMSDIntervalRoutine.extractTag A,
    body := fun tag =>
      if ht : ↑tag < A then r.body ⟨↑tag, ht⟩
      else
        if ↑tag = A then CodedSorting.CommonIntervalAdapter.extract q reader n base O input
        else if ↑tag = A + 1 then CodedSorting.CommonIntervalAdapter.restore q reader n base O target else [],
    next := fun tag ram =>
      if ht : ↑tag < A then
        if r.terminal ⟨↑tag, ht⟩ = true then CodedSorting.CommonMSDIntervalRoutine.restoreTag A
        else CodedSorting.CommonMSDIntervalRoutine.embed (r.next ⟨↑tag, ht⟩ ram)
      else
        if ↑tag = A then CodedSorting.CommonMSDIntervalRoutine.embed r.entry
        else CodedSorting.CommonMSDIntervalRoutine.doneTag A,
    terminal := fun tag => decide (↑tag = A + 2), safe := ⋯, terminal_empty := ⋯ }
```

**继续展开**

- [CodedSorting.CommonMSDIntervalRoutine.routine._proof_12](Routine.definitions.md#def-f8a97bccdf3c1c04)
- [CodedSorting.CommonLeafProgram.RAM](../../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonMSDRoutine.Routine.next](../../Framework/Routine.definitions.md#def-98bfba14816beee3)
- [CodedSorting.CommonMSDIntervalRoutine.embed](Routine.definitions.md#def-462240059bcf7402)
- [CodedSorting.CommonMSDRoutine.Routine.terminal](../../Framework/Routine.definitions.md#def-d011f4b47a3678f6)
- [CodedSorting.CommonMSDIntervalRoutine.doneTag](Routine.definitions.md#def-db4e82e447ca606d)
- [CodedSorting.CommonIntervalAdapter.restore](../../../../Shared/Memory/IntervalAdapter.definitions.md#def-af8ddb7ab659c71c)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonMSDIntervalRoutine.restoreTag](Routine.definitions.md#def-64928273e6b3dc30)
- [CodedSorting.CommonMSDIntervalRoutine.routine._proof_13](Routine.definitions.md#def-a8d7adacff52f270)
- [CodedSorting.CommonMSDRoutine.Routine.body](../../Framework/Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonMSDRoutine.Routine](../../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDIntervalRoutine.extractTag](Routine.definitions.md#def-5f24b8248fd156de)
- [CodedSorting.CommonMSDRoutine.Routine.mk](../../Framework/Routine.definitions.md#def-e820937768ee9afd)
- [CodedSorting.CommonIntervalAdapter.extract](../../../../Shared/Memory/IntervalAdapter.definitions.md#def-18d290b3cabddc31)

**基础库名称**

`Fin.mk`, `instDecidableEqBool`, `instOfNatNat`, `Fin.val`, `dite`, `Bool.true`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Decidable.decide`, `Eq`, `Not`, `List.nil`, `ite`

<a id="def-d3e0310b02932192"></a>
## `CodedSorting.CommonMSDIntervalRoutine.doneTag._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ (A : ℕ), A + 2 < A + 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-2a00a33bdb4ee48b"></a>
## `CodedSorting.CommonMSDIntervalRoutine.embed._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ {A : ℕ} (tag : Fin A), ↑tag < A + 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-66be5126876a630b"></a>
## `CodedSorting.CommonMSDIntervalRoutine.extractTag._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ (A : ℕ), A < A + 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-167ad43bbee52155"></a>
## `CodedSorting.CommonMSDIntervalRoutine.restoreTag._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ (A : ℕ), A + 1 < A + 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-f8a97bccdf3c1c04"></a>
## `CodedSorting.CommonMSDIntervalRoutine.routine._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (n base O input target : ℕ) {A : ℕ} (r : CodedSorting.CommonMSDRoutine.Routine q A) (tag : Fin (A + 3)),
  ∀
    i ∈
      if ht : ↑tag < A then r.body ⟨↑tag, ht⟩
      else
        if ↑tag = A then CodedSorting.CommonIntervalAdapter.extract q reader n base O input
        else if ↑tag = A + 1 then CodedSorting.CommonIntervalAdapter.restore q reader n base O target else [],
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.restore](../../../../Shared/Memory/IntervalAdapter.definitions.md#def-af8ddb7ab659c71c)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonMSDRoutine.Routine.body](../../Framework/Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMSDRoutine.Routine](../../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonIntervalAdapter.extract](../../../../Shared/Memory/IntervalAdapter.definitions.md#def-18d290b3cabddc31)

**基础库名称**

`Membership.mem`, `Fin.mk`, `instOfNatNat`, `Fin.val`, `dite`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Not`, `List.nil`, `ite`

<a id="def-a8d7adacff52f270"></a>
## `CodedSorting.CommonMSDIntervalRoutine.routine._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (n base O input target : ℕ) {A : ℕ} (r : CodedSorting.CommonMSDRoutine.Routine q A) (tag : Fin (A + 3)),
  decide (↑tag = A + 2) = true →
    (if ht : ↑tag < A then r.body ⟨↑tag, ht⟩
      else
        if ↑tag = A then CodedSorting.CommonIntervalAdapter.extract q reader n base O input
        else if ↑tag = A + 1 then CodedSorting.CommonIntervalAdapter.restore q reader n base O target else []) =
      []
```

**继续展开**

- [CodedSorting.CommonIntervalAdapter.restore](../../../../Shared/Memory/IntervalAdapter.definitions.md#def-af8ddb7ab659c71c)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonMSDRoutine.Routine.body](../../Framework/Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMSDRoutine.Routine](../../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonIntervalAdapter.extract](../../../../Shared/Memory/IntervalAdapter.definitions.md#def-18d290b3cabddc31)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `Fin.val`, `dite`, `Bool.true`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Decidable.decide`, `Eq`, `Not`, `List.nil`, `ite`
