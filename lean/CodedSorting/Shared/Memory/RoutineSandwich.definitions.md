# RoutineSandwich 的定义

[源码](RoutineSandwich.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-f5732497a0e73a48"></a>
## `CodedSorting.CommonRoutineSandwich.embed`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RoutineSandwich.lean#L15)

**类型**

```lean
{A : ℕ} → Fin A → Fin (A + 3)
```

**定义**

```lean
fun {A} tag => ⟨↑tag, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonRoutineSandwich.embed._proof_2](RoutineSandwich.definitions.md#def-ba7e1a4e5da672c8)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-18d557d116ab0a02"></a>
## `CodedSorting.CommonRoutineSandwich.beginTag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RoutineSandwich.lean#L16)

**类型**

```lean
(A : ℕ) → Fin (A + 3)
```

**定义**

```lean
fun A => ⟨A, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonRoutineSandwich.beginTag._proof_4](RoutineSandwich.definitions.md#def-4c2bbef92a50eb30)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-0b8694a57f68e1ff"></a>
## `CodedSorting.CommonRoutineSandwich.endTag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RoutineSandwich.lean#L17)

**类型**

```lean
(A : ℕ) → Fin (A + 3)
```

**定义**

```lean
fun A => ⟨A + 1, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonRoutineSandwich.endTag._proof_6](RoutineSandwich.definitions.md#def-06584e86d64d0d84)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-f508d6b3057330b1"></a>
## `CodedSorting.CommonRoutineSandwich.doneTag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RoutineSandwich.lean#L18)

**类型**

```lean
(A : ℕ) → Fin (A + 3)
```

**定义**

```lean
fun A => ⟨A + 2, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonRoutineSandwich.doneTag._proof_8](RoutineSandwich.definitions.md#def-7436d83eb344d03b)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-173e31029a8382dd"></a>
## `CodedSorting.CommonRoutineSandwich.routine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RoutineSandwich.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (pre post : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
    (∀ i ∈ pre, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
      (∀ i ∈ post, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
        {A : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → CodedSorting.CommonMSDRoutine.Routine q (A + 3)
```

**定义**

```lean
fun q pre post hpre hpost {A} r =>
  { entry := CodedSorting.CommonRoutineSandwich.beginTag A,
    body := fun tag =>
      if ht : ↑tag < A then r.body ⟨↑tag, ht⟩ else if ↑tag = A then pre else if ↑tag = A + 1 then post else [],
    next := fun tag ram =>
      if ht : ↑tag < A then
        if r.terminal ⟨↑tag, ht⟩ = true then CodedSorting.CommonRoutineSandwich.endTag A
        else CodedSorting.CommonRoutineSandwich.embed (r.next ⟨↑tag, ht⟩ ram)
      else
        if ↑tag = A then CodedSorting.CommonRoutineSandwich.embed r.entry
        else CodedSorting.CommonRoutineSandwich.doneTag A,
    terminal := fun tag => decide (↑tag = A + 2), safe := ⋯, terminal_empty := ⋯ }
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonMSDRoutine.Routine.next](../../Sorting/Radix/Framework/Routine.definitions.md#def-98bfba14816beee3)
- [CodedSorting.CommonRoutineSandwich.routine._proof_12](RoutineSandwich.definitions.md#def-0dd3b79b56752388)
- [CodedSorting.CommonMSDRoutine.Routine.terminal](../../Sorting/Radix/Framework/Routine.definitions.md#def-d011f4b47a3678f6)
- [CodedSorting.CommonMSDRoutine.Routine.body](../../Sorting/Radix/Framework/Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.CommonRoutineSandwich.beginTag](RoutineSandwich.definitions.md#def-18d557d116ab0a02)
- [CodedSorting.CommonRoutineSandwich.doneTag](RoutineSandwich.definitions.md#def-f508d6b3057330b1)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Sorting/Radix/Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonMSDRoutine.Routine](../../Sorting/Radix/Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDRoutine.Routine.mk](../../Sorting/Radix/Framework/Routine.definitions.md#def-e820937768ee9afd)
- [CodedSorting.CommonRoutineSandwich.routine._proof_13](RoutineSandwich.definitions.md#def-d119c474472a44b1)
- [CodedSorting.CommonRoutineSandwich.embed](RoutineSandwich.definitions.md#def-f5732497a0e73a48)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonRoutineSandwich.endTag](RoutineSandwich.definitions.md#def-0b8694a57f68e1ff)

**基础库名称**

`Membership.mem`, `Fin.mk`, `instDecidableEqBool`, `instOfNatNat`, `Fin.val`, `dite`, `Bool.true`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Decidable.decide`, `Eq`, `Not`, `List.nil`, `ite`

<a id="def-4c2bbef92a50eb30"></a>
## `CodedSorting.CommonRoutineSandwich.beginTag._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RoutineSandwich.lean)

**类型**

```lean
∀ (A : ℕ), A < A + 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-7436d83eb344d03b"></a>
## `CodedSorting.CommonRoutineSandwich.doneTag._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RoutineSandwich.lean)

**类型**

```lean
∀ (A : ℕ), A + 2 < A + 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-ba7e1a4e5da672c8"></a>
## `CodedSorting.CommonRoutineSandwich.embed._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RoutineSandwich.lean)

**类型**

```lean
∀ {A : ℕ} (tag : Fin A), ↑tag < A + 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-06584e86d64d0d84"></a>
## `CodedSorting.CommonRoutineSandwich.endTag._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RoutineSandwich.lean)

**类型**

```lean
∀ (A : ℕ), A + 1 < A + 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-0dd3b79b56752388"></a>
## `CodedSorting.CommonRoutineSandwich.routine._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RoutineSandwich.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (pre post : List (CodedSorting.CommonStaticSchedule.Instruction q)),
  (∀ i ∈ pre, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
    (∀ i ∈ post, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
      ∀ {A : ℕ} (r : CodedSorting.CommonMSDRoutine.Routine q A) (tag : Fin (A + 3)),
        ∀ i ∈ if ht : ↑tag < A then r.body ⟨↑tag, ht⟩ else if ↑tag = A then pre else if ↑tag = A + 1 then post else [],
          CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonMSDRoutine.Routine.body](../../Sorting/Radix/Framework/Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.CommonMSDRoutine.Routine](../../Sorting/Radix/Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `Fin.mk`, `instOfNatNat`, `Fin.val`, `dite`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Not`, `List.nil`, `ite`

<a id="def-d119c474472a44b1"></a>
## `CodedSorting.CommonRoutineSandwich.routine._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RoutineSandwich.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (pre post : List (CodedSorting.CommonStaticSchedule.Instruction q)) {A : ℕ}
  (r : CodedSorting.CommonMSDRoutine.Routine q A) (tag : Fin (A + 3)),
  decide (↑tag = A + 2) = true →
    (if ht : ↑tag < A then r.body ⟨↑tag, ht⟩ else if ↑tag = A then pre else if ↑tag = A + 1 then post else []) = []
```

**继续展开**

- [CodedSorting.CommonMSDRoutine.Routine.body](../../Sorting/Radix/Framework/Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.CommonMSDRoutine.Routine](../../Sorting/Radix/Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `Fin.val`, `dite`, `Bool.true`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Decidable.decide`, `Eq`, `Not`, `List.nil`, `ite`
