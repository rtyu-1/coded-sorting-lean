# Routine 的定义

[源码](Routine.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-231701da583a9604"></a>
## `CodedSorting.CommonMSDRoutine.Routine`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Routine.lean#L15)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDRoutine.Routine.mk](Routine.definitions.md#def-e820937768ee9afd)

**基础库名称**

`Nat`

<a id="def-e820937768ee9afd"></a>
## `CodedSorting.CommonMSDRoutine.Routine.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Routine.lean#L15)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A : ℕ} →
    Fin A →
      (body : Fin A → List (CodedSorting.CommonStaticSchedule.Instruction q)) →
        (Fin A → CodedSorting.CommonLeafProgram.RAM q → Fin A) →
          (terminal : Fin A → Bool) →
            (∀ (tag : Fin A), ∀ i ∈ body tag, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
              (∀ (tag : Fin A), terminal tag = true → body tag = []) → CodedSorting.CommonMSDRoutine.Routine q A
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `Bool.true`, `List`, `List.instMembership`, `Nat`, `Bool`, `Fin`, `Eq`, `List.nil`

<a id="def-647a853c84302453"></a>
## `CodedSorting.CommonMSDRoutine.Routine.entry`

读取 `CodedSorting.CommonMSDRoutine.Routine` 的 `entry` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Routine.lean#L16)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → Fin A
```

**定义**

```lean
fun q A self => self.1
```

**继续展开**

- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`, `Fin`

<a id="def-b2d665a14c5d2a8a"></a>
## `CodedSorting.CommonMSDRoutine.Routine.body`

读取 `CodedSorting.CommonMSDRoutine.Routine` 的 `body` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Routine.lean#L17)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → Fin A → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q A self => self.2
```

**继续展开**

- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List`, `Nat`, `Fin`

<a id="def-98bfba14816beee3"></a>
## `CodedSorting.CommonMSDRoutine.Routine.next`

读取 `CodedSorting.CommonMSDRoutine.Routine` 的 `next` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Routine.lean#L18)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → Fin A → CodedSorting.CommonLeafProgram.RAM q → Fin A
```

**定义**

```lean
fun q A self => self.3
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`, `Fin`

<a id="def-d011f4b47a3678f6"></a>
## `CodedSorting.CommonMSDRoutine.Routine.terminal`

读取 `CodedSorting.CommonMSDRoutine.Routine` 的 `terminal` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Routine.lean#L19)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → Fin A → Bool
```

**定义**

```lean
fun q A self => self.4
```

**继续展开**

- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`, `Bool`, `Fin`

<a id="def-e146f1f041d7ef5a"></a>
## `CodedSorting.CommonMSDRoutine.Routine.successor`

读取 `CodedSorting.CommonMSDRoutine.Routine` 的 `successor` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Routine.lean#L26)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → Fin A → CodedSorting.CommonLeafProgram.RAM q → Fin A
```

**定义**

```lean
fun {q} {A} r tag ram => r.next tag (CodedSorting.CommonStaticSchedule.setPC q 0 ram)
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonMSDRoutine.Routine.next](Routine.definitions.md#def-98bfba14816beee3)
- [CodedSorting.CommonStaticSchedule.setPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-8019447113f5daf6)
- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-5c1175da72799e18"></a>
## `CodedSorting.CommonMSDRoutine.Routine.transition`

读取 `CodedSorting.CommonMSDRoutine.Routine` 的 `transition` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Routine.lean#L33)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A : ℕ} →
    CodedSorting.CommonMSDRoutine.Routine q A →
      ℕ → Fin A → CodedSorting.CommonLeafProgram.RAM q → CodedSorting.CommonLeafProgram.RAM q
```

**定义**

```lean
fun {q} {A} r stride tag ram => CodedSorting.CommonStaticSchedule.setPC q (↑(r.successor tag ram) * stride) ram
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonStaticSchedule.setPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-8019447113f5daf6)
- [CodedSorting.CommonMSDRoutine.Routine.successor](Routine.definitions.md#def-e146f1f041d7ef5a)
- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.val`, `Nat`, `Fin`, `instHMul`

<a id="def-965de1a0fdc439c9"></a>
## `CodedSorting.CommonMSDRoutine.Routine.policy`

读取 `CodedSorting.CommonMSDRoutine.Routine` 的 `policy` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Routine.lean#L36)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → ℕ → CodedSorting.CommonSortingNormalization.SourcePolicy q
```

**定义**

```lean
fun {q} {A} r stride => CodedSorting.CommonTaggedController.policy q stride r.body r.terminal (r.transition stride)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourcePolicy](../../Resources/Framework/NormalizationFrames.definitions.md#def-1812a6349a1bc9a7)
- [CodedSorting.CommonMSDRoutine.Routine.terminal](Routine.definitions.md#def-d011f4b47a3678f6)
- [CodedSorting.CommonMSDRoutine.Routine.body](Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDRoutine.Routine.transition](Routine.definitions.md#def-5c1175da72799e18)
- [CodedSorting.CommonTaggedController.policy](../../../Shared/Memory/TaggedController.definitions.md#def-2aa68f130c0943c6)

**基础库名称**

`Nat`

<a id="def-650143401b3f700d"></a>
## `CodedSorting.CommonMSDRoutinePad.embed`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Routine.lean#L209)

**类型**

```lean
{A B : ℕ} → A ≤ B → Fin A → Fin B
```

**定义**

```lean
fun {A B} h tag => ⟨↑tag, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonMSDRoutinePad.embed._proof_1](Routine.definitions.md#def-46a21148f74a04c9)

**基础库名称**

`Fin.mk`, `LE.le`, `instLENat`, `Fin.val`, `Nat`, `Fin`

<a id="def-46914cb3fda49d20"></a>
## `CodedSorting.CommonMSDRoutinePad.extend`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Routine.lean#L212)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {A B : ℕ} → CodedSorting.CommonMSDRoutine.Routine q A → A ≤ B → CodedSorting.CommonMSDRoutine.Routine q B
```

**定义**

```lean
fun {q} {A B} r h =>
  { entry := CodedSorting.CommonMSDRoutinePad.embed h r.entry,
    body := fun tag => if ht : ↑tag < A then r.body ⟨↑tag, ht⟩ else [],
    next := fun tag ram =>
      if ht : ↑tag < A then CodedSorting.CommonMSDRoutinePad.embed h (r.next ⟨↑tag, ht⟩ ram) else tag,
    terminal := fun tag => if ht : ↑tag < A then r.terminal ⟨↑tag, ht⟩ else true, safe := ⋯, terminal_empty := ⋯ }
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonMSDRoutine.Routine.next](Routine.definitions.md#def-98bfba14816beee3)
- [CodedSorting.CommonMSDRoutine.Routine.terminal](Routine.definitions.md#def-d011f4b47a3678f6)
- [CodedSorting.CommonMSDRoutinePad.embed](Routine.definitions.md#def-650143401b3f700d)
- [CodedSorting.CommonMSDRoutine.Routine.body](Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.CommonMSDRoutine.Routine.entry](Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDRoutinePad.extend._proof_2](Routine.definitions.md#def-fce90baf5cb026f9)
- [CodedSorting.CommonMSDRoutinePad.extend._proof_3](Routine.definitions.md#def-3ff1397cf727d97a)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDRoutine.Routine.mk](Routine.definitions.md#def-e820937768ee9afd)

**基础库名称**

`Fin.mk`, `LE.le`, `instLENat`, `Fin.val`, `dite`, `Bool.true`, `List`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instLTNat`, `Fin`, `Not`, `List.nil`

<a id="def-46a21148f74a04c9"></a>
## `CodedSorting.CommonMSDRoutinePad.embed._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ {A B : ℕ}, A ≤ B → ∀ (tag : Fin A), ↑tag < B
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `LE.le`, `instLENat`, `Fin.val`, `Nat.instPreorder`, `Nat`, `LT.lt`, `Fin`

<a id="def-fce90baf5cb026f9"></a>
## `CodedSorting.CommonMSDRoutinePad.extend._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {A B : ℕ} (r : CodedSorting.CommonMSDRoutine.Routine q A)
  (tag : Fin B), ∀ i ∈ if ht : ↑tag < A then r.body ⟨↑tag, ht⟩ else [], CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonMSDRoutine.Routine.body](Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `Fin.mk`, `Fin.val`, `dite`, `List`, `List.instMembership`, `Nat`, `LT.lt`, `Nat.decLt`, `instLTNat`, `Fin`, `Not`, `List.nil`

<a id="def-3ff1397cf727d97a"></a>
## `CodedSorting.CommonMSDRoutinePad.extend._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Routine.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {A B : ℕ} (r : CodedSorting.CommonMSDRoutine.Routine q A)
  (tag : Fin B),
  (if ht : ↑tag < A then r.terminal ⟨↑tag, ht⟩ else true) = true →
    (if ht : ↑tag < A then r.body ⟨↑tag, ht⟩ else []) = []
```

**继续展开**

- [CodedSorting.CommonMSDRoutine.Routine.terminal](Routine.definitions.md#def-d011f4b47a3678f6)
- [CodedSorting.CommonMSDRoutine.Routine.body](Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.CommonMSDRoutine.Routine](Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`Fin.mk`, `Fin.val`, `dite`, `Bool.true`, `List`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instLTNat`, `Fin`, `Eq`, `Not`, `List.nil`
