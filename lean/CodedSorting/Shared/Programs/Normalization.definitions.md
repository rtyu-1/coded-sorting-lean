# Normalization 的定义

[源码](Normalization.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-674596978a99f625"></a>
## `CodedSorting.Normalization.Words`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L21)

**类型**

```lean
ℕ → Type u_1 → Type u_1
```

**定义**

```lean
fun n Word => Fin n → Word
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`, `Fin`

<a id="def-18f3e234560b5b4a"></a>
## `CodedSorting.Normalization.Disk`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L22)

**类型**

```lean
ℕ → ℕ → Type u_1 → Type u_1
```

**定义**

```lean
fun blocks size Word => Fin blocks → CodedSorting.Normalization.Words size Word
```

**继续展开**

- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)

**基础库名称**

`Nat`, `Fin`

<a id="def-532b4e9511b14109"></a>
## `CodedSorting.Normalization.Window`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Normalization.lean#L26)

**类型**

```lean
ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.Normalization.Window.mk](Normalization.definitions.md#def-50fd7e7bb45579b5)

**基础库名称**

`Nat`

<a id="def-50fd7e7bb45579b5"></a>
## `CodedSorting.Normalization.Window.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Normalization.lean#L27)

**类型**

```lean
{L b : ℕ} → (base : ℕ) → base + b ≤ L → CodedSorting.Normalization.Window L b
```

**继续展开**

- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-62b64a40f69e4b5b"></a>
## `CodedSorting.Normalization.Window.base`

读取 `CodedSorting.Normalization.Window` 的 `base` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Normalization.lean#L28)

**类型**

```lean
{L b : ℕ} → CodedSorting.Normalization.Window L b → ℕ
```

**定义**

```lean
fun L b self => self.1
```

**继续展开**

- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)

**基础库名称**

`Nat`

<a id="def-fcede4fc2d057680"></a>
## `CodedSorting.Normalization.load`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L31)

**类型**

```lean
{Word : Type u_1} →
  {L b : ℕ} →
    CodedSorting.Normalization.Words L Word →
      CodedSorting.Normalization.Window L b →
        CodedSorting.Normalization.Words b Word → CodedSorting.Normalization.Words L Word
```

**定义**

```lean
fun {Word} {L b} ram w block j => if h : w.base ≤ ↑j ∧ ↑j < w.base + b then block ⟨↑j - w.base, ⋯⟩ else ram j
```

**继续展开**

- [CodedSorting.Normalization.load._proof_2](Normalization.definitions.md#def-d8efe6617aaa7011)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Window.base](Normalization.definitions.md#def-62b64a40f69e4b5b)

**基础库名称**

`HSub.hSub`, `Fin.mk`, `instSubNat`, `LE.le`, `instLENat`, `Fin.val`, `dite`, `instHAdd`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instLTNat`, `instDecidableAnd`, `Fin`, `Not`, `Nat.decLe`

<a id="def-97003b863ad4a44f"></a>
## `CodedSorting.Normalization.slice`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L38)

**类型**

```lean
{Word : Type u_1} →
  {L b : ℕ} →
    CodedSorting.Normalization.Words L Word →
      CodedSorting.Normalization.Window L b → CodedSorting.Normalization.Words b Word
```

**定义**

```lean
fun {Word} {L b} ram w j => ram ⟨w.base + ↑j, ⋯⟩
```

**继续展开**

- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Window.base](Normalization.definitions.md#def-62b64a40f69e4b5b)
- [CodedSorting.Normalization.slice._proof_4](Normalization.definitions.md#def-fe06ac6510e17fab)

**基础库名称**

`Fin.mk`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-575e6dd1226e4cee"></a>
## `CodedSorting.Normalization.blockPrefix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L42)

**类型**

```lean
{Word : Type u_1} →
  {b B : ℕ} → b ≤ B → CodedSorting.Normalization.Words B Word → CodedSorting.Normalization.Words b Word
```

**定义**

```lean
fun {Word} {b B} h block j => block (Fin.castLE h j)
```

**继续展开**

- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)

**基础库名称**

`Fin.castLE`, `LE.le`, `instLENat`, `Nat`, `Fin`

<a id="def-97797717e5f5913c"></a>
## `CodedSorting.Normalization.pack`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L46)

**类型**

```lean
{Word : Type u_1} → {b B : ℕ} → Word → CodedSorting.Normalization.Words b Word → CodedSorting.Normalization.Words B Word
```

**定义**

```lean
fun {Word} {b B} padding block j => if h : ↑j < b then block ⟨↑j, h⟩ else padding
```

**继续展开**

- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)

**基础库名称**

`Fin.mk`, `Fin.val`, `dite`, `Nat`, `LT.lt`, `Nat.decLt`, `instLTNat`, `Fin`, `Not`

<a id="def-fe5b3999cdd6a29d"></a>
## `CodedSorting.Normalization.LogicalState`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Normalization.lean#L55)

**类型**

```lean
ℕ → ℕ → ℕ → Type u_2 → Type u_2
```

**继续展开**

- [CodedSorting.Normalization.LogicalState.mk](Normalization.definitions.md#def-406ff6c0f82deb9d)

**基础库名称**

`Nat`

<a id="def-406ff6c0f82deb9d"></a>
## `CodedSorting.Normalization.LogicalState.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Normalization.lean#L55)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} →
    CodedSorting.Normalization.Words L Word →
      CodedSorting.Normalization.Disk D b Word → CodedSorting.Normalization.LogicalState L b D Word
```

**继续展开**

- [CodedSorting.Normalization.Disk](Normalization.definitions.md#def-18f3e234560b5b4a)
- [CodedSorting.Normalization.LogicalState](Normalization.definitions.md#def-fe5b3999cdd6a29d)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)

**基础库名称**

`Nat`

<a id="def-234012a079102e4e"></a>
## `CodedSorting.Normalization.LogicalState.ram`

读取 `CodedSorting.Normalization.LogicalState` 的 `ram` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Normalization.lean#L56)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} → CodedSorting.Normalization.LogicalState L b D Word → CodedSorting.Normalization.Words L Word
```

**定义**

```lean
fun L b D Word self => self.1
```

**继续展开**

- [CodedSorting.Normalization.LogicalState](Normalization.definitions.md#def-fe5b3999cdd6a29d)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)

**基础库名称**

`Nat`

<a id="def-0daf3d2d8ddbdccc"></a>
## `CodedSorting.Normalization.LogicalState.disk`

读取 `CodedSorting.Normalization.LogicalState` 的 `disk` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Normalization.lean#L57)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} → CodedSorting.Normalization.LogicalState L b D Word → CodedSorting.Normalization.Disk D b Word
```

**定义**

```lean
fun L b D Word self => self.2
```

**继续展开**

- [CodedSorting.Normalization.Disk](Normalization.definitions.md#def-18f3e234560b5b4a)
- [CodedSorting.Normalization.LogicalState](Normalization.definitions.md#def-fe5b3999cdd6a29d)

**基础库名称**

`Nat`

<a id="def-fd728dbf7842361d"></a>
## `CodedSorting.Normalization.PhysicalState`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Normalization.lean#L59)

**类型**

```lean
ℕ → ℕ → ℕ → Type u_2 → Type u_2
```

**继续展开**

- [CodedSorting.Normalization.PhysicalState.mk](Normalization.definitions.md#def-2b2feddbbfb01c5b)

**基础库名称**

`Nat`

<a id="def-2b2feddbbfb01c5b"></a>
## `CodedSorting.Normalization.PhysicalState.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Normalization.lean#L59)

**类型**

```lean
{L B D : ℕ} →
  {Word : Type u_2} →
    CodedSorting.Normalization.Words L Word →
      CodedSorting.Normalization.Words B Word →
        CodedSorting.Normalization.Disk D B Word → CodedSorting.Normalization.PhysicalState L B D Word
```

**继续展开**

- [CodedSorting.Normalization.Disk](Normalization.definitions.md#def-18f3e234560b5b4a)
- [CodedSorting.Normalization.PhysicalState](Normalization.definitions.md#def-fd728dbf7842361d)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)

**基础库名称**

`Nat`

<a id="def-401047fe136aec1d"></a>
## `CodedSorting.Normalization.PhysicalState.ram`

读取 `CodedSorting.Normalization.PhysicalState` 的 `ram` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Normalization.lean#L60)

**类型**

```lean
{L B D : ℕ} →
  {Word : Type u_2} → CodedSorting.Normalization.PhysicalState L B D Word → CodedSorting.Normalization.Words L Word
```

**定义**

```lean
fun L B D Word self => self.1
```

**继续展开**

- [CodedSorting.Normalization.PhysicalState](Normalization.definitions.md#def-fd728dbf7842361d)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)

**基础库名称**

`Nat`

<a id="def-74cb96dbfc7116c1"></a>
## `CodedSorting.Normalization.PhysicalState.buffer`

读取 `CodedSorting.Normalization.PhysicalState` 的 `buffer` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Normalization.lean#L61)

**类型**

```lean
{L B D : ℕ} →
  {Word : Type u_2} → CodedSorting.Normalization.PhysicalState L B D Word → CodedSorting.Normalization.Words B Word
```

**定义**

```lean
fun L B D Word self => self.2
```

**继续展开**

- [CodedSorting.Normalization.PhysicalState](Normalization.definitions.md#def-fd728dbf7842361d)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)

**基础库名称**

`Nat`

<a id="def-df054804f555e188"></a>
## `CodedSorting.Normalization.PhysicalState.disk`

读取 `CodedSorting.Normalization.PhysicalState` 的 `disk` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Normalization.lean#L62)

**类型**

```lean
{L B D : ℕ} →
  {Word : Type u_2} → CodedSorting.Normalization.PhysicalState L B D Word → CodedSorting.Normalization.Disk D B Word
```

**定义**

```lean
fun L B D Word self => self.3
```

**继续展开**

- [CodedSorting.Normalization.Disk](Normalization.definitions.md#def-18f3e234560b5b4a)
- [CodedSorting.Normalization.PhysicalState](Normalization.definitions.md#def-fd728dbf7842361d)

**基础库名称**

`Nat`

<a id="def-5d1402e119d2b0bd"></a>
## `CodedSorting.Normalization.Command`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Normalization.lean#L64)

**类型**

```lean
ℕ → ℕ → ℕ → Type u_2 → Type u_2
```

**继续展开**

- [CodedSorting.Normalization.Command.write](Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.Normalization.Command.read](Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.Normalization.Command.localOp](Normalization.definitions.md#def-9456a9cd06b765ae)

**基础库名称**

`Nat`

<a id="def-d5874f9d23d9c310"></a>
## `CodedSorting.Normalization.Command.casesOn`

读取 `CodedSorting.Normalization.Command` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Normalization.lean#L64)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} →
    {motive : CodedSorting.Normalization.Command L b D Word → Sort u} →
      (t : CodedSorting.Normalization.Command L b D Word) →
        ((f : CodedSorting.Normalization.Words L Word → CodedSorting.Normalization.Words L Word) →
            motive (CodedSorting.Normalization.Command.localOp f)) →
          ((address : Fin D) →
              (window : CodedSorting.Normalization.Window L b) →
                motive (CodedSorting.Normalization.Command.read address window)) →
            ((address : Fin D) →
                (window : CodedSorting.Normalization.Window L b) →
                  motive (CodedSorting.Normalization.Command.write address window)) →
              motive t
```

**定义**

```lean
fun {L b D} {Word} {motive} t localOp read write =>
  CodedSorting.Normalization.Command.rec (fun f => localOp f) (fun address window => read address window)
    (fun address window => write address window) t
```

**继续展开**

- [CodedSorting.Normalization.Command.write](Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.Normalization.Command.read](Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command.rec](Normalization.definitions.md#def-81f2cd217f4998c2)
- [CodedSorting.Normalization.Command.localOp](Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`, `Fin`

<a id="def-81f2cd217f4998c2"></a>
## `CodedSorting.Normalization.Command.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](Normalization.lean#L64)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} →
    {motive : CodedSorting.Normalization.Command L b D Word → Sort u} →
      ((f : CodedSorting.Normalization.Words L Word → CodedSorting.Normalization.Words L Word) →
          motive (CodedSorting.Normalization.Command.localOp f)) →
        ((address : Fin D) →
            (window : CodedSorting.Normalization.Window L b) →
              motive (CodedSorting.Normalization.Command.read address window)) →
          ((address : Fin D) →
              (window : CodedSorting.Normalization.Window L b) →
                motive (CodedSorting.Normalization.Command.write address window)) →
            (t : CodedSorting.Normalization.Command L b D Word) → motive t
```

**继续展开**

- [CodedSorting.Normalization.Command.write](Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.Normalization.Command.read](Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command.localOp](Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`, `Fin`

<a id="def-9456a9cd06b765ae"></a>
## `CodedSorting.Normalization.Command.localOp`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Normalization.lean#L67)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} →
    (CodedSorting.Normalization.Words L Word → CodedSorting.Normalization.Words L Word) →
      CodedSorting.Normalization.Command L b D Word
```

**继续展开**

- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`

<a id="def-54b8143801baed43"></a>
## `CodedSorting.Normalization.Command.read`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Normalization.lean#L68)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} → Fin D → CodedSorting.Normalization.Window L b → CodedSorting.Normalization.Command L b D Word
```

**继续展开**

- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`, `Fin`

<a id="def-de92fb94cadb9bcc"></a>
## `CodedSorting.Normalization.Command.write`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Normalization.lean#L69)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} → Fin D → CodedSorting.Normalization.Window L b → CodedSorting.Normalization.Command L b D Word
```

**继续展开**

- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`, `Fin`

<a id="def-84f9b0413bed823d"></a>
## `CodedSorting.Normalization.transferCost`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L71)

**类型**

```lean
{Word : Type u_1} → {L b D : ℕ} → CodedSorting.Normalization.Command L b D Word → ℕ
```

**定义**

```lean
fun {Word} {L b D} x =>
  match x with
  | CodedSorting.Normalization.Command.localOp f => 0
  | CodedSorting.Normalization.Command.read address window => 1
  | CodedSorting.Normalization.Command.write address window => 1
```

**继续展开**

- [CodedSorting.Normalization.transferCost.match_1](Normalization.definitions.md#def-3ef46888448f4fef)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-65568248037e0c07"></a>
## `CodedSorting.Normalization.logicalStep`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L76)

**类型**

```lean
{Word : Type u_1} →
  {L b D : ℕ} →
    CodedSorting.Normalization.Command L b D Word →
      CodedSorting.Normalization.LogicalState L b D Word → CodedSorting.Normalization.LogicalState L b D Word
```

**定义**

```lean
fun {Word} {L b D} cmd s =>
  match cmd with
  | CodedSorting.Normalization.Command.localOp f => { ram := f s.ram, disk := s.disk }
  | CodedSorting.Normalization.Command.read i w =>
    { ram := CodedSorting.Normalization.load s.ram w (s.disk i), disk := s.disk }
  | CodedSorting.Normalization.Command.write i w =>
    { ram := s.ram, disk := Function.update s.disk i (CodedSorting.Normalization.slice s.ram w) }
```

**继续展开**

- [CodedSorting.Normalization.load](Normalization.definitions.md#def-fcede4fc2d057680)
- [CodedSorting.Normalization.LogicalState](Normalization.definitions.md#def-fe5b3999cdd6a29d)
- [CodedSorting.Normalization.LogicalState.ram](Normalization.definitions.md#def-234012a079102e4e)
- [CodedSorting.Normalization.transferCost.match_1](Normalization.definitions.md#def-3ef46888448f4fef)
- [CodedSorting.Normalization.slice](Normalization.definitions.md#def-97003b863ad4a44f)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)
- [CodedSorting.Normalization.LogicalState.mk](Normalization.definitions.md#def-406ff6c0f82deb9d)
- [CodedSorting.Normalization.LogicalState.disk](Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Function.update`, `instDecidableEqFin`, `Nat`, `Fin`

<a id="def-bb8eed12be50f878"></a>
## `CodedSorting.Normalization.logicalBlockSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Normalization.lean#L260)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun B K => max 1 (B / K)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `Nat.instMax_mathlib`, `HDiv.hDiv`, `instOfNatNat`, `Max.max`, `Nat`, `Nat.instDiv`, `OfNat.ofNat`

<a id="def-d8efe6617aaa7011"></a>
## `CodedSorting.Normalization.load._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Normalization.lean)

**类型**

```lean
∀ {L b : ℕ} (w : CodedSorting.Normalization.Window L b) (j : Fin L), w.base ≤ ↑j ∧ ↑j < w.base + b → ↑j - w.base < b
```

**继续展开**

- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Window.base](Normalization.definitions.md#def-62b64a40f69e4b5b)

**基础库名称**

`HSub.hSub`, `instSubNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`

<a id="def-fe06ac6510e17fab"></a>
## `CodedSorting.Normalization.slice._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Normalization.lean)

**类型**

```lean
∀ {L b : ℕ} (w : CodedSorting.Normalization.Window L b) (j : Fin b), w.base + ↑j < L
```

**继续展开**

- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Window.base](Normalization.definitions.md#def-62b64a40f69e4b5b)

**基础库名称**

`Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`

<a id="def-3ef46888448f4fef"></a>
## `CodedSorting.Normalization.transferCost.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Normalization.lean)

**类型**

```lean
{Word : Type u_1} →
  {L b D : ℕ} →
    (motive : CodedSorting.Normalization.Command L b D Word → Sort u_2) →
      (x : CodedSorting.Normalization.Command L b D Word) →
        ((f : CodedSorting.Normalization.Words L Word → CodedSorting.Normalization.Words L Word) →
            motive (CodedSorting.Normalization.Command.localOp f)) →
          ((address : Fin D) →
              (window : CodedSorting.Normalization.Window L b) →
                motive (CodedSorting.Normalization.Command.read address window)) →
            ((address : Fin D) →
                (window : CodedSorting.Normalization.Window L b) →
                  motive (CodedSorting.Normalization.Command.write address window)) →
              motive x
```

**定义**

```lean
fun {Word} {L b D} motive x h_1 h_2 h_3 =>
  CodedSorting.Normalization.Command.casesOn x (fun f => h_1 f) (fun address window => h_2 address window)
    fun address window => h_3 address window
```

**继续展开**

- [CodedSorting.Normalization.Command.write](Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.Normalization.Command.casesOn](Normalization.definitions.md#def-d5874f9d23d9c310)
- [CodedSorting.Normalization.Command.read](Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command.localOp](Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`, `Fin`
