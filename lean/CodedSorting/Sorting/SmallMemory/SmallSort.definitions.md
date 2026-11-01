# SmallSort 的定义

[源码](SmallSort.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-82390a35b2c034e0"></a>
## `CodedSorting.TwoWordBlockLift.Buffer`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L14)

**类型**

```lean
ℕ → Type u_2 → Type u_2
```

**定义**

```lean
fun B W => Fin B → W
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`, `Fin`

<a id="def-25d0a9a7fac3e554"></a>
## `CodedSorting.TwoWordBlockLift.State`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](SmallSort.lean#L15)

**类型**

```lean
ℕ → Type u_2 → Type u_2
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.State.mk](SmallSort.definitions.md#def-da5ed8a7dec082be)

**基础库名称**

`Nat`

<a id="def-da5ed8a7dec082be"></a>
## `CodedSorting.TwoWordBlockLift.State.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L15)

**类型**

```lean
{B : ℕ} →
  {W : Type u_2} →
    CodedSorting.TwoWordBlockLift.Buffer B W →
      CodedSorting.TwoWordBlockLift.Buffer B W →
        (ℕ → CodedSorting.TwoWordBlockLift.Buffer B W) → CodedSorting.TwoWordBlockLift.State B W
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)

**基础库名称**

`Nat`

<a id="def-2383655d2a21d782"></a>
## `CodedSorting.TwoWordBlockLift.State.left`

读取 `CodedSorting.TwoWordBlockLift.State` 的 `left` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SmallSort.lean#L16)

**类型**

```lean
{B : ℕ} → {W : Type u_2} → CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.Buffer B W
```

**定义**

```lean
fun B W self => self.1
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)

**基础库名称**

`Nat`

<a id="def-314a62e565628656"></a>
## `CodedSorting.TwoWordBlockLift.State.right`

读取 `CodedSorting.TwoWordBlockLift.State` 的 `right` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SmallSort.lean#L17)

**类型**

```lean
{B : ℕ} → {W : Type u_2} → CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.Buffer B W
```

**定义**

```lean
fun B W self => self.2
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)

**基础库名称**

`Nat`

<a id="def-1abac0bb04792a30"></a>
## `CodedSorting.TwoWordBlockLift.State.disk`

读取 `CodedSorting.TwoWordBlockLift.State` 的 `disk` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SmallSort.lean#L18)

**类型**

```lean
{B : ℕ} → {W : Type u_2} → CodedSorting.TwoWordBlockLift.State B W → ℕ → CodedSorting.TwoWordBlockLift.Buffer B W
```

**定义**

```lean
fun B W self => self.3
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)

**基础库名称**

`Nat`

<a id="def-23d83d1182c7c157"></a>
## `CodedSorting.TwoWordBlockLift.Command`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](SmallSort.lean#L20)

**类型**

```lean
ℕ → Type u_2 → Type u_2
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command.writeRight](SmallSort.definitions.md#def-4ea9be5d6a479fdd)
- [CodedSorting.TwoWordBlockLift.Command.readLeft](SmallSort.definitions.md#def-27005c471d1432cf)
- [CodedSorting.TwoWordBlockLift.Command.readRight](SmallSort.definitions.md#def-abd0500d4cb89cab)
- [CodedSorting.TwoWordBlockLift.Command.writeLeft](SmallSort.definitions.md#def-460a8fb76a136a38)
- [CodedSorting.TwoWordBlockLift.Command.cpu](SmallSort.definitions.md#def-e28b6e71b42884f6)

**基础库名称**

`Nat`

<a id="def-caa07ad4883d62d1"></a>
## `CodedSorting.TwoWordBlockLift.Command.casesOn`

读取 `CodedSorting.TwoWordBlockLift.Command` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SmallSort.lean#L20)

**类型**

```lean
{B : ℕ} →
  {W : Type u_2} →
    {motive : CodedSorting.TwoWordBlockLift.Command B W → Sort u} →
      (t : CodedSorting.TwoWordBlockLift.Command B W) →
        ((address : ℕ) → motive (CodedSorting.TwoWordBlockLift.Command.readLeft address)) →
          ((address : CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W → ℕ) →
              motive (CodedSorting.TwoWordBlockLift.Command.readRight address)) →
            ((address : ℕ) → motive (CodedSorting.TwoWordBlockLift.Command.writeLeft address)) →
              ((address : CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W → ℕ) →
                  motive (CodedSorting.TwoWordBlockLift.Command.writeRight address)) →
                ((f :
                      CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W →
                        CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W) →
                    motive (CodedSorting.TwoWordBlockLift.Command.cpu f)) →
                  motive t
```

**定义**

```lean
fun {B} {W} {motive} t readLeft readRight writeLeft writeRight cpu =>
  CodedSorting.TwoWordBlockLift.Command.rec (fun address => readLeft address) (fun address => readRight address)
    (fun address => writeLeft address) (fun address => writeRight address) (fun f => cpu f) t
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.Command.writeRight](SmallSort.definitions.md#def-4ea9be5d6a479fdd)
- [CodedSorting.TwoWordBlockLift.Command.readLeft](SmallSort.definitions.md#def-27005c471d1432cf)
- [CodedSorting.TwoWordBlockLift.Command.readRight](SmallSort.definitions.md#def-abd0500d4cb89cab)
- [CodedSorting.TwoWordBlockLift.Command.writeLeft](SmallSort.definitions.md#def-460a8fb76a136a38)
- [CodedSorting.TwoWordBlockLift.Command.cpu](SmallSort.definitions.md#def-e28b6e71b42884f6)
- [CodedSorting.TwoWordBlockLift.Command.rec](SmallSort.definitions.md#def-482235c1a68c3626)

**基础库名称**

`Nat`, `Prod`

<a id="def-482235c1a68c3626"></a>
## `CodedSorting.TwoWordBlockLift.Command.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](SmallSort.lean#L20)

**类型**

```lean
{B : ℕ} →
  {W : Type u_2} →
    {motive : CodedSorting.TwoWordBlockLift.Command B W → Sort u} →
      ((address : ℕ) → motive (CodedSorting.TwoWordBlockLift.Command.readLeft address)) →
        ((address : CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W → ℕ) →
            motive (CodedSorting.TwoWordBlockLift.Command.readRight address)) →
          ((address : ℕ) → motive (CodedSorting.TwoWordBlockLift.Command.writeLeft address)) →
            ((address : CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W → ℕ) →
                motive (CodedSorting.TwoWordBlockLift.Command.writeRight address)) →
              ((f :
                    CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W →
                      CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W) →
                  motive (CodedSorting.TwoWordBlockLift.Command.cpu f)) →
                (t : CodedSorting.TwoWordBlockLift.Command B W) → motive t
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.Command.writeRight](SmallSort.definitions.md#def-4ea9be5d6a479fdd)
- [CodedSorting.TwoWordBlockLift.Command.readLeft](SmallSort.definitions.md#def-27005c471d1432cf)
- [CodedSorting.TwoWordBlockLift.Command.readRight](SmallSort.definitions.md#def-abd0500d4cb89cab)
- [CodedSorting.TwoWordBlockLift.Command.writeLeft](SmallSort.definitions.md#def-460a8fb76a136a38)
- [CodedSorting.TwoWordBlockLift.Command.cpu](SmallSort.definitions.md#def-e28b6e71b42884f6)

**基础库名称**

`Nat`, `Prod`

<a id="def-27005c471d1432cf"></a>
## `CodedSorting.TwoWordBlockLift.Command.readLeft`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L21)

**类型**

```lean
{B : ℕ} → {W : Type u_2} → ℕ → CodedSorting.TwoWordBlockLift.Command B W
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)

**基础库名称**

`Nat`

<a id="def-abd0500d4cb89cab"></a>
## `CodedSorting.TwoWordBlockLift.Command.readRight`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L22)

**类型**

```lean
{B : ℕ} →
  {W : Type u_2} →
    (CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W → ℕ) →
      CodedSorting.TwoWordBlockLift.Command B W
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)

**基础库名称**

`Nat`, `Prod`

<a id="def-460a8fb76a136a38"></a>
## `CodedSorting.TwoWordBlockLift.Command.writeLeft`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L23)

**类型**

```lean
{B : ℕ} → {W : Type u_2} → ℕ → CodedSorting.TwoWordBlockLift.Command B W
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)

**基础库名称**

`Nat`

<a id="def-4ea9be5d6a479fdd"></a>
## `CodedSorting.TwoWordBlockLift.Command.writeRight`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L24)

**类型**

```lean
{B : ℕ} →
  {W : Type u_2} →
    (CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W → ℕ) →
      CodedSorting.TwoWordBlockLift.Command B W
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)

**基础库名称**

`Nat`, `Prod`

<a id="def-e28b6e71b42884f6"></a>
## `CodedSorting.TwoWordBlockLift.Command.cpu`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L25)

**类型**

```lean
{B : ℕ} →
  {W : Type u_2} →
    (CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W →
        CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W) →
      CodedSorting.TwoWordBlockLift.Command B W
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)

**基础库名称**

`Nat`, `Prod`

<a id="def-c2252ee0095dc811"></a>
## `CodedSorting.TwoWordBlockLift.step`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L27)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    CodedSorting.TwoWordBlockLift.Command B W →
      CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W
```

**定义**

```lean
fun {B} {W} cmd s =>
  match cmd with
  | CodedSorting.TwoWordBlockLift.Command.readLeft a => { left := s.disk a, right := s.right, disk := s.disk }
  | CodedSorting.TwoWordBlockLift.Command.readRight a =>
    { left := s.left, right := s.disk (a (s.left, s.right)), disk := s.disk }
  | CodedSorting.TwoWordBlockLift.Command.writeLeft a =>
    { left := s.left, right := s.right, disk := Function.update s.disk a s.left }
  | CodedSorting.TwoWordBlockLift.Command.writeRight a =>
    { left := s.left, right := s.right, disk := Function.update s.disk (a (s.left, s.right)) s.right }
  | CodedSorting.TwoWordBlockLift.Command.cpu f =>
    { left := (f (s.left, s.right)).1, right := (f (s.left, s.right)).2, disk := s.disk }
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.State.mk](SmallSort.definitions.md#def-da5ed8a7dec082be)
- [CodedSorting.TwoWordBlockLift.State.right](SmallSort.definitions.md#def-314a62e565628656)
- [CodedSorting.TwoWordBlockLift.step.match_1](SmallSort.definitions.md#def-3b2d8d18c9199124)
- [CodedSorting.TwoWordBlockLift.State.left](SmallSort.definitions.md#def-2383655d2a21d782)
- [CodedSorting.TwoWordBlockLift.State.disk](SmallSort.definitions.md#def-1abac0bb04792a30)

**基础库名称**

`Function.update`, `Prod.mk`, `Prod.fst`, `Nat`, `instDecidableEqNat`, `Prod`, `Prod.snd`

<a id="def-e4b26507be010962"></a>
## `CodedSorting.TwoWordBlockLift.cost`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L35)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → CodedSorting.TwoWordBlockLift.Command B W → ℕ
```

**定义**

```lean
fun {B} {W} x =>
  match x with
  | CodedSorting.TwoWordBlockLift.Command.cpu f => 0
  | x => 1
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.cost.match_1](SmallSort.definitions.md#def-8c838c260c896442)

**基础库名称**

`instOfNatNat`, `Nat`, `Prod`, `OfNat.ofNat`

<a id="def-88b9ad740a9b80d5"></a>
## `CodedSorting.TwoWordBlockLift.execute`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L38)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    List (CodedSorting.TwoWordBlockLift.Command B W) →
      CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W
```

**定义**

```lean
fun {B} {W} x x_1 =>
  List.brecOn (motive := fun x => CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W) x
    (fun x f x_2 =>
      (match (motive :=
          (x : List (CodedSorting.TwoWordBlockLift.Command B W)) →
            CodedSorting.TwoWordBlockLift.State B W →
              List.below (motive := fun x =>
                  CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W) x →
                CodedSorting.TwoWordBlockLift.State B W)
          x, x_2 with
        | [], s => fun x => s
        | cmd :: rest, s => fun x => x.1 (CodedSorting.TwoWordBlockLift.step cmd s))
        f)
    x_1
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.step](SmallSort.definitions.md#def-c2252ee0095dc811)
- [CodedSorting.TwoWordBlockLift.execute.match_1](SmallSort.definitions.md#def-f7ac38dc95886ce9)

**基础库名称**

`List.brecOn`, `List.cons`, `List`, `PProd`, `Nat`, `List.below`, `List.nil`

<a id="def-d0e569e9b6fa843c"></a>
## `CodedSorting.TwoWordBlockLift.transfers`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L41)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → List (CodedSorting.TwoWordBlockLift.Command B W) → ℕ
```

**定义**

```lean
fun {B} {W} x =>
  List.brecOn x fun x f =>
    (match (motive := (x : List (CodedSorting.TwoWordBlockLift.Command B W)) → List.below x → ℕ) x with
      | [] => fun x => 0
      | cmd :: rest => fun x => CodedSorting.TwoWordBlockLift.cost cmd + x.1)
      f
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.transfers.match_1](SmallSort.definitions.md#def-563f4f87adb5ad7d)
- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.cost](SmallSort.definitions.md#def-e4b26507be010962)

**基础库名称**

`List.brecOn`, `instOfNatNat`, `List.cons`, `List`, `instHAdd`, `Unit`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.below`, `OfNat.ofNat`, `List.nil`

<a id="def-f394483af754d48e"></a>
## `CodedSorting.TwoWordBlockLift.compile`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L48)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    0 < B → ℕ → CodedSorting.TwoWordPhysicalAddresses.Command W → CodedSorting.TwoWordBlockLift.Command B W
```

**定义**

```lean
fun {B} {W} hB base x =>
  match x with
  | CodedSorting.TwoWordPhysicalAddresses.Command.readLeft a =>
    CodedSorting.TwoWordBlockLift.Command.readLeft (base + a)
  | CodedSorting.TwoWordPhysicalAddresses.Command.readRight a =>
    CodedSorting.TwoWordBlockLift.Command.readRight fun x => base + a
  | CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt a =>
    CodedSorting.TwoWordBlockLift.Command.readRight fun r => base + a (r.1 ⟨0, hB⟩, r.2 ⟨0, hB⟩)
  | CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft a =>
    CodedSorting.TwoWordBlockLift.Command.writeLeft (base + a)
  | CodedSorting.TwoWordPhysicalAddresses.Command.writeRight a =>
    CodedSorting.TwoWordBlockLift.Command.writeRight fun r => base + a (r.1 ⟨0, hB⟩, r.2 ⟨0, hB⟩)
  | CodedSorting.TwoWordPhysicalAddresses.Command.localOp f =>
    CodedSorting.TwoWordBlockLift.Command.cpu fun r =>
      let v := f (r.1 ⟨0, hB⟩, r.2 ⟨0, hB⟩);
      (fun x => v.1, fun x => v.2)
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordBlockLift.Command.writeRight](SmallSort.definitions.md#def-4ea9be5d6a479fdd)
- [CodedSorting.TwoWordBlockLift.Command.readLeft](SmallSort.definitions.md#def-27005c471d1432cf)
- [CodedSorting.TwoWordSpill.Resident](PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)
- [CodedSorting.TwoWordBlockLift.Command.readRight](SmallSort.definitions.md#def-abd0500d4cb89cab)
- [CodedSorting.TwoWordBlockLift.Command.writeLeft](SmallSort.definitions.md#def-460a8fb76a136a38)
- [CodedSorting.TwoWordBlockLift.compile.match_1](SmallSort.definitions.md#def-71b337707d811e53)
- [CodedSorting.TwoWordBlockLift.Command.cpu](SmallSort.definitions.md#def-e28b6e71b42884f6)

**基础库名称**

`Fin.mk`, `Prod.mk`, `instOfNatNat`, `Prod.fst`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`

<a id="def-87dee668b3cf278c"></a>
## `CodedSorting.TwoWordBlockLift.check`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L96)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    ℕ →
      CodedSorting.TwoWordUniformLoop.Physical.Program W →
        CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W
```

**定义**

```lean
fun {B} {W} base p s =>
  CodedSorting.TwoWordBlockLift.step (CodedSorting.TwoWordBlockLift.Command.readLeft (base + p.pcAddress)) s
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordBlockLift.Command.readLeft](SmallSort.definitions.md#def-27005c471d1432cf)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.step](SmallSort.definitions.md#def-c2252ee0095dc811)
- [CodedSorting.TwoWordUniformLoop.Physical.Program.pcAddress](Uniform/Loop.definitions.md#def-39fb5e508f68d9fd)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-6b526f725fac5875"></a>
## `CodedSorting.TwoWordBlockLift.next`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L98)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    0 < B →
      ℕ →
        CodedSorting.TwoWordUniformLoop.Physical.Program W →
          CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W
```

**定义**

```lean
fun {B} {W} hB base p s =>
  CodedSorting.TwoWordBlockLift.execute (List.map (CodedSorting.TwoWordBlockLift.compile hB base) p.body)
    (CodedSorting.TwoWordBlockLift.check base p s)
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordBlockLift.check](SmallSort.definitions.md#def-87dee668b3cf278c)
- [CodedSorting.TwoWordBlockLift.execute](SmallSort.definitions.md#def-88b9ad740a9b80d5)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordUniformLoop.Physical.Program.body](Uniform/Loop.definitions.md#def-2ecb4f4fd3b78862)
- [CodedSorting.TwoWordBlockLift.compile](SmallSort.definitions.md#def-f394483af754d48e)

**基础库名称**

`List.map`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-af6a371c034d27b0"></a>
## `CodedSorting.TwoWordBlockLift.LoopExecutes`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](SmallSort.lean#L107)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    0 < B →
      ℕ →
        CodedSorting.TwoWordUniformLoop.Physical.Program W →
          CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W → ℕ → Prop
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordBlockLift.LoopExecutes.stop](SmallSort.definitions.md#def-fe0a7481e3eef9a6)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.LoopExecutes.more](SmallSort.definitions.md#def-ca5199fdb125c2a2)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-fe0a7481e3eef9a6"></a>
## `CodedSorting.TwoWordBlockLift.LoopExecutes.stop`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L109)

**类型**

```lean
∀ {B : ℕ} {W : Type u_1} {hB : 0 < B} {base : ℕ} {p : CodedSorting.TwoWordUniformLoop.Physical.Program W}
  (s : CodedSorting.TwoWordBlockLift.State B W),
  (CodedSorting.TwoWordBlockLift.check base p s).left ⟨0, hB⟩ = p.halt →
    CodedSorting.TwoWordBlockLift.LoopExecutes hB base p s (CodedSorting.TwoWordBlockLift.check base p s) 1
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordBlockLift.LoopExecutes](SmallSort.definitions.md#def-af6a371c034d27b0)
- [CodedSorting.TwoWordUniformLoop.Physical.Program.halt](Uniform/Loop.definitions.md#def-f8401a593749612b)
- [CodedSorting.TwoWordBlockLift.check](SmallSort.definitions.md#def-87dee668b3cf278c)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.State.left](SmallSort.definitions.md#def-2383655d2a21d782)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Eq`

<a id="def-ca5199fdb125c2a2"></a>
## `CodedSorting.TwoWordBlockLift.LoopExecutes.more`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L111)

**类型**

```lean
∀ {B : ℕ} {W : Type u_1} {hB : 0 < B} {base : ℕ} {p : CodedSorting.TwoWordUniformLoop.Physical.Program W}
  (s t : CodedSorting.TwoWordBlockLift.State B W) (c : ℕ),
  (CodedSorting.TwoWordBlockLift.check base p s).left ⟨0, hB⟩ ≠ p.halt →
    CodedSorting.TwoWordBlockLift.LoopExecutes hB base p (CodedSorting.TwoWordBlockLift.next hB base p s) t c →
      CodedSorting.TwoWordBlockLift.LoopExecutes hB base p s t
        (1 + CodedSorting.TwoWordBlockLift.transfers (List.map (CodedSorting.TwoWordBlockLift.compile hB base) p.body) +
          c)
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordBlockLift.next](SmallSort.definitions.md#def-6b526f725fac5875)
- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.LoopExecutes](SmallSort.definitions.md#def-af6a371c034d27b0)
- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordUniformLoop.Physical.Program.halt](Uniform/Loop.definitions.md#def-f8401a593749612b)
- [CodedSorting.TwoWordBlockLift.check](SmallSort.definitions.md#def-87dee668b3cf278c)
- [CodedSorting.TwoWordBlockLift.transfers](SmallSort.definitions.md#def-d0e569e9b6fa843c)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.State.left](SmallSort.definitions.md#def-2383655d2a21d782)
- [CodedSorting.TwoWordUniformLoop.Physical.Program.body](Uniform/Loop.definitions.md#def-2ecb4f4fd3b78862)
- [CodedSorting.TwoWordBlockLift.compile](SmallSort.definitions.md#def-f394483af754d48e)

**基础库名称**

`List.map`, `Fin.mk`, `Ne`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-1f31d0b4d4cb4c30"></a>
## `CodedSorting.TwoWordBlockLift.Executes`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](SmallSort.lean#L134)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    0 < B →
      ℕ →
        List (CodedSorting.TwoWordRadixPreparedBuild.Stage W) →
          CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W → ℕ → Prop
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Executes.done](SmallSort.definitions.md#def-5928766e905efecf)
- [CodedSorting.TwoWordBlockLift.Executes.loop](SmallSort.definitions.md#def-f269047a07a26b16)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.Executes.straight](SmallSort.definitions.md#def-a1794d46735296cd)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)

**基础库名称**

`instOfNatNat`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-5928766e905efecf"></a>
## `CodedSorting.TwoWordBlockLift.Executes.done`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L136)

**类型**

```lean
∀ {B : ℕ} {W : Type u_1} {hB : 0 < B} {base : ℕ} (s : CodedSorting.TwoWordBlockLift.State B W),
  CodedSorting.TwoWordBlockLift.Executes hB base [] s s 0
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.Executes](SmallSort.definitions.md#def-1f31d0b4d4cb4c30)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `List.nil`

<a id="def-a1794d46735296cd"></a>
## `CodedSorting.TwoWordBlockLift.Executes.straight`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L137)

**类型**

```lean
∀ {B : ℕ} {W : Type u_1} {hB : 0 < B} {base : ℕ} (code : List (CodedSorting.TwoWordPhysicalAddresses.Command W))
  (rest : List (CodedSorting.TwoWordRadixPreparedBuild.Stage W)) (s t : CodedSorting.TwoWordBlockLift.State B W)
  (c : ℕ),
  CodedSorting.TwoWordBlockLift.Executes hB base rest
      (CodedSorting.TwoWordBlockLift.execute (List.map (CodedSorting.TwoWordBlockLift.compile hB base) code) s) t c →
    CodedSorting.TwoWordBlockLift.Executes hB base (CodedSorting.TwoWordRadixPreparedBuild.Stage.straight code :: rest)
      s t (CodedSorting.TwoWordBlockLift.transfers (List.map (CodedSorting.TwoWordBlockLift.compile hB base) code) + c)
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordBlockLift.execute](SmallSort.definitions.md#def-88b9ad740a9b80d5)
- [CodedSorting.TwoWordBlockLift.transfers](SmallSort.definitions.md#def-d0e569e9b6fa843c)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.Executes](SmallSort.definitions.md#def-1f31d0b4d4cb4c30)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.straight](Radix/Initialize.definitions.md#def-a8dd39815ba3f078)
- [CodedSorting.TwoWordBlockLift.compile](SmallSort.definitions.md#def-f394483af754d48e)

**基础库名称**

`List.map`, `instOfNatNat`, `List.cons`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-f269047a07a26b16"></a>
## `CodedSorting.TwoWordBlockLift.Executes.loop`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallSort.lean#L141)

**类型**

```lean
∀ {B : ℕ} {W : Type u_1} {hB : 0 < B} {base : ℕ} (p : CodedSorting.TwoWordUniformLoop.Physical.Program W)
  (rest : List (CodedSorting.TwoWordRadixPreparedBuild.Stage W)) (s mid t : CodedSorting.TwoWordBlockLift.State B W)
  (ca cb : ℕ),
  CodedSorting.TwoWordBlockLift.LoopExecutes hB base p s mid ca →
    CodedSorting.TwoWordBlockLift.Executes hB base rest mid t cb →
      CodedSorting.TwoWordBlockLift.Executes hB base (CodedSorting.TwoWordRadixPreparedBuild.Stage.loop p :: rest) s t
        (ca + cb)
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordBlockLift.LoopExecutes](SmallSort.definitions.md#def-af6a371c034d27b0)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.Executes](SmallSort.definitions.md#def-1f31d0b4d4cb4c30)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.loop](Radix/Initialize.definitions.md#def-37406744c0a136a6)

**基础库名称**

`instOfNatNat`, `List.cons`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-6b6804b241d9f6e6"></a>
## `CodedSorting.TwoWordBlockFootprint.BoundedCommand`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L414)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → ℕ → CodedSorting.TwoWordBlockLift.Command B W → Prop
```

**定义**

```lean
fun {B} {W} L x =>
  match x with
  | CodedSorting.TwoWordBlockLift.Command.readLeft a => a < L
  | CodedSorting.TwoWordBlockLift.Command.readRight a =>
    ∀ (r : CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W), a r < L
  | CodedSorting.TwoWordBlockLift.Command.writeLeft a => a < L
  | CodedSorting.TwoWordBlockLift.Command.writeRight a =>
    ∀ (r : CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W), a r < L
  | CodedSorting.TwoWordBlockLift.Command.cpu f => True
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.step.match_1](SmallSort.definitions.md#def-3b2d8d18c9199124)

**基础库名称**

`Nat`, `LT.lt`, `True`, `instLTNat`, `Prod`

<a id="def-f08ed3beb558eea2"></a>
## `CodedSorting.TwoWordBlockFootprint.BoundedCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L420)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → ℕ → List (CodedSorting.TwoWordBlockLift.Command B W) → Prop
```

**定义**

```lean
fun {B} {W} L code => ∀ cmd ∈ code, CodedSorting.TwoWordBlockFootprint.BoundedCommand L cmd
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockFootprint.BoundedCommand](SmallSort.definitions.md#def-6b6804b241d9f6e6)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`

<a id="def-76161e6fc2ea4d2d"></a>
## `CodedSorting.TwoWordBlockFormat.cell`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L502)

**类型**

```lean
{B : ℕ} → 0 < B → ℕ → Fin B
```

**定义**

```lean
fun {B} hB i => ⟨i % B, ⋯⟩
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Fin.mk`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `Nat.mod_lt`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-dcb9f8bceedd2b3d"></a>
## `CodedSorting.TwoWordBlockFormat.wordAt`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L503)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → 0 < B → (ℕ → CodedSorting.TwoWordBlockLift.Buffer B W) → ℕ → W
```

**定义**

```lean
fun {B} {W} hB disk i => disk (i / B) (CodedSorting.TwoWordBlockFormat.cell hB i)
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockFormat.cell](SmallSort.definitions.md#def-76161e6fc2ea4d2d)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `instOfNatNat`, `Nat`, `LT.lt`, `Nat.instDiv`, `instLTNat`, `OfNat.ofNat`

<a id="def-b0a7b147d4de0b57"></a>
## `CodedSorting.TwoWordBlockFormat.File`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SmallSort.lean#L504)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → 0 < B → (ℕ → CodedSorting.TwoWordBlockLift.Buffer B W) → List W → Prop
```

**定义**

```lean
fun {B} {W} hB disk xs => ∀ (j : Fin xs.length), CodedSorting.TwoWordBlockFormat.wordAt hB disk ↑j = xs.get j
```

**继续展开**

- [CodedSorting.TwoWordBlockFormat.wordAt](SmallSort.definitions.md#def-dcb9f8bceedd2b3d)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)

**基础库名称**

`List.get`, `instOfNatNat`, `Fin.val`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `List.length`

<a id="def-71b337707d811e53"></a>
## `CodedSorting.TwoWordBlockLift.compile.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](SmallSort.lean)

**类型**

```lean
{W : Type u_1} →
  (motive : CodedSorting.TwoWordPhysicalAddresses.Command W → Sort u_2) →
    (x : CodedSorting.TwoWordPhysicalAddresses.Command W) →
      ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.readLeft a)) →
        ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.readRight a)) →
          ((a : CodedSorting.TwoWordSpill.Resident W → ℕ) →
              motive (CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt a)) →
            ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft a)) →
              ((a : CodedSorting.TwoWordSpill.Resident W → ℕ) →
                  motive (CodedSorting.TwoWordPhysicalAddresses.Command.writeRight a)) →
                ((f : CodedSorting.TwoWordSpill.Resident W → CodedSorting.TwoWordSpill.Resident W) →
                    motive (CodedSorting.TwoWordPhysicalAddresses.Command.localOp f)) →
                  motive x
```

**定义**

```lean
fun {W} motive x h_1 h_2 h_3 h_4 h_5 h_6 =>
  CodedSorting.TwoWordPhysicalAddresses.Command.casesOn x (fun a => h_1 a) (fun a => h_2 a) (fun a => h_3 a)
    (fun a => h_4 a) (fun a => h_5 a) fun f => h_6 f
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command.readRight](PhysicalAddresses.definitions.md#def-80ee4e0629315e7a)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeRight](PhysicalAddresses.definitions.md#def-ba338466a2ed8462)
- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordPhysicalAddresses.Command.localOp](PhysicalAddresses.definitions.md#def-c713e8bf83b71ce0)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readLeft](PhysicalAddresses.definitions.md#def-10977754ba9e1532)
- [CodedSorting.TwoWordPhysicalAddresses.Command.casesOn](PhysicalAddresses.definitions.md#def-a499b9b9d54d5380)
- [CodedSorting.TwoWordSpill.Resident](PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft](PhysicalAddresses.definitions.md#def-38889ca9c555a290)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt](PhysicalAddresses.definitions.md#def-463ccc65763d544d)

**基础库名称**

`Nat`

<a id="def-8c838c260c896442"></a>
## `CodedSorting.TwoWordBlockLift.cost.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](SmallSort.lean)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    (motive : CodedSorting.TwoWordBlockLift.Command B W → Sort u_2) →
      (x : CodedSorting.TwoWordBlockLift.Command B W) →
        ((f :
              CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W →
                CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W) →
            motive (CodedSorting.TwoWordBlockLift.Command.cpu f)) →
          ((x : CodedSorting.TwoWordBlockLift.Command B W) → motive x) → motive x
```

**定义**

```lean
fun {B} {W} motive x h_1 h_2 =>
  CodedSorting.TwoWordBlockLift.Command.casesOn x
    (fun address => h_2 (CodedSorting.TwoWordBlockLift.Command.readLeft address))
    (fun address => h_2 (CodedSorting.TwoWordBlockLift.Command.readRight address))
    (fun address => h_2 (CodedSorting.TwoWordBlockLift.Command.writeLeft address))
    (fun address => h_2 (CodedSorting.TwoWordBlockLift.Command.writeRight address)) fun f => h_1 f
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.Command.writeRight](SmallSort.definitions.md#def-4ea9be5d6a479fdd)
- [CodedSorting.TwoWordBlockLift.Command.readLeft](SmallSort.definitions.md#def-27005c471d1432cf)
- [CodedSorting.TwoWordBlockLift.Command.readRight](SmallSort.definitions.md#def-abd0500d4cb89cab)
- [CodedSorting.TwoWordBlockLift.Command.writeLeft](SmallSort.definitions.md#def-460a8fb76a136a38)
- [CodedSorting.TwoWordBlockLift.Command.cpu](SmallSort.definitions.md#def-e28b6e71b42884f6)
- [CodedSorting.TwoWordBlockLift.Command.casesOn](SmallSort.definitions.md#def-caa07ad4883d62d1)

**基础库名称**

`Nat`, `Prod`

<a id="def-f7ac38dc95886ce9"></a>
## `CodedSorting.TwoWordBlockLift.execute.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](SmallSort.lean)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    (motive : List (CodedSorting.TwoWordBlockLift.Command B W) → CodedSorting.TwoWordBlockLift.State B W → Sort u_2) →
      (x : List (CodedSorting.TwoWordBlockLift.Command B W)) →
        (x_1 : CodedSorting.TwoWordBlockLift.State B W) →
          ((s : CodedSorting.TwoWordBlockLift.State B W) → motive [] s) →
            ((cmd : CodedSorting.TwoWordBlockLift.Command B W) →
                (rest : List (CodedSorting.TwoWordBlockLift.Command B W)) →
                  (s : CodedSorting.TwoWordBlockLift.State B W) → motive (cmd :: rest) s) →
              motive x x_1
```

**定义**

```lean
fun {B} {W} motive x x_1 h_1 h_2 => List.casesOn x (h_1 x_1) fun head tail => h_2 head tail x_1
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)

**基础库名称**

`List.cons`, `List`, `Nat`, `List.casesOn`, `List.nil`

<a id="def-3b2d8d18c9199124"></a>
## `CodedSorting.TwoWordBlockLift.step.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](SmallSort.lean)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    (motive : CodedSorting.TwoWordBlockLift.Command B W → Sort u_2) →
      (cmd : CodedSorting.TwoWordBlockLift.Command B W) →
        ((a : ℕ) → motive (CodedSorting.TwoWordBlockLift.Command.readLeft a)) →
          ((a : CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W → ℕ) →
              motive (CodedSorting.TwoWordBlockLift.Command.readRight a)) →
            ((a : ℕ) → motive (CodedSorting.TwoWordBlockLift.Command.writeLeft a)) →
              ((a : CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W → ℕ) →
                  motive (CodedSorting.TwoWordBlockLift.Command.writeRight a)) →
                ((f :
                      CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W →
                        CodedSorting.TwoWordBlockLift.Buffer B W × CodedSorting.TwoWordBlockLift.Buffer B W) →
                    motive (CodedSorting.TwoWordBlockLift.Command.cpu f)) →
                  motive cmd
```

**定义**

```lean
fun {B} {W} motive cmd h_1 h_2 h_3 h_4 h_5 =>
  CodedSorting.TwoWordBlockLift.Command.casesOn cmd (fun address => h_1 address) (fun address => h_2 address)
    (fun address => h_3 address) (fun address => h_4 address) fun f => h_5 f
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordBlockLift.Buffer](SmallSort.definitions.md#def-82390a35b2c034e0)
- [CodedSorting.TwoWordBlockLift.Command.writeRight](SmallSort.definitions.md#def-4ea9be5d6a479fdd)
- [CodedSorting.TwoWordBlockLift.Command.readLeft](SmallSort.definitions.md#def-27005c471d1432cf)
- [CodedSorting.TwoWordBlockLift.Command.readRight](SmallSort.definitions.md#def-abd0500d4cb89cab)
- [CodedSorting.TwoWordBlockLift.Command.writeLeft](SmallSort.definitions.md#def-460a8fb76a136a38)
- [CodedSorting.TwoWordBlockLift.Command.cpu](SmallSort.definitions.md#def-e28b6e71b42884f6)
- [CodedSorting.TwoWordBlockLift.Command.casesOn](SmallSort.definitions.md#def-caa07ad4883d62d1)

**基础库名称**

`Nat`, `Prod`

<a id="def-563f4f87adb5ad7d"></a>
## `CodedSorting.TwoWordBlockLift.transfers.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](SmallSort.lean)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    (motive : List (CodedSorting.TwoWordBlockLift.Command B W) → Sort u_2) →
      (x : List (CodedSorting.TwoWordBlockLift.Command B W)) →
        (Unit → motive []) →
          ((cmd : CodedSorting.TwoWordBlockLift.Command B W) →
              (rest : List (CodedSorting.TwoWordBlockLift.Command B W)) → motive (cmd :: rest)) →
            motive x
```

**定义**

```lean
fun {B} {W} motive x h_1 h_2 => List.casesOn x (h_1 ()) fun head tail => h_2 head tail
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `Nat`, `List.casesOn`, `List.nil`
