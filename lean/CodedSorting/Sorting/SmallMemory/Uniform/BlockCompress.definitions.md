# BlockCompress 的定义

[源码](BlockCompress.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-99162c6b8098700b"></a>
## `CodedSorting.TwoWordUniformBlockFormat.LoopProgram`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](BlockCompress.lean#L21)

**类型**

```lean
ℕ → Type u_1 → Type u_1
```

**继续展开**

- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram.mk](BlockCompress.definitions.md#def-fc90652ab1d5f156)

**基础库名称**

`Nat`

<a id="def-fc90652ab1d5f156"></a>
## `CodedSorting.TwoWordUniformBlockFormat.LoopProgram.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](BlockCompress.lean#L21)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    ℕ → W → List (CodedSorting.TwoWordBlockLift.Command B W) → CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](../SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`List`, `Nat`

<a id="def-16203fa9410a5968"></a>
## `CodedSorting.TwoWordUniformBlockFormat.LoopProgram.flagAddress`

读取 `CodedSorting.TwoWordUniformBlockFormat.LoopProgram` 的 `flagAddress` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](BlockCompress.lean#L22)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W → ℕ
```

**定义**

```lean
fun B W self => self.1
```

**继续展开**

- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`Nat`

<a id="def-57fd0d98cc1c5d23"></a>
## `CodedSorting.TwoWordUniformBlockFormat.LoopProgram.halt`

读取 `CodedSorting.TwoWordUniformBlockFormat.LoopProgram` 的 `halt` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](BlockCompress.lean#L23)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W → W
```

**定义**

```lean
fun B W self => self.2
```

**继续展开**

- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`Nat`

<a id="def-67c8f6f48be4519b"></a>
## `CodedSorting.TwoWordUniformBlockFormat.LoopProgram.body`

读取 `CodedSorting.TwoWordUniformBlockFormat.LoopProgram` 的 `body` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](BlockCompress.lean#L24)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W → List (CodedSorting.TwoWordBlockLift.Command B W)
```

**定义**

```lean
fun B W self => self.3
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](../SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`List`, `Nat`

<a id="def-9bb3d59f3811cc78"></a>
## `CodedSorting.TwoWordUniformBlockFormat.check`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockCompress.lean#L26)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W →
      CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W
```

**定义**

```lean
fun {B} {W} p s => CodedSorting.TwoWordBlockLift.step (CodedSorting.TwoWordBlockLift.Command.readLeft p.flagAddress) s
```

**继续展开**

- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram.flagAddress](BlockCompress.definitions.md#def-16203fa9410a5968)
- [CodedSorting.TwoWordBlockLift.Command.readLeft](../SmallSort.definitions.md#def-27005c471d1432cf)
- [CodedSorting.TwoWordBlockLift.State](../SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.step](../SmallSort.definitions.md#def-c2252ee0095dc811)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`Nat`

<a id="def-403a8ee9bc60bb59"></a>
## `CodedSorting.TwoWordUniformBlockFormat.next`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockCompress.lean#L28)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W →
      CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W
```

**定义**

```lean
fun {B} {W} p s => CodedSorting.TwoWordBlockLift.execute p.body (CodedSorting.TwoWordUniformBlockFormat.check p s)
```

**继续展开**

- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram.body](BlockCompress.definitions.md#def-67c8f6f48be4519b)
- [CodedSorting.TwoWordBlockLift.execute](../SmallSort.definitions.md#def-88b9ad740a9b80d5)
- [CodedSorting.TwoWordBlockLift.State](../SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordUniformBlockFormat.check](BlockCompress.definitions.md#def-9bb3d59f3811cc78)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`Nat`

<a id="def-4134960b56382293"></a>
## `CodedSorting.TwoWordUniformBlockFormat.Executes`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](BlockCompress.lean#L30)

**类型**

```lean
{B : ℕ} →
  {W : Type u_1} →
    0 < B →
      CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W →
        CodedSorting.TwoWordBlockLift.State B W → CodedSorting.TwoWordBlockLift.State B W → ℕ → Prop
```

**继续展开**

- [CodedSorting.TwoWordUniformBlockFormat.Executes.stop](BlockCompress.definitions.md#def-2d898a0501e0bd8d)
- [CodedSorting.TwoWordBlockLift.State](../SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordUniformBlockFormat.Executes.more](BlockCompress.definitions.md#def-e6b267019bc342ad)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-2d898a0501e0bd8d"></a>
## `CodedSorting.TwoWordUniformBlockFormat.Executes.stop`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](BlockCompress.lean#L32)

**类型**

```lean
∀ {B : ℕ} {W : Type u_1} {hB : 0 < B} {p : CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W}
  (s : CodedSorting.TwoWordBlockLift.State B W),
  (CodedSorting.TwoWordUniformBlockFormat.check p s).left ⟨0, hB⟩ = p.halt →
    CodedSorting.TwoWordUniformBlockFormat.Executes hB p s (CodedSorting.TwoWordUniformBlockFormat.check p s) 1
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.State](../SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordUniformBlockFormat.check](BlockCompress.definitions.md#def-9bb3d59f3811cc78)
- [CodedSorting.TwoWordBlockLift.State.left](../SmallSort.definitions.md#def-2383655d2a21d782)
- [CodedSorting.TwoWordUniformBlockFormat.Executes](BlockCompress.definitions.md#def-4134960b56382293)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram.halt](BlockCompress.definitions.md#def-57fd0d98cc1c5d23)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Eq`

<a id="def-e6b267019bc342ad"></a>
## `CodedSorting.TwoWordUniformBlockFormat.Executes.more`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](BlockCompress.lean#L34)

**类型**

```lean
∀ {B : ℕ} {W : Type u_1} {hB : 0 < B} {p : CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W}
  (s t : CodedSorting.TwoWordBlockLift.State B W) (cost : ℕ),
  (CodedSorting.TwoWordUniformBlockFormat.check p s).left ⟨0, hB⟩ ≠ p.halt →
    CodedSorting.TwoWordUniformBlockFormat.Executes hB p (CodedSorting.TwoWordUniformBlockFormat.next p s) t cost →
      CodedSorting.TwoWordUniformBlockFormat.Executes hB p s t
        (1 + CodedSorting.TwoWordBlockLift.transfers p.body + cost)
```

**继续展开**

- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram.body](BlockCompress.definitions.md#def-67c8f6f48be4519b)
- [CodedSorting.TwoWordBlockLift.transfers](../SmallSort.definitions.md#def-d0e569e9b6fa843c)
- [CodedSorting.TwoWordBlockLift.State](../SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordUniformBlockFormat.next](BlockCompress.definitions.md#def-403a8ee9bc60bb59)
- [CodedSorting.TwoWordUniformBlockFormat.check](BlockCompress.definitions.md#def-9bb3d59f3811cc78)
- [CodedSorting.TwoWordBlockLift.State.left](../SmallSort.definitions.md#def-2383655d2a21d782)
- [CodedSorting.TwoWordUniformBlockFormat.Executes](BlockCompress.definitions.md#def-4134960b56382293)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram.halt](BlockCompress.definitions.md#def-57fd0d98cc1c5d23)

**基础库名称**

`Fin.mk`, `Ne`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-bc21d648ca326a5d"></a>
## `CodedSorting.TwoWordUniformBlockFormat.BoundedProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockCompress.lean#L203)

**类型**

```lean
{B : ℕ} → {W : Type u_1} → ℕ → CodedSorting.TwoWordUniformBlockFormat.LoopProgram B W → Prop
```

**定义**

```lean
fun {B} {W} L p => p.flagAddress < L ∧ CodedSorting.TwoWordBlockFootprint.BoundedCode L p.body
```

**继续展开**

- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram.body](BlockCompress.definitions.md#def-67c8f6f48be4519b)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram.flagAddress](BlockCompress.definitions.md#def-16203fa9410a5968)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](BlockCompress.definitions.md#def-99162c6b8098700b)
- [CodedSorting.TwoWordBlockFootprint.BoundedCode](../SmallSort.definitions.md#def-f08ed3beb558eea2)

**基础库名称**

`And`, `Nat`, `LT.lt`, `instLTNat`
