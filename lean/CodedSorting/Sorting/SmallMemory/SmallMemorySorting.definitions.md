# SmallMemorySorting 的定义

[源码](SmallMemorySorting.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-f8b2d4cb2dbe218e"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Stage`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](SmallMemorySorting.lean#L17)

**类型**

```lean
ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.TwoWordSmallMemorySorting.Stage.core](SmallMemorySorting.definitions.md#def-f93aaca4b29b78b6)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.loop](SmallMemorySorting.definitions.md#def-4c18ff2e8e4357db)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.straight](SmallMemorySorting.definitions.md#def-4432479eb5484b4e)

**基础库名称**

`Nat`

<a id="def-10f7cb9a470a74be"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Stage.casesOn`

读取 `CodedSorting.TwoWordSmallMemorySorting.Stage` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SmallMemorySorting.lean#L17)

**类型**

```lean
{B w : ℕ} →
  {motive : CodedSorting.TwoWordSmallMemorySorting.Stage B w → Sort u} →
    (t : CodedSorting.TwoWordSmallMemorySorting.Stage B w) →
      ((body : List (CodedSorting.TwoWordBlockLift.Command B (CodedSorting.TwoWordRadixInsert.Word w))) →
          motive (CodedSorting.TwoWordSmallMemorySorting.Stage.straight body)) →
        ((p : CodedSorting.TwoWordUniformBlockFormat.LoopProgram B (CodedSorting.TwoWordRadixInsert.Word w)) →
            motive (CodedSorting.TwoWordSmallMemorySorting.Stage.loop p)) →
          ((base : ℕ) →
              (body : List (CodedSorting.TwoWordRadixPreparedBuild.Stage (CodedSorting.TwoWordRadixInsert.Word w))) →
                motive (CodedSorting.TwoWordSmallMemorySorting.Stage.core base body)) →
            motive t
```

**定义**

```lean
fun {B w} {motive} t straight loop core =>
  CodedSorting.TwoWordSmallMemorySorting.Stage.rec (fun body => straight body) (fun p => loop p)
    (fun base body => core base body) t
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.rec](SmallMemorySorting.definitions.md#def-4f5aebc4a4cdc453)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.core](SmallMemorySorting.definitions.md#def-f93aaca4b29b78b6)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.loop](SmallMemorySorting.definitions.md#def-4c18ff2e8e4357db)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.straight](SmallMemorySorting.definitions.md#def-4432479eb5484b4e)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](Uniform/BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`List`, `Nat`

<a id="def-4f5aebc4a4cdc453"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Stage.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](SmallMemorySorting.lean#L17)

**类型**

```lean
{B w : ℕ} →
  {motive : CodedSorting.TwoWordSmallMemorySorting.Stage B w → Sort u} →
    ((body : List (CodedSorting.TwoWordBlockLift.Command B (CodedSorting.TwoWordRadixInsert.Word w))) →
        motive (CodedSorting.TwoWordSmallMemorySorting.Stage.straight body)) →
      ((p : CodedSorting.TwoWordUniformBlockFormat.LoopProgram B (CodedSorting.TwoWordRadixInsert.Word w)) →
          motive (CodedSorting.TwoWordSmallMemorySorting.Stage.loop p)) →
        ((base : ℕ) →
            (body : List (CodedSorting.TwoWordRadixPreparedBuild.Stage (CodedSorting.TwoWordRadixInsert.Word w))) →
              motive (CodedSorting.TwoWordSmallMemorySorting.Stage.core base body)) →
          (t : CodedSorting.TwoWordSmallMemorySorting.Stage B w) → motive t
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.core](SmallMemorySorting.definitions.md#def-f93aaca4b29b78b6)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.loop](SmallMemorySorting.definitions.md#def-4c18ff2e8e4357db)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.straight](SmallMemorySorting.definitions.md#def-4432479eb5484b4e)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](Uniform/BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`List`, `Nat`

<a id="def-4432479eb5484b4e"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Stage.straight`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallMemorySorting.lean#L18)

**类型**

```lean
{B w : ℕ} →
  List (CodedSorting.TwoWordBlockLift.Command B (CodedSorting.TwoWordRadixInsert.Word w)) →
    CodedSorting.TwoWordSmallMemorySorting.Stage B w
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)

**基础库名称**

`List`, `Nat`

<a id="def-4c18ff2e8e4357db"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Stage.loop`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallMemorySorting.lean#L19)

**类型**

```lean
{B w : ℕ} →
  CodedSorting.TwoWordUniformBlockFormat.LoopProgram B (CodedSorting.TwoWordRadixInsert.Word w) →
    CodedSorting.TwoWordSmallMemorySorting.Stage B w
```

**继续展开**

- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](Uniform/BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`Nat`

<a id="def-f93aaca4b29b78b6"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Stage.core`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallMemorySorting.lean#L20)

**类型**

```lean
{B w : ℕ} →
  ℕ →
    List (CodedSorting.TwoWordRadixPreparedBuild.Stage (CodedSorting.TwoWordRadixInsert.Word w)) →
      CodedSorting.TwoWordSmallMemorySorting.Stage B w
```

**继续展开**

- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)

**基础库名称**

`List`, `Nat`

<a id="def-1a41d1fc1b157ab5"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Executes`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](SmallMemorySorting.lean#L22)

**类型**

```lean
{B w : ℕ} →
  0 < B →
    List (CodedSorting.TwoWordSmallMemorySorting.Stage B w) →
      CodedSorting.TwoWordBlockLift.State B (CodedSorting.TwoWordRadixInsert.Word w) →
        CodedSorting.TwoWordBlockLift.State B (CodedSorting.TwoWordRadixInsert.Word w) → ℕ → Prop
```

**继续展开**

- [CodedSorting.TwoWordSmallMemorySorting.Executes.straight](SmallMemorySorting.definitions.md#def-9e4f8b78a8f0c502)
- [CodedSorting.TwoWordSmallMemorySorting.Executes.core](SmallMemorySorting.definitions.md#def-dcdf992e88412312)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordSmallMemorySorting.Executes.done](SmallMemorySorting.definitions.md#def-e1fb1a450a96e3d8)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordSmallMemorySorting.Executes.loop](SmallMemorySorting.definitions.md#def-9e0d64cc85dca930)

**基础库名称**

`instOfNatNat`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-e1fb1a450a96e3d8"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Executes.done`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallMemorySorting.lean#L24)

**类型**

```lean
∀ {B w : ℕ} {hB : 0 < B} (s : CodedSorting.TwoWordBlockLift.State B (CodedSorting.TwoWordRadixInsert.Word w)),
  CodedSorting.TwoWordSmallMemorySorting.Executes hB [] s s 0
```

**继续展开**

- [CodedSorting.TwoWordSmallMemorySorting.Executes](SmallMemorySorting.definitions.md#def-1a41d1fc1b157ab5)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `List.nil`

<a id="def-9e4f8b78a8f0c502"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Executes.straight`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallMemorySorting.lean#L25)

**类型**

```lean
∀ {B w : ℕ} {hB : 0 < B}
  (body : List (CodedSorting.TwoWordBlockLift.Command B (CodedSorting.TwoWordRadixInsert.Word w)))
  (rest : List (CodedSorting.TwoWordSmallMemorySorting.Stage B w))
  (s t : CodedSorting.TwoWordBlockLift.State B (CodedSorting.TwoWordRadixInsert.Word w)) (cost : ℕ),
  CodedSorting.TwoWordSmallMemorySorting.Executes hB rest (CodedSorting.TwoWordBlockLift.execute body s) t cost →
    CodedSorting.TwoWordSmallMemorySorting.Executes hB
      (CodedSorting.TwoWordSmallMemorySorting.Stage.straight body :: rest) s t
      (CodedSorting.TwoWordBlockLift.transfers body + cost)
```

**继续展开**

- [CodedSorting.TwoWordSmallMemorySorting.Executes](SmallMemorySorting.definitions.md#def-1a41d1fc1b157ab5)
- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordBlockLift.execute](SmallSort.definitions.md#def-88b9ad740a9b80d5)
- [CodedSorting.TwoWordBlockLift.transfers](SmallSort.definitions.md#def-d0e569e9b6fa843c)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.straight](SmallMemorySorting.definitions.md#def-4432479eb5484b4e)

**基础库名称**

`instOfNatNat`, `List.cons`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-9e0d64cc85dca930"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Executes.loop`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallMemorySorting.lean#L29)

**类型**

```lean
∀ {B w : ℕ} {hB : 0 < B}
  (p : CodedSorting.TwoWordUniformBlockFormat.LoopProgram B (CodedSorting.TwoWordRadixInsert.Word w))
  (rest : List (CodedSorting.TwoWordSmallMemorySorting.Stage B w))
  (s mid t : CodedSorting.TwoWordBlockLift.State B (CodedSorting.TwoWordRadixInsert.Word w)) (ca cb : ℕ),
  CodedSorting.TwoWordUniformBlockFormat.Executes hB p s mid ca →
    CodedSorting.TwoWordSmallMemorySorting.Executes hB rest mid t cb →
      CodedSorting.TwoWordSmallMemorySorting.Executes hB (CodedSorting.TwoWordSmallMemorySorting.Stage.loop p :: rest) s
        t (ca + cb)
```

**继续展开**

- [CodedSorting.TwoWordSmallMemorySorting.Executes](SmallMemorySorting.definitions.md#def-1a41d1fc1b157ab5)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.loop](SmallMemorySorting.definitions.md#def-4c18ff2e8e4357db)
- [CodedSorting.TwoWordUniformBlockFormat.Executes](Uniform/BlockCompress.definitions.md#def-4134960b56382293)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](Uniform/BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`instOfNatNat`, `List.cons`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-dcdf992e88412312"></a>
## `CodedSorting.TwoWordSmallMemorySorting.Executes.core`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SmallMemorySorting.lean#L34)

**类型**

```lean
∀ {B w : ℕ} {hB : 0 < B} (base : ℕ)
  (body : List (CodedSorting.TwoWordRadixPreparedBuild.Stage (CodedSorting.TwoWordRadixInsert.Word w)))
  (rest : List (CodedSorting.TwoWordSmallMemorySorting.Stage B w))
  (s mid t : CodedSorting.TwoWordBlockLift.State B (CodedSorting.TwoWordRadixInsert.Word w)) (ca cb : ℕ),
  CodedSorting.TwoWordBlockLift.Executes hB base body s mid ca →
    CodedSorting.TwoWordSmallMemorySorting.Executes hB rest mid t cb →
      CodedSorting.TwoWordSmallMemorySorting.Executes hB
        (CodedSorting.TwoWordSmallMemorySorting.Stage.core base body :: rest) s t (ca + cb)
```

**继续展开**

- [CodedSorting.TwoWordSmallMemorySorting.Executes](SmallMemorySorting.definitions.md#def-1a41d1fc1b157ab5)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.core](SmallMemorySorting.definitions.md#def-f93aaca4b29b78b6)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordBlockLift.State](SmallSort.definitions.md#def-25d0a9a7fac3e554)
- [CodedSorting.TwoWordBlockLift.Executes](SmallSort.definitions.md#def-1f31d0b4d4cb4c30)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)

**基础库名称**

`instOfNatNat`, `List.cons`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`
