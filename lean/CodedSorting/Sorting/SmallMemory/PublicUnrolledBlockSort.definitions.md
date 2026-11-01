# PublicUnrolledBlockSort 的定义

[源码](PublicUnrolledBlockSort.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e8de11280cbfd4ed"></a>
## `CodedSorting.TwoWordSmallMemoryFootprint.BoundedStage`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PublicUnrolledBlockSort.lean#L23)

**类型**

```lean
{B w : ℕ} → ℕ → CodedSorting.TwoWordSmallMemorySorting.Stage B w → Prop
```

**定义**

```lean
fun {B w} L x =>
  match x with
  | CodedSorting.TwoWordSmallMemorySorting.Stage.straight body => CodedSorting.TwoWordBlockFootprint.BoundedCode L body
  | CodedSorting.TwoWordSmallMemorySorting.Stage.loop p => CodedSorting.TwoWordUniformBlockFormat.BoundedProgram L p
  | CodedSorting.TwoWordSmallMemorySorting.Stage.core base body =>
    ∃ R, base + R ≤ L ∧ CodedSorting.TwoWordRadixFootprint.BoundedCode R body
```

**继续展开**

- [CodedSorting.TwoWordRadixFootprint.BoundedCode](Radix/Sort.definitions.md#def-d6a278ca2e43429a)
- [CodedSorting.TwoWordUniformBlockFormat.BoundedProgram](Uniform/BlockCompress.definitions.md#def-bc21d648ca326a5d)
- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordSmallMemoryFootprint.BoundedStage.match_1](PublicUnrolledBlockSort.definitions.md#def-2da1c3f32b26c2dc)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](Uniform/BlockCompress.definitions.md#def-99162c6b8098700b)
- [CodedSorting.TwoWordBlockFootprint.BoundedCode](SmallSort.definitions.md#def-f08ed3beb558eea2)

**基础库名称**

`Exists`, `LE.le`, `instLENat`, `List`, `instHAdd`, `And`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-1ba4ebc7d39a7d39"></a>
## `CodedSorting.TwoWordSmallMemoryFootprint.BoundedCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PublicUnrolledBlockSort.lean#L28)

**类型**

```lean
{B w : ℕ} → ℕ → List (CodedSorting.TwoWordSmallMemorySorting.Stage B w) → Prop
```

**定义**

```lean
fun {B w} L code => ∀ st ∈ code, CodedSorting.TwoWordSmallMemoryFootprint.BoundedStage L st
```

**继续展开**

- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordSmallMemoryFootprint.BoundedStage](PublicUnrolledBlockSort.definitions.md#def-e8de11280cbfd4ed)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`

<a id="def-2da1c3f32b26c2dc"></a>
## `CodedSorting.TwoWordSmallMemoryFootprint.BoundedStage.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PublicUnrolledBlockSort.lean)

**类型**

```lean
{B w : ℕ} →
  (motive : CodedSorting.TwoWordSmallMemorySorting.Stage B w → Sort u_1) →
    (x : CodedSorting.TwoWordSmallMemorySorting.Stage B w) →
      ((body : List (CodedSorting.TwoWordBlockLift.Command B (CodedSorting.TwoWordRadixInsert.Word w))) →
          motive (CodedSorting.TwoWordSmallMemorySorting.Stage.straight body)) →
        ((p : CodedSorting.TwoWordUniformBlockFormat.LoopProgram B (CodedSorting.TwoWordRadixInsert.Word w)) →
            motive (CodedSorting.TwoWordSmallMemorySorting.Stage.loop p)) →
          ((base : ℕ) →
              (body : List (CodedSorting.TwoWordRadixPreparedBuild.Stage (CodedSorting.TwoWordRadixInsert.Word w))) →
                motive (CodedSorting.TwoWordSmallMemorySorting.Stage.core base body)) →
            motive x
```

**定义**

```lean
fun {B w} motive x h_1 h_2 h_3 =>
  CodedSorting.TwoWordSmallMemorySorting.Stage.casesOn x (fun body => h_1 body) (fun p => h_2 p) fun base body =>
    h_3 base body
```

**继续展开**

- [CodedSorting.TwoWordBlockLift.Command](SmallSort.definitions.md#def-23d83d1182c7c157)
- [CodedSorting.TwoWordRadixInsert.Word](Radix/Build.definitions.md#def-a487bfd2fd8ec550)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.casesOn](SmallMemorySorting.definitions.md#def-10f7cb9a470a74be)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.core](SmallMemorySorting.definitions.md#def-f93aaca4b29b78b6)
- [CodedSorting.TwoWordSmallMemorySorting.Stage](SmallMemorySorting.definitions.md#def-f8b2d4cb2dbe218e)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.loop](SmallMemorySorting.definitions.md#def-4c18ff2e8e4357db)
- [CodedSorting.TwoWordSmallMemorySorting.Stage.straight](SmallMemorySorting.definitions.md#def-4432479eb5484b4e)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Radix/Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordUniformBlockFormat.LoopProgram](Uniform/BlockCompress.definitions.md#def-99162c6b8098700b)

**基础库名称**

`List`, `Nat`
