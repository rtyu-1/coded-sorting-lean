# Initialize 的定义

[源码](Initialize.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-472036ed275c48db"></a>
## `CodedSorting.TwoWordRadixPreparedBuild.Stage`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Initialize.lean#L196)

**类型**

```lean
Type u_1 → Type u_1
```

**继续展开**

- [CodedSorting.TwoWordRadixPreparedBuild.Stage.straight](Initialize.definitions.md#def-a8dd39815ba3f078)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.loop](Initialize.definitions.md#def-37406744c0a136a6)

<a id="def-b6f64e5ac7614dd7"></a>
## `CodedSorting.TwoWordRadixPreparedBuild.Stage.casesOn`

读取 `CodedSorting.TwoWordRadixPreparedBuild.Stage` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Initialize.lean#L196)

**类型**

```lean
{W : Type u_1} →
  {motive : CodedSorting.TwoWordRadixPreparedBuild.Stage W → Sort u} →
    (t : CodedSorting.TwoWordRadixPreparedBuild.Stage W) →
      ((code : List (CodedSorting.TwoWordPhysicalAddresses.Command W)) →
          motive (CodedSorting.TwoWordRadixPreparedBuild.Stage.straight code)) →
        ((program : CodedSorting.TwoWordUniformLoop.Physical.Program W) →
            motive (CodedSorting.TwoWordRadixPreparedBuild.Stage.loop program)) →
          motive t
```

**定义**

```lean
fun {W} {motive} t straight loop =>
  CodedSorting.TwoWordRadixPreparedBuild.Stage.rec (fun code => straight code) (fun program => loop program) t
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](../Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.straight](Initialize.definitions.md#def-a8dd39815ba3f078)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.rec](Initialize.definitions.md#def-04628f4951f48b4f)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.loop](Initialize.definitions.md#def-37406744c0a136a6)

**基础库名称**

`List`

<a id="def-04628f4951f48b4f"></a>
## `CodedSorting.TwoWordRadixPreparedBuild.Stage.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](Initialize.lean#L196)

**类型**

```lean
{W : Type u_1} →
  {motive : CodedSorting.TwoWordRadixPreparedBuild.Stage W → Sort u} →
    ((code : List (CodedSorting.TwoWordPhysicalAddresses.Command W)) →
        motive (CodedSorting.TwoWordRadixPreparedBuild.Stage.straight code)) →
      ((program : CodedSorting.TwoWordUniformLoop.Physical.Program W) →
          motive (CodedSorting.TwoWordRadixPreparedBuild.Stage.loop program)) →
        (t : CodedSorting.TwoWordRadixPreparedBuild.Stage W) → motive t
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](../Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.straight](Initialize.definitions.md#def-a8dd39815ba3f078)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.loop](Initialize.definitions.md#def-37406744c0a136a6)

**基础库名称**

`List`

<a id="def-a8dd39815ba3f078"></a>
## `CodedSorting.TwoWordRadixPreparedBuild.Stage.straight`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Initialize.lean#L197)

**类型**

```lean
{W : Type u_1} → List (CodedSorting.TwoWordPhysicalAddresses.Command W) → CodedSorting.TwoWordRadixPreparedBuild.Stage W
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Initialize.definitions.md#def-472036ed275c48db)

**基础库名称**

`List`

<a id="def-37406744c0a136a6"></a>
## `CodedSorting.TwoWordRadixPreparedBuild.Stage.loop`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Initialize.lean#L198)

**类型**

```lean
{W : Type u_1} → CodedSorting.TwoWordUniformLoop.Physical.Program W → CodedSorting.TwoWordRadixPreparedBuild.Stage W
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](../Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Initialize.definitions.md#def-472036ed275c48db)
