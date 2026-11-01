# Loop 的定义

[源码](Loop.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-5efe9fa745fd2b70"></a>
## `CodedSorting.TwoWordUniformLoop.Physical.Program`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Loop.lean#L26)

**类型**

```lean
Type u_2 → Type u_2
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program.mk](Loop.definitions.md#def-2deda023eeda9fdd)

<a id="def-2deda023eeda9fdd"></a>
## `CodedSorting.TwoWordUniformLoop.Physical.Program.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Loop.lean#L26)

**类型**

```lean
{W : Type u_2} →
  ℕ → W → List (CodedSorting.TwoWordPhysicalAddresses.Command W) → CodedSorting.TwoWordUniformLoop.Physical.Program W
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)

**基础库名称**

`List`, `Nat`

<a id="def-39fb5e508f68d9fd"></a>
## `CodedSorting.TwoWordUniformLoop.Physical.Program.pcAddress`

读取 `CodedSorting.TwoWordUniformLoop.Physical.Program` 的 `pcAddress` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Loop.lean#L27)

**类型**

```lean
{W : Type u_2} → CodedSorting.TwoWordUniformLoop.Physical.Program W → ℕ
```

**定义**

```lean
fun W self => self.1
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Loop.definitions.md#def-5efe9fa745fd2b70)

**基础库名称**

`Nat`

<a id="def-f8401a593749612b"></a>
## `CodedSorting.TwoWordUniformLoop.Physical.Program.halt`

读取 `CodedSorting.TwoWordUniformLoop.Physical.Program` 的 `halt` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Loop.lean#L28)

**类型**

```lean
{W : Type u_2} → CodedSorting.TwoWordUniformLoop.Physical.Program W → W
```

**定义**

```lean
fun W self => self.2
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Loop.definitions.md#def-5efe9fa745fd2b70)

<a id="def-2ecb4f4fd3b78862"></a>
## `CodedSorting.TwoWordUniformLoop.Physical.Program.body`

读取 `CodedSorting.TwoWordUniformLoop.Physical.Program` 的 `body` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Loop.lean#L29)

**类型**

```lean
{W : Type u_2} →
  CodedSorting.TwoWordUniformLoop.Physical.Program W → List (CodedSorting.TwoWordPhysicalAddresses.Command W)
```

**定义**

```lean
fun W self => self.3
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)

**基础库名称**

`List`
