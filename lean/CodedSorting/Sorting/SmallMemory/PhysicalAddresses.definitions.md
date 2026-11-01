# PhysicalAddresses 的定义

[源码](PhysicalAddresses.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-06c53f2492a6c79b"></a>
## `CodedSorting.TwoWordSpill.Resident`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalAddresses.lean#L44)

**类型**

```lean
Type u_3 → Type u_3
```

**定义**

```lean
fun Word => Word × Word
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Prod`

<a id="def-e0c87ff3db4dbd69"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](PhysicalAddresses.lean#L577)

**类型**

```lean
Type u_3 → Type u_3
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command.readRight](PhysicalAddresses.definitions.md#def-80ee4e0629315e7a)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeRight](PhysicalAddresses.definitions.md#def-ba338466a2ed8462)
- [CodedSorting.TwoWordPhysicalAddresses.Command.localOp](PhysicalAddresses.definitions.md#def-c713e8bf83b71ce0)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readLeft](PhysicalAddresses.definitions.md#def-10977754ba9e1532)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft](PhysicalAddresses.definitions.md#def-38889ca9c555a290)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt](PhysicalAddresses.definitions.md#def-463ccc65763d544d)

<a id="def-a499b9b9d54d5380"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command.casesOn`

读取 `CodedSorting.TwoWordPhysicalAddresses.Command` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalAddresses.lean#L577)

**类型**

```lean
{W : Type u_3} →
  {motive : CodedSorting.TwoWordPhysicalAddresses.Command W → Sort u} →
    (t : CodedSorting.TwoWordPhysicalAddresses.Command W) →
      ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.readLeft a)) →
        ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.readRight a)) →
          ((a : CodedSorting.TwoWordSpill.Resident W → ℕ) →
              motive (CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt a)) →
            ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft a)) →
              ((a : CodedSorting.TwoWordSpill.Resident W → ℕ) →
                  motive (CodedSorting.TwoWordPhysicalAddresses.Command.writeRight a)) →
                ((f : CodedSorting.TwoWordSpill.Resident W → CodedSorting.TwoWordSpill.Resident W) →
                    motive (CodedSorting.TwoWordPhysicalAddresses.Command.localOp f)) →
                  motive t
```

**定义**

```lean
fun {W} {motive} t readLeft readRight readRightAt writeLeft writeRight localOp =>
  CodedSorting.TwoWordPhysicalAddresses.Command.rec (fun a => readLeft a) (fun a => readRight a)
    (fun a => readRightAt a) (fun a => writeLeft a) (fun a => writeRight a) (fun f => localOp f) t
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command.readRight](PhysicalAddresses.definitions.md#def-80ee4e0629315e7a)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeRight](PhysicalAddresses.definitions.md#def-ba338466a2ed8462)
- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordPhysicalAddresses.Command.localOp](PhysicalAddresses.definitions.md#def-c713e8bf83b71ce0)
- [CodedSorting.TwoWordPhysicalAddresses.Command.rec](PhysicalAddresses.definitions.md#def-a1a1840c78904a81)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readLeft](PhysicalAddresses.definitions.md#def-10977754ba9e1532)
- [CodedSorting.TwoWordSpill.Resident](PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft](PhysicalAddresses.definitions.md#def-38889ca9c555a290)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt](PhysicalAddresses.definitions.md#def-463ccc65763d544d)

**基础库名称**

`Nat`

<a id="def-a1a1840c78904a81"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](PhysicalAddresses.lean#L577)

**类型**

```lean
{W : Type u_3} →
  {motive : CodedSorting.TwoWordPhysicalAddresses.Command W → Sort u} →
    ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.readLeft a)) →
      ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.readRight a)) →
        ((a : CodedSorting.TwoWordSpill.Resident W → ℕ) →
            motive (CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt a)) →
          ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft a)) →
            ((a : CodedSorting.TwoWordSpill.Resident W → ℕ) →
                motive (CodedSorting.TwoWordPhysicalAddresses.Command.writeRight a)) →
              ((f : CodedSorting.TwoWordSpill.Resident W → CodedSorting.TwoWordSpill.Resident W) →
                  motive (CodedSorting.TwoWordPhysicalAddresses.Command.localOp f)) →
                (t : CodedSorting.TwoWordPhysicalAddresses.Command W) → motive t
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command.readRight](PhysicalAddresses.definitions.md#def-80ee4e0629315e7a)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeRight](PhysicalAddresses.definitions.md#def-ba338466a2ed8462)
- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordPhysicalAddresses.Command.localOp](PhysicalAddresses.definitions.md#def-c713e8bf83b71ce0)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readLeft](PhysicalAddresses.definitions.md#def-10977754ba9e1532)
- [CodedSorting.TwoWordSpill.Resident](PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft](PhysicalAddresses.definitions.md#def-38889ca9c555a290)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt](PhysicalAddresses.definitions.md#def-463ccc65763d544d)

**基础库名称**

`Nat`

<a id="def-10977754ba9e1532"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command.readLeft`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalAddresses.lean#L578)

**类型**

```lean
{W : Type u_3} → ℕ → CodedSorting.TwoWordPhysicalAddresses.Command W
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)

**基础库名称**

`Nat`

<a id="def-80ee4e0629315e7a"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command.readRight`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalAddresses.lean#L579)

**类型**

```lean
{W : Type u_3} → ℕ → CodedSorting.TwoWordPhysicalAddresses.Command W
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)

**基础库名称**

`Nat`

<a id="def-463ccc65763d544d"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalAddresses.lean#L580)

**类型**

```lean
{W : Type u_3} → (CodedSorting.TwoWordSpill.Resident W → ℕ) → CodedSorting.TwoWordPhysicalAddresses.Command W
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordSpill.Resident](PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)

**基础库名称**

`Nat`

<a id="def-38889ca9c555a290"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalAddresses.lean#L581)

**类型**

```lean
{W : Type u_3} → ℕ → CodedSorting.TwoWordPhysicalAddresses.Command W
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)

**基础库名称**

`Nat`

<a id="def-ba338466a2ed8462"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command.writeRight`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalAddresses.lean#L582)

**类型**

```lean
{W : Type u_3} → (CodedSorting.TwoWordSpill.Resident W → ℕ) → CodedSorting.TwoWordPhysicalAddresses.Command W
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordSpill.Resident](PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)

**基础库名称**

`Nat`

<a id="def-c713e8bf83b71ce0"></a>
## `CodedSorting.TwoWordPhysicalAddresses.Command.localOp`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalAddresses.lean#L583)

**类型**

```lean
{W : Type u_3} →
  (CodedSorting.TwoWordSpill.Resident W → CodedSorting.TwoWordSpill.Resident W) →
    CodedSorting.TwoWordPhysicalAddresses.Command W
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command](PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordSpill.Resident](PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)
