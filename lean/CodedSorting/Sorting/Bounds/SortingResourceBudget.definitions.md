# SortingResourceBudget 的定义

[源码](SortingResourceBudget.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-c75060ed230df145"></a>
## `CodedSorting.SortingResourceBudget.Inventory`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](SortingResourceBudget.lean#L13)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory.mk](SortingResourceBudget.definitions.md#def-0e997c35e77a1441)

<a id="def-0e997c35e77a1441"></a>
## `CodedSorting.SortingResourceBudget.Inventory.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](SortingResourceBudget.lean#L15)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → CodedSorting.SortingResourceBudget.Inventory
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat`

<a id="def-57a55c8de06b50b7"></a>
## `CodedSorting.SortingResourceBudget.Inventory.readers`

读取 `CodedSorting.SortingResourceBudget.Inventory` 的 `readers` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SortingResourceBudget.lean#L16)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ
```

**定义**

```lean
fun self => self.1
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat`

<a id="def-05f5194f09efb8fc"></a>
## `CodedSorting.SortingResourceBudget.Inventory.writers`

读取 `CodedSorting.SortingResourceBudget.Inventory` 的 `writers` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SortingResourceBudget.lean#L17)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ
```

**定义**

```lean
fun self => self.2
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat`

<a id="def-b107122480bc6937"></a>
## `CodedSorting.SortingResourceBudget.Inventory.keys`

读取 `CodedSorting.SortingResourceBudget.Inventory` 的 `keys` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SortingResourceBudget.lean#L18)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ
```

**定义**

```lean
fun self => self.3
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat`

<a id="def-42f9d44e4c026d81"></a>
## `CodedSorting.SortingResourceBudget.Inventory.pc`

读取 `CodedSorting.SortingResourceBudget.Inventory` 的 `pc` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SortingResourceBudget.lean#L19)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ
```

**定义**

```lean
fun self => self.4
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat`

<a id="def-197343a4949f7653"></a>
## `CodedSorting.SortingResourceBudget.Inventory.ratio`

读取 `CodedSorting.SortingResourceBudget.Inventory` 的 `ratio` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](SortingResourceBudget.lean#L20)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ
```

**定义**

```lean
fun self => self.5
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat`

<a id="def-ea371db150e4467a"></a>
## `CodedSorting.SortingResourceBudget.digits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SortingResourceBudget.lean#L22)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun c exponent => c * (exponent + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-5df4ad7855a35b51"></a>
## `CodedSorting.SortingResourceBudget.payloadCoefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SortingResourceBudget.lean#L23)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ
```

**定义**

```lean
fun v => 1537 + v.readers + v.writers
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory.readers](SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.SortingResourceBudget.Inventory.writers](SortingResourceBudget.definitions.md#def-05f5194f09efb8fc)
- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-5190ff014c28590b"></a>
## `CodedSorting.SortingResourceBudget.metadata`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SortingResourceBudget.lean#L24)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ → ℕ
```

**定义**

```lean
fun v d => (4 * v.readers + 3 * v.writers + 6 * v.keys + 42) * d + 1 + 3 * v.pc
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory.readers](SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.SortingResourceBudget.Inventory.writers](SortingResourceBudget.definitions.md#def-05f5194f09efb8fc)
- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.Inventory.pc](SortingResourceBudget.definitions.md#def-42f9d44e4c026d81)
- [CodedSorting.SortingResourceBudget.Inventory.keys](SortingResourceBudget.definitions.md#def-b107122480bc6937)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-9e7e2eeee9930238"></a>
## `CodedSorting.SortingResourceBudget.reserve`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SortingResourceBudget.lean#L30)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ → ℕ → ℕ
```

**定义**

```lean
fun v c d =>
  16 *
    (CodedSorting.SortingResourceBudget.payloadCoefficient v + CodedSorting.SortingResourceBudget.metadata v d +
            (4 * d + 3) +
          v.ratio +
        2 ^ (3 * c) +
      1)
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory.ratio](SortingResourceBudget.definitions.md#def-197343a4949f7653)
- [CodedSorting.SortingResourceBudget.payloadCoefficient](SortingResourceBudget.definitions.md#def-5df4ad7855a35b51)
- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.metadata](SortingResourceBudget.definitions.md#def-5190ff014c28590b)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-c389dd4158f0ee74"></a>
## `CodedSorting.SortingResourceBudget.H`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SortingResourceBudget.lean#L32)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun v c d M => M / CodedSorting.SortingResourceBudget.reserve v c d
```

**继续展开**

- [CodedSorting.SortingResourceBudget.reserve](SortingResourceBudget.definitions.md#def-9e7e2eeee9930238)
- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `Nat`, `Nat.instDiv`

<a id="def-49532a5e2a2934bc"></a>
## `CodedSorting.SortingResourceBudget.block`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SortingResourceBudget.lean#L33)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun v c d B => CodedSorting.Normalization.logicalBlockSize B (CodedSorting.SortingResourceBudget.reserve v c d ^ 2)
```

**继续展开**

- [CodedSorting.SortingResourceBudget.reserve](SortingResourceBudget.definitions.md#def-9e7e2eeee9930238)
- [CodedSorting.Normalization.logicalBlockSize](../../Shared/Programs/Normalization.definitions.md#def-bb8eed12be50f878)
- [CodedSorting.SortingResourceBudget.Inventory](SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`
