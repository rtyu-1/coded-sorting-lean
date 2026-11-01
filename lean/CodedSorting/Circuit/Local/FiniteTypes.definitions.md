# FiniteTypes 的定义

[源码](FiniteTypes.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-050ce19ea890dc32"></a>
## `CodedSorting.Construction.FiniteCertificate.Gate`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](FiniteTypes.lean#L22)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](FiniteTypes.definitions.md#def-7c9ac588cd2d0597)

<a id="def-7c9ac588cd2d0597"></a>
## `CodedSorting.Construction.FiniteCertificate.Gate.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](FiniteTypes.lean#L22)

**类型**

```lean
ℕ → ℕ → List ℕ → CodedSorting.Construction.FiniteCertificate.Gate
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`List`, `Nat`

<a id="def-bb43c3add3b6fb8d"></a>
## `CodedSorting.Construction.FiniteCertificate.Gate.frame`

读取 `CodedSorting.Construction.FiniteCertificate.Gate` 的 `frame` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteTypes.lean#L23)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Gate → ℕ
```

**定义**

```lean
fun self => self.1
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`Nat`

<a id="def-b03234f707cb6726"></a>
## `CodedSorting.Construction.FiniteCertificate.Gate.destination`

读取 `CodedSorting.Construction.FiniteCertificate.Gate` 的 `destination` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteTypes.lean#L24)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Gate → ℕ
```

**定义**

```lean
fun self => self.2
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`Nat`

<a id="def-516947edde89b6d1"></a>
## `CodedSorting.Construction.FiniteCertificate.Gate.sources`

读取 `CodedSorting.Construction.FiniteCertificate.Gate` 的 `sources` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteTypes.lean#L25)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Gate → List ℕ
```

**定义**

```lean
fun self => self.3
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate](FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`List`, `Nat`

<a id="def-1cfe6fae6693f682"></a>
## `CodedSorting.Construction.FiniteCertificate.Projection`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](FiniteTypes.lean#L28)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection.mk](FiniteTypes.definitions.md#def-1a9be6880576c401)

<a id="def-1a9be6880576c401"></a>
## `CodedSorting.Construction.FiniteCertificate.Projection.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](FiniteTypes.lean#L28)

**类型**

```lean
ℤ → ℕ → Array ℤ → CodedSorting.Construction.FiniteCertificate.Projection
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](FiniteTypes.definitions.md#def-1cfe6fae6693f682)

**基础库名称**

`Int`, `Array`, `Nat`

<a id="def-fe61a69b89d86ced"></a>
## `CodedSorting.Construction.FiniteCertificate.Projection.denominator`

读取 `CodedSorting.Construction.FiniteCertificate.Projection` 的 `denominator` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteTypes.lean#L29)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Projection → ℤ
```

**定义**

```lean
fun self => self.1
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](FiniteTypes.definitions.md#def-1cfe6fae6693f682)

**基础库名称**

`Int`

<a id="def-98d789a781723f22"></a>
## `CodedSorting.Construction.FiniteCertificate.Projection.numerator`

读取 `CodedSorting.Construction.FiniteCertificate.Projection` 的 `numerator` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteTypes.lean#L31)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Projection → Array ℤ
```

**定义**

```lean
fun self => self.3
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](FiniteTypes.definitions.md#def-1cfe6fae6693f682)

**基础库名称**

`Int`, `Array`

<a id="def-667ce4a32a1e5f8b"></a>
## `CodedSorting.Construction.FiniteCertificate.instInhabitedProjection`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](FiniteTypes.lean#L32)

**类型**

```lean
Inhabited CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

```lean
{ default := { denominator := default, dimension := default, numerator := default } }
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Inhabited.default`, `Int.instInhabited`, `instInhabitedNat`, `Int`, `Array`, `Array.instInhabited`, `Nat`, `Inhabited`, `Inhabited.mk`

<a id="def-be4c1d670d56138f"></a>
## `CodedSorting.Construction.FiniteCertificate.portCount`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](FiniteTypes.lean#L34)

**类型**

```lean
ℕ
```

**定义**

```lean
111
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-6410b1b9a0cf1a12"></a>
## `CodedSorting.Construction.FiniteCertificate.registerCount`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](FiniteTypes.lean#L36)

**类型**

```lean
ℕ
```

**定义**

```lean
661
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`
