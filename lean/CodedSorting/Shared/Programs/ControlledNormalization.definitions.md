# ControlledNormalization 的定义

[源码](ControlledNormalization.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2df5a4e499f7c5c7"></a>
## `CodedSorting.ControlledNormalization.Instruction`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ControlledNormalization.lean#L14)

**类型**

```lean
ℕ → ℕ → ℕ → Type u_2 → Type u_2
```

**继续展开**

- [CodedSorting.ControlledNormalization.Instruction.mk](ControlledNormalization.definitions.md#def-5b44b5b9869102be)

**基础库名称**

`Nat`

<a id="def-5b44b5b9869102be"></a>
## `CodedSorting.ControlledNormalization.Instruction.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ControlledNormalization.lean#L14)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} →
    CodedSorting.Normalization.Command L b D Word →
      (CodedSorting.Normalization.Words L Word → CodedSorting.Normalization.Words L Word) →
        CodedSorting.ControlledNormalization.Instruction L b D Word
```

**继续展开**

- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)
- [CodedSorting.ControlledNormalization.Instruction](ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`Nat`

<a id="def-3d5141c25fe6587d"></a>
## `CodedSorting.ControlledNormalization.Instruction.operation`

读取 `CodedSorting.ControlledNormalization.Instruction` 的 `operation` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ControlledNormalization.lean#L15)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} →
    CodedSorting.ControlledNormalization.Instruction L b D Word → CodedSorting.Normalization.Command L b D Word
```

**定义**

```lean
fun L b D Word self => self.1
```

**继续展开**

- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)
- [CodedSorting.ControlledNormalization.Instruction](ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`Nat`

<a id="def-f9b13fabe559e990"></a>
## `CodedSorting.ControlledNormalization.Instruction.resume`

读取 `CodedSorting.ControlledNormalization.Instruction` 的 `resume` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ControlledNormalization.lean#L16)

**类型**

```lean
{L b D : ℕ} →
  {Word : Type u_2} →
    CodedSorting.ControlledNormalization.Instruction L b D Word →
      CodedSorting.Normalization.Words L Word → CodedSorting.Normalization.Words L Word
```

**定义**

```lean
fun L b D Word self => self.2
```

**继续展开**

- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.ControlledNormalization.Instruction](ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`Nat`

<a id="def-311feb3c44e69784"></a>
## `CodedSorting.ControlledNormalization.Policy`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ControlledNormalization.lean#L18)

**类型**

```lean
ℕ → ℕ → ℕ → Type u_2 → Type u_2
```

**定义**

```lean
fun L b D Word =>
  CodedSorting.Normalization.Words L Word → Option (CodedSorting.ControlledNormalization.Instruction L b D Word)
```

**继续展开**

- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.ControlledNormalization.Instruction](ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`Nat`, `Option`

<a id="def-66ac60db55b282bd"></a>
## `CodedSorting.ControlledNormalization.logicalStep`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ControlledNormalization.lean#L21)

**类型**

```lean
{Word : Type u_1} →
  {L b D : ℕ} →
    CodedSorting.ControlledNormalization.Instruction L b D Word →
      CodedSorting.Normalization.LogicalState L b D Word → CodedSorting.Normalization.LogicalState L b D Word
```

**定义**

```lean
fun {Word} {L b D} i s =>
  CodedSorting.Normalization.logicalStep (CodedSorting.Normalization.Command.localOp i.resume)
    (CodedSorting.Normalization.logicalStep i.operation s)
```

**继续展开**

- [CodedSorting.ControlledNormalization.Instruction.resume](ControlledNormalization.definitions.md#def-f9b13fabe559e990)
- [CodedSorting.ControlledNormalization.Instruction.operation](ControlledNormalization.definitions.md#def-3d5141c25fe6587d)
- [CodedSorting.Normalization.LogicalState](Normalization.definitions.md#def-fe5b3999cdd6a29d)
- [CodedSorting.Normalization.logicalStep](Normalization.definitions.md#def-65568248037e0c07)
- [CodedSorting.Normalization.Command.localOp](Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.ControlledNormalization.Instruction](ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`Nat`
