# ConcreteWorkspace 的定义

[源码](ConcreteWorkspace.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-faa5344600e25d31"></a>
## `CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.exchangeCoefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteWorkspace.lean#L108)

**类型**

```lean
ℕ
```

**定义**

```lean
CodedSorting.Construction.Sorting.CommonSortingSpaceBudget.coefficient
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonSortingSpaceBudget.coefficient](../Resources/SpaceBudget.definitions.md#def-1e0a2a921a3a1ef0)

**基础库名称**

`Nat`

<a id="def-9ac8e29c0a861d94"></a>
## `CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.coefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ConcreteWorkspace.lean#L109)

**类型**

```lean
ℕ
```

**定义**

```lean
5020 + 4 * CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.exchangeCoefficient
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.exchangeCoefficient](ConcreteWorkspace.definitions.md#def-faa5344600e25d31)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`
