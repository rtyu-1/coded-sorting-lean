# Grouping 的定义

[源码](Grouping.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-f3d883dd37c94564"></a>
## `CodedSorting.CommonLeafGrouping.columns`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Grouping.lean#L11)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun capacity rows => capacity / rows
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `Nat`, `Nat.instDiv`

<a id="def-9472467428d4900c"></a>
## `CodedSorting.CommonLeafGrouping.groups`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Grouping.lean#L12)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun capacity rows count =>
  CodedSorting.LocalSortingCost.blockCount (CodedSorting.CommonLeafGrouping.columns capacity rows) count
```

**继续展开**

- [CodedSorting.LocalSortingCost.blockCount](../../../Sorting/Local/Framework/LocalSortingCost.definitions.md#def-05df3efddf58db36)
- [CodedSorting.CommonLeafGrouping.columns](Grouping.definitions.md#def-f3d883dd37c94564)

**基础库名称**

`Nat`

<a id="def-6fbb52144658b40e"></a>
## `CodedSorting.CommonLeafGrouping.groupRecords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Grouping.lean#L13)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun capacity rows => CodedSorting.CommonLeafGrouping.columns capacity rows * rows
```

**继续展开**

- [CodedSorting.CommonLeafGrouping.columns](Grouping.definitions.md#def-f3d883dd37c94564)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-cef78037c66d44b3"></a>
## `CodedSorting.CommonLeafGrouping.paddedRecords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Grouping.lean#L14)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun capacity rows count =>
  CodedSorting.CommonLeafGrouping.groups capacity rows count *
    CodedSorting.CommonLeafGrouping.groupRecords capacity rows
```

**继续展开**

- [CodedSorting.CommonLeafGrouping.groupRecords](Grouping.definitions.md#def-6fbb52144658b40e)
- [CodedSorting.CommonLeafGrouping.groups](Grouping.definitions.md#def-9472467428d4900c)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`
