# Counts 的定义

[源码](Counts.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-582c9f03179a1516"></a>
## `CodedSorting.Construction.lineCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Counts.lean#L17)

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

<a id="def-1c1a92157b7ae1ea"></a>
## `CodedSorting.Construction.localHelperCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Counts.lean#L18)

**类型**

```lean
ℕ
```

**定义**

```lean
439
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-6535389c6aaa0726"></a>
## `CodedSorting.Construction.copiedTotalCost`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Counts.lean#L19)

**类型**

```lean
ℕ
```

**定义**

```lean
63
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-d9b1f0218bf392c3"></a>
## `CodedSorting.Construction.ambientDimension`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Counts.lean#L20)

**类型**

```lean
ℕ
```

**定义**

```lean
512
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-8dbf3b9bec362266"></a>
## `CodedSorting.Construction.streamCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Counts.lean#L22)

**类型**

```lean
ℕ
```

**定义**

```lean
3 * CodedSorting.Construction.lineCount ^ 2 *
  (2 * CodedSorting.Construction.lineCount + CodedSorting.Construction.localHelperCount)
```

**继续展开**

- [CodedSorting.Construction.localHelperCount](Counts.definitions.md#def-1c1a92157b7ae1ea)
- [CodedSorting.Construction.lineCount](Counts.definitions.md#def-582c9f03179a1516)

**基础库名称**

`instPowNat`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `instNatPowNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-64416b74593cf091"></a>
## `CodedSorting.Construction.rankBudget`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Counts.lean#L25)

**类型**

```lean
ℕ
```

**定义**

```lean
6 * CodedSorting.Construction.lineCount ^ 3 * (CodedSorting.Construction.ambientDimension - 1) +
    3 * CodedSorting.Construction.lineCount ^ 2 * CodedSorting.Construction.localHelperCount *
      CodedSorting.Construction.ambientDimension +
  9 * CodedSorting.Construction.lineCount ^ 2 * CodedSorting.Construction.copiedTotalCost
```

**继续展开**

- [CodedSorting.Construction.localHelperCount](Counts.definitions.md#def-1c1a92157b7ae1ea)
- [CodedSorting.Construction.copiedTotalCost](Counts.definitions.md#def-6535389c6aaa0726)
- [CodedSorting.Construction.lineCount](Counts.definitions.md#def-582c9f03179a1516)
- [CodedSorting.Construction.ambientDimension](Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`instPowNat`, `HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `instOfNatNat`, `instNatPowNat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`
