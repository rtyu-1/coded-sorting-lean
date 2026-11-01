# PhysicalFrameWordData 的定义

[源码](PhysicalFrameWordData.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-447407dc57ac7037"></a>
## `CodedSorting.Construction.PhysicalFramePaths.physicalPrefix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWordData.lean#L28)

**类型**

```lean
List CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
List.take CodedSorting.Construction.FiniteCertificate.beforeScatterCount
  CodedSorting.Construction.FiniteCertificate.gates.toList
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.gates](../../Generated/FiniteCircuit/Data.definitions.md#def-1b8de7a898d28b81)
- [CodedSorting.Construction.FiniteCertificate.Gate](../Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.FiniteCertificate.beforeScatterCount](../../Generated/FiniteCircuit/Data.definitions.md#def-8594ece3c1c04e1b)

**基础库名称**

`Array.toList`, `List`, `List.take`

<a id="def-d1f8f6b329be583a"></a>
## `CodedSorting.Construction.PhysicalFramePaths.physicalScatter`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWordData.lean#L29)

**类型**

```lean
List CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
List.take CodedSorting.Construction.FiniteCertificate.portCount
  (List.drop CodedSorting.Construction.FiniteCertificate.beforeScatterCount
    CodedSorting.Construction.FiniteCertificate.gates.toList)
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.gates](../../Generated/FiniteCircuit/Data.definitions.md#def-1b8de7a898d28b81)
- [CodedSorting.Construction.FiniteCertificate.Gate](../Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.FiniteCertificate.portCount](../Local/FiniteTypes.definitions.md#def-be4c1d670d56138f)
- [CodedSorting.Construction.FiniteCertificate.beforeScatterCount](../../Generated/FiniteCircuit/Data.definitions.md#def-8594ece3c1c04e1b)

**基础库名称**

`Array.toList`, `List`, `List.drop`, `List.take`

<a id="def-da276d2c2da84939"></a>
## `CodedSorting.Construction.PhysicalFramePaths.physicalSuffix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFrameWordData.lean#L30)

**类型**

```lean
List CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
List.drop
  (CodedSorting.Construction.FiniteCertificate.beforeScatterCount +
    CodedSorting.Construction.FiniteCertificate.portCount)
  CodedSorting.Construction.FiniteCertificate.gates.toList
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.gates](../../Generated/FiniteCircuit/Data.definitions.md#def-1b8de7a898d28b81)
- [CodedSorting.Construction.FiniteCertificate.Gate](../Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.FiniteCertificate.portCount](../Local/FiniteTypes.definitions.md#def-be4c1d670d56138f)
- [CodedSorting.Construction.FiniteCertificate.beforeScatterCount](../../Generated/FiniteCircuit/Data.definitions.md#def-8594ece3c1c04e1b)

**基础库名称**

`Array.toList`, `List`, `instHAdd`, `List.drop`, `HAdd.hAdd`, `Nat`, `instAddNat`
