# PhysicalFramePaths 的定义

[源码](PhysicalFramePaths.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-f8f0b66be4cf5f89"></a>
## `CodedSorting.Construction.TensorFrameGeometry.LocalMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFramePaths.lean#L32)

**类型**

```lean
Type
```

**定义**

```lean
Matrix (Fin 8) (Fin 8) ℚ
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Matrix`, `Rat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-c985f0fda5be0bcd"></a>
## `CodedSorting.Construction.PhysicalFramePaths.frameMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalFramePaths.lean#L60)

**类型**

```lean
ℕ → CodedSorting.Construction.TensorFrameGeometry.LocalMatrix
```

**定义**

```lean
fun f =>
  CodedSorting.Construction.IntegerProjection.certificateMatrix
    CodedSorting.Construction.FiniteCertificate.projections[f]!
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.instInhabitedProjection](../Local/FiniteTypes.definitions.md#def-667ce4a32a1e5f8b)
- [CodedSorting.Construction.FiniteCertificate.projections](../../Generated/FiniteCircuit/Data.definitions.md#def-e9867ef4e9ce82c3)
- [CodedSorting.Construction.IntegerProjection.certificateMatrix](../Labels/FiniteInterpretation.definitions.md#def-bd328f0d6e991056)
- [CodedSorting.Construction.TensorFrameGeometry.LocalMatrix](PhysicalFramePaths.definitions.md#def-f8f0b66be4cf5f89)
- [CodedSorting.Construction.FiniteCertificate.Projection](../Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)

**基础库名称**

`Array`, `Nat`, `LT.lt`, `instLTNat`, `GetElem?.getElem!`, `Array.size`, `Array.instGetElem?NatLtSize`
