# Data 的定义

[源码](Data.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-de37911e973d5580"></a>
## `CodedSorting.Construction.FiniteCertificate.linesChunk0`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L10)

**类型**

```lean
Array (Array ℤ)
```

**定义**

```lean
#[#[2, 0, 0, 0, 0, 0, 0, 0], #[0, 2, 0, 0, 0, 0, 0, 0], #[0, 0, 2, 0, 0, 0, 0, 0], #[0, 0, 0, 2, 0, 0, 0, 0],
  #[0, 0, 0, 0, 2, 0, 0, 0], #[0, 0, 0, 0, 0, 2, 0, 0], #[0, 0, 0, 0, 0, 0, 2, 0], #[0, 0, 0, 0, 0, 0, 0, 2],
  #[0, 1, 1, 0, 1, 0, 0, 1], #[0, 1, 1, 0, 1, 0, 0, -1], #[0, 1, 1, 0, -1, 0, 0, -1], #[0, 1, -1, 0, 1, 0, 0, 1],
  #[0, 1, -1, 0, 1, 0, 0, -1], #[0, 1, -1, 0, -1, 0, 0, 1], #[1, 0, 1, 0, 1, 0, 1, 0], #[1, 0, 1, 0, 1, 0, -1, 0],
  #[1, 0, 1, 0, -1, 0, 1, 0], #[1, 0, 1, 0, -1, 0, -1, 0], #[1, 0, -1, 0, 1, 0, 1, 0], #[1, 0, -1, 0, 1, 0, -1, 0],
  #[1, 0, -1, 0, -1, 0, 1, 0], #[1, 0, -1, 0, -1, 0, -1, 0], #[1, 1, 0, 0, 0, 0, 1, 1], #[1, 1, 0, 0, 0, 0, 1, -1],
  #[1, 1, 0, 0, 0, 0, -1, 1], #[1, 1, 0, 0, 0, 0, -1, -1], #[1, -1, 0, 0, 0, 0, 1, 1], #[1, -1, 0, 0, 0, 0, 1, -1],
  #[1, -1, 0, 0, 0, 0, -1, 1], #[1, -1, 0, 0, 0, 0, -1, -1], #[1, 1, 0, 0, 1, 1, 0, 0], #[1, 1, 0, 0, 1, -1, 0, 0]]
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Int.instNegInt`, `Int`, `List.toArray`, `List.cons`, `Array`, `instOfNat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-a79fdfa1fdc937df"></a>
## `CodedSorting.Construction.FiniteCertificate.linesChunk1`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L43)

**类型**

```lean
Array (Array ℤ)
```

**定义**

```lean
#[#[1, 1, 0, 0, -1, 1, 0, 0], #[1, 1, 0, 0, -1, -1, 0, 0], #[1, -1, 0, 0, 1, 1, 0, 0], #[1, -1, 0, 0, 1, -1, 0, 0],
  #[1, -1, 0, 0, -1, 1, 0, 0], #[1, -1, 0, 0, -1, -1, 0, 0], #[1, 0, 1, 0, 0, 1, 0, 1], #[1, 0, 1, 0, 0, 1, 0, -1],
  #[1, 0, 1, 0, 0, -1, 0, 1], #[1, 0, 1, 0, 0, -1, 0, -1], #[1, 0, -1, 0, 0, 1, 0, 1], #[1, 0, -1, 0, 0, 1, 0, -1],
  #[1, 0, -1, 0, 0, -1, 0, 1], #[1, 0, -1, 0, 0, -1, 0, -1], #[0, 1, 1, 0, 0, 1, 1, 0], #[0, 1, 1, 0, 0, 1, -1, 0],
  #[0, 1, 1, 0, 0, -1, 1, 0], #[0, 1, -1, 0, 0, 1, 1, 0], #[0, 1, -1, 0, 0, -1, 1, 0], #[0, 1, -1, 0, 0, -1, -1, 0],
  #[0, 0, 0, 0, 1, 1, 1, -1], #[0, 0, 0, 0, 1, 1, -1, 1], #[0, 0, 0, 0, 1, 1, -1, -1], #[0, 0, 0, 0, 1, -1, 1, 1],
  #[0, 0, 0, 0, 1, -1, 1, -1], #[0, 0, 0, 0, 1, -1, -1, 1], #[0, 0, 0, 0, 1, -1, -1, -1], #[1, 1, 1, 1, 0, 0, 0, 0],
  #[1, 1, 1, -1, 0, 0, 0, 0], #[1, 1, -1, -1, 0, 0, 0, 0], #[1, -1, 1, 1, 0, 0, 0, 0], #[1, -1, 1, -1, 0, 0, 0, 0]]
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Int.instNegInt`, `Int`, `List.toArray`, `List.cons`, `Array`, `instOfNat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-642f0cf310e8017f"></a>
## `CodedSorting.Construction.FiniteCertificate.linesChunk2`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L76)

**类型**

```lean
Array (Array ℤ)
```

**定义**

```lean
#[#[1, -1, -1, 1, 0, 0, 0, 0], #[1, -1, -1, -1, 0, 0, 0, 0], #[1, 0, 0, 1, 1, 0, 0, -1], #[1, 0, 0, 1, -1, 0, 0, 1],
  #[1, 0, 0, 1, -1, 0, 0, -1], #[1, 0, 0, -1, 1, 0, 0, 1], #[1, 0, 0, -1, 1, 0, 0, -1], #[1, 0, 0, -1, -1, 0, 0, 1],
  #[1, 0, 0, -1, -1, 0, 0, -1], #[0, 1, 0, 1, 1, 0, 1, 0], #[0, 1, 0, 1, 1, 0, -1, 0], #[0, 1, 0, 1, -1, 0, 1, 0],
  #[0, 1, 0, 1, -1, 0, -1, 0], #[0, 1, 0, -1, 1, 0, 1, 0], #[0, 1, 0, -1, 1, 0, -1, 0], #[0, 1, 0, -1, -1, 0, 1, 0],
  #[0, 1, 0, -1, -1, 0, -1, 0], #[0, 0, 1, 1, 0, 0, 1, 1], #[0, 0, 1, 1, 0, 0, -1, 1], #[0, 0, 1, 1, 0, 0, -1, -1],
  #[0, 0, 1, -1, 0, 0, 1, 1], #[0, 0, 1, -1, 0, 0, 1, -1], #[0, 0, 1, -1, 0, 0, -1, 1], #[0, 0, 1, -1, 0, 0, -1, -1],
  #[0, 0, 1, 1, 1, 1, 0, 0], #[0, 0, 1, 1, 1, -1, 0, 0], #[0, 0, 1, 1, -1, 1, 0, 0], #[0, 0, 1, 1, -1, -1, 0, 0],
  #[0, 0, 1, -1, 1, 1, 0, 0], #[0, 0, 1, -1, 1, -1, 0, 0], #[0, 0, 1, -1, -1, 1, 0, 0], #[0, 0, 1, -1, -1, -1, 0, 0]]
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Int.instNegInt`, `Int`, `List.toArray`, `List.cons`, `Array`, `instOfNat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-c792e58d1de31619"></a>
## `CodedSorting.Construction.FiniteCertificate.linesChunk3`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L109)

**类型**

```lean
Array (Array ℤ)
```

**定义**

```lean
#[#[0, 1, 0, 1, 0, 1, 0, 1], #[0, 1, 0, 1, 0, 1, 0, -1], #[0, 1, 0, 1, 0, -1, 0, 1], #[0, 1, 0, 1, 0, -1, 0, -1],
  #[0, 1, 0, -1, 0, 1, 0, 1], #[0, 1, 0, -1, 0, 1, 0, -1], #[0, 1, 0, -1, 0, -1, 0, 1], #[1, 0, 0, 1, 0, 1, 1, 0],
  #[1, 0, 0, 1, 0, 1, -1, 0], #[1, 0, 0, 1, 0, -1, 1, 0], #[1, 0, 0, 1, 0, -1, -1, 0], #[1, 0, 0, -1, 0, 1, 1, 0],
  #[1, 0, 0, -1, 0, 1, -1, 0], #[1, 0, 0, -1, 0, -1, 1, 0], #[1, 0, 0, -1, 0, -1, -1, 0]]
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Int.instNegInt`, `Int`, `List.toArray`, `List.cons`, `Array`, `instOfNat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-b85746934906bd4e"></a>
## `CodedSorting.Construction.FiniteCertificate.lines`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L125)

**类型**

```lean
Array (Array ℤ)
```

**定义**

```lean
Array.foldl (fun a b => a ++ b) #[]
  #[CodedSorting.Construction.FiniteCertificate.linesChunk0, CodedSorting.Construction.FiniteCertificate.linesChunk1,
    CodedSorting.Construction.FiniteCertificate.linesChunk2, CodedSorting.Construction.FiniteCertificate.linesChunk3]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.linesChunk1](Data.definitions.md#def-a79fdfa1fdc937df)
- [CodedSorting.Construction.FiniteCertificate.linesChunk3](Data.definitions.md#def-c792e58d1de31619)
- [CodedSorting.Construction.FiniteCertificate.linesChunk0](Data.definitions.md#def-de37911e973d5580)
- [CodedSorting.Construction.FiniteCertificate.linesChunk2](Data.definitions.md#def-642f0cf310e8017f)

**基础库名称**

`Array.instAppend`, `instOfNatNat`, `Int`, `List.toArray`, `Array.foldl`, `List.cons`, `Array`, `instHAppendOfAppend`, `Nat`, `OfNat.ofNat`, `Array.size`, `HAppend.hAppend`, `List.nil`

<a id="def-3db68d548332b3a0"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk0`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L807)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L807)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-73662379ca3f34a3"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk1`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L840)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L840)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-a569726275e279e1"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk2`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L873)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L873)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-de86071cf6ef306f"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk3`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L906)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L906)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-4771a18205812c57"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk4`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L939)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L939)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-68d04d2c489e56b5"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk5`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L972)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L972)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-39aa40929b9e8f3d"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk6`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1005)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1005)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-5c8049873671391a"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk7`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1038)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1038)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-823e2456c6beb841"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk8`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1071)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1071)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-91fb16b734f085ba"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk9`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1104)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1104)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-68014263fb686c13"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk10`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1137)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1137)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-61d97d1e0851b960"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk11`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1170)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1170)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-e7a07bdc0cf8a5b4"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk12`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1203)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1203)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-39d5607558875e8a"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk13`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1236)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1236)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-2fc69cbcb935cafb"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk14`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1269)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1269)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-05318aead9270cdc"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk15`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1302)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1302)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-207b826a5af1a18f"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk16`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1335)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1335)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-a5dfad7923fab9d8"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk17`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1368)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1368)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-9953fa97374a0bcb"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk18`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1401)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1401)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-0a5b7aa404757e83"></a>
## `CodedSorting.Construction.FiniteCertificate.projectionsChunk19`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1434)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1434)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-1a9be6880576c401)

**基础库名称**

`Int.instNegInt`, `instOfNatNat`, `Int`, `List.toArray`, `List.cons`, `Array`, `List`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Neg.neg`, `List.nil`

<a id="def-e9867ef4e9ce82c3"></a>
## `CodedSorting.Construction.FiniteCertificate.projections`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1463)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Projection
```

**定义**

```lean
Array.foldl (fun a b => a ++ b) #[]
  #[CodedSorting.Construction.FiniteCertificate.projectionsChunk0,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk1,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk2,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk3,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk4,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk5,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk6,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk7,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk8,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk9,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk10,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk11,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk12,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk13,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk14,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk15,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk16,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk17,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk18,
    CodedSorting.Construction.FiniteCertificate.projectionsChunk19]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.projectionsChunk13](Data.definitions.md#def-39d5607558875e8a)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk15](Data.definitions.md#def-05318aead9270cdc)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk10](Data.definitions.md#def-68014263fb686c13)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk19](Data.definitions.md#def-0a5b7aa404757e83)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk18](Data.definitions.md#def-9953fa97374a0bcb)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk7](Data.definitions.md#def-5c8049873671391a)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk14](Data.definitions.md#def-2fc69cbcb935cafb)
- [CodedSorting.Construction.FiniteCertificate.Projection](../../Circuit/Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk12](Data.definitions.md#def-e7a07bdc0cf8a5b4)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk9](Data.definitions.md#def-91fb16b734f085ba)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk6](Data.definitions.md#def-39aa40929b9e8f3d)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk17](Data.definitions.md#def-a5dfad7923fab9d8)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk1](Data.definitions.md#def-73662379ca3f34a3)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk4](Data.definitions.md#def-4771a18205812c57)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk5](Data.definitions.md#def-68d04d2c489e56b5)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk2](Data.definitions.md#def-a569726275e279e1)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk11](Data.definitions.md#def-61d97d1e0851b960)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk0](Data.definitions.md#def-3db68d548332b3a0)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk3](Data.definitions.md#def-de86071cf6ef306f)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk16](Data.definitions.md#def-207b826a5af1a18f)
- [CodedSorting.Construction.FiniteCertificate.projectionsChunk8](Data.definitions.md#def-823e2456c6beb841)

**基础库名称**

`Array.instAppend`, `instOfNatNat`, `List.toArray`, `Array.foldl`, `List.cons`, `Array`, `instHAppendOfAppend`, `Nat`, `OfNat.ofNat`, `Array.size`, `HAppend.hAppend`, `List.nil`

<a id="def-981a72463683f667"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk0`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1484)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1484)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `List`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e8f13884dbf56437"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk1`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1517)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1517)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `List`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-965a813d6c9af834"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk2`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1550)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1550)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `List`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-77b62cd9919378bf"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk3`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1583)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

此定义包含较长的固定数据或构造表达式，完整内容见[源码](Data.lean#L1583)。其全部自定义依赖仍列在下面。

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `List`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-b7c1f6812be49501"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk4`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1616)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 10, destination := 239, sources := [8] }, { frame := 11, destination := 240, sources := [9] },
  { frame := 11, destination := 241, sources := [9] }, { frame := 12, destination := 244, sources := [10] },
  { frame := 12, destination := 245, sources := [10] }, { frame := 13, destination := 246, sources := [11] },
  { frame := 13, destination := 247, sources := [11] }, { frame := 14, destination := 248, sources := [12] },
  { frame := 14, destination := 249, sources := [12] }, { frame := 15, destination := 250, sources := [13] },
  { frame := 15, destination := 251, sources := [13] }, { frame := 16, destination := 254, sources := [14] },
  { frame := 16, destination := 255, sources := [14] }, { frame := 17, destination := 256, sources := [15] },
  { frame := 17, destination := 257, sources := [15] }, { frame := 18, destination := 258, sources := [16] },
  { frame := 18, destination := 259, sources := [16] }, { frame := 19, destination := 260, sources := [17] },
  { frame := 19, destination := 261, sources := [17] }, { frame := 20, destination := 262, sources := [18] },
  { frame := 20, destination := 263, sources := [18] }, { frame := 21, destination := 264, sources := [19] },
  { frame := 21, destination := 265, sources := [19] }, { frame := 22, destination := 266, sources := [20] },
  { frame := 22, destination := 267, sources := [20] }, { frame := 23, destination := 268, sources := [21] },
  { frame := 23, destination := 269, sources := [21] }, { frame := 24, destination := 270, sources := [22] },
  { frame := 24, destination := 271, sources := [22] }, { frame := 25, destination := 272, sources := [23] },
  { frame := 25, destination := 273, sources := [23] }, { frame := 26, destination := 274, sources := [24] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-78df6fcb58aadec5"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk5`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1649)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 26, destination := 275, sources := [24] }, { frame := 27, destination := 276, sources := [25] },
  { frame := 27, destination := 277, sources := [25] }, { frame := 28, destination := 278, sources := [26] },
  { frame := 28, destination := 279, sources := [26] }, { frame := 29, destination := 280, sources := [27] },
  { frame := 29, destination := 281, sources := [27] }, { frame := 30, destination := 282, sources := [28] },
  { frame := 30, destination := 283, sources := [28] }, { frame := 31, destination := 284, sources := [29] },
  { frame := 31, destination := 285, sources := [29] }, { frame := 32, destination := 286, sources := [30] },
  { frame := 32, destination := 287, sources := [30] }, { frame := 33, destination := 288, sources := [31] },
  { frame := 33, destination := 289, sources := [31] }, { frame := 34, destination := 290, sources := [32] },
  { frame := 34, destination := 291, sources := [32] }, { frame := 35, destination := 292, sources := [33] },
  { frame := 35, destination := 293, sources := [33] }, { frame := 36, destination := 294, sources := [34] },
  { frame := 36, destination := 295, sources := [34] }, { frame := 37, destination := 296, sources := [35] },
  { frame := 37, destination := 297, sources := [35] }, { frame := 38, destination := 298, sources := [36] },
  { frame := 38, destination := 299, sources := [36] }, { frame := 39, destination := 300, sources := [37] },
  { frame := 39, destination := 301, sources := [37] }, { frame := 40, destination := 302, sources := [38] },
  { frame := 40, destination := 303, sources := [38] }, { frame := 41, destination := 304, sources := [39] },
  { frame := 41, destination := 305, sources := [39] }, { frame := 42, destination := 306, sources := [40] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-b04ab019858f0384"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk6`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1682)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 42, destination := 307, sources := [40] }, { frame := 43, destination := 308, sources := [41] },
  { frame := 43, destination := 309, sources := [41] }, { frame := 44, destination := 310, sources := [42] },
  { frame := 44, destination := 311, sources := [42] }, { frame := 45, destination := 312, sources := [43] },
  { frame := 45, destination := 313, sources := [43] }, { frame := 46, destination := 314, sources := [44] },
  { frame := 46, destination := 315, sources := [44] }, { frame := 47, destination := 316, sources := [45] },
  { frame := 47, destination := 317, sources := [45] }, { frame := 48, destination := 318, sources := [46] },
  { frame := 48, destination := 319, sources := [46] }, { frame := 49, destination := 320, sources := [47] },
  { frame := 49, destination := 321, sources := [47] }, { frame := 50, destination := 322, sources := [48] },
  { frame := 50, destination := 323, sources := [48] }, { frame := 51, destination := 326, sources := [49] },
  { frame := 51, destination := 327, sources := [49] }, { frame := 52, destination := 330, sources := [50] },
  { frame := 52, destination := 331, sources := [50] }, { frame := 53, destination := 332, sources := [51] },
  { frame := 53, destination := 333, sources := [51] }, { frame := 54, destination := 336, sources := [52] },
  { frame := 54, destination := 337, sources := [52] }, { frame := 55, destination := 338, sources := [53] },
  { frame := 55, destination := 339, sources := [53] }, { frame := 56, destination := 340, sources := [54] },
  { frame := 56, destination := 341, sources := [54] }, { frame := 57, destination := 342, sources := [55] },
  { frame := 57, destination := 343, sources := [55] }, { frame := 58, destination := 344, sources := [56] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-58da97a0a4992d56"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk7`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1715)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 58, destination := 345, sources := [56] }, { frame := 59, destination := 346, sources := [57] },
  { frame := 59, destination := 347, sources := [57] }, { frame := 60, destination := 348, sources := [58] },
  { frame := 60, destination := 349, sources := [58] }, { frame := 61, destination := 350, sources := [59] },
  { frame := 61, destination := 351, sources := [59] }, { frame := 62, destination := 352, sources := [60] },
  { frame := 62, destination := 353, sources := [60] }, { frame := 63, destination := 356, sources := [61] },
  { frame := 63, destination := 357, sources := [61] }, { frame := 64, destination := 358, sources := [62] },
  { frame := 64, destination := 359, sources := [62] }, { frame := 65, destination := 360, sources := [63] },
  { frame := 65, destination := 361, sources := [63] }, { frame := 66, destination := 362, sources := [64] },
  { frame := 66, destination := 363, sources := [64] }, { frame := 67, destination := 364, sources := [65] },
  { frame := 67, destination := 365, sources := [65] }, { frame := 68, destination := 368, sources := [66] },
  { frame := 68, destination := 369, sources := [66] }, { frame := 69, destination := 370, sources := [67] },
  { frame := 69, destination := 371, sources := [67] }, { frame := 70, destination := 372, sources := [68] },
  { frame := 70, destination := 373, sources := [68] }, { frame := 71, destination := 374, sources := [69] },
  { frame := 71, destination := 375, sources := [69] }, { frame := 72, destination := 376, sources := [70] },
  { frame := 72, destination := 377, sources := [70] }, { frame := 73, destination := 378, sources := [71] },
  { frame := 73, destination := 379, sources := [71] }, { frame := 74, destination := 380, sources := [72] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-d2e9a6dc70c0180a"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk8`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1748)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 74, destination := 381, sources := [72] }, { frame := 75, destination := 382, sources := [73] },
  { frame := 75, destination := 383, sources := [73] }, { frame := 76, destination := 384, sources := [74] },
  { frame := 76, destination := 385, sources := [74] }, { frame := 77, destination := 386, sources := [75] },
  { frame := 77, destination := 387, sources := [75] }, { frame := 78, destination := 388, sources := [76] },
  { frame := 78, destination := 389, sources := [76] }, { frame := 79, destination := 390, sources := [77] },
  { frame := 79, destination := 391, sources := [77] }, { frame := 80, destination := 392, sources := [78] },
  { frame := 80, destination := 393, sources := [78] }, { frame := 81, destination := 394, sources := [79] },
  { frame := 81, destination := 395, sources := [79] }, { frame := 82, destination := 396, sources := [80] },
  { frame := 82, destination := 397, sources := [80] }, { frame := 83, destination := 398, sources := [81] },
  { frame := 83, destination := 399, sources := [81] }, { frame := 84, destination := 402, sources := [82] },
  { frame := 84, destination := 403, sources := [82] }, { frame := 85, destination := 404, sources := [83] },
  { frame := 85, destination := 405, sources := [83] }, { frame := 86, destination := 406, sources := [84] },
  { frame := 86, destination := 407, sources := [84] }, { frame := 87, destination := 408, sources := [85] },
  { frame := 87, destination := 409, sources := [85] }, { frame := 88, destination := 410, sources := [86] },
  { frame := 88, destination := 411, sources := [86] }, { frame := 89, destination := 412, sources := [87] },
  { frame := 89, destination := 413, sources := [87] }, { frame := 90, destination := 414, sources := [88] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-294cf70c2cf864f1"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk9`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1781)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 90, destination := 415, sources := [88] }, { frame := 91, destination := 416, sources := [89] },
  { frame := 91, destination := 417, sources := [89] }, { frame := 92, destination := 418, sources := [90] },
  { frame := 92, destination := 419, sources := [90] }, { frame := 93, destination := 420, sources := [91] },
  { frame := 93, destination := 421, sources := [91] }, { frame := 94, destination := 422, sources := [92] },
  { frame := 94, destination := 423, sources := [92] }, { frame := 95, destination := 424, sources := [93] },
  { frame := 95, destination := 425, sources := [93] }, { frame := 96, destination := 426, sources := [94] },
  { frame := 96, destination := 427, sources := [94] }, { frame := 97, destination := 428, sources := [95] },
  { frame := 97, destination := 429, sources := [95] }, { frame := 98, destination := 430, sources := [96] },
  { frame := 98, destination := 431, sources := [96] }, { frame := 99, destination := 432, sources := [97] },
  { frame := 99, destination := 433, sources := [97] }, { frame := 100, destination := 434, sources := [98] },
  { frame := 100, destination := 435, sources := [98] }, { frame := 101, destination := 436, sources := [99] },
  { frame := 101, destination := 437, sources := [99] }, { frame := 102, destination := 438, sources := [100] },
  { frame := 102, destination := 439, sources := [100] }, { frame := 103, destination := 440, sources := [101] },
  { frame := 103, destination := 441, sources := [101] }, { frame := 104, destination := 442, sources := [102] },
  { frame := 104, destination := 443, sources := [102] }, { frame := 105, destination := 446, sources := [103] },
  { frame := 105, destination := 447, sources := [103] }, { frame := 106, destination := 448, sources := [104] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-874dbac41705c56a"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk10`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1814)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 106, destination := 449, sources := [104] }, { frame := 107, destination := 450, sources := [105] },
  { frame := 107, destination := 451, sources := [105] }, { frame := 108, destination := 452, sources := [106] },
  { frame := 108, destination := 453, sources := [106] }, { frame := 109, destination := 454, sources := [107] },
  { frame := 109, destination := 455, sources := [107] }, { frame := 110, destination := 456, sources := [108] },
  { frame := 110, destination := 457, sources := [108] }, { frame := 111, destination := 458, sources := [109] },
  { frame := 111, destination := 459, sources := [109] }, { frame := 112, destination := 460, sources := [110] },
  { frame := 112, destination := 461, sources := [110] }, { frame := 49, destination := 462, sources := [47] },
  { frame := 54, destination := 463, sources := [52] }, { frame := 56, destination := 464, sources := [54] },
  { frame := 2, destination := 465, sources := [0] }, { frame := 21, destination := 466, sources := [19] },
  { frame := 29, destination := 467, sources := [27] }, { frame := 40, destination := 468, sources := [38] },
  { frame := 52, destination := 469, sources := [50] }, { frame := 79, destination := 470, sources := [77] },
  { frame := 94, destination := 471, sources := [92] }, { frame := 8, destination := 472, sources := [6] },
  { frame := 13, destination := 473, sources := [11] }, { frame := 58, destination := 474, sources := [56] },
  { frame := 59, destination := 475, sources := [57] }, { frame := 69, destination := 476, sources := [67] },
  { frame := 71, destination := 477, sources := [69] }, { frame := 70, destination := 478, sources := [68] },
  { frame := 45, destination := 479, sources := [43] }, { frame := 19, destination := 480, sources := [17] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-105a4c5e4a1c6a8f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk11`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1847)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 113, destination := 232, sources := [6] }, { frame := 113, destination := 481, sources := [232] },
  { frame := 114, destination := 240, sources := [5] }, { frame := 114, destination := 482, sources := [240] },
  { frame := 7, destination := 242, sources := [233] }, { frame := 7, destination := 483, sources := [242] },
  { frame := 115, destination := 234, sources := [241] }, { frame := 115, destination := 484, sources := [234] },
  { frame := 8, destination := 485, sources := [235] }, { frame := 11, destination := 243, sources := [9] },
  { frame := 11, destination := 486, sources := [243] }, { frame := 48, destination := 324, sources := [46] },
  { frame := 48, destination := 487, sources := [324] }, { frame := 116, destination := 318, sources := [340] },
  { frame := 116, destination := 488, sources := [318] }, { frame := 117, destination := 344, sources := [319] },
  { frame := 117, destination := 489, sources := [344] }, { frame := 56, destination := 325, sources := [54] },
  { frame := 56, destination := 490, sources := [325] }, { frame := 58, destination := 491, sources := [345] },
  { frame := 118, destination := 341, sources := [56] }, { frame := 118, destination := 492, sources := [341] },
  { frame := 119, destination := 320, sources := [48] }, { frame := 119, destination := 493, sources := [320] },
  { frame := 120, destination := 321, sources := [52] }, { frame := 120, destination := 494, sources := [321] },
  { frame := 121, destination := 348, sources := [47] }, { frame := 121, destination := 495, sources := [348] },
  { frame := 122, destination := 336, sources := [322] }, { frame := 122, destination := 496, sources := [336] },
  { frame := 123, destination := 323, sources := [349] }, { frame := 123, destination := 497, sources := [323] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-09f95ff8239b0840"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk12`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1880)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 124, destination := 337, sources := [58] }, { frame := 124, destination := 498, sources := [337] },
  { frame := 125, destination := 222, sources := [228] }, { frame := 125, destination := 499, sources := [222] },
  { frame := 126, destination := 223, sources := [11] }, { frame := 126, destination := 500, sources := [223] },
  { frame := 2, destination := 252, sources := [0] }, { frame := 2, destination := 501, sources := [252] },
  { frame := 127, destination := 246, sources := [3] }, { frame := 127, destination := 502, sources := [246] },
  { frame := 5, destination := 253, sources := [229] }, { frame := 5, destination := 503, sources := [253] },
  { frame := 13, destination := 504, sources := [247] }, { frame := 64, destination := 354, sources := [358] },
  { frame := 64, destination := 505, sources := [354] }, { frame := 71, destination := 506, sources := [374] },
  { frame := 74, destination := 355, sources := [72] }, { frame := 74, destination := 507, sources := [355] },
  { frame := 128, destination := 359, sources := [69] }, { frame := 128, destination := 508, sources := [359] },
  { frame := 129, destination := 380, sources := [62] }, { frame := 129, destination := 509, sources := [380] },
  { frame := 130, destination := 375, sources := [381] }, { frame := 130, destination := 510, sources := [375] },
  { frame := 131, destination := 356, sources := [63] }, { frame := 131, destination := 511, sources := [356] },
  { frame := 63, destination := 366, sources := [61] }, { frame := 63, destination := 512, sources := [366] },
  { frame := 132, destination := 372, sources := [357] }, { frame := 132, destination := 513, sources := [372] },
  { frame := 65, destination := 367, sources := [360] }, { frame := 65, destination := 514, sources := [367] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-8e5826d029b87bfe"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk13`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1913)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 133, destination := 361, sources := [68] }, { frame := 133, destination := 515, sources := [361] },
  { frame := 70, destination := 516, sources := [373] }, { frame := 134, destination := 272, sources := [15] },
  { frame := 134, destination := 517, sources := [272] }, { frame := 135, destination := 256, sources := [91] },
  { frame := 135, destination := 518, sources := [256] }, { frame := 136, destination := 430, sources := [257] },
  { frame := 136, destination := 519, sources := [430] }, { frame := 137, destination := 420, sources := [23] },
  { frame := 137, destination := 520, sources := [420] }, { frame := 138, destination := 431, sources := [273] },
  { frame := 138, destination := 521, sources := [431] }, { frame := 139, destination := 421, sources := [96] },
  { frame := 139, destination := 522, sources := [421] }, { frame := 140, destination := 308, sources := [30] },
  { frame := 140, destination := 523, sources := [308] }, { frame := 141, destination := 286, sources := [386] },
  { frame := 141, destination := 524, sources := [286] }, { frame := 142, destination := 402, sources := [287] },
  { frame := 142, destination := 525, sources := [402] }, { frame := 143, destination := 387, sources := [41] },
  { frame := 143, destination := 526, sources := [387] }, { frame := 144, destination := 309, sources := [82] },
  { frame := 144, destination := 527, sources := [309] }, { frame := 145, destination := 403, sources := [75] },
  { frame := 145, destination := 528, sources := [403] }, { frame := 146, destination := 338, sources := [49] },
  { frame := 146, destination := 529, sources := [338] }, { frame := 147, destination := 326, sources := [59] },
  { frame := 147, destination := 530, sources := [326] }, { frame := 148, destination := 376, sources := [327] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-175848d5e3e72784"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk14`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1946)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 148, destination := 531, sources := [376] }, { frame := 149, destination := 350, sources := [53] },
  { frame := 149, destination := 532, sources := [350] }, { frame := 150, destination := 339, sources := [70] },
  { frame := 150, destination := 533, sources := [339] }, { frame := 151, destination := 351, sources := [377] },
  { frame := 151, destination := 534, sources := [351] }, { frame := 152, destination := 280, sources := [19] },
  { frame := 152, destination := 535, sources := [280] }, { frame := 153, destination := 264, sources := [416] },
  { frame := 153, destination := 536, sources := [264] }, { frame := 154, destination := 265, sources := [97] },
  { frame := 154, destination := 537, sources := [265] }, { frame := 155, destination := 281, sources := [89] },
  { frame := 155, destination := 538, sources := [281] }, { frame := 156, destination := 432, sources := [27] },
  { frame := 156, destination := 539, sources := [432] }, { frame := 157, destination := 417, sources := [433] },
  { frame := 157, destination := 540, sources := [417] }, { frame := 158, destination := 296, sources := [43] },
  { frame := 158, destination := 541, sources := [296] }, { frame := 159, destination := 384, sources := [35] },
  { frame := 159, destination := 542, sources := [384] }, { frame := 37, destination := 400, sources := [297] },
  { frame := 37, destination := 543, sources := [400] }, { frame := 160, destination := 312, sources := [74] },
  { frame := 160, destination := 544, sources := [312] }, { frame := 45, destination := 545, sources := [313] },
  { frame := 76, destination := 401, sources := [385] }, { frame := 76, destination := 546, sources := [401] },
  { frame := 59, destination := 547, sources := [346] }, { frame := 67, destination := 328, sources := [65] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-67fd06da2416b50b"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk15`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L1979)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 67, destination := 548, sources := [328] }, { frame := 68, destination := 329, sources := [66] },
  { frame := 68, destination := 549, sources := [329] }, { frame := 161, destination := 364, sources := [57] },
  { frame := 161, destination := 550, sources := [364] }, { frame := 162, destination := 347, sources := [368] },
  { frame := 162, destination := 551, sources := [347] }, { frame := 163, destination := 369, sources := [365] },
  { frame := 163, destination := 552, sources := [369] }, { frame := 164, destination := 268, sources := [278] },
  { frame := 164, destination := 553, sources := [268] }, { frame := 165, destination := 426, sources := [21] },
  { frame := 165, destination := 554, sources := [426] }, { frame := 166, destination := 269, sources := [102] },
  { frame := 166, destination := 555, sources := [269] }, { frame := 167, destination := 279, sources := [94] },
  { frame := 167, destination := 556, sources := [279] }, { frame := 168, destination := 442, sources := [26] },
  { frame := 168, destination := 557, sources := [442] }, { frame := 169, destination := 427, sources := [443] },
  { frame := 169, destination := 558, sources := [427] }, { frame := 170, destination := 298, sources := [44] },
  { frame := 170, destination := 559, sources := [298] }, { frame := 171, destination := 299, sources := [396] },
  { frame := 171, destination := 560, sources := [299] }, { frame := 172, destination := 406, sources := [36] },
  { frame := 172, destination := 561, sources := [406] }, { frame := 173, destination := 314, sources := [80] },
  { frame := 173, destination := 562, sources := [314] }, { frame := 174, destination := 315, sources := [84] },
  { frame := 174, destination := 563, sources := [315] }, { frame := 175, destination := 397, sources := [407] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-f991c791abb18e4d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk16`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2012)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 175, destination := 564, sources := [397] }, { frame := 176, destination := 342, sources := [332] },
  { frame := 176, destination := 565, sources := [342] }, { frame := 177, destination := 362, sources := [333] },
  { frame := 177, destination := 566, sources := [362] }, { frame := 178, destination := 378, sources := [51] },
  { frame := 178, destination := 567, sources := [378] }, { frame := 179, destination := 363, sources := [55] },
  { frame := 179, destination := 568, sources := [363] }, { frame := 180, destination := 343, sources := [71] },
  { frame := 180, destination := 569, sources := [343] }, { frame := 181, destination := 379, sources := [64] },
  { frame := 181, destination := 570, sources := [379] }, { frame := 182, destination := 260, sources := [22] },
  { frame := 182, destination := 571, sources := [260] }, { frame := 183, destination := 422, sources := [17] },
  { frame := 183, destination := 572, sources := [422] }, { frame := 19, destination := 573, sources := [261] },
  { frame := 184, destination := 270, sources := [92] }, { frame := 184, destination := 574, sources := [270] },
  { frame := 24, destination := 445, sources := [271] }, { frame := 24, destination := 575, sources := [445] },
  { frame := 94, destination := 576, sources := [423] }, { frame := 185, destination := 302, sources := [33] },
  { frame := 185, destination := 577, sources := [302] }, { frame := 186, destination := 292, sources := [77] },
  { frame := 186, destination := 578, sources := [292] }, { frame := 187, destination := 412, sources := [293] },
  { frame := 187, destination := 579, sources := [412] }, { frame := 188, destination := 390, sources := [38] },
  { frame := 188, destination := 580, sources := [390] }, { frame := 189, destination := 303, sources := [87] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-395573e15e2509e5"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk17`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2045)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 189, destination := 581, sources := [303] }, { frame := 190, destination := 391, sources := [413] },
  { frame := 190, destination := 582, sources := [391] }, { frame := 52, destination := 334, sources := [50] },
  { frame := 52, destination := 583, sources := [334] }, { frame := 191, destination := 330, sources := [352] },
  { frame := 191, destination := 584, sources := [330] }, { frame := 192, destination := 331, sources := [67] },
  { frame := 192, destination := 585, sources := [331] }, { frame := 62, destination := 335, sources := [60] },
  { frame := 62, destination := 586, sources := [335] }, { frame := 69, destination := 587, sources := [370] },
  { frame := 193, destination := 353, sources := [371] }, { frame := 193, destination := 588, sources := [353] },
  { frame := 194, destination := 244, sources := [13] }, { frame := 194, destination := 589, sources := [244] },
  { frame := 195, destination := 448, sources := [10] }, { frame := 195, destination := 590, sources := [448] },
  { frame := 196, destination := 454, sources := [245] }, { frame := 196, destination := 591, sources := [454] },
  { frame := 197, destination := 449, sources := [250] }, { frame := 197, destination := 592, sources := [449] },
  { frame := 198, destination := 251, sources := [107] }, { frame := 198, destination := 593, sources := [251] },
  { frame := 199, destination := 455, sources := [104] }, { frame := 199, destination := 594, sources := [455] },
  { frame := 200, destination := 294, sources := [290] }, { frame := 200, destination := 595, sources := [294] },
  { frame := 201, destination := 291, sources := [83] }, { frame := 201, destination := 596, sources := [291] },
  { frame := 202, destination := 408, sources := [32] }, { frame := 202, destination := 597, sources := [408] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-48d4d45a349b3e2e"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk18`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2078)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 203, destination := 404, sources := [295] }, { frame := 203, destination := 598, sources := [404] },
  { frame := 204, destination := 409, sources := [34] }, { frame := 204, destination := 599, sources := [409] },
  { frame := 205, destination := 405, sources := [85] }, { frame := 205, destination := 600, sources := [405] },
  { frame := 206, destination := 304, sources := [42] }, { frame := 206, destination := 601, sources := [304] },
  { frame := 207, destination := 388, sources := [39] }, { frame := 207, destination := 602, sources := [388] },
  { frame := 208, destination := 305, sources := [394] }, { frame := 208, destination := 603, sources := [305] },
  { frame := 209, destination := 310, sources := [76] }, { frame := 209, destination := 604, sources := [310] },
  { frame := 210, destination := 395, sources := [311] }, { frame := 210, destination := 605, sources := [395] },
  { frame := 211, destination := 389, sources := [79] }, { frame := 211, destination := 606, sources := [389] },
  { frame := 212, destination := 236, sources := [1] }, { frame := 212, destination := 607, sources := [236] },
  { frame := 213, destination := 224, sources := [452] }, { frame := 213, destination := 608, sources := [224] },
  { frame := 214, destination := 225, sources := [108] }, { frame := 214, destination := 609, sources := [225] },
  { frame := 215, destination := 453, sources := [7] }, { frame := 215, destination := 610, sources := [453] },
  { frame := 216, destination := 456, sources := [237] }, { frame := 216, destination := 611, sources := [456] },
  { frame := 217, destination := 457, sources := [106] }, { frame := 217, destination := 612, sources := [457] },
  { frame := 218, destination := 274, sources := [284] }, { frame := 218, destination := 613, sources := [274] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-479a251b5320a1e1"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk19`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2111)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 219, destination := 275, sources := [99] }, { frame := 219, destination := 614, sources := [275] },
  { frame := 220, destination := 440, sources := [24] }, { frame := 220, destination := 615, sources := [440] },
  { frame := 221, destination := 285, sources := [436] }, { frame := 221, destination := 616, sources := [285] },
  { frame := 222, destination := 441, sources := [29] }, { frame := 222, destination := 617, sources := [441] },
  { frame := 223, destination := 437, sources := [101] }, { frame := 223, destination := 618, sources := [437] },
  { frame := 224, destination := 276, sources := [28] }, { frame := 224, destination := 619, sources := [276] },
  { frame := 225, destination := 434, sources := [277] }, { frame := 225, destination := 620, sources := [434] },
  { frame := 226, destination := 438, sources := [25] }, { frame := 226, destination := 621, sources := [438] },
  { frame := 227, destination := 282, sources := [435] }, { frame := 227, destination := 622, sources := [282] },
  { frame := 228, destination := 283, sources := [100] }, { frame := 228, destination := 623, sources := [283] },
  { frame := 229, destination := 439, sources := [98] }, { frame := 229, destination := 624, sources := [439] },
  { frame := 230, destination := 226, sources := [4] }, { frame := 230, destination := 625, sources := [226] },
  { frame := 231, destination := 446, sources := [2] }, { frame := 231, destination := 626, sources := [446] },
  { frame := 232, destination := 458, sources := [227] }, { frame := 232, destination := 627, sources := [458] },
  { frame := 233, destination := 230, sources := [103] }, { frame := 233, destination := 628, sources := [230] },
  { frame := 234, destination := 231, sources := [459] }, { frame := 234, destination := 629, sources := [231] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-d9f54cd7156076cb"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk20`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2144)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 235, destination := 447, sources := [109] }, { frame := 235, destination := 630, sources := [447] },
  { frame := 236, destination := 266, sources := [14] }, { frame := 236, destination := 631, sources := [266] },
  { frame := 237, destination := 418, sources := [254] }, { frame := 237, destination := 632, sources := [418] },
  { frame := 238, destination := 255, sources := [428] }, { frame := 238, destination := 633, sources := [255] },
  { frame := 239, destination := 267, sources := [90] }, { frame := 239, destination := 634, sources := [267] },
  { frame := 240, destination := 429, sources := [20] }, { frame := 240, destination := 635, sources := [429] },
  { frame := 241, destination := 419, sources := [95] }, { frame := 241, destination := 636, sources := [419] },
  { frame := 242, destination := 258, sources := [18] }, { frame := 242, destination := 637, sources := [258] },
  { frame := 243, destination := 414, sources := [16] }, { frame := 243, destination := 638, sources := [414] },
  { frame := 244, destination := 424, sources := [259] }, { frame := 244, destination := 639, sources := [424] },
  { frame := 245, destination := 262, sources := [415] }, { frame := 245, destination := 640, sources := [262] },
  { frame := 246, destination := 263, sources := [93] }, { frame := 246, destination := 641, sources := [263] },
  { frame := 247, destination := 425, sources := [88] }, { frame := 247, destination := 642, sources := [425] },
  { frame := 248, destination := 238, sources := [248] }, { frame := 248, destination := 643, sources := [238] },
  { frame := 249, destination := 450, sources := [8] }, { frame := 249, destination := 644, sources := [450] },
  { frame := 250, destination := 239, sources := [110] }, { frame := 250, destination := 645, sources := [239] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-faec46b539e0ac5f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk21`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2177)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 251, destination := 249, sources := [105] }, { frame := 251, destination := 646, sources := [249] },
  { frame := 252, destination := 460, sources := [12] }, { frame := 252, destination := 647, sources := [460] },
  { frame := 253, destination := 461, sources := [451] }, { frame := 253, destination := 648, sources := [461] },
  { frame := 254, destination := 288, sources := [37] }, { frame := 254, destination := 649, sources := [288] },
  { frame := 255, destination := 289, sources := [398] }, { frame := 255, destination := 650, sources := [289] },
  { frame := 256, destination := 410, sources := [31] }, { frame := 256, destination := 651, sources := [410] },
  { frame := 257, destination := 300, sources := [81] }, { frame := 257, destination := 652, sources := [300] },
  { frame := 258, destination := 301, sources := [411] }, { frame := 258, destination := 653, sources := [301] },
  { frame := 259, destination := 399, sources := [86] }, { frame := 259, destination := 654, sources := [399] },
  { frame := 260, destination := 316, sources := [40] }, { frame := 260, destination := 655, sources := [316] },
  { frame := 261, destination := 306, sources := [382] }, { frame := 261, destination := 656, sources := [306] },
  { frame := 262, destination := 392, sources := [307] }, { frame := 262, destination := 657, sources := [392] },
  { frame := 263, destination := 383, sources := [45] }, { frame := 263, destination := 658, sources := [383] },
  { frame := 264, destination := 317, sources := [78] }, { frame := 264, destination := 659, sources := [317] },
  { frame := 265, destination := 393, sources := [73] }, { frame := 265, destination := 660, sources := [393] },
  { frame := 266, destination := 243, sources := [244] }, { frame := 266, destination := 243, sources := [236] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-ce16eaa5e0ede74a"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk22`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2210)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 266, destination := 243, sources := [226] }, { frame := 266, destination := 243, sources := [238] },
  { frame := 266, destination := 247, sources := [244] }, { frame := 266, destination := 247, sources := [236] },
  { frame := 266, destination := 247, sources := [226] }, { frame := 266, destination := 247, sources := [238] },
  { frame := 266, destination := 244, sources := [236] }, { frame := 266, destination := 244, sources := [226] },
  { frame := 266, destination := 236, sources := [238] }, { frame := 266, destination := 226, sources := [238] },
  { frame := 266, destination := 238, sources := [243] }, { frame := 266, destination := 238, sources := [247] },
  { frame := 266, destination := 238, sources := [236] }, { frame := 266, destination := 238, sources := [226] },
  { frame := 266, destination := 226, sources := [243] }, { frame := 266, destination := 226, sources := [247] },
  { frame := 266, destination := 226, sources := [244] }, { frame := 266, destination := 236, sources := [243] },
  { frame := 266, destination := 236, sources := [247] }, { frame := 266, destination := 236, sources := [244] },
  { frame := 266, destination := 244, sources := [243] }, { frame := 266, destination := 244, sources := [247] },
  { frame := 267, destination := 486, sources := [351] }, { frame := 267, destination := 486, sources := [369] },
  { frame := 267, destination := 486, sources := [379] }, { frame := 267, destination := 486, sources := [353] },
  { frame := 267, destination := 222, sources := [351] }, { frame := 267, destination := 222, sources := [379] },
  { frame := 267, destination := 351, sources := [369] }, { frame := 267, destination := 351, sources := [379] },
  { frame := 267, destination := 351, sources := [353] }, { frame := 267, destination := 379, sources := [353] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-8f45a3bf2d30eb9d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk23`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2243)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 267, destination := 353, sources := [486] }, { frame := 267, destination := 353, sources := [222] },
  { frame := 267, destination := 353, sources := [351] }, { frame := 267, destination := 379, sources := [486] },
  { frame := 267, destination := 379, sources := [222] }, { frame := 267, destination := 379, sources := [351] },
  { frame := 267, destination := 379, sources := [369] }, { frame := 267, destination := 369, sources := [486] },
  { frame := 267, destination := 369, sources := [222] }, { frame := 267, destination := 369, sources := [351] },
  { frame := 267, destination := 222, sources := [486] }, { frame := 268, destination := 235, sources := [280] },
  { frame := 268, destination := 235, sources := [260] }, { frame := 268, destination := 235, sources := [274] },
  { frame := 268, destination := 235, sources := [258] }, { frame := 268, destination := 223, sources := [280] },
  { frame := 268, destination := 223, sources := [260] }, { frame := 268, destination := 223, sources := [274] },
  { frame := 268, destination := 223, sources := [258] }, { frame := 268, destination := 280, sources := [274] },
  { frame := 268, destination := 280, sources := [258] }, { frame := 268, destination := 260, sources := [274] },
  { frame := 268, destination := 260, sources := [258] }, { frame := 268, destination := 274, sources := [258] },
  { frame := 268, destination := 258, sources := [235] }, { frame := 268, destination := 258, sources := [223] },
  { frame := 268, destination := 258, sources := [280] }, { frame := 268, destination := 258, sources := [260] },
  { frame := 268, destination := 258, sources := [274] }, { frame := 268, destination := 274, sources := [235] },
  { frame := 268, destination := 274, sources := [223] }, { frame := 268, destination := 260, sources := [235] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-dd45cf550dc9f84b"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk24`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2276)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 268, destination := 260, sources := [223] }, { frame := 268, destination := 260, sources := [280] },
  { frame := 268, destination := 280, sources := [235] }, { frame := 268, destination := 280, sources := [223] },
  { frame := 269, destination := 485, sources := [403] }, { frame := 269, destination := 485, sources := [397] },
  { frame := 269, destination := 485, sources := [389] }, { frame := 269, destination := 485, sources := [399] },
  { frame := 269, destination := 253, sources := [403] }, { frame := 269, destination := 403, sources := [397] },
  { frame := 269, destination := 403, sources := [389] }, { frame := 269, destination := 403, sources := [399] },
  { frame := 269, destination := 389, sources := [399] }, { frame := 269, destination := 399, sources := [485] },
  { frame := 269, destination := 399, sources := [253] }, { frame := 269, destination := 399, sources := [403] },
  { frame := 269, destination := 399, sources := [397] }, { frame := 269, destination := 389, sources := [485] },
  { frame := 269, destination := 389, sources := [253] }, { frame := 269, destination := 389, sources := [403] },
  { frame := 269, destination := 397, sources := [485] }, { frame := 269, destination := 397, sources := [253] },
  { frame := 269, destination := 397, sources := [403] }, { frame := 269, destination := 253, sources := [485] },
  { frame := 270, destination := 234, sources := [272] }, { frame := 270, destination := 234, sources := [268] },
  { frame := 270, destination := 234, sources := [276] }, { frame := 270, destination := 234, sources := [266] },
  { frame := 270, destination := 252, sources := [272] }, { frame := 270, destination := 272, sources := [268] },
  { frame := 270, destination := 272, sources := [276] }, { frame := 270, destination := 272, sources := [266] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-9738dfffed20f9de"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk25`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2309)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 270, destination := 266, sources := [234] }, { frame := 270, destination := 266, sources := [252] },
  { frame := 270, destination := 266, sources := [272] }, { frame := 270, destination := 266, sources := [268] },
  { frame := 270, destination := 276, sources := [234] }, { frame := 270, destination := 276, sources := [252] },
  { frame := 270, destination := 276, sources := [272] }, { frame := 270, destination := 276, sources := [268] },
  { frame := 270, destination := 268, sources := [234] }, { frame := 270, destination := 268, sources := [252] },
  { frame := 270, destination := 252, sources := [234] }, { frame := 271, destination := 484, sources := [401] },
  { frame := 271, destination := 484, sources := [391] }, { frame := 271, destination := 484, sources := [405] },
  { frame := 271, destination := 484, sources := [393] }, { frame := 271, destination := 246, sources := [401] },
  { frame := 271, destination := 246, sources := [391] }, { frame := 271, destination := 246, sources := [405] },
  { frame := 271, destination := 246, sources := [393] }, { frame := 271, destination := 401, sources := [405] },
  { frame := 271, destination := 401, sources := [393] }, { frame := 271, destination := 391, sources := [405] },
  { frame := 271, destination := 391, sources := [393] }, { frame := 271, destination := 405, sources := [393] },
  { frame := 271, destination := 393, sources := [484] }, { frame := 271, destination := 393, sources := [246] },
  { frame := 271, destination := 393, sources := [401] }, { frame := 271, destination := 393, sources := [391] },
  { frame := 271, destination := 393, sources := [405] }, { frame := 271, destination := 405, sources := [484] },
  { frame := 271, destination := 405, sources := [246] }, { frame := 271, destination := 391, sources := [484] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-263c5b213d0425d4"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk26`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2342)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 271, destination := 391, sources := [246] }, { frame := 271, destination := 391, sources := [401] },
  { frame := 271, destination := 401, sources := [484] }, { frame := 271, destination := 401, sources := [246] },
  { frame := 272, destination := 242, sources := [296] }, { frame := 272, destination := 242, sources := [302] },
  { frame := 272, destination := 242, sources := [294] }, { frame := 272, destination := 242, sources := [316] },
  { frame := 272, destination := 501, sources := [296] }, { frame := 272, destination := 501, sources := [302] },
  { frame := 272, destination := 501, sources := [294] }, { frame := 272, destination := 501, sources := [316] },
  { frame := 272, destination := 296, sources := [294] }, { frame := 272, destination := 296, sources := [316] },
  { frame := 272, destination := 302, sources := [294] }, { frame := 272, destination := 294, sources := [316] },
  { frame := 272, destination := 316, sources := [242] }, { frame := 272, destination := 316, sources := [501] },
  { frame := 272, destination := 316, sources := [296] }, { frame := 272, destination := 316, sources := [302] },
  { frame := 272, destination := 294, sources := [242] }, { frame := 272, destination := 294, sources := [501] },
  { frame := 272, destination := 302, sources := [242] }, { frame := 272, destination := 302, sources := [501] },
  { frame := 272, destination := 302, sources := [296] }, { frame := 272, destination := 296, sources := [242] },
  { frame := 272, destination := 296, sources := [501] }, { frame := 273, destination := 483, sources := [421] },
  { frame := 273, destination := 483, sources := [427] }, { frame := 273, destination := 483, sources := [439] },
  { frame := 273, destination := 483, sources := [419] }, { frame := 273, destination := 502, sources := [421] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-187709613b47ab18"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk27`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2375)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 273, destination := 421, sources := [427] }, { frame := 273, destination := 421, sources := [439] },
  { frame := 273, destination := 421, sources := [419] }, { frame := 273, destination := 419, sources := [483] },
  { frame := 273, destination := 419, sources := [502] }, { frame := 273, destination := 419, sources := [421] },
  { frame := 273, destination := 419, sources := [427] }, { frame := 273, destination := 439, sources := [483] },
  { frame := 273, destination := 439, sources := [502] }, { frame := 273, destination := 439, sources := [421] },
  { frame := 273, destination := 439, sources := [427] }, { frame := 273, destination := 427, sources := [483] },
  { frame := 273, destination := 427, sources := [502] }, { frame := 273, destination := 502, sources := [483] },
  { frame := 274, destination := 240, sources := [308] }, { frame := 274, destination := 240, sources := [298] },
  { frame := 274, destination := 240, sources := [304] }, { frame := 274, destination := 240, sources := [288] },
  { frame := 274, destination := 500, sources := [308] }, { frame := 274, destination := 308, sources := [298] },
  { frame := 274, destination := 308, sources := [304] }, { frame := 274, destination := 308, sources := [288] },
  { frame := 274, destination := 288, sources := [240] }, { frame := 274, destination := 288, sources := [500] },
  { frame := 274, destination := 288, sources := [308] }, { frame := 274, destination := 288, sources := [298] },
  { frame := 274, destination := 304, sources := [240] }, { frame := 274, destination := 304, sources := [500] },
  { frame := 274, destination := 304, sources := [308] }, { frame := 274, destination := 304, sources := [298] },
  { frame := 274, destination := 298, sources := [240] }, { frame := 274, destination := 298, sources := [500] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0a472cda28b58404"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk28`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2408)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 274, destination := 500, sources := [240] }, { frame := 275, destination := 482, sources := [503] },
  { frame := 275, destination := 482, sources := [417] }, { frame := 275, destination := 482, sources := [437] },
  { frame := 275, destination := 482, sources := [425] }, { frame := 275, destination := 503, sources := [417] },
  { frame := 275, destination := 503, sources := [423] }, { frame := 275, destination := 503, sources := [437] },
  { frame := 275, destination := 503, sources := [425] }, { frame := 275, destination := 417, sources := [423] },
  { frame := 275, destination := 417, sources := [437] }, { frame := 275, destination := 417, sources := [425] },
  { frame := 275, destination := 423, sources := [437] }, { frame := 275, destination := 437, sources := [425] },
  { frame := 275, destination := 425, sources := [482] }, { frame := 275, destination := 425, sources := [423] },
  { frame := 275, destination := 437, sources := [482] }, { frame := 275, destination := 437, sources := [417] },
  { frame := 275, destination := 423, sources := [482] }, { frame := 276, destination := 232, sources := [504] },
  { frame := 276, destination := 232, sources := [338] }, { frame := 276, destination := 232, sources := [346] },
  { frame := 276, destination := 232, sources := [334] }, { frame := 276, destination := 504, sources := [338] },
  { frame := 276, destination := 504, sources := [346] }, { frame := 276, destination := 504, sources := [342] },
  { frame := 276, destination := 504, sources := [334] }, { frame := 276, destination := 338, sources := [346] },
  { frame := 276, destination := 338, sources := [342] }, { frame := 276, destination := 338, sources := [334] },
  { frame := 276, destination := 346, sources := [342] }, { frame := 276, destination := 346, sources := [334] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-b528b0d2854eb091"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk29`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2441)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 276, destination := 342, sources := [334] }, { frame := 276, destination := 334, sources := [232] },
  { frame := 276, destination := 334, sources := [346] }, { frame := 276, destination := 342, sources := [232] },
  { frame := 276, destination := 346, sources := [232] }, { frame := 276, destination := 346, sources := [338] },
  { frame := 277, destination := 481, sources := [499] }, { frame := 277, destination := 481, sources := [455] },
  { frame := 277, destination := 481, sources := [457] }, { frame := 277, destination := 481, sources := [447] },
  { frame := 277, destination := 499, sources := [455] }, { frame := 277, destination := 499, sources := [457] },
  { frame := 277, destination := 499, sources := [447] }, { frame := 277, destination := 499, sources := [461] },
  { frame := 277, destination := 455, sources := [457] }, { frame := 277, destination := 455, sources := [447] },
  { frame := 277, destination := 455, sources := [461] }, { frame := 277, destination := 457, sources := [447] },
  { frame := 277, destination := 457, sources := [461] }, { frame := 277, destination := 447, sources := [461] },
  { frame := 277, destination := 461, sources := [481] }, { frame := 277, destination := 461, sources := [455] },
  { frame := 277, destination := 461, sources := [457] }, { frame := 277, destination := 447, sources := [481] },
  { frame := 277, destination := 457, sources := [481] }, { frame := 278, destination := 341, sources := [339] },
  { frame := 278, destination := 341, sources := [343] }, { frame := 278, destination := 341, sources := [456] },
  { frame := 278, destination := 341, sources := [231] }, { frame := 278, destination := 375, sources := [339] },
  { frame := 278, destination := 375, sources := [343] }, { frame := 278, destination := 375, sources := [456] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-62dfa45edb796267"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk30`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2474)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 278, destination := 375, sources := [231] }, { frame := 278, destination := 339, sources := [343] },
  { frame := 278, destination := 339, sources := [231] }, { frame := 278, destination := 343, sources := [456] },
  { frame := 278, destination := 343, sources := [231] }, { frame := 278, destination := 456, sources := [231] },
  { frame := 278, destination := 231, sources := [341] }, { frame := 278, destination := 231, sources := [375] },
  { frame := 278, destination := 231, sources := [339] }, { frame := 278, destination := 456, sources := [341] },
  { frame := 278, destination := 456, sources := [375] }, { frame := 278, destination := 343, sources := [341] },
  { frame := 278, destination := 343, sources := [375] }, { frame := 278, destination := 339, sources := [341] },
  { frame := 278, destination := 339, sources := [375] }, { frame := 279, destination := 492, sources := [354] },
  { frame := 279, destination := 492, sources := [329] }, { frame := 279, destination := 492, sources := [449] },
  { frame := 279, destination := 492, sources := [249] }, { frame := 279, destination := 354, sources := [329] },
  { frame := 279, destination := 354, sources := [331] }, { frame := 279, destination := 354, sources := [449] },
  { frame := 279, destination := 354, sources := [249] }, { frame := 279, destination := 329, sources := [331] },
  { frame := 279, destination := 329, sources := [449] }, { frame := 279, destination := 329, sources := [249] },
  { frame := 279, destination := 331, sources := [449] }, { frame := 279, destination := 331, sources := [249] },
  { frame := 279, destination := 249, sources := [492] }, { frame := 279, destination := 249, sources := [331] },
  { frame := 279, destination := 449, sources := [492] }, { frame := 279, destination := 449, sources := [331] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-f5e2440dee830190"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk31`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2507)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 279, destination := 331, sources := [492] }, { frame := 279, destination := 331, sources := [329] },
  { frame := 280, destination := 345, sources := [309] }, { frame := 280, destination := 345, sources := [281] },
  { frame := 280, destination := 345, sources := [299] }, { frame := 280, destination := 345, sources := [261] },
  { frame := 280, destination := 380, sources := [309] }, { frame := 280, destination := 380, sources := [281] },
  { frame := 280, destination := 380, sources := [299] }, { frame := 280, destination := 380, sources := [261] },
  { frame := 280, destination := 309, sources := [281] }, { frame := 280, destination := 309, sources := [261] },
  { frame := 280, destination := 281, sources := [299] }, { frame := 280, destination := 299, sources := [261] },
  { frame := 280, destination := 261, sources := [345] }, { frame := 280, destination := 261, sources := [380] },
  { frame := 280, destination := 261, sources := [281] }, { frame := 280, destination := 299, sources := [345] },
  { frame := 280, destination := 299, sources := [380] }, { frame := 280, destination := 299, sources := [309] },
  { frame := 280, destination := 281, sources := [345] }, { frame := 280, destination := 281, sources := [380] },
  { frame := 280, destination := 281, sources := [309] }, { frame := 280, destination := 309, sources := [345] },
  { frame := 280, destination := 309, sources := [380] }, { frame := 281, destination := 491, sources := [310] },
  { frame := 281, destination := 491, sources := [275] }, { frame := 281, destination := 491, sources := [263] },
  { frame := 281, destination := 491, sources := [410] }, { frame := 281, destination := 374, sources := [310] },
  { frame := 281, destination := 374, sources := [410] }, { frame := 281, destination := 310, sources := [275] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2c73f9112e9cfebf"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk32`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2540)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 281, destination := 310, sources := [263] }, { frame := 281, destination := 310, sources := [410] },
  { frame := 281, destination := 410, sources := [491] }, { frame := 281, destination := 410, sources := [374] },
  { frame := 281, destination := 410, sources := [310] }, { frame := 281, destination := 410, sources := [275] },
  { frame := 281, destination := 410, sources := [263] }, { frame := 281, destination := 263, sources := [491] },
  { frame := 281, destination := 263, sources := [374] }, { frame := 281, destination := 263, sources := [310] },
  { frame := 281, destination := 275, sources := [491] }, { frame := 281, destination := 275, sources := [374] },
  { frame := 281, destination := 275, sources := [310] }, { frame := 281, destination := 374, sources := [491] },
  { frame := 282, destination := 325, sources := [256] }, { frame := 282, destination := 325, sources := [442] },
  { frame := 282, destination := 325, sources := [404] }, { frame := 282, destination := 325, sources := [392] },
  { frame := 282, destination := 359, sources := [256] }, { frame := 282, destination := 256, sources := [442] },
  { frame := 282, destination := 256, sources := [404] }, { frame := 282, destination := 256, sources := [392] },
  { frame := 282, destination := 392, sources := [325] }, { frame := 282, destination := 392, sources := [359] },
  { frame := 282, destination := 392, sources := [256] }, { frame := 282, destination := 392, sources := [442] },
  { frame := 282, destination := 404, sources := [325] }, { frame := 282, destination := 404, sources := [359] },
  { frame := 282, destination := 404, sources := [256] }, { frame := 282, destination := 404, sources := [442] },
  { frame := 282, destination := 442, sources := [325] }, { frame := 282, destination := 442, sources := [359] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-5c3a26497320ede2"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk33`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2573)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 282, destination := 359, sources := [325] }, { frame := 283, destination := 490, sources := [312] },
  { frame := 283, destination := 490, sources := [412] }, { frame := 283, destination := 490, sources := [434] },
  { frame := 283, destination := 490, sources := [429] }, { frame := 283, destination := 355, sources := [312] },
  { frame := 283, destination := 355, sources := [412] }, { frame := 283, destination := 312, sources := [412] },
  { frame := 283, destination := 312, sources := [434] }, { frame := 283, destination := 312, sources := [429] },
  { frame := 283, destination := 429, sources := [490] }, { frame := 283, destination := 429, sources := [355] },
  { frame := 283, destination := 429, sources := [312] }, { frame := 283, destination := 434, sources := [490] },
  { frame := 283, destination := 434, sources := [355] }, { frame := 283, destination := 434, sources := [312] },
  { frame := 283, destination := 412, sources := [490] }, { frame := 283, destination := 412, sources := [355] },
  { frame := 283, destination := 355, sources := [490] }, { frame := 284, destination := 344, sources := [400] },
  { frame := 284, destination := 344, sources := [390] }, { frame := 284, destination := 344, sources := [283] },
  { frame := 284, destination := 344, sources := [418] }, { frame := 284, destination := 508, sources := [400] },
  { frame := 284, destination := 508, sources := [390] }, { frame := 284, destination := 400, sources := [390] },
  { frame := 284, destination := 400, sources := [283] }, { frame := 284, destination := 400, sources := [418] },
  { frame := 284, destination := 390, sources := [283] }, { frame := 284, destination := 390, sources := [418] },
  { frame := 284, destination := 418, sources := [344] }, { frame := 284, destination := 418, sources := [508] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-36c128df45445f1f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk34`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2606)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 284, destination := 418, sources := [400] }, { frame := 284, destination := 283, sources := [344] },
  { frame := 284, destination := 283, sources := [508] }, { frame := 284, destination := 283, sources := [400] },
  { frame := 284, destination := 390, sources := [344] }, { frame := 284, destination := 390, sources := [508] },
  { frame := 284, destination := 390, sources := [400] }, { frame := 284, destination := 508, sources := [344] },
  { frame := 285, destination := 489, sources := [431] }, { frame := 285, destination := 489, sources := [426] },
  { frame := 285, destination := 489, sources := [408] }, { frame := 285, destination := 489, sources := [383] },
  { frame := 285, destination := 507, sources := [431] }, { frame := 285, destination := 507, sources := [426] },
  { frame := 285, destination := 507, sources := [408] }, { frame := 285, destination := 507, sources := [383] },
  { frame := 285, destination := 431, sources := [408] }, { frame := 285, destination := 431, sources := [383] },
  { frame := 285, destination := 426, sources := [408] }, { frame := 285, destination := 426, sources := [383] },
  { frame := 285, destination := 383, sources := [489] }, { frame := 285, destination := 383, sources := [507] },
  { frame := 285, destination := 383, sources := [431] }, { frame := 285, destination := 383, sources := [426] },
  { frame := 285, destination := 408, sources := [489] }, { frame := 285, destination := 408, sources := [507] },
  { frame := 285, destination := 408, sources := [431] }, { frame := 285, destination := 408, sources := [426] },
  { frame := 285, destination := 426, sources := [489] }, { frame := 285, destination := 426, sources := [507] },
  { frame := 285, destination := 431, sources := [489] }, { frame := 285, destination := 431, sources := [507] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-557730a5838ff4f8"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk35`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2639)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 286, destination := 318, sources := [509] }, { frame := 286, destination := 318, sources := [441] },
  { frame := 286, destination := 318, sources := [414] }, { frame := 286, destination := 318, sources := [300] },
  { frame := 286, destination := 509, sources := [305] }, { frame := 286, destination := 509, sources := [441] },
  { frame := 286, destination := 509, sources := [414] }, { frame := 286, destination := 509, sources := [300] },
  { frame := 286, destination := 305, sources := [441] }, { frame := 286, destination := 305, sources := [414] },
  { frame := 286, destination := 305, sources := [300] }, { frame := 286, destination := 441, sources := [300] },
  { frame := 286, destination := 414, sources := [300] }, { frame := 286, destination := 300, sources := [318] },
  { frame := 286, destination := 300, sources := [305] }, { frame := 286, destination := 414, sources := [318] },
  { frame := 286, destination := 414, sources := [305] }, { frame := 286, destination := 414, sources := [441] },
  { frame := 286, destination := 441, sources := [318] }, { frame := 286, destination := 441, sources := [305] },
  { frame := 287, destination := 488, sources := [286] }, { frame := 287, destination := 488, sources := [265] },
  { frame := 287, destination := 488, sources := [315] }, { frame := 287, destination := 488, sources := [270] },
  { frame := 287, destination := 506, sources := [286] }, { frame := 287, destination := 506, sources := [265] },
  { frame := 287, destination := 506, sources := [315] }, { frame := 287, destination := 506, sources := [270] },
  { frame := 287, destination := 286, sources := [315] }, { frame := 287, destination := 265, sources := [315] },
  { frame := 287, destination := 265, sources := [270] }, { frame := 287, destination := 270, sources := [488] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-9244d70a8b0870ae"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk36`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2672)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 287, destination := 270, sources := [506] }, { frame := 287, destination := 270, sources := [286] },
  { frame := 287, destination := 270, sources := [265] }, { frame := 287, destination := 270, sources := [315] },
  { frame := 287, destination := 315, sources := [488] }, { frame := 287, destination := 315, sources := [506] },
  { frame := 287, destination := 315, sources := [265] }, { frame := 287, destination := 265, sources := [488] },
  { frame := 287, destination := 265, sources := [506] }, { frame := 287, destination := 286, sources := [488] },
  { frame := 287, destination := 286, sources := [506] }, { frame := 288, destination := 324, sources := [326] },
  { frame := 288, destination := 324, sources := [362] }, { frame := 288, destination := 324, sources := [224] },
  { frame := 288, destination := 324, sources := [446] }, { frame := 288, destination := 505, sources := [326] },
  { frame := 288, destination := 505, sources := [362] }, { frame := 288, destination := 326, sources := [362] },
  { frame := 288, destination := 326, sources := [224] }, { frame := 288, destination := 326, sources := [446] },
  { frame := 288, destination := 446, sources := [324] }, { frame := 288, destination := 446, sources := [505] },
  { frame := 288, destination := 446, sources := [326] }, { frame := 288, destination := 224, sources := [324] },
  { frame := 288, destination := 224, sources := [505] }, { frame := 288, destination := 224, sources := [326] },
  { frame := 288, destination := 362, sources := [324] }, { frame := 288, destination := 362, sources := [505] },
  { frame := 288, destination := 505, sources := [324] }, { frame := 289, destination := 487, sources := [510] },
  { frame := 289, destination := 487, sources := [335] }, { frame := 289, destination := 487, sources := [454] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-fc32fe26c054fbe4"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk37`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2705)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 289, destination := 487, sources := [239] }, { frame := 289, destination := 510, sources := [364] },
  { frame := 289, destination := 510, sources := [335] }, { frame := 289, destination := 510, sources := [454] },
  { frame := 289, destination := 510, sources := [239] }, { frame := 289, destination := 364, sources := [335] },
  { frame := 289, destination := 364, sources := [454] }, { frame := 289, destination := 364, sources := [239] },
  { frame := 289, destination := 454, sources := [239] }, { frame := 289, destination := 239, sources := [487] },
  { frame := 289, destination := 239, sources := [364] }, { frame := 289, destination := 239, sources := [335] },
  { frame := 289, destination := 239, sources := [454] }, { frame := 289, destination := 454, sources := [487] },
  { frame := 289, destination := 454, sources := [364] }, { frame := 289, destination := 335, sources := [487] },
  { frame := 289, destination := 335, sources := [364] }, { frame := 290, destination := 337, sources := [373] },
  { frame := 290, destination := 337, sources := [370] }, { frame := 290, destination := 337, sources := [453] },
  { frame := 290, destination := 337, sources := [230] }, { frame := 290, destination := 373, sources := [347] },
  { frame := 290, destination := 373, sources := [370] }, { frame := 290, destination := 373, sources := [453] },
  { frame := 290, destination := 373, sources := [230] }, { frame := 290, destination := 347, sources := [370] },
  { frame := 290, destination := 347, sources := [453] }, { frame := 290, destination := 347, sources := [230] },
  { frame := 290, destination := 453, sources := [230] }, { frame := 290, destination := 230, sources := [337] },
  { frame := 290, destination := 230, sources := [347] }, { frame := 290, destination := 230, sources := [370] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-c41d6870797e685e"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk38`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2738)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 290, destination := 230, sources := [453] }, { frame := 290, destination := 453, sources := [337] },
  { frame := 290, destination := 453, sources := [347] }, { frame := 290, destination := 370, sources := [337] },
  { frame := 290, destination := 370, sources := [347] }, { frame := 291, destination := 498, sources := [376] },
  { frame := 291, destination := 498, sources := [378] }, { frame := 291, destination := 498, sources := [251] },
  { frame := 291, destination := 498, sources := [460] }, { frame := 291, destination := 356, sources := [376] },
  { frame := 291, destination := 356, sources := [378] }, { frame := 291, destination := 356, sources := [251] },
  { frame := 291, destination := 356, sources := [460] }, { frame := 291, destination := 376, sources := [378] },
  { frame := 291, destination := 376, sources := [251] }, { frame := 291, destination := 378, sources := [251] },
  { frame := 291, destination := 378, sources := [460] }, { frame := 291, destination := 251, sources := [460] },
  { frame := 291, destination := 460, sources := [498] }, { frame := 291, destination := 460, sources := [356] },
  { frame := 291, destination := 460, sources := [376] }, { frame := 291, destination := 460, sources := [251] },
  { frame := 291, destination := 251, sources := [498] }, { frame := 291, destination := 251, sources := [356] },
  { frame := 291, destination := 378, sources := [498] }, { frame := 291, destination := 378, sources := [356] },
  { frame := 291, destination := 376, sources := [498] }, { frame := 291, destination := 376, sources := [356] },
  { frame := 292, destination := 323, sources := [387] }, { frame := 292, destination := 323, sources := [406] },
  { frame := 292, destination := 323, sources := [285] }, { frame := 292, destination := 323, sources := [424] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-beca1c9883e0514a"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk39`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2771)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 292, destination := 361, sources := [406] }, { frame := 292, destination := 387, sources := [406] },
  { frame := 292, destination := 387, sources := [285] }, { frame := 292, destination := 387, sources := [424] },
  { frame := 292, destination := 406, sources := [424] }, { frame := 292, destination := 285, sources := [424] },
  { frame := 292, destination := 424, sources := [323] }, { frame := 292, destination := 424, sources := [361] },
  { frame := 292, destination := 424, sources := [406] }, { frame := 292, destination := 424, sources := [285] },
  { frame := 292, destination := 285, sources := [323] }, { frame := 292, destination := 285, sources := [361] },
  { frame := 292, destination := 285, sources := [387] }, { frame := 292, destination := 406, sources := [323] },
  { frame := 292, destination := 406, sources := [361] }, { frame := 292, destination := 361, sources := [323] },
  { frame := 293, destination := 497, sources := [366] }, { frame := 293, destination := 497, sources := [264] },
  { frame := 293, destination := 497, sources := [395] }, { frame := 293, destination := 497, sources := [289] },
  { frame := 293, destination := 366, sources := [264] }, { frame := 293, destination := 366, sources := [445] },
  { frame := 293, destination := 366, sources := [395] }, { frame := 293, destination := 366, sources := [289] },
  { frame := 293, destination := 264, sources := [445] }, { frame := 293, destination := 264, sources := [395] },
  { frame := 293, destination := 264, sources := [289] }, { frame := 293, destination := 445, sources := [395] },
  { frame := 293, destination := 395, sources := [289] }, { frame := 293, destination := 289, sources := [497] },
  { frame := 293, destination := 289, sources := [445] }, { frame := 293, destination := 395, sources := [497] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-7ab1f245e17f420d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk40`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2804)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 293, destination := 395, sources := [264] }, { frame := 293, destination := 445, sources := [497] },
  { frame := 294, destination := 336, sources := [409] }, { frame := 294, destination := 336, sources := [282] },
  { frame := 294, destination := 336, sources := [255] }, { frame := 294, destination := 336, sources := [306] },
  { frame := 294, destination := 367, sources := [409] }, { frame := 294, destination := 409, sources := [282] },
  { frame := 294, destination := 409, sources := [255] }, { frame := 294, destination := 409, sources := [306] },
  { frame := 294, destination := 282, sources := [255] }, { frame := 294, destination := 255, sources := [306] },
  { frame := 294, destination := 306, sources := [336] }, { frame := 294, destination := 306, sources := [367] },
  { frame := 294, destination := 306, sources := [409] }, { frame := 294, destination := 255, sources := [336] },
  { frame := 294, destination := 255, sources := [367] }, { frame := 294, destination := 255, sources := [409] },
  { frame := 294, destination := 282, sources := [336] }, { frame := 294, destination := 282, sources := [367] },
  { frame := 294, destination := 282, sources := [409] }, { frame := 294, destination := 367, sources := [336] },
  { frame := 295, destination := 496, sources := [420] }, { frame := 295, destination := 496, sources := [313] },
  { frame := 295, destination := 496, sources := [269] }, { frame := 295, destination := 496, sources := [292] },
  { frame := 295, destination := 372, sources := [420] }, { frame := 295, destination := 372, sources := [313] },
  { frame := 295, destination := 372, sources := [269] }, { frame := 295, destination := 372, sources := [292] },
  { frame := 295, destination := 420, sources := [269] }, { frame := 295, destination := 420, sources := [292] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-ff541d6f1ae9af96"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk41`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2837)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 295, destination := 313, sources := [292] }, { frame := 295, destination := 269, sources := [292] },
  { frame := 295, destination := 292, sources := [496] }, { frame := 295, destination := 292, sources := [372] },
  { frame := 295, destination := 292, sources := [420] }, { frame := 295, destination := 269, sources := [496] },
  { frame := 295, destination := 269, sources := [372] }, { frame := 295, destination := 269, sources := [420] },
  { frame := 295, destination := 269, sources := [313] }, { frame := 295, destination := 313, sources := [496] },
  { frame := 295, destination := 313, sources := [372] }, { frame := 295, destination := 420, sources := [496] },
  { frame := 295, destination := 420, sources := [372] }, { frame := 296, destination := 348, sources := [514] },
  { frame := 296, destination := 348, sources := [430] }, { frame := 296, destination := 348, sources := [384] },
  { frame := 296, destination := 348, sources := [303] }, { frame := 296, destination := 514, sources := [430] },
  { frame := 296, destination := 514, sources := [384] }, { frame := 296, destination := 514, sources := [279] },
  { frame := 296, destination := 514, sources := [303] }, { frame := 296, destination := 430, sources := [384] },
  { frame := 296, destination := 430, sources := [279] }, { frame := 296, destination := 430, sources := [303] },
  { frame := 296, destination := 384, sources := [279] }, { frame := 296, destination := 279, sources := [303] },
  { frame := 296, destination := 303, sources := [348] }, { frame := 296, destination := 303, sources := [384] },
  { frame := 296, destination := 279, sources := [348] }, { frame := 296, destination := 279, sources := [430] },
  { frame := 296, destination := 279, sources := [384] }, { frame := 296, destination := 384, sources := [348] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-7eba5658fe0ec801"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk42`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2870)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 297, destination := 495, sources := [291] }, { frame := 297, destination := 495, sources := [438] },
  { frame := 297, destination := 495, sources := [267] }, { frame := 297, destination := 495, sources := [317] },
  { frame := 297, destination := 513, sources := [317] }, { frame := 297, destination := 291, sources := [438] },
  { frame := 297, destination := 291, sources := [267] }, { frame := 297, destination := 291, sources := [317] },
  { frame := 297, destination := 438, sources := [317] }, { frame := 297, destination := 317, sources := [495] },
  { frame := 297, destination := 317, sources := [513] }, { frame := 297, destination := 317, sources := [291] },
  { frame := 297, destination := 317, sources := [438] }, { frame := 297, destination := 317, sources := [267] },
  { frame := 297, destination := 267, sources := [495] }, { frame := 297, destination := 267, sources := [513] },
  { frame := 297, destination := 267, sources := [438] }, { frame := 297, destination := 438, sources := [495] },
  { frame := 297, destination := 438, sources := [513] }, { frame := 297, destination := 513, sources := [495] },
  { frame := 298, destination := 321, sources := [432] }, { frame := 298, destination := 321, sources := [422] },
  { frame := 298, destination := 321, sources := [388] }, { frame := 298, destination := 321, sources := [301] },
  { frame := 298, destination := 515, sources := [422] }, { frame := 298, destination := 432, sources := [422] },
  { frame := 298, destination := 432, sources := [388] }, { frame := 298, destination := 432, sources := [301] },
  { frame := 298, destination := 422, sources := [388] }, { frame := 298, destination := 388, sources := [301] },
  { frame := 298, destination := 301, sources := [321] }, { frame := 298, destination := 301, sources := [515] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-a2703010a56710b1"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk43`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2903)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 298, destination := 301, sources := [422] }, { frame := 298, destination := 388, sources := [321] },
  { frame := 298, destination := 388, sources := [515] }, { frame := 298, destination := 388, sources := [432] },
  { frame := 298, destination := 422, sources := [321] }, { frame := 298, destination := 422, sources := [515] },
  { frame := 298, destination := 515, sources := [321] }, { frame := 299, destination := 494, sources := [402] },
  { frame := 299, destination := 494, sources := [314] }, { frame := 299, destination := 494, sources := [440] },
  { frame := 299, destination := 494, sources := [262] }, { frame := 299, destination := 512, sources := [402] },
  { frame := 299, destination := 402, sources := [314] }, { frame := 299, destination := 402, sources := [440] },
  { frame := 299, destination := 402, sources := [262] }, { frame := 299, destination := 440, sources := [262] },
  { frame := 299, destination := 262, sources := [494] }, { frame := 299, destination := 262, sources := [512] },
  { frame := 299, destination := 262, sources := [402] }, { frame := 299, destination := 262, sources := [314] },
  { frame := 299, destination := 262, sources := [440] }, { frame := 299, destination := 440, sources := [494] },
  { frame := 299, destination := 440, sources := [512] }, { frame := 299, destination := 440, sources := [402] },
  { frame := 299, destination := 314, sources := [494] }, { frame := 299, destination := 314, sources := [512] },
  { frame := 299, destination := 314, sources := [402] }, { frame := 299, destination := 512, sources := [494] },
  { frame := 300, destination := 320, sources := [328] }, { frame := 300, destination := 320, sources := [330] },
  { frame := 300, destination := 320, sources := [225] }, { frame := 300, destination := 320, sources := [458] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-9f6ae63434d39d49"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk44`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2936)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 300, destination := 511, sources := [328] }, { frame := 300, destination := 511, sources := [330] },
  { frame := 300, destination := 511, sources := [225] }, { frame := 300, destination := 511, sources := [458] },
  { frame := 300, destination := 328, sources := [225] }, { frame := 300, destination := 328, sources := [458] },
  { frame := 300, destination := 330, sources := [225] }, { frame := 300, destination := 225, sources := [458] },
  { frame := 300, destination := 458, sources := [320] }, { frame := 300, destination := 458, sources := [511] },
  { frame := 300, destination := 458, sources := [328] }, { frame := 300, destination := 458, sources := [330] },
  { frame := 300, destination := 225, sources := [320] }, { frame := 300, destination := 225, sources := [511] },
  { frame := 300, destination := 330, sources := [320] }, { frame := 300, destination := 330, sources := [511] },
  { frame := 300, destination := 330, sources := [328] }, { frame := 300, destination := 328, sources := [320] },
  { frame := 300, destination := 328, sources := [511] }, { frame := 301, destination := 493, sources := [350] },
  { frame := 301, destination := 493, sources := [363] }, { frame := 301, destination := 493, sources := [448] },
  { frame := 301, destination := 493, sources := [450] }, { frame := 301, destination := 516, sources := [350] },
  { frame := 301, destination := 516, sources := [363] }, { frame := 301, destination := 516, sources := [448] },
  { frame := 301, destination := 516, sources := [450] }, { frame := 301, destination := 350, sources := [363] },
  { frame := 301, destination := 350, sources := [448] }, { frame := 301, destination := 363, sources := [448] },
  { frame := 301, destination := 363, sources := [450] }, { frame := 301, destination := 448, sources := [450] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-b5376f1c1be0f0a7"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk45`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L2969)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 301, destination := 450, sources := [493] }, { frame := 301, destination := 450, sources := [516] },
  { frame := 301, destination := 450, sources := [350] }, { frame := 301, destination := 450, sources := [448] },
  { frame := 301, destination := 448, sources := [493] }, { frame := 301, destination := 448, sources := [516] },
  { frame := 301, destination := 363, sources := [493] }, { frame := 301, destination := 363, sources := [516] },
  { frame := 301, destination := 350, sources := [493] }, { frame := 301, destination := 350, sources := [516] },
  { frame := 302, destination := 522, sources := [548] }, { frame := 302, destination := 522, sources := [553] },
  { frame := 302, destination := 522, sources := [604] }, { frame := 302, destination := 522, sources := [652] },
  { frame := 302, destination := 548, sources := [587] }, { frame := 302, destination := 548, sources := [604] },
  { frame := 302, destination := 548, sources := [652] }, { frame := 302, destination := 587, sources := [604] },
  { frame := 302, destination := 587, sources := [652] }, { frame := 302, destination := 652, sources := [522] },
  { frame := 302, destination := 652, sources := [587] }, { frame := 302, destination := 604, sources := [522] },
  { frame := 302, destination := 604, sources := [587] }, { frame := 302, destination := 587, sources := [522] },
  { frame := 302, destination := 587, sources := [548] }, { frame := 302, destination := 553, sources := [548] },
  { frame := 303, destination := 521, sources := [557] }, { frame := 303, destination := 521, sources := [575] },
  { frame := 303, destination := 521, sources := [607] }, { frame := 303, destination := 521, sources := [630] },
  { frame := 303, destination := 539, sources := [575] }, { frame := 303, destination := 539, sources := [607] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-5e45c7676a164772"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk46`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3002)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 303, destination := 539, sources := [630] }, { frame := 303, destination := 557, sources := [575] },
  { frame := 303, destination := 557, sources := [607] }, { frame := 303, destination := 557, sources := [630] },
  { frame := 303, destination := 607, sources := [630] }, { frame := 303, destination := 630, sources := [521] },
  { frame := 303, destination := 630, sources := [539] }, { frame := 303, destination := 630, sources := [575] },
  { frame := 303, destination := 630, sources := [607] }, { frame := 303, destination := 607, sources := [521] },
  { frame := 303, destination := 607, sources := [539] }, { frame := 303, destination := 575, sources := [521] },
  { frame := 303, destination := 575, sources := [539] }, { frame := 303, destination := 557, sources := [521] },
  { frame := 303, destination := 557, sources := [539] }, { frame := 304, destination := 520, sources := [591] },
  { frame := 304, destination := 520, sources := [618] }, { frame := 304, destination := 520, sources := [637] },
  { frame := 304, destination := 520, sources := [646] }, { frame := 304, destination := 556, sources := [591] },
  { frame := 304, destination := 556, sources := [618] }, { frame := 304, destination := 556, sources := [637] },
  { frame := 304, destination := 556, sources := [646] }, { frame := 304, destination := 591, sources := [646] },
  { frame := 304, destination := 618, sources := [637] }, { frame := 304, destination := 646, sources := [520] },
  { frame := 304, destination := 646, sources := [556] }, { frame := 304, destination := 646, sources := [591] },
  { frame := 304, destination := 646, sources := [618] }, { frame := 304, destination := 637, sources := [520] },
  { frame := 304, destination := 637, sources := [556] }, { frame := 304, destination := 637, sources := [591] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e86a7151bf9e28fc"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk47`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3035)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 304, destination := 618, sources := [520] }, { frame := 304, destination := 618, sources := [556] },
  { frame := 304, destination := 591, sources := [520] }, { frame := 304, destination := 591, sources := [556] },
  { frame := 305, destination := 519, sources := [592] }, { frame := 305, destination := 519, sources := [613] },
  { frame := 305, destination := 519, sources := [642] }, { frame := 305, destination := 519, sources := [645] },
  { frame := 305, destination := 555, sources := [592] }, { frame := 305, destination := 555, sources := [613] },
  { frame := 305, destination := 555, sources := [642] }, { frame := 305, destination := 555, sources := [645] },
  { frame := 305, destination := 592, sources := [645] }, { frame := 305, destination := 613, sources := [642] },
  { frame := 305, destination := 613, sources := [645] }, { frame := 305, destination := 645, sources := [519] },
  { frame := 305, destination := 645, sources := [555] }, { frame := 305, destination := 645, sources := [613] },
  { frame := 305, destination := 642, sources := [519] }, { frame := 305, destination := 642, sources := [555] },
  { frame := 305, destination := 642, sources := [592] }, { frame := 305, destination := 613, sources := [519] },
  { frame := 305, destination := 613, sources := [555] }, { frame := 305, destination := 592, sources := [519] },
  { frame := 305, destination := 592, sources := [555] }, { frame := 306, destination := 518, sources := [554] },
  { frame := 306, destination := 518, sources := [612] }, { frame := 306, destination := 518, sources := [625] },
  { frame := 306, destination := 536, sources := [554] }, { frame := 306, destination := 536, sources := [572] },
  { frame := 306, destination := 536, sources := [612] }, { frame := 306, destination := 536, sources := [625] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e3ccb218a607691f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk48`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3068)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 306, destination := 554, sources := [572] }, { frame := 306, destination := 554, sources := [612] },
  { frame := 306, destination := 554, sources := [625] }, { frame := 306, destination := 572, sources := [612] },
  { frame := 306, destination := 572, sources := [625] }, { frame := 306, destination := 612, sources := [625] },
  { frame := 306, destination := 625, sources := [518] }, { frame := 306, destination := 625, sources := [536] },
  { frame := 306, destination := 625, sources := [554] }, { frame := 306, destination := 625, sources := [572] },
  { frame := 306, destination := 612, sources := [518] }, { frame := 306, destination := 612, sources := [536] },
  { frame := 306, destination := 572, sources := [518] }, { frame := 306, destination := 572, sources := [536] },
  { frame := 306, destination := 572, sources := [554] }, { frame := 306, destination := 554, sources := [518] },
  { frame := 306, destination := 554, sources := [536] }, { frame := 307, destination := 517, sources := [551] },
  { frame := 307, destination := 517, sources := [584] }, { frame := 307, destination := 517, sources := [603] },
  { frame := 307, destination := 517, sources := [651] }, { frame := 307, destination := 551, sources := [558] },
  { frame := 307, destination := 558, sources := [584] }, { frame := 307, destination := 584, sources := [603] },
  { frame := 307, destination := 584, sources := [651] }, { frame := 307, destination := 651, sources := [517] },
  { frame := 307, destination := 651, sources := [558] }, { frame := 307, destination := 651, sources := [584] },
  { frame := 307, destination := 603, sources := [517] }, { frame := 307, destination := 603, sources := [558] },
  { frame := 307, destination := 603, sources := [584] }, { frame := 307, destination := 584, sources := [551] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-7588c836c5c4d0cd"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk49`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3101)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 307, destination := 558, sources := [517] }, { frame := 307, destination := 551, sources := [517] },
  { frame := 308, destination := 528, sources := [559] }, { frame := 308, destination := 528, sources := [622] },
  { frame := 308, destination := 528, sources := [634] }, { frame := 308, destination := 550, sources := [585] },
  { frame := 308, destination := 550, sources := [622] }, { frame := 308, destination := 550, sources := [634] },
  { frame := 308, destination := 559, sources := [622] }, { frame := 308, destination := 559, sources := [634] },
  { frame := 308, destination := 634, sources := [528] }, { frame := 308, destination := 634, sources := [550] },
  { frame := 308, destination := 622, sources := [528] }, { frame := 308, destination := 622, sources := [550] },
  { frame := 308, destination := 585, sources := [528] }, { frame := 308, destination := 559, sources := [528] },
  { frame := 308, destination := 559, sources := [550] }, { frame := 309, destination := 527, sources := [563] },
  { frame := 309, destination := 527, sources := [610] }, { frame := 309, destination := 527, sources := [627] },
  { frame := 309, destination := 527, sources := [655] }, { frame := 309, destination := 563, sources := [600] },
  { frame := 309, destination := 563, sources := [610] }, { frame := 309, destination := 563, sources := [627] },
  { frame := 309, destination := 563, sources := [655] }, { frame := 309, destination := 600, sources := [610] },
  { frame := 309, destination := 600, sources := [627] }, { frame := 309, destination := 600, sources := [655] },
  { frame := 309, destination := 610, sources := [627] }, { frame := 309, destination := 627, sources := [655] },
  { frame := 309, destination := 655, sources := [527] }, { frame := 309, destination := 655, sources := [600] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-55e6c30cb17f43c3"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk50`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3134)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 309, destination := 627, sources := [527] }, { frame := 309, destination := 627, sources := [600] },
  { frame := 309, destination := 610, sources := [527] }, { frame := 309, destination := 610, sources := [600] },
  { frame := 310, destination := 526, sources := [562] }, { frame := 310, destination := 526, sources := [579] },
  { frame := 310, destination := 526, sources := [589] }, { frame := 310, destination := 526, sources := [648] },
  { frame := 310, destination := 543, sources := [562] }, { frame := 310, destination := 543, sources := [579] },
  { frame := 310, destination := 543, sources := [589] }, { frame := 310, destination := 543, sources := [648] },
  { frame := 310, destination := 589, sources := [648] }, { frame := 310, destination := 648, sources := [526] },
  { frame := 310, destination := 648, sources := [543] }, { frame := 310, destination := 648, sources := [562] },
  { frame := 310, destination := 648, sources := [579] }, { frame := 310, destination := 648, sources := [589] },
  { frame := 310, destination := 589, sources := [526] }, { frame := 310, destination := 589, sources := [543] },
  { frame := 310, destination := 589, sources := [562] }, { frame := 310, destination := 579, sources := [526] },
  { frame := 310, destination := 579, sources := [543] }, { frame := 310, destination := 579, sources := [562] },
  { frame := 310, destination := 562, sources := [543] }, { frame := 311, destination := 525, sources := [544] },
  { frame := 311, destination := 525, sources := [580] }, { frame := 311, destination := 525, sources := [594] },
  { frame := 311, destination := 525, sources := [643] }, { frame := 311, destination := 544, sources := [580] },
  { frame := 311, destination := 544, sources := [594] }, { frame := 311, destination := 544, sources := [643] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-d5c088e27a732e19"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk51`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3167)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 311, destination := 561, sources := [580] }, { frame := 311, destination := 580, sources := [594] },
  { frame := 311, destination := 580, sources := [643] }, { frame := 311, destination := 594, sources := [643] },
  { frame := 311, destination := 643, sources := [525] }, { frame := 311, destination := 643, sources := [561] },
  { frame := 311, destination := 643, sources := [580] }, { frame := 311, destination := 643, sources := [594] },
  { frame := 311, destination := 594, sources := [525] }, { frame := 311, destination := 594, sources := [544] },
  { frame := 311, destination := 594, sources := [561] }, { frame := 311, destination := 580, sources := [525] },
  { frame := 311, destination := 580, sources := [561] }, { frame := 311, destination := 561, sources := [525] },
  { frame := 312, destination := 524, sources := [595] }, { frame := 312, destination := 524, sources := [609] },
  { frame := 312, destination := 524, sources := [628] }, { frame := 312, destination := 524, sources := [660] },
  { frame := 312, destination := 560, sources := [595] }, { frame := 312, destination := 595, sources := [609] },
  { frame := 312, destination := 595, sources := [628] }, { frame := 312, destination := 595, sources := [660] },
  { frame := 312, destination := 609, sources := [660] }, { frame := 312, destination := 628, sources := [660] },
  { frame := 312, destination := 660, sources := [524] }, { frame := 312, destination := 660, sources := [560] },
  { frame := 312, destination := 660, sources := [595] }, { frame := 312, destination := 628, sources := [524] },
  { frame := 312, destination := 628, sources := [560] }, { frame := 312, destination := 628, sources := [595] },
  { frame := 312, destination := 628, sources := [609] }, { frame := 312, destination := 609, sources := [524] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e8bafe79d2e6dd41"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk52`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3200)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 312, destination := 609, sources := [560] }, { frame := 312, destination := 609, sources := [595] },
  { frame := 312, destination := 560, sources := [524] }, { frame := 313, destination := 523, sources := [549] },
  { frame := 313, destination := 523, sources := [564] }, { frame := 313, destination := 523, sources := [621] },
  { frame := 313, destination := 523, sources := [633] }, { frame := 313, destination := 549, sources := [586] },
  { frame := 313, destination := 549, sources := [621] }, { frame := 313, destination := 549, sources := [633] },
  { frame := 313, destination := 564, sources := [586] }, { frame := 313, destination := 586, sources := [633] },
  { frame := 313, destination := 621, sources := [633] }, { frame := 313, destination := 633, sources := [523] },
  { frame := 313, destination := 633, sources := [586] }, { frame := 313, destination := 633, sources := [621] },
  { frame := 313, destination := 621, sources := [523] }, { frame := 313, destination := 621, sources := [549] },
  { frame := 313, destination := 586, sources := [523] }, { frame := 313, destination := 564, sources := [523] },
  { frame := 314, destination := 534, sources := [602] }, { frame := 314, destination := 534, sources := [620] },
  { frame := 314, destination := 534, sources := [632] }, { frame := 314, destination := 534, sources := [650] },
  { frame := 314, destination := 565, sources := [650] }, { frame := 314, destination := 602, sources := [620] },
  { frame := 314, destination := 602, sources := [632] }, { frame := 314, destination := 602, sources := [650] },
  { frame := 314, destination := 620, sources := [650] }, { frame := 314, destination := 632, sources := [650] },
  { frame := 314, destination := 650, sources := [534] }, { frame := 314, destination := 650, sources := [565] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e4f6e83c6d928826"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk53`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3233)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 314, destination := 650, sources := [602] }, { frame := 314, destination := 650, sources := [620] },
  { frame := 314, destination := 650, sources := [632] }, { frame := 314, destination := 632, sources := [534] },
  { frame := 314, destination := 632, sources := [565] }, { frame := 314, destination := 620, sources := [534] },
  { frame := 314, destination := 620, sources := [565] }, { frame := 314, destination := 565, sources := [534] },
  { frame := 315, destination := 533, sources := [535] }, { frame := 315, destination := 533, sources := [566] },
  { frame := 315, destination := 533, sources := [599] }, { frame := 315, destination := 533, sources := [659] },
  { frame := 315, destination := 535, sources := [576] }, { frame := 315, destination := 535, sources := [599] },
  { frame := 315, destination := 535, sources := [659] }, { frame := 315, destination := 566, sources := [576] },
  { frame := 315, destination := 576, sources := [599] }, { frame := 315, destination := 599, sources := [659] },
  { frame := 315, destination := 659, sources := [533] }, { frame := 315, destination := 659, sources := [576] },
  { frame := 315, destination := 599, sources := [533] }, { frame := 315, destination := 599, sources := [535] },
  { frame := 315, destination := 576, sources := [533] }, { frame := 315, destination := 566, sources := [533] },
  { frame := 316, destination := 532, sources := [546] }, { frame := 316, destination := 532, sources := [567] },
  { frame := 316, destination := 532, sources := [614] }, { frame := 316, destination := 532, sources := [638] },
  { frame := 316, destination := 546, sources := [567] }, { frame := 316, destination := 546, sources := [577] },
  { frame := 316, destination := 546, sources := [614] }, { frame := 316, destination := 546, sources := [638] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-6cbfd3bfa7380bf5"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk54`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3266)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 316, destination := 567, sources := [577] }, { frame := 316, destination := 577, sources := [614] },
  { frame := 316, destination := 577, sources := [638] }, { frame := 316, destination := 614, sources := [638] },
  { frame := 316, destination := 638, sources := [532] }, { frame := 316, destination := 638, sources := [577] },
  { frame := 316, destination := 614, sources := [532] }, { frame := 316, destination := 614, sources := [546] },
  { frame := 316, destination := 614, sources := [567] }, { frame := 316, destination := 577, sources := [532] },
  { frame := 316, destination := 567, sources := [532] }, { frame := 317, destination := 531, sources := [568] },
  { frame := 317, destination := 531, sources := [582] }, { frame := 317, destination := 531, sources := [617] },
  { frame := 317, destination := 531, sources := [641] }, { frame := 317, destination := 541, sources := [568] },
  { frame := 317, destination := 541, sources := [582] }, { frame := 317, destination := 541, sources := [617] },
  { frame := 317, destination := 541, sources := [641] }, { frame := 317, destination := 568, sources := [582] },
  { frame := 317, destination := 568, sources := [641] }, { frame := 317, destination := 617, sources := [641] },
  { frame := 317, destination := 641, sources := [531] }, { frame := 317, destination := 641, sources := [541] },
  { frame := 317, destination := 641, sources := [568] }, { frame := 317, destination := 617, sources := [531] },
  { frame := 317, destination := 617, sources := [541] }, { frame := 317, destination := 617, sources := [582] },
  { frame := 317, destination := 582, sources := [531] }, { frame := 317, destination := 568, sources := [531] },
  { frame := 317, destination := 568, sources := [541] }, { frame := 318, destination := 530, sources := [540] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0c7d6f25d7da4566"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk55`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3299)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 318, destination := 530, sources := [571] }, { frame := 318, destination := 530, sources := [596] },
  { frame := 318, destination := 530, sources := [656] }, { frame := 318, destination := 540, sources := [571] },
  { frame := 318, destination := 540, sources := [596] }, { frame := 318, destination := 540, sources := [656] },
  { frame := 318, destination := 569, sources := [571] }, { frame := 318, destination := 571, sources := [596] },
  { frame := 318, destination := 596, sources := [656] }, { frame := 318, destination := 656, sources := [530] },
  { frame := 318, destination := 656, sources := [569] }, { frame := 318, destination := 656, sources := [571] },
  { frame := 318, destination := 596, sources := [530] }, { frame := 318, destination := 596, sources := [540] },
  { frame := 318, destination := 596, sources := [569] }, { frame := 318, destination := 571, sources := [530] },
  { frame := 318, destination := 571, sources := [569] }, { frame := 318, destination := 569, sources := [530] },
  { frame := 319, destination := 529, sources := [570] }, { frame := 319, destination := 529, sources := [623] },
  { frame := 319, destination := 529, sources := [635] }, { frame := 319, destination := 529, sources := [653] },
  { frame := 319, destination := 570, sources := [605] }, { frame := 319, destination := 570, sources := [623] },
  { frame := 319, destination := 570, sources := [635] }, { frame := 319, destination := 570, sources := [653] },
  { frame := 319, destination := 605, sources := [623] }, { frame := 319, destination := 605, sources := [635] },
  { frame := 319, destination := 605, sources := [653] }, { frame := 319, destination := 623, sources := [635] },
  { frame := 319, destination := 635, sources := [653] }, { frame := 319, destination := 653, sources := [529] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e0b5367d0fd7b5d6"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk56`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3332)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 319, destination := 653, sources := [605] }, { frame := 319, destination := 635, sources := [529] },
  { frame := 319, destination := 635, sources := [605] }, { frame := 319, destination := 623, sources := [529] },
  { frame := 319, destination := 623, sources := [605] }, { frame := 320, destination := 538, sources := [593] },
  { frame := 320, destination := 538, sources := [624] }, { frame := 320, destination := 538, sources := [631] },
  { frame := 320, destination := 538, sources := [644] }, { frame := 320, destination := 574, sources := [593] },
  { frame := 320, destination := 574, sources := [624] }, { frame := 320, destination := 574, sources := [631] },
  { frame := 320, destination := 574, sources := [644] }, { frame := 320, destination := 593, sources := [644] },
  { frame := 320, destination := 624, sources := [631] }, { frame := 320, destination := 644, sources := [538] },
  { frame := 320, destination := 644, sources := [574] }, { frame := 320, destination := 644, sources := [593] },
  { frame := 320, destination := 644, sources := [624] }, { frame := 320, destination := 631, sources := [538] },
  { frame := 320, destination := 631, sources := [574] }, { frame := 320, destination := 631, sources := [593] },
  { frame := 320, destination := 624, sources := [538] }, { frame := 320, destination := 624, sources := [574] },
  { frame := 320, destination := 593, sources := [538] }, { frame := 320, destination := 593, sources := [574] },
  { frame := 321, destination := 537, sources := [590] }, { frame := 321, destination := 537, sources := [619] },
  { frame := 321, destination := 537, sources := [636] }, { frame := 321, destination := 537, sources := [647] },
  { frame := 321, destination := 573, sources := [590] }, { frame := 321, destination := 573, sources := [619] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2171962bbfb4e0f1"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk57`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3365)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 321, destination := 573, sources := [636] }, { frame := 321, destination := 573, sources := [647] },
  { frame := 321, destination := 590, sources := [636] }, { frame := 321, destination := 590, sources := [647] },
  { frame := 321, destination := 619, sources := [636] }, { frame := 321, destination := 619, sources := [647] },
  { frame := 321, destination := 647, sources := [537] }, { frame := 321, destination := 647, sources := [573] },
  { frame := 321, destination := 647, sources := [619] }, { frame := 321, destination := 636, sources := [537] },
  { frame := 321, destination := 636, sources := [573] }, { frame := 321, destination := 636, sources := [590] },
  { frame := 321, destination := 619, sources := [537] }, { frame := 321, destination := 619, sources := [573] },
  { frame := 321, destination := 590, sources := [537] }, { frame := 321, destination := 590, sources := [573] },
  { frame := 322, destination := 545, sources := [581] }, { frame := 322, destination := 545, sources := [601] },
  { frame := 322, destination := 545, sources := [611] }, { frame := 322, destination := 545, sources := [626] },
  { frame := 322, destination := 581, sources := [601] }, { frame := 322, destination := 581, sources := [611] },
  { frame := 322, destination := 581, sources := [626] }, { frame := 322, destination := 581, sources := [654] },
  { frame := 322, destination := 601, sources := [611] }, { frame := 322, destination := 601, sources := [626] },
  { frame := 322, destination := 601, sources := [654] }, { frame := 322, destination := 611, sources := [654] },
  { frame := 322, destination := 626, sources := [654] }, { frame := 322, destination := 654, sources := [545] },
  { frame := 322, destination := 654, sources := [601] }, { frame := 322, destination := 654, sources := [611] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-7f1cf0b76bded46a"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk58`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3398)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 322, destination := 654, sources := [626] }, { frame := 322, destination := 626, sources := [545] },
  { frame := 322, destination := 611, sources := [545] }, { frame := 323, destination := 542, sources := [606] },
  { frame := 323, destination := 542, sources := [608] }, { frame := 323, destination := 542, sources := [629] },
  { frame := 323, destination := 542, sources := [649] }, { frame := 323, destination := 578, sources := [606] },
  { frame := 323, destination := 606, sources := [608] }, { frame := 323, destination := 606, sources := [629] },
  { frame := 323, destination := 606, sources := [649] }, { frame := 323, destination := 608, sources := [649] },
  { frame := 323, destination := 629, sources := [649] }, { frame := 323, destination := 649, sources := [542] },
  { frame := 323, destination := 649, sources := [578] }, { frame := 323, destination := 629, sources := [542] },
  { frame := 323, destination := 629, sources := [578] }, { frame := 323, destination := 629, sources := [606] },
  { frame := 323, destination := 608, sources := [542] }, { frame := 323, destination := 608, sources := [578] },
  { frame := 323, destination := 608, sources := [606] }, { frame := 323, destination := 578, sources := [542] },
  { frame := 324, destination := 552, sources := [583] }, { frame := 324, destination := 552, sources := [598] },
  { frame := 324, destination := 552, sources := [616] }, { frame := 324, destination := 552, sources := [640] },
  { frame := 324, destination := 583, sources := [598] }, { frame := 324, destination := 583, sources := [616] },
  { frame := 324, destination := 583, sources := [640] }, { frame := 324, destination := 583, sources := [658] },
  { frame := 324, destination := 598, sources := [616] }, { frame := 324, destination := 598, sources := [640] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-4bd43d195e9c490f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk59`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3431)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 324, destination := 598, sources := [658] }, { frame := 324, destination := 616, sources := [658] },
  { frame := 324, destination := 658, sources := [552] }, { frame := 324, destination := 658, sources := [598] },
  { frame := 324, destination := 658, sources := [616] }, { frame := 324, destination := 658, sources := [640] },
  { frame := 324, destination := 640, sources := [552] }, { frame := 324, destination := 640, sources := [616] },
  { frame := 324, destination := 616, sources := [552] }, { frame := 325, destination := 547, sources := [597] },
  { frame := 325, destination := 547, sources := [615] }, { frame := 325, destination := 547, sources := [639] },
  { frame := 325, destination := 547, sources := [657] }, { frame := 325, destination := 588, sources := [657] },
  { frame := 325, destination := 597, sources := [615] }, { frame := 325, destination := 597, sources := [639] },
  { frame := 325, destination := 597, sources := [657] }, { frame := 325, destination := 615, sources := [657] },
  { frame := 325, destination := 657, sources := [547] }, { frame := 325, destination := 657, sources := [588] },
  { frame := 325, destination := 657, sources := [597] }, { frame := 325, destination := 657, sources := [615] },
  { frame := 325, destination := 657, sources := [639] }, { frame := 325, destination := 639, sources := [547] },
  { frame := 325, destination := 639, sources := [588] }, { frame := 325, destination := 639, sources := [615] },
  { frame := 325, destination := 615, sources := [547] }, { frame := 325, destination := 615, sources := [588] },
  { frame := 325, destination := 588, sources := [547] }, { frame := 326, destination := 247, sources := [351] },
  { frame := 327, destination := 235, sources := [403] }, { frame := 328, destination := 234, sources := [484] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-75215f0db58ba3bc"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk60`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3464)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 329, destination := 501, sources := [483] }, { frame := 330, destination := 240, sources := [417] },
  { frame := 331, destination := 504, sources := [499] }, { frame := 332, destination := 375, sources := [329] },
  { frame := 333, destination := 345, sources := [310] }, { frame := 334, destination := 256, sources := [490] },
  { frame := 335, destination := 400, sources := [507] }, { frame := 336, destination := 509, sources := [488] },
  { frame := 337, destination := 326, sources := [510] }, { frame := 338, destination := 373, sources := [498] },
  { frame := 339, destination := 323, sources := [366] }, { frame := 340, destination := 409, sources := [372] },
  { frame := 341, destination := 430, sources := [291] }, { frame := 342, destination := 432, sources := [402] },
  { frame := 343, destination := 511, sources := [493] }, { frame := 344, destination := 243, sources := [338] },
  { frame := 345, destination := 485, sources := [503] }, { frame := 346, destination := 246, sources := [421] },
  { frame := 347, destination := 272, sources := [242] }, { frame := 348, destination := 223, sources := [308] },
  { frame := 349, destination := 486, sources := [455] }, { frame := 350, destination := 341, sources := [364] },
  { frame := 351, destination := 305, sources := [380] }, { frame := 352, destination := 344, sources := [325] },
  { frame := 353, destination := 312, sources := [489] }, { frame := 354, destination := 491, sources := [506] },
  { frame := 355, destination := 324, sources := [354] }, { frame := 356, destination := 347, sources := [516] },
  { frame := 357, destination := 387, sources := [321] }, { frame := 358, destination := 336, sources := [514] },
  { frame := 359, destination := 495, sources := [496] }, { frame := 360, destination := 494, sources := [264] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-5165d8854b7bbc7b"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk61`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3497)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 361, destination := 320, sources := [356] }, { frame := 362, destination := 502, sources := [548] },
  { frame := 363, destination := 539, sources := [426] }, { frame := 364, destination := 520, sources := [313] },
  { frame := 365, destination := 555, sources := [348] }, { frame := 366, destination := 536, sources := [359] },
  { frame := 367, destination := 252, sources := [517] }, { frame := 368, destination := 253, sources := [550] },
  { frame := 369, destination := 600, sources := [309] }, { frame := 370, destination := 543, sources := [361] },
  { frame := 371, destination := 525, sources := [512] }, { frame := 372, destination := 595, sources := [265] },
  { frame := 373, destination := 500, sources := [549] }, { frame := 374, destination := 222, sources := [534] },
  { frame := 375, destination := 456, sources := [535] }, { frame := 376, destination := 363, sources := [546] },
  { frame := 377, destination := 251, sources := [541] }, { frame := 378, destination := 505, sources := [530] },
  { frame := 379, destination := 232, sources := [570] }, { frame := 380, destination := 482, sources := [569] },
  { frame := 381, destination := 521, sources := [515] }, { frame := 382, destination := 574, sources := [281] },
  { frame := 383, destination := 573, sources := [286] }, { frame := 384, destination := 518, sources := [497] },
  { frame := 385, destination := 274, sources := [533] }, { frame := 386, destination := 405, sources := [532] },
  { frame := 387, destination := 601, sources := [420] }, { frame := 388, destination := 561, sources := [355] },
  { frame := 389, destination := 526, sources := [508] }, { frame := 390, destination := 606, sources := [384] },
  { frame := 391, destination := 296, sources := [531] }, { frame := 392, destination := 369, sources := [598] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-cddade364a420928"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk62`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3530)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 393, destination := 337, sources := [551] }, { frame := 394, destination := 487, sources := [528] },
  { frame := 395, destination := 492, sources := [523] }, { frame := 396, destination := 225, sources := [522] },
  { frame := 397, destination := 342, sources := [597] }, { frame := 398, destination := 427, sources := [584] },
  { frame := 399, destination := 557, sources := [442] }, { frame := 400, destination := 556, sources := [279] },
  { frame := 401, destination := 519, sources := [269] }, { frame := 402, destination := 612, sources := [431] },
  { frame := 403, destination := 268, sources := [553] }, { frame := 404, destination := 389, sources := [564] },
  { frame := 405, destination := 563, sources := [315] }, { frame := 406, destination := 562, sources := [440] },
  { frame := 407, destination := 544, sources := [285] }, { frame := 408, destination := 524, sources := [261] },
  { frame := 409, destination := 298, sources := [559] }, { frame := 410, destination := 379, sources := [605] },
  { frame := 411, destination := 343, sources := [540] }, { frame := 412, destination := 448, sources := [617] },
  { frame := 413, destination := 378, sources := [567] }, { frame := 414, destination := 362, sources := [566] },
  { frame := 415, destination := 346, sources := [602] }, { frame := 416, destination := 437, sources := [599] },
  { frame := 417, destination := 607, sources := [395] }, { frame := 418, destination := 538, sources := [270] },
  { frame := 419, destination := 537, sources := [299] }, { frame := 420, destination := 554, sources := [388] },
  { frame := 421, destination := 280, sources := [596] }, { frame := 422, destination := 401, sources := [582] },
  { frame := 423, destination := 581, sources := [303] }, { frame := 424, destination := 594, sources := [390] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-a24bf7d058a93099"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk63`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3563)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 425, destination := 589, sources := [412] }, { frame := 426, destination := 542, sources := [292] },
  { frame := 427, destination := 294, sources := [614] }, { frame := 428, destination := 353, sources := [547] },
  { frame := 429, destination := 453, sources := [587] }, { frame := 430, destination := 454, sources := [621] },
  { frame := 431, destination := 331, sources := [585] }, { frame := 432, destination := 328, sources := [558] },
  { frame := 433, destination := 334, sources := [583] }, { frame := 434, destination := 481, sources := [580] },
  { frame := 435, destination := 624, sources := [376] }, { frame := 436, destination := 613, sources := [249] },
  { frame := 437, destination := 618, sources := [335] }, { frame := 438, destination := 619, sources := [350] },
  { frame := 439, destination := 244, sources := [579] }, { frame := 440, destination := 527, sources := [391] },
  { frame := 441, destination := 367, sources := [576] }, { frame := 442, destination := 392, sources := [552] },
  { frame := 443, destination := 588, sources := [383] }, { frame := 444, destination := 571, sources := [513] },
  { frame := 445, destination := 302, sources := [560] }, { frame := 446, destination := 578, sources := [397] },
  { frame := 447, destination := 445, sources := [529] }, { frame := 448, destination := 374, sources := [604] },
  { frame := 449, destination := 603, sources := [318] }, { frame := 450, destination := 565, sources := [422] },
  { frame := 451, destination := 304, sources := [545] }, { frame := 452, destination := 457, sources := [572] },
  { frame := 453, destination := 626, sources := [339] }, { frame := 454, destination := 627, sources := [370] },
  { frame := 455, destination := 660, sources := [330] }, { frame := 456, destination := 608, sources := [446] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-eb823ed6c0976eae"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk64`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3596)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 457, destination := 236, sources := [575] }, { frame := 458, destination := 423, sources := [591] },
  { frame := 459, destination := 568, sources := [441] }, { frame := 460, destination := 616, sources := [406] },
  { frame := 461, destination := 314, sources := [615] }, { frame := 462, destination := 275, sources := [577] },
  { frame := 463, destination := 260, sources := [592] }, { frame := 464, destination := 419, sources := [593] },
  { frame := 465, destination := 283, sources := [635] }, { frame := 466, destination := 255, sources := [634] },
  { frame := 467, destination := 586, sources := [438] }, { frame := 468, destination := 620, sources := [434] },
  { frame := 469, destination := 266, sources := [590] }, { frame := 470, destination := 447, sources := [630] },
  { frame := 471, destination := 629, sources := [231] }, { frame := 472, destination := 609, sources := [230] },
  { frame := 473, destination := 655, sources := [458] }, { frame := 474, destination := 611, sources := [224] },
  { frame := 475, destination := 226, sources := [625] }, { frame := 476, destination := 439, sources := [636] },
  { frame := 477, destination := 429, sources := [653] }, { frame := 478, destination := 267, sources := [622] },
  { frame := 479, destination := 633, sources := [306] }, { frame := 480, destination := 632, sources := [418] },
  { frame := 481, destination := 276, sources := [631] }, { frame := 482, destination := 425, sources := [642] },
  { frame := 483, destination := 263, sources := [641] }, { frame := 484, destination := 262, sources := [640] },
  { frame := 485, destination := 639, sources := [424] }, { frame := 486, destination := 638, sources := [300] },
  { frame := 487, destination := 258, sources := [637] }, { frame := 488, destination := 461, sources := [648] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-6f54a22d5083cca1"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk65`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3629)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 489, destination := 647, sources := [460] }, { frame := 490, destination := 646, sources := [449] },
  { frame := 491, destination := 645, sources := [239] }, { frame := 492, destination := 644, sources := [450] },
  { frame := 493, destination := 238, sources := [643] }, { frame := 494, destination := 654, sources := [399] },
  { frame := 495, destination := 301, sources := [623] }, { frame := 496, destination := 414, sources := [652] },
  { frame := 497, destination := 651, sources := [410] }, { frame := 498, destination := 650, sources := [289] },
  { frame := 499, destination := 288, sources := [649] }, { frame := 500, destination := 628, sources := [393] },
  { frame := 501, destination := 659, sources := [317] }, { frame := 502, destination := 658, sources := [408] },
  { frame := 503, destination := 404, sources := [657] }, { frame := 504, destination := 282, sources := [656] },
  { frame := 505, destination := 316, sources := [610] },
  { frame := 506, destination := 349, sources := [6, 56, 233, 319, 322, 340, 462, 463] },
  { frame := 506, destination := 340, sources := [233, 241, 319, 349, 464] },
  { frame := 506, destination := 241, sources := [6, 56, 233, 319, 322, 463, 464] },
  { frame := 507, destination := 360, sources := [68, 69, 357, 358, 381] },
  { frame := 507, destination := 381, sources := [11, 69, 228, 358, 360, 465] },
  { frame := 508, destination := 385, sources := [43, 57, 297, 416, 433, 466, 467] },
  { frame := 508, destination := 368, sources := [365, 385, 433, 466] },
  { frame := 79, destination := 444, sources := [470] },
  { frame := 509, destination := 444, sources := [17, 271, 293, 352, 413, 468, 471] },
  { frame := 509, destination := 413, sources := [17, 271, 293, 352, 371, 471] },
  { frame := 470, destination := 436, sources := [447] }, { frame := 348, destination := 349, sources := [223] },
  { frame := 330, destination := 228, sources := [240] }, { frame := 455, destination := 415, sources := [660] },
  { frame := 456, destination := 227, sources := [608] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-701043954c54178a"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk66`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3662)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 490, destination := 311, sources := [646] }, { frame := 331, destination := 360, sources := [504] },
  { frame := 349, destination := 322, sources := [486] }, { frame := 491, destination := 295, sources := [645] },
  { frame := 438, destination := 382, sources := [619] }, { frame := 478, destination := 435, sources := [267] },
  { frame := 364, destination := 396, sources := [520] }, { frame := 483, destination := 237, sources := [263] },
  { frame := 418, destination := 433, sources := [538] }, { frame := 485, destination := 284, sources := [639] },
  { frame := 380, destination := 293, sources := [482] }, { frame := 382, destination := 271, sources := [574] },
  { frame := 399, destination := 257, sources := [557] }, { frame := 420, destination := 368, sources := [554] },
  { frame := 458, destination := 459, sources := [423] }, { frame := 465, destination := 254, sources := [283] },
  { frame := 401, destination := 273, sources := [519] }, { frame := 461, destination := 259, sources := [314] },
  { frame := 441, destination := 307, sources := [367] }, { frame := 444, destination := 248, sources := [571] },
  { frame := 406, destination := 327, sources := [562] }, { frame := 497, destination := 245, sources := [651] },
  { frame := 426, destination := 416, sources := [542] }, { frame := 447, destination := 451, sources := [445] },
  { frame := 501, destination := 290, sources := [659] }, { frame := 371, destination := 333, sources := [525] },
  { frame := 372, destination := 278, sources := [595] }, { frame := 449, destination := 398, sources := [603] },
  { frame := 390, destination := 413, sources := [606] }, { frame := 517, destination := 413, sources := [469] },
  { frame := 408, destination := 377, sources := [524] }, { frame := 332, destination := 381, sources := [375] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-3738122d3222df28"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk67`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3695)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 340, destination := 358, sources := [409] }, { frame := 341, destination := 357, sources := [430] },
  { frame := 336, destination := 229, sources := [509] }, { frame := 374, destination := 332, sources := [222] },
  { frame := 376, destination := 407, sources := [363] }, { frame := 392, destination := 444, sources := [369] },
  { frame := 393, destination := 352, sources := [337] }, { frame := 428, destination := 385, sources := [353] },
  { frame := 411, destination := 386, sources := [343] }, { frame := 412, destination := 287, sources := [448] },
  { frame := 432, destination := 365, sources := [328] }, { frame := 351, destination := 340, sources := [305] },
  { frame := 352, destination := 233, sources := [344] }, { frame := 357, destination := 319, sources := [387] },
  { frame := 361, destination := 241, sources := [320] }, { frame := 505, destination := 250, sources := [316] },
  { frame := 391, destination := 371, sources := [296] }, { frame := 427, destination := 297, sources := [294] },
  { frame := 499, destination := 394, sources := [288] }, { frame := 481, destination := 452, sources := [276] },
  { frame := 367, destination := 443, sources := [252] }, { frame := 469, destination := 428, sources := [266] },
  { frame := 475, destination := 277, sources := [226] }, { frame := 439, destination := 411, sources := [244] },
  { frame := 328, destination := 472, sources := [234] }, { frame := 510, destination := 472, sources := [240, 360] },
  { frame := 346, destination := 473, sources := [246] }, { frame := 511, destination := 473, sources := [349, 486] },
  { frame := 335, destination := 474, sources := [400] }, { frame := 512, destination := 474, sources := [381, 509] },
  { frame := 394, destination := 475, sources := [487] }, { frame := 513, destination := 475, sources := [444, 337] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-80e8e42cfc7d5e1e"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk68`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3728)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 431, destination := 476, sources := [331] }, { frame := 514, destination := 476, sources := [385, 328] },
  { frame := 350, destination := 477, sources := [341] }, { frame := 515, destination := 477, sources := [340, 233] },
  { frame := 359, destination := 478, sources := [495] }, { frame := 516, destination := 478, sources := [387, 241] },
  { frame := 388, destination := 479, sources := [561] }, { frame := 517, destination := 479, sources := [413, 296] },
  { frame := 421, destination := 480, sources := [280] }, { frame := 518, destination := 480, sources := [538, 368] },
  { frame := 636, destination := 111, sources := [476, 477, 478, 479, 480] },
  { frame := 636, destination := 112, sources := [473, 474, 476] },
  { frame := 636, destination := 113, sources := [472, 473, 474, 475, 476, 477, 478, 479, 480] },
  { frame := 636, destination := 114, sources := [472, 475, 476] },
  { frame := 636, destination := 115, sources := [472, 474, 476] },
  { frame := 636, destination := 116, sources := [472, 473, 476, 477, 478, 479, 480] },
  { frame := 636, destination := 117, sources := [473, 475, 476] },
  { frame := 636, destination := 118, sources := [474, 475, 476, 477, 478, 479, 480] },
  { frame := 636, destination := 119, sources := [473, 474, 476, 477, 478] },
  { frame := 636, destination := 120, sources := [475, 477, 478, 479, 480] },
  { frame := 636, destination := 121, sources := [472, 473, 474, 475, 476, 479, 480] },
  { frame := 636, destination := 122, sources := [472, 473, 475, 477, 478, 479, 480] },
  { frame := 636, destination := 123, sources := [472, 474, 476, 477, 478] },
  { frame := 636, destination := 124, sources := [474, 475, 476, 479, 480] },
  { frame := 636, destination := 125, sources := [472, 475, 476, 478, 479] },
  { frame := 636, destination := 126, sources := [472, 477, 479] },
  { frame := 636, destination := 127, sources := [473, 474, 475, 477, 479] },
  { frame := 636, destination := 128, sources := [473, 474, 476, 478, 479] },
  { frame := 636, destination := 129, sources := [474, 478, 480] },
  { frame := 636, destination := 130, sources := [474, 475, 476, 477, 480] },
  { frame := 636, destination := 131, sources := [472, 473, 476, 477, 480] },
  { frame := 636, destination := 132, sources := [472, 473, 475, 478, 480] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-339a59bb54a5cb46"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk69`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3761)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 636, destination := 133, sources := [472, 473, 474, 477, 480] },
  { frame := 636, destination := 134, sources := [472, 475, 476, 477, 479] },
  { frame := 636, destination := 135, sources := [472, 473, 474, 475, 476, 478, 480] },
  { frame := 636, destination := 136, sources := [472, 478, 479] },
  { frame := 636, destination := 137, sources := [472, 473, 476, 478, 480] },
  { frame := 636, destination := 138, sources := [472, 474, 475, 478, 479] },
  { frame := 636, destination := 139, sources := [472, 473, 475, 477, 480] },
  { frame := 636, destination := 140, sources := [472, 474, 476, 477, 479] },
  { frame := 636, destination := 141, sources := [472, 473, 476, 477, 479] },
  { frame := 636, destination := 142, sources := [473, 477, 480] },
  { frame := 636, destination := 143, sources := [474, 478, 479] },
  { frame := 636, destination := 144, sources := [472, 474, 476, 478, 480] },
  { frame := 636, destination := 145, sources := [472, 473, 474, 478, 479] },
  { frame := 636, destination := 146, sources := [473, 474, 476, 478, 480] },
  { frame := 636, destination := 147, sources := [476, 477, 479] },
  { frame := 636, destination := 148, sources := [472, 477, 480] },
  { frame := 636, destination := 149, sources := [474, 477, 479] },
  { frame := 636, destination := 150, sources := [473, 475, 476, 477, 480] },
  { frame := 636, destination := 151, sources := [472, 474, 476, 477, 480] },
  { frame := 636, destination := 152, sources := [472, 473, 475, 477, 479] },
  { frame := 636, destination := 153, sources := [472, 475, 476, 477, 480] },
  { frame := 636, destination := 154, sources := [472, 473, 474, 477, 479] },
  { frame := 636, destination := 155, sources := [475, 477, 479] },
  { frame := 636, destination := 156, sources := [473, 474, 476, 477, 480] },
  { frame := 636, destination := 157, sources := [472, 474, 475, 477, 478, 479, 480] },
  { frame := 636, destination := 158, sources := [472, 474, 476, 479, 480] },
  { frame := 636, destination := 159, sources := [474, 475, 476, 477, 478] },
  { frame := 636, destination := 160, sources := [476, 477, 478] },
  { frame := 636, destination := 161, sources := [472, 477, 478, 479, 480] },
  { frame := 636, destination := 162, sources := [472, 475, 476, 479, 480] },
  { frame := 636, destination := 163, sources := [473, 474, 475, 479, 480] },
  { frame := 636, destination := 164, sources := [475, 477, 478] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e58af66372143d50"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk70`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3794)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 636, destination := 165, sources := [473, 474, 476, 477, 478, 479, 480] },
  { frame := 636, destination := 166, sources := [472, 479, 480] },
  { frame := 636, destination := 167, sources := [472, 473, 474, 475, 476] },
  { frame := 636, destination := 168, sources := [472, 475, 476, 477, 478, 479, 480] },
  { frame := 636, destination := 169, sources := [472, 473, 474, 477, 478] },
  { frame := 636, destination := 170, sources := [472, 474, 475, 476, 477, 479, 480] },
  { frame := 636, destination := 171, sources := [473, 474, 478, 479, 480] },
  { frame := 636, destination := 172, sources := [472, 473, 475, 476, 478] },
  { frame := 636, destination := 173, sources := [472, 475, 478, 479, 480] },
  { frame := 636, destination := 174, sources := [473, 476, 477, 479, 480] },
  { frame := 636, destination := 175, sources := [474, 476, 478] },
  { frame := 636, destination := 176, sources := [472, 473, 474, 475, 477] },
  { frame := 636, destination := 177, sources := [473, 474, 475, 476, 478, 479, 480] },
  { frame := 636, destination := 178, sources := [472, 473, 474, 476, 477] },
  { frame := 636, destination := 179, sources := [472, 475, 477, 479, 480] },
  { frame := 636, destination := 180, sources := [472, 473, 475, 476, 477] },
  { frame := 636, destination := 181, sources := [472, 474, 477, 479, 480] },
  { frame := 636, destination := 182, sources := [474, 475, 478] },
  { frame := 636, destination := 183, sources := [473, 476, 478, 479, 480] },
  { frame := 636, destination := 184, sources := [472, 475, 480] },
  { frame := 636, destination := 185, sources := [472, 476, 477, 478, 480] },
  { frame := 636, destination := 186, sources := [473, 474, 475, 476, 477, 478, 480] },
  { frame := 636, destination := 187, sources := [473, 474, 480] },
  { frame := 636, destination := 188, sources := [473, 476, 477, 478, 480] },
  { frame := 636, destination := 189, sources := [473, 475, 480] },
  { frame := 636, destination := 190, sources := [472, 474, 480] },
  { frame := 636, destination := 191, sources := [472, 474, 475, 476, 477, 478, 480] },
  { frame := 636, destination := 192, sources := [473, 474, 475, 476, 480] },
  { frame := 636, destination := 193, sources := [473, 474, 477, 478, 480] },
  { frame := 636, destination := 194, sources := [475, 476, 477, 478, 479] },
  { frame := 636, destination := 195, sources := [472, 474, 477, 478, 480] },
  { frame := 636, destination := 196, sources := [472, 473, 475, 476, 477, 478, 479] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2fca826fb5616849"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk71`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3827)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 636, destination := 197, sources := [472, 474, 475, 476, 480] },
  { frame := 636, destination := 198, sources := [472, 473, 479] },
  { frame := 636, destination := 199, sources := [473, 475, 479] },
  { frame := 636, destination := 200, sources := [472, 473, 475, 476, 480] },
  { frame := 636, destination := 201, sources := [472, 474, 475, 476, 477, 478, 479] },
  { frame := 636, destination := 202, sources := [474, 475, 477, 478, 480] },
  { frame := 636, destination := 203, sources := [472, 476, 477, 478, 479] },
  { frame := 636, destination := 204, sources := [477, 478, 480] },
  { frame := 636, destination := 205, sources := [473, 474, 479] },
  { frame := 636, destination := 206, sources := [472, 473, 474, 476, 480] },
  { frame := 636, destination := 207, sources := [474, 476, 477, 478, 480] },
  { frame := 636, destination := 208, sources := [473, 475, 477, 478, 479] },
  { frame := 636, destination := 209, sources := [472, 474, 477, 478, 479] },
  { frame := 636, destination := 210, sources := [472, 473, 475, 476, 477, 478, 480] },
  { frame := 636, destination := 211, sources := [472, 473, 474, 475, 480] },
  { frame := 636, destination := 212, sources := [472, 476, 479] },
  { frame := 636, destination := 213, sources := [473, 474, 475, 476, 479] },
  { frame := 636, destination := 214, sources := [472, 473, 475, 476, 478, 479, 480] },
  { frame := 636, destination := 215, sources := [472, 473, 477, 479, 480] },
  { frame := 636, destination := 216, sources := [473, 475, 478] },
  { frame := 636, destination := 217, sources := [473, 476, 477] },
  { frame := 636, destination := 218, sources := [477, 479, 480] },
  { frame := 636, destination := 219, sources := [475, 476, 478, 479, 480] },
  { frame := 636, destination := 220, sources := [472, 476, 477] },
  { frame := 636, destination := 221, sources := [472, 475, 478] },
  { frame := 127, destination := 111, sources := [3] }, { frame := 217, destination := 112, sources := [106] },
  { frame := 233, destination := 113, sources := [103] }, { frame := 235, destination := 115, sources := [109] },
  { frame := 11, destination := 116, sources := [9] }, { frame := 114, destination := 117, sources := [5] },
  { frame := 214, destination := 118, sources := [108] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-1a7135e11d09ec59"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk72`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3860)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 252, destination := 119, sources := [12] }, { frame := 198, destination := 121, sources := [107] },
  { frame := 2, destination := 122, sources := [0] }, { frame := 249, destination := 123, sources := [8] },
  { frame := 199, destination := 124, sources := [104] }, { frame := 239, destination := 125, sources := [90] },
  { frame := 139, destination := 126, sources := [96] }, { frame := 246, destination := 127, sources := [93] },
  { frame := 184, destination := 128, sources := [92] }, { frame := 247, destination := 129, sources := [88] },
  { frame := 155, destination := 130, sources := [89] }, { frame := 241, destination := 131, sources := [95] },
  { frame := 168, destination := 132, sources := [26] }, { frame := 135, destination := 134, sources := [91] },
  { frame := 222, destination := 135, sources := [29] }, { frame := 229, destination := 136, sources := [98] },
  { frame := 165, destination := 137, sources := [21] }, { frame := 154, destination := 138, sources := [97] },
  { frame := 226, destination := 139, sources := [25] }, { frame := 223, destination := 140, sources := [101] },
  { frame := 143, destination := 141, sources := [41] }, { frame := 257, destination := 142, sources := [81] },
  { frame := 205, destination := 143, sources := [85] }, { frame := 188, destination := 144, sources := [38] },
  { frame := 202, destination := 145, sources := [32] }, { frame := 160, destination := 146, sources := [74] },
  { frame := 173, destination := 147, sources := [80] }, { frame := 259, destination := 148, sources := [86] },
  { frame := 186, destination := 149, sources := [77] }, { frame := 211, destination := 150, sources := [79] },
  { frame := 263, destination := 151, sources := [45] }, { frame := 145, destination := 152, sources := [75] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-1fbc617dd8aa190f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk73`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3893)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 207, destination := 153, sources := [39] }, { frame := 159, destination := 154, sources := [35] },
  { frame := 172, destination := 155, sources := [36] }, { frame := 265, destination := 156, sources := [73] },
  { frame := 124, destination := 158, sources := [58] }, { frame := 121, destination := 159, sources := [47] },
  { frame := 149, destination := 160, sources := [53] }, { frame := 62, destination := 161, sources := [60] },
  { frame := 181, destination := 162, sources := [64] }, { frame := 119, destination := 163, sources := [48] },
  { frame := 147, destination := 164, sources := [59] }, { frame := 48, destination := 165, sources := [46] },
  { frame := 178, destination := 166, sources := [51] }, { frame := 56, destination := 167, sources := [54] },
  { frame := 67, destination := 168, sources := [65] }, { frame := 120, destination := 169, sources := [52] },
  { frame := 150, destination := 170, sources := [70] }, { frame := 74, destination := 173, sources := [72] },
  { frame := 63, destination := 174, sources := [61] }, { frame := 180, destination := 175, sources := [71] },
  { frame := 68, destination := 176, sources := [66] }, { frame := 52, destination := 178, sources := [50] },
  { frame := 131, destination := 179, sources := [63] }, { frame := 129, destination := 180, sources := [62] },
  { frame := 146, destination := 181, sources := [49] }, { frame := 179, destination := 182, sources := [55] },
  { frame := 264, destination := 184, sources := [78] }, { frame := 144, destination := 186, sources := [82] },
  { frame := 206, destination := 187, sources := [42] }, { frame := 189, destination := 188, sources := [87] },
  { frame := 260, destination := 189, sources := [40] }, { frame := 209, destination := 190, sources := [76] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-67b009238f7f2bf7"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk74`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3926)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 174, destination := 191, sources := [84] }, { frame := 256, destination := 192, sources := [31] },
  { frame := 140, destination := 193, sources := [30] }, { frame := 204, destination := 194, sources := [34] },
  { frame := 170, destination := 195, sources := [44] }, { frame := 201, destination := 196, sources := [83] },
  { frame := 254, destination := 197, sources := [37] }, { frame := 185, destination := 198, sources := [33] },
  { frame := 242, destination := 199, sources := [18] }, { frame := 156, destination := 200, sources := [27] },
  { frame := 240, destination := 201, sources := [20] }, { frame := 134, destination := 202, sources := [15] },
  { frame := 182, destination := 203, sources := [22] }, { frame := 243, destination := 204, sources := [16] },
  { frame := 166, destination := 205, sources := [102] }, { frame := 236, destination := 206, sources := [14] },
  { frame := 137, destination := 207, sources := [23] }, { frame := 152, destination := 208, sources := [19] },
  { frame := 228, destination := 209, sources := [100] }, { frame := 220, destination := 210, sources := [24] },
  { frame := 224, destination := 211, sources := [28] }, { frame := 219, destination := 212, sources := [99] },
  { frame := 167, destination := 213, sources := [94] }, { frame := 230, destination := 214, sources := [4] },
  { frame := 194, destination := 215, sources := [13] }, { frame := 250, destination := 216, sources := [110] },
  { frame := 212, destination := 217, sources := [1] }, { frame := 195, destination := 218, sources := [10] },
  { frame := 215, destination := 219, sources := [7] }, { frame := 231, destination := 220, sources := [2] },
  { frame := 251, destination := 221, sources := [105] }, { frame := 506, destination := 52, sources := [47] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e37e5a7f1b0090f7"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk75`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3959)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 506, destination := 52, sources := [56] }, { frame := 506, destination := 52, sources := [5] },
  { frame := 506, destination := 52, sources := [54] }, { frame := 506, destination := 52, sources := [9] },
  { frame := 506, destination := 52, sources := [58] }, { frame := 506, destination := 52, sources := [6] },
  { frame := 506, destination := 52, sources := [46] }, { frame := 506, destination := 52, sources := [48] },
  { frame := 506, destination := 47, sources := [46] }, { frame := 506, destination := 47, sources := [48] },
  { frame := 506, destination := 5, sources := [9] }, { frame := 506, destination := 9, sources := [6] },
  { frame := 506, destination := 58, sources := [48] }, { frame := 506, destination := 48, sources := [52] },
  { frame := 506, destination := 48, sources := [5] }, { frame := 506, destination := 48, sources := [6] },
  { frame := 506, destination := 46, sources := [52] }, { frame := 506, destination := 46, sources := [56] },
  { frame := 506, destination := 46, sources := [54] }, { frame := 506, destination := 58, sources := [52] },
  { frame := 506, destination := 9, sources := [52] }, { frame := 506, destination := 54, sources := [52] },
  { frame := 506, destination := 5, sources := [52] }, { frame := 506, destination := 56, sources := [52] },
  { frame := 506, destination := 47, sources := [52] }, { frame := 507, destination := 68, sources := [11] },
  { frame := 507, destination := 68, sources := [63] }, { frame := 507, destination := 68, sources := [72] },
  { frame := 507, destination := 68, sources := [0] }, { frame := 507, destination := 68, sources := [61] },
  { frame := 507, destination := 3, sources := [62] }, { frame := 507, destination := 465, sources := [69] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-3b87019b059b1a6f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk76`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L3992)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 507, destination := 465, sources := [63] }, { frame := 507, destination := 465, sources := [0] },
  { frame := 507, destination := 69, sources := [11] }, { frame := 507, destination := 69, sources := [62] },
  { frame := 507, destination := 63, sources := [72] }, { frame := 507, destination := 63, sources := [62] },
  { frame := 507, destination := 63, sources := [0] }, { frame := 507, destination := 61, sources := [3] },
  { frame := 507, destination := 61, sources := [69] }, { frame := 507, destination := 61, sources := [72] },
  { frame := 507, destination := 61, sources := [62] }, { frame := 507, destination := 61, sources := [0] },
  { frame := 507, destination := 0, sources := [68] }, { frame := 507, destination := 0, sources := [69] },
  { frame := 507, destination := 62, sources := [68] }, { frame := 507, destination := 62, sources := [3] },
  { frame := 507, destination := 62, sources := [69] }, { frame := 507, destination := 72, sources := [68] },
  { frame := 507, destination := 72, sources := [3] }, { frame := 507, destination := 63, sources := [3] },
  { frame := 507, destination := 63, sources := [69] }, { frame := 507, destination := 11, sources := [68] },
  { frame := 507, destination := 11, sources := [3] }, { frame := 507, destination := 11, sources := [69] },
  { frame := 507, destination := 69, sources := [68] }, { frame := 507, destination := 465, sources := [68] },
  { frame := 507, destination := 465, sources := [3] }, { frame := 507, destination := 3, sources := [68] },
  { frame := 519, destination := 59, sources := [49] }, { frame := 519, destination := 59, sources := [30] },
  { frame := 519, destination := 59, sources := [53] }, { frame := 519, destination := 59, sources := [41] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-5bba896070e4edac"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk77`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4025)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 519, destination := 59, sources := [82] }, { frame := 519, destination := 59, sources := [70] },
  { frame := 519, destination := 59, sources := [75] }, { frame := 519, destination := 15, sources := [91] },
  { frame := 519, destination := 15, sources := [23] }, { frame := 519, destination := 15, sources := [96] },
  { frame := 519, destination := 49, sources := [41] }, { frame := 519, destination := 49, sources := [75] },
  { frame := 519, destination := 30, sources := [82] }, { frame := 519, destination := 30, sources := [70] },
  { frame := 519, destination := 30, sources := [75] }, { frame := 519, destination := 53, sources := [41] },
  { frame := 519, destination := 53, sources := [75] }, { frame := 519, destination := 41, sources := [82] },
  { frame := 519, destination := 82, sources := [70] }, { frame := 519, destination := 75, sources := [59] },
  { frame := 519, destination := 75, sources := [15] }, { frame := 519, destination := 75, sources := [82] },
  { frame := 519, destination := 75, sources := [70] }, { frame := 519, destination := 70, sources := [59] },
  { frame := 519, destination := 70, sources := [15] }, { frame := 519, destination := 82, sources := [15] },
  { frame := 519, destination := 82, sources := [53] }, { frame := 519, destination := 96, sources := [59] },
  { frame := 519, destination := 96, sources := [23] }, { frame := 519, destination := 41, sources := [59] },
  { frame := 519, destination := 41, sources := [15] }, { frame := 519, destination := 23, sources := [59] },
  { frame := 519, destination := 23, sources := [15] }, { frame := 519, destination := 53, sources := [59] },
  { frame := 519, destination := 53, sources := [15] }, { frame := 519, destination := 53, sources := [49] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-3de77b7ff5a6bda1"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk78`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4058)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 519, destination := 91, sources := [59] }, { frame := 519, destination := 30, sources := [15] },
  { frame := 519, destination := 30, sources := [49] }, { frame := 519, destination := 49, sources := [59] },
  { frame := 519, destination := 49, sources := [15] }, { frame := 519, destination := 15, sources := [59] },
  { frame := 508, destination := 89, sources := [27] }, { frame := 508, destination := 89, sources := [74] },
  { frame := 508, destination := 89, sources := [43] }, { frame := 508, destination := 89, sources := [19] },
  { frame := 508, destination := 89, sources := [35] }, { frame := 508, destination := 89, sources := [97] },
  { frame := 508, destination := 66, sources := [74] }, { frame := 508, destination := 66, sources := [43] },
  { frame := 508, destination := 66, sources := [19] }, { frame := 508, destination := 66, sources := [35] },
  { frame := 508, destination := 66, sources := [57] }, { frame := 508, destination := 66, sources := [65] },
  { frame := 508, destination := 66, sources := [97] }, { frame := 508, destination := 466, sources := [43] },
  { frame := 508, destination := 466, sources := [97] }, { frame := 508, destination := 74, sources := [43] },
  { frame := 508, destination := 74, sources := [19] }, { frame := 508, destination := 74, sources := [97] },
  { frame := 508, destination := 43, sources := [19] }, { frame := 508, destination := 43, sources := [97] },
  { frame := 508, destination := 35, sources := [97] }, { frame := 508, destination := 97, sources := [66] },
  { frame := 508, destination := 97, sources := [27] }, { frame := 508, destination := 97, sources := [19] },
  { frame := 508, destination := 65, sources := [89] }, { frame := 508, destination := 57, sources := [89] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2d1df7296bf01edb"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk79`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4091)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 508, destination := 35, sources := [89] }, { frame := 508, destination := 35, sources := [66] },
  { frame := 508, destination := 35, sources := [27] }, { frame := 508, destination := 35, sources := [74] },
  { frame := 508, destination := 43, sources := [89] }, { frame := 508, destination := 43, sources := [66] },
  { frame := 508, destination := 74, sources := [89] }, { frame := 508, destination := 74, sources := [66] },
  { frame := 508, destination := 466, sources := [89] }, { frame := 508, destination := 466, sources := [66] },
  { frame := 508, destination := 27, sources := [66] }, { frame := 520, destination := 55, sources := [44] },
  { frame := 520, destination := 55, sources := [84] }, { frame := 520, destination := 55, sources := [51] },
  { frame := 520, destination := 55, sources := [36] }, { frame := 520, destination := 55, sources := [71] },
  { frame := 520, destination := 55, sources := [64] }, { frame := 520, destination := 55, sources := [80] },
  { frame := 520, destination := 44, sources := [84] }, { frame := 520, destination := 44, sources := [94] },
  { frame := 520, destination := 44, sources := [21] }, { frame := 520, destination := 44, sources := [36] },
  { frame := 520, destination := 44, sources := [80] }, { frame := 520, destination := 44, sources := [102] },
  { frame := 520, destination := 44, sources := [26] }, { frame := 520, destination := 84, sources := [71] },
  { frame := 520, destination := 84, sources := [64] }, { frame := 520, destination := 94, sources := [21] },
  { frame := 520, destination := 21, sources := [26] }, { frame := 520, destination := 36, sources := [80] },
  { frame := 520, destination := 80, sources := [102] }, { frame := 520, destination := 26, sources := [55] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-a126ebad80e58baf"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk80`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4124)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 520, destination := 26, sources := [94] }, { frame := 520, destination := 26, sources := [51] },
  { frame := 520, destination := 26, sources := [36] }, { frame := 520, destination := 26, sources := [102] },
  { frame := 520, destination := 102, sources := [55] }, { frame := 520, destination := 102, sources := [94] },
  { frame := 520, destination := 80, sources := [55] }, { frame := 520, destination := 80, sources := [21] },
  { frame := 520, destination := 64, sources := [44] }, { frame := 520, destination := 64, sources := [51] },
  { frame := 520, destination := 71, sources := [44] }, { frame := 520, destination := 71, sources := [51] },
  { frame := 520, destination := 36, sources := [55] }, { frame := 520, destination := 36, sources := [44] },
  { frame := 520, destination := 51, sources := [44] }, { frame := 520, destination := 21, sources := [55] },
  { frame := 520, destination := 21, sources := [94] }, { frame := 520, destination := 94, sources := [55] },
  { frame := 520, destination := 84, sources := [44] }, { frame := 520, destination := 44, sources := [55] },
  { frame := 509, destination := 87, sources := [92] }, { frame := 509, destination := 87, sources := [67] },
  { frame := 509, destination := 87, sources := [38] }, { frame := 509, destination := 87, sources := [22] },
  { frame := 509, destination := 87, sources := [60] }, { frame := 509, destination := 87, sources := [50] },
  { frame := 509, destination := 87, sources := [77] }, { frame := 509, destination := 92, sources := [22] },
  { frame := 509, destination := 92, sources := [33] }, { frame := 509, destination := 17, sources := [33] },
  { frame := 509, destination := 38, sources := [33] }, { frame := 509, destination := 77, sources := [87] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-dbfc69df3a573764"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk81`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4157)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 509, destination := 77, sources := [17] }, { frame := 509, destination := 77, sources := [33] },
  { frame := 509, destination := 468, sources := [87] }, { frame := 509, destination := 468, sources := [92] },
  { frame := 509, destination := 468, sources := [38] }, { frame := 509, destination := 468, sources := [33] },
  { frame := 509, destination := 50, sources := [87] }, { frame := 509, destination := 50, sources := [17] },
  { frame := 509, destination := 50, sources := [67] }, { frame := 509, destination := 60, sources := [87] },
  { frame := 509, destination := 60, sources := [17] }, { frame := 509, destination := 33, sources := [87] },
  { frame := 509, destination := 33, sources := [22] }, { frame := 509, destination := 38, sources := [87] },
  { frame := 509, destination := 38, sources := [17] }, { frame := 509, destination := 67, sources := [87] },
  { frame := 509, destination := 67, sources := [17] }, { frame := 509, destination := 17, sources := [87] },
  { frame := 509, destination := 92, sources := [87] }, { frame := 521, destination := 83, sources := [10] },
  { frame := 521, destination := 83, sources := [79] }, { frame := 521, destination := 83, sources := [76] },
  { frame := 521, destination := 83, sources := [104] }, { frame := 521, destination := 83, sources := [13] },
  { frame := 521, destination := 83, sources := [34] }, { frame := 521, destination := 83, sources := [42] },
  { frame := 521, destination := 83, sources := [107] }, { frame := 521, destination := 83, sources := [85] },
  { frame := 521, destination := 83, sources := [32] }, { frame := 521, destination := 10, sources := [39] },
  { frame := 521, destination := 10, sources := [107] }, { frame := 521, destination := 79, sources := [76] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-34ebbb4d38280cd1"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk82`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4190)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 521, destination := 79, sources := [104] }, { frame := 521, destination := 79, sources := [13] },
  { frame := 521, destination := 79, sources := [42] }, { frame := 521, destination := 79, sources := [85] },
  { frame := 521, destination := 76, sources := [42] }, { frame := 521, destination := 76, sources := [107] },
  { frame := 521, destination := 104, sources := [34] }, { frame := 521, destination := 104, sources := [107] },
  { frame := 521, destination := 13, sources := [34] }, { frame := 521, destination := 13, sources := [39] },
  { frame := 521, destination := 13, sources := [85] }, { frame := 521, destination := 34, sources := [42] },
  { frame := 521, destination := 34, sources := [39] }, { frame := 521, destination := 32, sources := [83] },
  { frame := 521, destination := 32, sources := [34] }, { frame := 521, destination := 32, sources := [42] },
  { frame := 521, destination := 85, sources := [10] }, { frame := 521, destination := 85, sources := [79] },
  { frame := 521, destination := 107, sources := [83] }, { frame := 521, destination := 107, sources := [79] },
  { frame := 521, destination := 107, sources := [104] }, { frame := 521, destination := 107, sources := [13] },
  { frame := 521, destination := 107, sources := [42] }, { frame := 521, destination := 39, sources := [83] },
  { frame := 521, destination := 42, sources := [83] }, { frame := 521, destination := 34, sources := [83] },
  { frame := 521, destination := 34, sources := [104] }, { frame := 521, destination := 13, sources := [83] },
  { frame := 521, destination := 104, sources := [83] }, { frame := 521, destination := 104, sources := [10] },
  { frame := 521, destination := 76, sources := [83] }, { frame := 521, destination := 76, sources := [10] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-f07bccdfe5f044e7"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk83`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4223)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 521, destination := 79, sources := [10] }, { frame := 521, destination := 10, sources := [83] },
  { frame := 522, destination := 28, sources := [1] }, { frame := 522, destination := 28, sources := [100] },
  { frame := 522, destination := 28, sources := [101] }, { frame := 522, destination := 28, sources := [24] },
  { frame := 522, destination := 28, sources := [29] }, { frame := 522, destination := 28, sources := [7] },
  { frame := 522, destination := 28, sources := [99] }, { frame := 522, destination := 28, sources := [106] },
  { frame := 522, destination := 28, sources := [25] }, { frame := 522, destination := 28, sources := [108] },
  { frame := 522, destination := 28, sources := [98] }, { frame := 522, destination := 1, sources := [108] },
  { frame := 522, destination := 100, sources := [25] }, { frame := 522, destination := 101, sources := [24] },
  { frame := 522, destination := 101, sources := [7] }, { frame := 522, destination := 29, sources := [99] },
  { frame := 522, destination := 29, sources := [25] }, { frame := 522, destination := 29, sources := [98] },
  { frame := 522, destination := 7, sources := [25] }, { frame := 522, destination := 7, sources := [108] },
  { frame := 522, destination := 108, sources := [98] }, { frame := 522, destination := 98, sources := [28] },
  { frame := 522, destination := 108, sources := [28] }, { frame := 522, destination := 108, sources := [101] },
  { frame := 522, destination := 108, sources := [24] }, { frame := 522, destination := 108, sources := [29] },
  { frame := 522, destination := 108, sources := [7] }, { frame := 522, destination := 108, sources := [99] },
  { frame := 522, destination := 25, sources := [28] }, { frame := 522, destination := 25, sources := [7] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-bd7408ad51d0ad20"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk84`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4256)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 522, destination := 106, sources := [1] }, { frame := 522, destination := 106, sources := [101] },
  { frame := 522, destination := 106, sources := [29] }, { frame := 522, destination := 99, sources := [28] },
  { frame := 522, destination := 7, sources := [28] }, { frame := 522, destination := 7, sources := [1] },
  { frame := 522, destination := 29, sources := [1] }, { frame := 522, destination := 29, sources := [100] },
  { frame := 522, destination := 29, sources := [101] }, { frame := 522, destination := 24, sources := [28] },
  { frame := 522, destination := 101, sources := [28] }, { frame := 522, destination := 100, sources := [28] },
  { frame := 522, destination := 1, sources := [28] }, { frame := 523, destination := 103, sources := [2] },
  { frame := 523, destination := 103, sources := [88] }, { frame := 523, destination := 103, sources := [4] },
  { frame := 523, destination := 103, sources := [93] }, { frame := 523, destination := 103, sources := [16] },
  { frame := 523, destination := 103, sources := [109] }, { frame := 523, destination := 103, sources := [18] },
  { frame := 523, destination := 20, sources := [88] }, { frame := 523, destination := 20, sources := [95] },
  { frame := 523, destination := 20, sources := [14] }, { frame := 523, destination := 20, sources := [90] },
  { frame := 523, destination := 2, sources := [4] }, { frame := 523, destination := 2, sources := [93] },
  { frame := 523, destination := 2, sources := [16] }, { frame := 523, destination := 2, sources := [18] },
  { frame := 523, destination := 88, sources := [18] }, { frame := 523, destination := 93, sources := [16] },
  { frame := 523, destination := 95, sources := [18] }, { frame := 523, destination := 109, sources := [18] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-6a10f6e454362d9c"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk85`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4289)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 523, destination := 14, sources := [90] }, { frame := 523, destination := 14, sources := [18] },
  { frame := 523, destination := 18, sources := [103] }, { frame := 523, destination := 18, sources := [20] },
  { frame := 523, destination := 90, sources := [103] }, { frame := 523, destination := 14, sources := [103] },
  { frame := 523, destination := 14, sources := [20] }, { frame := 523, destination := 14, sources := [88] },
  { frame := 523, destination := 109, sources := [103] }, { frame := 523, destination := 109, sources := [20] },
  { frame := 523, destination := 109, sources := [88] }, { frame := 523, destination := 16, sources := [103] },
  { frame := 523, destination := 16, sources := [20] }, { frame := 523, destination := 95, sources := [103] },
  { frame := 523, destination := 95, sources := [20] }, { frame := 523, destination := 95, sources := [88] },
  { frame := 523, destination := 93, sources := [103] }, { frame := 523, destination := 93, sources := [20] },
  { frame := 523, destination := 93, sources := [2] }, { frame := 523, destination := 93, sources := [88] },
  { frame := 523, destination := 4, sources := [20] }, { frame := 523, destination := 4, sources := [2] },
  { frame := 523, destination := 88, sources := [103] }, { frame := 523, destination := 88, sources := [20] },
  { frame := 523, destination := 2, sources := [20] }, { frame := 523, destination := 20, sources := [103] },
  { frame := 524, destination := 110, sources := [31] }, { frame := 524, destination := 110, sources := [37] },
  { frame := 524, destination := 110, sources := [78] }, { frame := 524, destination := 110, sources := [8] },
  { frame := 524, destination := 110, sources := [81] }, { frame := 524, destination := 110, sources := [86] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0119a0c61e687104"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk86`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4322)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 524, destination := 110, sources := [12] }, { frame := 524, destination := 110, sources := [105] },
  { frame := 524, destination := 40, sources := [45] }, { frame := 524, destination := 40, sources := [86] },
  { frame := 524, destination := 40, sources := [73] }, { frame := 524, destination := 31, sources := [37] },
  { frame := 524, destination := 31, sources := [78] }, { frame := 524, destination := 31, sources := [81] },
  { frame := 524, destination := 8, sources := [86] }, { frame := 524, destination := 8, sources := [105] },
  { frame := 524, destination := 12, sources := [73] }, { frame := 524, destination := 73, sources := [40] },
  { frame := 524, destination := 73, sources := [31] }, { frame := 524, destination := 73, sources := [8] },
  { frame := 524, destination := 73, sources := [86] }, { frame := 524, destination := 105, sources := [110] },
  { frame := 524, destination := 105, sources := [40] }, { frame := 524, destination := 105, sources := [31] },
  { frame := 524, destination := 105, sources := [37] }, { frame := 524, destination := 105, sources := [78] },
  { frame := 524, destination := 12, sources := [110] }, { frame := 524, destination := 86, sources := [110] },
  { frame := 524, destination := 86, sources := [40] }, { frame := 524, destination := 81, sources := [110] },
  { frame := 524, destination := 81, sources := [40] }, { frame := 524, destination := 8, sources := [110] },
  { frame := 524, destination := 8, sources := [40] }, { frame := 524, destination := 78, sources := [110] },
  { frame := 524, destination := 78, sources := [40] }, { frame := 524, destination := 78, sources := [31] },
  { frame := 524, destination := 37, sources := [110] }, { frame := 524, destination := 37, sources := [40] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-1549ea84e5c02310"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk87`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4355)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 524, destination := 45, sources := [110] }, { frame := 524, destination := 31, sources := [40] },
  { frame := 524, destination := 40, sources := [110] }, { frame := 345, destination := 9, sources := [485] },
  { frame := 454, destination := 93, sources := [627] }, { frame := 471, destination := 99, sources := [629] },
  { frame := 344, destination := 5, sources := [243] }, { frame := 474, destination := 25, sources := [611] },
  { frame := 327, destination := 62, sources := [235] }, { frame := 326, destination := 0, sources := [247] },
  { frame := 452, destination := 2, sources := [457] }, { frame := 488, destination := 34, sources := [461] },
  { frame := 329, destination := 69, sources := [501] }, { frame := 434, destination := 31, sources := [481] },
  { frame := 347, destination := 48, sources := [272] }, { frame := 492, destination := 39, sources := [644] },
  { frame := 437, destination := 73, sources := [618] }, { frame := 477, destination := 106, sources := [429] },
  { frame := 363, destination := 21, sources := [539] }, { frame := 484, destination := 101, sources := [262] },
  { frame := 416, destination := 97, sources := [437] }, { frame := 482, destination := 28, sources := [425] },
  { frame := 381, destination := 92, sources := [521] }, { frame := 476, destination := 100, sources := [439] },
  { frame := 400, destination := 91, sources := [556] }, { frame := 419, destination := 35, sources := [537] },
  { frame := 362, destination := 94, sources := [502] }, { frame := 459, destination := 109, sources := [568] },
  { frame := 466, destination := 95, sources := [255] }, { frame := 398, destination := 23, sources := [427] },
  { frame := 384, destination := 87, sources := [518] }, { frame := 464, destination := 103, sources := [419] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-4239d20278256caa"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk88`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4388)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 462, destination := 16, sources := [275] }, { frame := 369, destination := 36, sources := [600] },
  { frame := 496, destination := 42, sources := [414] }, { frame := 440, destination := 45, sources := [527] },
  { frame := 422, destination := 43, sources := [401] }, { frame := 443, destination := 86, sources := [588] },
  { frame := 386, destination := 77, sources := [405] }, { frame := 405, destination := 49, sources := [563] },
  { frame := 494, destination := 76, sources := [654] }, { frame := 425, destination := 27, sources := [589] },
  { frame := 448, destination := 81, sources := [374] }, { frame := 500, destination := 79, sources := [628] },
  { frame := 368, destination := 102, sources := [253] }, { frame := 446, destination := 78, sources := [578] },
  { frame := 389, destination := 38, sources := [526] }, { frame := 404, destination := 41, sources := [389] },
  { frame := 504, destination := 32, sources := [282] }, { frame := 333, destination := 72, sources := [345] },
  { frame := 338, destination := 11, sources := [373] }, { frame := 342, destination := 63, sources := [432] },
  { frame := 375, destination := 51, sources := [456] }, { frame := 429, destination := 89, sources := [453] },
  { frame := 410, destination := 82, sources := [379] }, { frame := 339, destination := 465, sources := [323] },
  { frame := 377, destination := 71, sources := [251] }, { frame := 337, destination := 3, sources := [326] },
  { frame := 413, destination := 15, sources := [378] }, { frame := 334, destination := 68, sources := [256] },
  { frame := 395, destination := 17, sources := [492] }, { frame := 343, destination := 61, sources := [511] },
  { frame := 379, destination := 64, sources := [232] }, { frame := 433, destination := 65, sources := [334] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-9c2296f8a748b87e"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk89`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4421)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 356, destination := 47, sources := [347] }, { frame := 354, destination := 46, sources := [491] },
  { frame := 360, destination := 58, sources := [494] }, { frame := 415, destination := 30, sources := [346] },
  { frame := 397, destination := 50, sources := [342] }, { frame := 396, destination := 60, sources := [225] },
  { frame := 430, destination := 57, sources := [454] }, { frame := 358, destination := 52, sources := [336] },
  { frame := 353, destination := 56, sources := [312] }, { frame := 378, destination := 84, sources := [505] },
  { frame := 414, destination := 53, sources := [362] }, { frame := 355, destination := 54, sources := [324] },
  { frame := 503, destination := 13, sources := [404] }, { frame := 387, destination := 67, sources := [601] },
  { frame := 373, destination := 26, sources := [500] }, { frame := 451, destination := 105, sources := [304] },
  { frame := 423, destination := 74, sources := [581] }, { frame := 502, destination := 85, sources := [658] },
  { frame := 450, destination := 37, sources := [565] }, { frame := 407, destination := 75, sources := [544] },
  { frame := 495, destination := 107, sources := [301] }, { frame := 370, destination := 44, sources := [543] },
  { frame := 445, destination := 110, sources := [302] }, { frame := 409, destination := 70, sources := [298] },
  { frame := 442, destination := 12, sources := [392] }, { frame := 498, destination := 83, sources := [650] },
  { frame := 424, destination := 466, sources := [594] }, { frame := 487, destination := 24, sources := [258] },
  { frame := 383, destination := 33, sources := [573] }, { frame := 479, destination := 29, sources := [633] },
  { frame := 365, destination := 55, sources := [555] }, { frame := 417, destination := 66, sources := [607] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-3019a5aa1de72411"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk90`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4454)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 486, destination := 108, sources := [638] }, { frame := 403, destination := 96, sources := [268] },
  { frame := 480, destination := 98, sources := [632] }, { frame := 366, destination := 80, sources := [536] },
  { frame := 385, destination := 468, sources := [274] }, { frame := 467, destination := 90, sources := [586] },
  { frame := 463, destination := 88, sources := [260] }, { frame := 468, destination := 14, sources := [620] },
  { frame := 460, destination := 18, sources := [616] }, { frame := 402, destination := 59, sources := [612] },
  { frame := 473, destination := 7, sources := [655] }, { frame := 435, destination := 40, sources := [624] },
  { frame := 489, destination := 104, sources := [647] }, { frame := 453, destination := 20, sources := [626] },
  { frame := 436, destination := 8, sources := [613] }, { frame := 457, destination := 4, sources := [236] },
  { frame := 472, destination := 1, sources := [609] }, { frame := 493, destination := 10, sources := [238] },
  { frame := 525, destination := 111, sources := [243, 9, 246] },
  { frame := 526, destination := 112, sources := [457, 626, 93] },
  { frame := 527, destination := 113, sources := [436, 99, 609] },
  { frame := 528, destination := 114, sources := [5, 272, 223] },
  { frame := 529, destination := 115, sources := [447, 655, 25] },
  { frame := 530, destination := 116, sources := [247, 62, 234] },
  { frame := 531, destination := 117, sources := [0, 501, 228] },
  { frame := 532, destination := 118, sources := [2, 660, 608] },
  { frame := 533, destination := 119, sources := [34, 647, 311] },
  { frame := 534, destination := 120, sources := [235, 69, 504] },
  { frame := 535, destination := 121, sources := [31, 624, 613] },
  { frame := 536, destination := 122, sources := [485, 48, 322] },
  { frame := 537, destination := 123, sources := [461, 645, 39] },
  { frame := 538, destination := 124, sources := [481, 73, 382] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-94ae544a78e339b2"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk91`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4487)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 539, destination := 125, sources := [439, 106, 267] },
  { frame := 540, destination := 126, sources := [502, 21, 520] },
  { frame := 541, destination := 127, sources := [425, 237, 101] },
  { frame := 542, destination := 128, sources := [97, 607, 433] },
  { frame := 543, destination := 129, sources := [28, 639, 638] },
  { frame := 544, destination := 130, sources := [482, 92, 271] },
  { frame := 545, destination := 131, sources := [100, 633, 632] },
  { frame := 546, destination := 132, sources := [427, 257, 91] },
  { frame := 547, destination := 133, sources := [437, 35, 554] },
  { frame := 548, destination := 134, sources := [94, 555, 536] },
  { frame := 549, destination := 135, sources := [459, 109, 616] },
  { frame := 550, destination := 136, sources := [419, 254, 95] },
  { frame := 551, destination := 137, sources := [23, 273, 612] },
  { frame := 552, destination := 138, sources := [293, 573, 87] },
  { frame := 553, destination := 139, sources := [103, 586, 620] },
  { frame := 554, destination := 140, sources := [423, 314, 16] },
  { frame := 555, destination := 141, sources := [253, 36, 543] },
  { frame := 556, destination := 142, sources := [654, 301, 42] },
  { frame := 557, destination := 143, sources := [45, 367, 392] },
  { frame := 558, destination := 144, sources := [43, 581, 594] },
  { frame := 559, destination := 145, sources := [527, 86, 571] },
  { frame := 560, destination := 146, sources := [77, 601, 561] },
  { frame := 561, destination := 147, sources := [389, 49, 327] },
  { frame := 562, destination := 148, sources := [76, 245, 650] },
  { frame := 563, destination := 149, sources := [401, 27, 416] },
  { frame := 564, destination := 150, sources := [578, 445, 81] },
  { frame := 565, destination := 151, sources := [79, 290, 658] },
  { frame := 566, destination := 152, sources := [102, 525, 278] },
  { frame := 567, destination := 153, sources := [78, 603, 565] },
  { frame := 568, destination := 154, sources := [405, 38, 606] },
  { frame := 569, destination := 155, sources := [41, 544, 524] },
  { frame := 570, destination := 156, sources := [628, 404, 32] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0b2044c3cf0f35d4"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk92`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4520)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 571, destination := 157, sources := [375, 72, 256] },
  { frame := 572, destination := 158, sources := [11, 323, 358] },
  { frame := 573, destination := 159, sources := [373, 357, 63] },
  { frame := 574, destination := 160, sources := [332, 51, 363] },
  { frame := 575, destination := 161, sources := [353, 89, 454] },
  { frame := 576, destination := 162, sources := [82, 343, 287] },
  { frame := 577, destination := 163, sources := [465, 430, 511] },
  { frame := 578, destination := 164, sources := [222, 71, 505] },
  { frame := 579, destination := 165, sources := [345, 400, 3] },
  { frame := 580, destination := 166, sources := [379, 15, 362] },
  { frame := 581, destination := 167, sources := [68, 229, 326] },
  { frame := 582, destination := 168, sources := [369, 17, 225] },
  { frame := 583, destination := 169, sources := [409, 432, 61] },
  { frame := 584, destination := 170, sources := [456, 251, 64] },
  { frame := 585, destination := 171, sources := [453, 331, 65] },
  { frame := 586, destination := 172, sources := [47, 319, 336] },
  { frame := 587, destination := 173, sources := [341, 312, 46] },
  { frame := 588, destination := 174, sources := [347, 495, 58] },
  { frame := 589, destination := 175, sources := [386, 378, 30] },
  { frame := 590, destination := 176, sources := [352, 492, 50] },
  { frame := 591, destination := 177, sources := [487, 60, 342] },
  { frame := 592, destination := 178, sources := [57, 365, 334] },
  { frame := 593, destination := 179, sources := [52, 494, 320] },
  { frame := 594, destination := 180, sources := [305, 56, 324] },
  { frame := 595, destination := 181, sources := [407, 84, 232] },
  { frame := 596, destination := 182, sources := [448, 53, 346] },
  { frame := 597, destination := 183, sources := [344, 491, 54] },
  { frame := 598, destination := 184, sources := [659, 13, 250] },
  { frame := 599, destination := 185, sources := [67, 526, 371] },
  { frame := 600, destination := 186, sources := [600, 333, 26] },
  { frame := 601, destination := 187, sources := [451, 398, 105] },
  { frame := 602, destination := 188, sources := [74, 589, 294] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-849e7c322bbf01f6"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk93`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4553)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 603, destination := 189, sources := [85, 282, 316] },
  { frame := 604, destination := 190, sources := [374, 37, 304] },
  { frame := 605, destination := 191, sources := [563, 75, 298] },
  { frame := 606, destination := 192, sources := [107, 651, 288] },
  { frame := 607, destination := 193, sources := [44, 595, 500] },
  { frame := 608, destination := 194, sources := [307, 588, 110] },
  { frame := 609, destination := 195, sources := [562, 377, 70] },
  { frame := 610, destination := 196, sources := [12, 248, 302] },
  { frame := 611, destination := 197, sources := [414, 83, 394] },
  { frame := 612, destination := 198, sources := [466, 542, 297] },
  { frame := 613, destination := 199, sources := [263, 284, 24] },
  { frame := 614, destination := 200, sources := [521, 33, 274] },
  { frame := 615, destination := 201, sources := [429, 29, 452] },
  { frame := 616, destination := 202, sources := [539, 55, 252] },
  { frame := 617, destination := 203, sources := [66, 537, 280] },
  { frame := 618, destination := 204, sources := [262, 108, 258] },
  { frame := 619, destination := 205, sources := [557, 519, 96] },
  { frame := 620, destination := 206, sources := [435, 98, 276] },
  { frame := 621, destination := 207, sources := [396, 80, 443] },
  { frame := 622, destination := 208, sources := [574, 518, 468] },
  { frame := 623, destination := 209, sources := [283, 90, 428] },
  { frame := 624, destination := 210, sources := [568, 259, 88] },
  { frame := 625, destination := 211, sources := [255, 14, 266] },
  { frame := 626, destination := 212, sources := [18, 275, 260] },
  { frame := 627, destination := 213, sources := [556, 59, 268] },
  { frame := 628, destination := 214, sources := [629, 7, 277] },
  { frame := 629, destination := 215, sources := [40, 618, 411] },
  { frame := 630, destination := 216, sources := [104, 295, 238] },
  { frame := 631, destination := 217, sources := [20, 415, 236] },
  { frame := 632, destination := 218, sources := [8, 619, 244] },
  { frame := 633, destination := 219, sources := [627, 227, 4] },
  { frame := 634, destination := 220, sources := [1, 611, 226] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-7e7fe91bdcaa9824"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk94`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4586)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 635, destination := 221, sources := [646, 644, 10] }, { frame := 1, destination := 10, sources := [238] },
  { frame := 1, destination := 1, sources := [609] }, { frame := 1, destination := 4, sources := [236] },
  { frame := 1, destination := 8, sources := [613] }, { frame := 1, destination := 20, sources := [626] },
  { frame := 1, destination := 104, sources := [647] }, { frame := 1, destination := 40, sources := [624] },
  { frame := 1, destination := 7, sources := [655] }, { frame := 1, destination := 59, sources := [612] },
  { frame := 1, destination := 18, sources := [616] }, { frame := 1, destination := 14, sources := [620] },
  { frame := 1, destination := 88, sources := [260] }, { frame := 1, destination := 90, sources := [586] },
  { frame := 1, destination := 468, sources := [274] }, { frame := 1, destination := 80, sources := [536] },
  { frame := 1, destination := 98, sources := [632] }, { frame := 1, destination := 96, sources := [268] },
  { frame := 1, destination := 108, sources := [638] }, { frame := 1, destination := 66, sources := [607] },
  { frame := 1, destination := 55, sources := [555] }, { frame := 1, destination := 29, sources := [633] },
  { frame := 1, destination := 33, sources := [573] }, { frame := 1, destination := 24, sources := [258] },
  { frame := 1, destination := 466, sources := [594] }, { frame := 1, destination := 83, sources := [650] },
  { frame := 1, destination := 12, sources := [392] }, { frame := 1, destination := 70, sources := [298] },
  { frame := 1, destination := 110, sources := [302] }, { frame := 1, destination := 44, sources := [543] },
  { frame := 1, destination := 107, sources := [301] }, { frame := 1, destination := 75, sources := [544] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e110db567ebe2b6d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk95`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4619)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 37, sources := [565] }, { frame := 1, destination := 85, sources := [658] },
  { frame := 1, destination := 74, sources := [581] }, { frame := 1, destination := 105, sources := [304] },
  { frame := 1, destination := 26, sources := [500] }, { frame := 1, destination := 67, sources := [601] },
  { frame := 1, destination := 13, sources := [404] }, { frame := 1, destination := 54, sources := [324] },
  { frame := 1, destination := 53, sources := [362] }, { frame := 1, destination := 84, sources := [505] },
  { frame := 1, destination := 56, sources := [312] }, { frame := 1, destination := 52, sources := [336] },
  { frame := 1, destination := 57, sources := [454] }, { frame := 1, destination := 60, sources := [225] },
  { frame := 1, destination := 50, sources := [342] }, { frame := 1, destination := 30, sources := [346] },
  { frame := 1, destination := 58, sources := [494] }, { frame := 1, destination := 46, sources := [491] },
  { frame := 1, destination := 47, sources := [347] }, { frame := 1, destination := 65, sources := [334] },
  { frame := 1, destination := 64, sources := [232] }, { frame := 1, destination := 61, sources := [511] },
  { frame := 1, destination := 17, sources := [492] }, { frame := 1, destination := 68, sources := [256] },
  { frame := 1, destination := 15, sources := [378] }, { frame := 1, destination := 3, sources := [326] },
  { frame := 1, destination := 71, sources := [251] }, { frame := 1, destination := 465, sources := [323] },
  { frame := 1, destination := 82, sources := [379] }, { frame := 1, destination := 89, sources := [453] },
  { frame := 1, destination := 51, sources := [456] }, { frame := 1, destination := 63, sources := [432] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-474d7095ee8b039a"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk96`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4652)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 11, sources := [373] }, { frame := 1, destination := 72, sources := [345] },
  { frame := 1, destination := 32, sources := [282] }, { frame := 1, destination := 41, sources := [389] },
  { frame := 1, destination := 38, sources := [526] }, { frame := 1, destination := 78, sources := [578] },
  { frame := 1, destination := 102, sources := [253] }, { frame := 1, destination := 79, sources := [628] },
  { frame := 1, destination := 81, sources := [374] }, { frame := 1, destination := 27, sources := [589] },
  { frame := 1, destination := 76, sources := [654] }, { frame := 1, destination := 49, sources := [563] },
  { frame := 1, destination := 77, sources := [405] }, { frame := 1, destination := 86, sources := [588] },
  { frame := 1, destination := 43, sources := [401] }, { frame := 1, destination := 45, sources := [527] },
  { frame := 1, destination := 42, sources := [414] }, { frame := 1, destination := 36, sources := [600] },
  { frame := 1, destination := 16, sources := [275] }, { frame := 1, destination := 103, sources := [419] },
  { frame := 1, destination := 87, sources := [518] }, { frame := 1, destination := 23, sources := [427] },
  { frame := 1, destination := 95, sources := [255] }, { frame := 1, destination := 109, sources := [568] },
  { frame := 1, destination := 94, sources := [502] }, { frame := 1, destination := 35, sources := [537] },
  { frame := 1, destination := 91, sources := [556] }, { frame := 1, destination := 100, sources := [439] },
  { frame := 1, destination := 92, sources := [521] }, { frame := 1, destination := 28, sources := [425] },
  { frame := 1, destination := 97, sources := [437] }, { frame := 1, destination := 101, sources := [262] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-77ebd7287e16b5ae"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk97`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4685)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 21, sources := [539] }, { frame := 1, destination := 106, sources := [429] },
  { frame := 1, destination := 73, sources := [618] }, { frame := 1, destination := 39, sources := [644] },
  { frame := 1, destination := 48, sources := [272] }, { frame := 1, destination := 31, sources := [481] },
  { frame := 1, destination := 69, sources := [501] }, { frame := 1, destination := 34, sources := [461] },
  { frame := 1, destination := 2, sources := [457] }, { frame := 1, destination := 0, sources := [247] },
  { frame := 1, destination := 62, sources := [235] }, { frame := 1, destination := 25, sources := [611] },
  { frame := 1, destination := 5, sources := [243] }, { frame := 1, destination := 99, sources := [629] },
  { frame := 1, destination := 93, sources := [627] }, { frame := 1, destination := 9, sources := [485] },
  { frame := 1, destination := 40, sources := [110] }, { frame := 1, destination := 31, sources := [40] },
  { frame := 1, destination := 45, sources := [110] }, { frame := 1, destination := 37, sources := [40] },
  { frame := 1, destination := 37, sources := [110] }, { frame := 1, destination := 78, sources := [31] },
  { frame := 1, destination := 78, sources := [40] }, { frame := 1, destination := 78, sources := [110] },
  { frame := 1, destination := 8, sources := [40] }, { frame := 1, destination := 8, sources := [110] },
  { frame := 1, destination := 81, sources := [40] }, { frame := 1, destination := 81, sources := [110] },
  { frame := 1, destination := 86, sources := [40] }, { frame := 1, destination := 86, sources := [110] },
  { frame := 1, destination := 12, sources := [110] }, { frame := 1, destination := 105, sources := [78] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-5ecec1b4a23190d5"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk98`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4718)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 105, sources := [37] }, { frame := 1, destination := 105, sources := [31] },
  { frame := 1, destination := 105, sources := [40] }, { frame := 1, destination := 105, sources := [110] },
  { frame := 1, destination := 73, sources := [86] }, { frame := 1, destination := 73, sources := [8] },
  { frame := 1, destination := 73, sources := [31] }, { frame := 1, destination := 73, sources := [40] },
  { frame := 1, destination := 12, sources := [73] }, { frame := 1, destination := 8, sources := [105] },
  { frame := 1, destination := 8, sources := [86] }, { frame := 1, destination := 31, sources := [81] },
  { frame := 1, destination := 31, sources := [78] }, { frame := 1, destination := 31, sources := [37] },
  { frame := 1, destination := 40, sources := [73] }, { frame := 1, destination := 40, sources := [86] },
  { frame := 1, destination := 40, sources := [45] }, { frame := 1, destination := 110, sources := [105] },
  { frame := 1, destination := 110, sources := [12] }, { frame := 1, destination := 110, sources := [86] },
  { frame := 1, destination := 110, sources := [81] }, { frame := 1, destination := 110, sources := [8] },
  { frame := 1, destination := 110, sources := [78] }, { frame := 1, destination := 110, sources := [37] },
  { frame := 1, destination := 110, sources := [31] }, { frame := 1, destination := 20, sources := [103] },
  { frame := 1, destination := 2, sources := [20] }, { frame := 1, destination := 88, sources := [20] },
  { frame := 1, destination := 88, sources := [103] }, { frame := 1, destination := 4, sources := [2] },
  { frame := 1, destination := 4, sources := [20] }, { frame := 1, destination := 93, sources := [88] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e2501750cfedf91b"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk99`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4751)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 93, sources := [2] }, { frame := 1, destination := 93, sources := [20] },
  { frame := 1, destination := 93, sources := [103] }, { frame := 1, destination := 95, sources := [88] },
  { frame := 1, destination := 95, sources := [20] }, { frame := 1, destination := 95, sources := [103] },
  { frame := 1, destination := 16, sources := [20] }, { frame := 1, destination := 16, sources := [103] },
  { frame := 1, destination := 109, sources := [88] }, { frame := 1, destination := 109, sources := [20] },
  { frame := 1, destination := 109, sources := [103] }, { frame := 1, destination := 14, sources := [88] },
  { frame := 1, destination := 14, sources := [20] }, { frame := 1, destination := 14, sources := [103] },
  { frame := 1, destination := 90, sources := [103] }, { frame := 1, destination := 18, sources := [20] },
  { frame := 1, destination := 18, sources := [103] }, { frame := 1, destination := 14, sources := [18] },
  { frame := 1, destination := 14, sources := [90] }, { frame := 1, destination := 109, sources := [18] },
  { frame := 1, destination := 95, sources := [18] }, { frame := 1, destination := 93, sources := [16] },
  { frame := 1, destination := 88, sources := [18] }, { frame := 1, destination := 2, sources := [18] },
  { frame := 1, destination := 2, sources := [16] }, { frame := 1, destination := 2, sources := [93] },
  { frame := 1, destination := 2, sources := [4] }, { frame := 1, destination := 20, sources := [90] },
  { frame := 1, destination := 20, sources := [14] }, { frame := 1, destination := 20, sources := [95] },
  { frame := 1, destination := 20, sources := [88] }, { frame := 1, destination := 103, sources := [18] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-3cff84da5008fbcd"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk100`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4784)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 103, sources := [109] }, { frame := 1, destination := 103, sources := [16] },
  { frame := 1, destination := 103, sources := [93] }, { frame := 1, destination := 103, sources := [4] },
  { frame := 1, destination := 103, sources := [88] }, { frame := 1, destination := 103, sources := [2] },
  { frame := 1, destination := 1, sources := [28] }, { frame := 1, destination := 100, sources := [28] },
  { frame := 1, destination := 101, sources := [28] }, { frame := 1, destination := 24, sources := [28] },
  { frame := 1, destination := 29, sources := [101] }, { frame := 1, destination := 29, sources := [100] },
  { frame := 1, destination := 29, sources := [1] }, { frame := 1, destination := 7, sources := [1] },
  { frame := 1, destination := 7, sources := [28] }, { frame := 1, destination := 99, sources := [28] },
  { frame := 1, destination := 106, sources := [29] }, { frame := 1, destination := 106, sources := [101] },
  { frame := 1, destination := 106, sources := [1] }, { frame := 1, destination := 25, sources := [7] },
  { frame := 1, destination := 25, sources := [28] }, { frame := 1, destination := 108, sources := [99] },
  { frame := 1, destination := 108, sources := [7] }, { frame := 1, destination := 108, sources := [29] },
  { frame := 1, destination := 108, sources := [24] }, { frame := 1, destination := 108, sources := [101] },
  { frame := 1, destination := 108, sources := [28] }, { frame := 1, destination := 98, sources := [28] },
  { frame := 1, destination := 108, sources := [98] }, { frame := 1, destination := 7, sources := [108] },
  { frame := 1, destination := 7, sources := [25] }, { frame := 1, destination := 29, sources := [98] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-b9146d34ad6fe8b7"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk101`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4817)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 29, sources := [25] }, { frame := 1, destination := 29, sources := [99] },
  { frame := 1, destination := 101, sources := [7] }, { frame := 1, destination := 101, sources := [24] },
  { frame := 1, destination := 100, sources := [25] }, { frame := 1, destination := 1, sources := [108] },
  { frame := 1, destination := 28, sources := [98] }, { frame := 1, destination := 28, sources := [108] },
  { frame := 1, destination := 28, sources := [25] }, { frame := 1, destination := 28, sources := [106] },
  { frame := 1, destination := 28, sources := [99] }, { frame := 1, destination := 28, sources := [7] },
  { frame := 1, destination := 28, sources := [29] }, { frame := 1, destination := 28, sources := [24] },
  { frame := 1, destination := 28, sources := [101] }, { frame := 1, destination := 28, sources := [100] },
  { frame := 1, destination := 28, sources := [1] }, { frame := 1, destination := 10, sources := [83] },
  { frame := 1, destination := 79, sources := [10] }, { frame := 1, destination := 76, sources := [10] },
  { frame := 1, destination := 76, sources := [83] }, { frame := 1, destination := 104, sources := [10] },
  { frame := 1, destination := 104, sources := [83] }, { frame := 1, destination := 13, sources := [83] },
  { frame := 1, destination := 34, sources := [104] }, { frame := 1, destination := 34, sources := [83] },
  { frame := 1, destination := 42, sources := [83] }, { frame := 1, destination := 39, sources := [83] },
  { frame := 1, destination := 107, sources := [42] }, { frame := 1, destination := 107, sources := [13] },
  { frame := 1, destination := 107, sources := [104] }, { frame := 1, destination := 107, sources := [79] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-8448f3dd32d26589"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk102`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4850)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 107, sources := [83] }, { frame := 1, destination := 85, sources := [79] },
  { frame := 1, destination := 85, sources := [10] }, { frame := 1, destination := 32, sources := [42] },
  { frame := 1, destination := 32, sources := [34] }, { frame := 1, destination := 32, sources := [83] },
  { frame := 1, destination := 34, sources := [39] }, { frame := 1, destination := 34, sources := [42] },
  { frame := 1, destination := 13, sources := [85] }, { frame := 1, destination := 13, sources := [39] },
  { frame := 1, destination := 13, sources := [34] }, { frame := 1, destination := 104, sources := [107] },
  { frame := 1, destination := 104, sources := [34] }, { frame := 1, destination := 76, sources := [107] },
  { frame := 1, destination := 76, sources := [42] }, { frame := 1, destination := 79, sources := [85] },
  { frame := 1, destination := 79, sources := [42] }, { frame := 1, destination := 79, sources := [13] },
  { frame := 1, destination := 79, sources := [104] }, { frame := 1, destination := 79, sources := [76] },
  { frame := 1, destination := 10, sources := [107] }, { frame := 1, destination := 10, sources := [39] },
  { frame := 1, destination := 83, sources := [32] }, { frame := 1, destination := 83, sources := [85] },
  { frame := 1, destination := 83, sources := [107] }, { frame := 1, destination := 83, sources := [42] },
  { frame := 1, destination := 83, sources := [34] }, { frame := 1, destination := 83, sources := [13] },
  { frame := 1, destination := 83, sources := [104] }, { frame := 1, destination := 83, sources := [76] },
  { frame := 1, destination := 83, sources := [79] }, { frame := 1, destination := 83, sources := [10] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-1294b1eafff69100"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk103`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4883)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 92, sources := [87] }, { frame := 1, destination := 17, sources := [87] },
  { frame := 1, destination := 67, sources := [17] }, { frame := 1, destination := 67, sources := [87] },
  { frame := 1, destination := 38, sources := [17] }, { frame := 1, destination := 38, sources := [87] },
  { frame := 1, destination := 33, sources := [22] }, { frame := 1, destination := 33, sources := [87] },
  { frame := 1, destination := 60, sources := [17] }, { frame := 1, destination := 60, sources := [87] },
  { frame := 1, destination := 50, sources := [67] }, { frame := 1, destination := 50, sources := [17] },
  { frame := 1, destination := 50, sources := [87] }, { frame := 1, destination := 468, sources := [33] },
  { frame := 1, destination := 468, sources := [38] }, { frame := 1, destination := 468, sources := [92] },
  { frame := 1, destination := 468, sources := [87] }, { frame := 1, destination := 77, sources := [33] },
  { frame := 1, destination := 77, sources := [17] }, { frame := 1, destination := 77, sources := [87] },
  { frame := 1, destination := 38, sources := [33] }, { frame := 1, destination := 17, sources := [33] },
  { frame := 1, destination := 92, sources := [33] }, { frame := 1, destination := 92, sources := [22] },
  { frame := 1, destination := 87, sources := [77] }, { frame := 1, destination := 87, sources := [50] },
  { frame := 1, destination := 87, sources := [60] }, { frame := 1, destination := 87, sources := [22] },
  { frame := 1, destination := 87, sources := [38] }, { frame := 1, destination := 87, sources := [67] },
  { frame := 1, destination := 87, sources := [92] }, { frame := 1, destination := 44, sources := [55] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-bf5cc2507274ab60"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk104`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4916)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 84, sources := [44] }, { frame := 1, destination := 94, sources := [55] },
  { frame := 1, destination := 21, sources := [94] }, { frame := 1, destination := 21, sources := [55] },
  { frame := 1, destination := 51, sources := [44] }, { frame := 1, destination := 36, sources := [44] },
  { frame := 1, destination := 36, sources := [55] }, { frame := 1, destination := 71, sources := [51] },
  { frame := 1, destination := 71, sources := [44] }, { frame := 1, destination := 64, sources := [51] },
  { frame := 1, destination := 64, sources := [44] }, { frame := 1, destination := 80, sources := [21] },
  { frame := 1, destination := 80, sources := [55] }, { frame := 1, destination := 102, sources := [94] },
  { frame := 1, destination := 102, sources := [55] }, { frame := 1, destination := 26, sources := [102] },
  { frame := 1, destination := 26, sources := [36] }, { frame := 1, destination := 26, sources := [51] },
  { frame := 1, destination := 26, sources := [94] }, { frame := 1, destination := 26, sources := [55] },
  { frame := 1, destination := 80, sources := [102] }, { frame := 1, destination := 36, sources := [80] },
  { frame := 1, destination := 21, sources := [26] }, { frame := 1, destination := 94, sources := [21] },
  { frame := 1, destination := 84, sources := [64] }, { frame := 1, destination := 84, sources := [71] },
  { frame := 1, destination := 44, sources := [26] }, { frame := 1, destination := 44, sources := [102] },
  { frame := 1, destination := 44, sources := [80] }, { frame := 1, destination := 44, sources := [36] },
  { frame := 1, destination := 44, sources := [21] }, { frame := 1, destination := 44, sources := [94] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-3c6e71d5c44d97ff"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk105`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4949)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 44, sources := [84] }, { frame := 1, destination := 55, sources := [80] },
  { frame := 1, destination := 55, sources := [64] }, { frame := 1, destination := 55, sources := [71] },
  { frame := 1, destination := 55, sources := [36] }, { frame := 1, destination := 55, sources := [51] },
  { frame := 1, destination := 55, sources := [84] }, { frame := 1, destination := 55, sources := [44] },
  { frame := 1, destination := 27, sources := [66] }, { frame := 1, destination := 466, sources := [66] },
  { frame := 1, destination := 466, sources := [89] }, { frame := 1, destination := 74, sources := [66] },
  { frame := 1, destination := 74, sources := [89] }, { frame := 1, destination := 43, sources := [66] },
  { frame := 1, destination := 43, sources := [89] }, { frame := 1, destination := 35, sources := [74] },
  { frame := 1, destination := 35, sources := [27] }, { frame := 1, destination := 35, sources := [66] },
  { frame := 1, destination := 35, sources := [89] }, { frame := 1, destination := 57, sources := [89] },
  { frame := 1, destination := 65, sources := [89] }, { frame := 1, destination := 97, sources := [19] },
  { frame := 1, destination := 97, sources := [27] }, { frame := 1, destination := 97, sources := [66] },
  { frame := 1, destination := 35, sources := [97] }, { frame := 1, destination := 43, sources := [97] },
  { frame := 1, destination := 43, sources := [19] }, { frame := 1, destination := 74, sources := [97] },
  { frame := 1, destination := 74, sources := [19] }, { frame := 1, destination := 74, sources := [43] },
  { frame := 1, destination := 466, sources := [97] }, { frame := 1, destination := 466, sources := [43] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-41d4550fd772a9cb"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk106`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L4982)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 66, sources := [97] }, { frame := 1, destination := 66, sources := [65] },
  { frame := 1, destination := 66, sources := [57] }, { frame := 1, destination := 66, sources := [35] },
  { frame := 1, destination := 66, sources := [19] }, { frame := 1, destination := 66, sources := [43] },
  { frame := 1, destination := 66, sources := [74] }, { frame := 1, destination := 89, sources := [97] },
  { frame := 1, destination := 89, sources := [35] }, { frame := 1, destination := 89, sources := [19] },
  { frame := 1, destination := 89, sources := [43] }, { frame := 1, destination := 89, sources := [74] },
  { frame := 1, destination := 89, sources := [27] }, { frame := 1, destination := 15, sources := [59] },
  { frame := 1, destination := 49, sources := [15] }, { frame := 1, destination := 49, sources := [59] },
  { frame := 1, destination := 30, sources := [49] }, { frame := 1, destination := 30, sources := [15] },
  { frame := 1, destination := 91, sources := [59] }, { frame := 1, destination := 53, sources := [49] },
  { frame := 1, destination := 53, sources := [15] }, { frame := 1, destination := 53, sources := [59] },
  { frame := 1, destination := 23, sources := [15] }, { frame := 1, destination := 23, sources := [59] },
  { frame := 1, destination := 41, sources := [15] }, { frame := 1, destination := 41, sources := [59] },
  { frame := 1, destination := 96, sources := [23] }, { frame := 1, destination := 96, sources := [59] },
  { frame := 1, destination := 82, sources := [53] }, { frame := 1, destination := 82, sources := [15] },
  { frame := 1, destination := 70, sources := [15] }, { frame := 1, destination := 70, sources := [59] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-4efd61e9db3bac3f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk107`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5015)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 75, sources := [70] }, { frame := 1, destination := 75, sources := [82] },
  { frame := 1, destination := 75, sources := [15] }, { frame := 1, destination := 75, sources := [59] },
  { frame := 1, destination := 82, sources := [70] }, { frame := 1, destination := 41, sources := [82] },
  { frame := 1, destination := 53, sources := [75] }, { frame := 1, destination := 53, sources := [41] },
  { frame := 1, destination := 30, sources := [75] }, { frame := 1, destination := 30, sources := [70] },
  { frame := 1, destination := 30, sources := [82] }, { frame := 1, destination := 49, sources := [75] },
  { frame := 1, destination := 49, sources := [41] }, { frame := 1, destination := 15, sources := [96] },
  { frame := 1, destination := 15, sources := [23] }, { frame := 1, destination := 15, sources := [91] },
  { frame := 1, destination := 59, sources := [75] }, { frame := 1, destination := 59, sources := [70] },
  { frame := 1, destination := 59, sources := [82] }, { frame := 1, destination := 59, sources := [41] },
  { frame := 1, destination := 59, sources := [53] }, { frame := 1, destination := 59, sources := [30] },
  { frame := 1, destination := 59, sources := [49] }, { frame := 1, destination := 3, sources := [68] },
  { frame := 1, destination := 465, sources := [3] }, { frame := 1, destination := 465, sources := [68] },
  { frame := 1, destination := 69, sources := [68] }, { frame := 1, destination := 11, sources := [69] },
  { frame := 1, destination := 11, sources := [3] }, { frame := 1, destination := 11, sources := [68] },
  { frame := 1, destination := 63, sources := [69] }, { frame := 1, destination := 63, sources := [3] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-b0262d2fefa53786"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk108`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5048)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 72, sources := [3] }, { frame := 1, destination := 72, sources := [68] },
  { frame := 1, destination := 62, sources := [69] }, { frame := 1, destination := 62, sources := [3] },
  { frame := 1, destination := 62, sources := [68] }, { frame := 1, destination := 0, sources := [69] },
  { frame := 1, destination := 0, sources := [68] }, { frame := 1, destination := 61, sources := [0] },
  { frame := 1, destination := 61, sources := [62] }, { frame := 1, destination := 61, sources := [72] },
  { frame := 1, destination := 61, sources := [69] }, { frame := 1, destination := 61, sources := [3] },
  { frame := 1, destination := 63, sources := [0] }, { frame := 1, destination := 63, sources := [62] },
  { frame := 1, destination := 63, sources := [72] }, { frame := 1, destination := 69, sources := [62] },
  { frame := 1, destination := 69, sources := [11] }, { frame := 1, destination := 465, sources := [0] },
  { frame := 1, destination := 465, sources := [63] }, { frame := 1, destination := 465, sources := [69] },
  { frame := 1, destination := 3, sources := [62] }, { frame := 1, destination := 68, sources := [61] },
  { frame := 1, destination := 68, sources := [0] }, { frame := 1, destination := 68, sources := [72] },
  { frame := 1, destination := 68, sources := [63] }, { frame := 1, destination := 68, sources := [11] },
  { frame := 1, destination := 47, sources := [52] }, { frame := 1, destination := 56, sources := [52] },
  { frame := 1, destination := 5, sources := [52] }, { frame := 1, destination := 54, sources := [52] },
  { frame := 1, destination := 9, sources := [52] }, { frame := 1, destination := 58, sources := [52] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0694f6cd9e373dda"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk109`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5081)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 46, sources := [54] }, { frame := 1, destination := 46, sources := [56] },
  { frame := 1, destination := 46, sources := [52] }, { frame := 1, destination := 48, sources := [6] },
  { frame := 1, destination := 48, sources := [5] }, { frame := 1, destination := 48, sources := [52] },
  { frame := 1, destination := 58, sources := [48] }, { frame := 1, destination := 9, sources := [6] },
  { frame := 1, destination := 5, sources := [9] }, { frame := 1, destination := 47, sources := [48] },
  { frame := 1, destination := 47, sources := [46] }, { frame := 1, destination := 52, sources := [48] },
  { frame := 1, destination := 52, sources := [46] }, { frame := 1, destination := 52, sources := [6] },
  { frame := 1, destination := 52, sources := [58] }, { frame := 1, destination := 52, sources := [9] },
  { frame := 1, destination := 52, sources := [54] }, { frame := 1, destination := 52, sources := [5] },
  { frame := 1, destination := 52, sources := [56] }, { frame := 1, destination := 52, sources := [47] },
  { frame := 1, destination := 480, sources := [538, 368] }, { frame := 1, destination := 480, sources := [280] },
  { frame := 1, destination := 479, sources := [413, 296] }, { frame := 1, destination := 479, sources := [561] },
  { frame := 1, destination := 478, sources := [387, 241] }, { frame := 1, destination := 478, sources := [495] },
  { frame := 1, destination := 477, sources := [340, 233] }, { frame := 1, destination := 477, sources := [341] },
  { frame := 1, destination := 476, sources := [385, 328] }, { frame := 1, destination := 476, sources := [331] },
  { frame := 1, destination := 475, sources := [444, 337] }, { frame := 1, destination := 475, sources := [487] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-f4f984f71ef51bf0"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk110`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5114)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 474, sources := [381, 509] }, { frame := 1, destination := 474, sources := [400] },
  { frame := 1, destination := 473, sources := [349, 486] }, { frame := 1, destination := 473, sources := [246] },
  { frame := 1, destination := 472, sources := [240, 360] }, { frame := 1, destination := 472, sources := [234] },
  { frame := 1, destination := 411, sources := [244] }, { frame := 1, destination := 277, sources := [226] },
  { frame := 1, destination := 428, sources := [266] }, { frame := 1, destination := 443, sources := [252] },
  { frame := 1, destination := 452, sources := [276] }, { frame := 1, destination := 394, sources := [288] },
  { frame := 1, destination := 297, sources := [294] }, { frame := 1, destination := 371, sources := [296] },
  { frame := 1, destination := 250, sources := [316] }, { frame := 1, destination := 241, sources := [320] },
  { frame := 1, destination := 319, sources := [387] }, { frame := 1, destination := 233, sources := [344] },
  { frame := 1, destination := 340, sources := [305] }, { frame := 1, destination := 365, sources := [328] },
  { frame := 1, destination := 287, sources := [448] }, { frame := 1, destination := 386, sources := [343] },
  { frame := 1, destination := 385, sources := [353] }, { frame := 1, destination := 352, sources := [337] },
  { frame := 1, destination := 444, sources := [369] }, { frame := 1, destination := 407, sources := [363] },
  { frame := 1, destination := 332, sources := [222] }, { frame := 1, destination := 229, sources := [509] },
  { frame := 1, destination := 357, sources := [430] }, { frame := 1, destination := 358, sources := [409] },
  { frame := 1, destination := 381, sources := [375] }, { frame := 1, destination := 377, sources := [524] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-aa94978b487d7769"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk111`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5147)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 413, sources := [469] }, { frame := 1, destination := 413, sources := [606] },
  { frame := 1, destination := 398, sources := [603] }, { frame := 1, destination := 278, sources := [595] },
  { frame := 1, destination := 333, sources := [525] }, { frame := 1, destination := 290, sources := [659] },
  { frame := 1, destination := 451, sources := [445] }, { frame := 1, destination := 416, sources := [542] },
  { frame := 1, destination := 245, sources := [651] }, { frame := 1, destination := 327, sources := [562] },
  { frame := 1, destination := 248, sources := [571] }, { frame := 1, destination := 307, sources := [367] },
  { frame := 1, destination := 259, sources := [314] }, { frame := 1, destination := 273, sources := [519] },
  { frame := 1, destination := 254, sources := [283] }, { frame := 1, destination := 459, sources := [423] },
  { frame := 1, destination := 368, sources := [554] }, { frame := 1, destination := 257, sources := [557] },
  { frame := 1, destination := 271, sources := [574] }, { frame := 1, destination := 293, sources := [482] },
  { frame := 1, destination := 284, sources := [639] }, { frame := 1, destination := 433, sources := [538] },
  { frame := 1, destination := 237, sources := [263] }, { frame := 1, destination := 396, sources := [520] },
  { frame := 1, destination := 435, sources := [267] }, { frame := 1, destination := 382, sources := [619] },
  { frame := 1, destination := 295, sources := [645] }, { frame := 1, destination := 322, sources := [486] },
  { frame := 1, destination := 360, sources := [504] }, { frame := 1, destination := 311, sources := [646] },
  { frame := 1, destination := 227, sources := [608] }, { frame := 1, destination := 415, sources := [660] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-96f2ee959a95f5a8"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk112`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5180)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 228, sources := [240] }, { frame := 1, destination := 349, sources := [223] },
  { frame := 1, destination := 436, sources := [447] },
  { frame := 1, destination := 413, sources := [17, 271, 293, 352, 371, 471] },
  { frame := 1, destination := 444, sources := [17, 271, 293, 352, 413, 468, 471] },
  { frame := 1, destination := 444, sources := [470] },
  { frame := 1, destination := 368, sources := [365, 385, 433, 466] },
  { frame := 1, destination := 385, sources := [43, 57, 297, 416, 433, 466, 467] },
  { frame := 1, destination := 381, sources := [11, 69, 228, 358, 360, 465] },
  { frame := 1, destination := 360, sources := [68, 69, 357, 358, 381] },
  { frame := 1, destination := 241, sources := [6, 56, 233, 319, 322, 463, 464] },
  { frame := 1, destination := 340, sources := [233, 241, 319, 349, 464] },
  { frame := 1, destination := 349, sources := [6, 56, 233, 319, 322, 340, 462, 463] },
  { frame := 1, destination := 316, sources := [610] }, { frame := 1, destination := 282, sources := [656] },
  { frame := 1, destination := 404, sources := [657] }, { frame := 1, destination := 658, sources := [408] },
  { frame := 1, destination := 659, sources := [317] }, { frame := 1, destination := 628, sources := [393] },
  { frame := 1, destination := 288, sources := [649] }, { frame := 1, destination := 650, sources := [289] },
  { frame := 1, destination := 651, sources := [410] }, { frame := 1, destination := 414, sources := [652] },
  { frame := 1, destination := 301, sources := [623] }, { frame := 1, destination := 654, sources := [399] },
  { frame := 1, destination := 238, sources := [643] }, { frame := 1, destination := 644, sources := [450] },
  { frame := 1, destination := 645, sources := [239] }, { frame := 1, destination := 646, sources := [449] },
  { frame := 1, destination := 647, sources := [460] }, { frame := 1, destination := 461, sources := [648] },
  { frame := 1, destination := 258, sources := [637] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-5ec748a5905d3c3f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk113`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5213)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 638, sources := [300] }, { frame := 1, destination := 639, sources := [424] },
  { frame := 1, destination := 262, sources := [640] }, { frame := 1, destination := 263, sources := [641] },
  { frame := 1, destination := 425, sources := [642] }, { frame := 1, destination := 276, sources := [631] },
  { frame := 1, destination := 632, sources := [418] }, { frame := 1, destination := 633, sources := [306] },
  { frame := 1, destination := 267, sources := [622] }, { frame := 1, destination := 429, sources := [653] },
  { frame := 1, destination := 439, sources := [636] }, { frame := 1, destination := 226, sources := [625] },
  { frame := 1, destination := 611, sources := [224] }, { frame := 1, destination := 655, sources := [458] },
  { frame := 1, destination := 609, sources := [230] }, { frame := 1, destination := 629, sources := [231] },
  { frame := 1, destination := 447, sources := [630] }, { frame := 1, destination := 266, sources := [590] },
  { frame := 1, destination := 620, sources := [434] }, { frame := 1, destination := 586, sources := [438] },
  { frame := 1, destination := 255, sources := [634] }, { frame := 1, destination := 283, sources := [635] },
  { frame := 1, destination := 419, sources := [593] }, { frame := 1, destination := 260, sources := [592] },
  { frame := 1, destination := 275, sources := [577] }, { frame := 1, destination := 314, sources := [615] },
  { frame := 1, destination := 616, sources := [406] }, { frame := 1, destination := 568, sources := [441] },
  { frame := 1, destination := 423, sources := [591] }, { frame := 1, destination := 236, sources := [575] },
  { frame := 1, destination := 608, sources := [446] }, { frame := 1, destination := 660, sources := [330] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-a74015e476e3ac55"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk114`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5246)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 627, sources := [370] }, { frame := 1, destination := 626, sources := [339] },
  { frame := 1, destination := 457, sources := [572] }, { frame := 1, destination := 304, sources := [545] },
  { frame := 1, destination := 565, sources := [422] }, { frame := 1, destination := 603, sources := [318] },
  { frame := 1, destination := 374, sources := [604] }, { frame := 1, destination := 445, sources := [529] },
  { frame := 1, destination := 578, sources := [397] }, { frame := 1, destination := 302, sources := [560] },
  { frame := 1, destination := 571, sources := [513] }, { frame := 1, destination := 588, sources := [383] },
  { frame := 1, destination := 392, sources := [552] }, { frame := 1, destination := 367, sources := [576] },
  { frame := 1, destination := 527, sources := [391] }, { frame := 1, destination := 244, sources := [579] },
  { frame := 1, destination := 619, sources := [350] }, { frame := 1, destination := 618, sources := [335] },
  { frame := 1, destination := 613, sources := [249] }, { frame := 1, destination := 624, sources := [376] },
  { frame := 1, destination := 481, sources := [580] }, { frame := 1, destination := 334, sources := [583] },
  { frame := 1, destination := 328, sources := [558] }, { frame := 1, destination := 331, sources := [585] },
  { frame := 1, destination := 454, sources := [621] }, { frame := 1, destination := 453, sources := [587] },
  { frame := 1, destination := 353, sources := [547] }, { frame := 1, destination := 294, sources := [614] },
  { frame := 1, destination := 542, sources := [292] }, { frame := 1, destination := 589, sources := [412] },
  { frame := 1, destination := 594, sources := [390] }, { frame := 1, destination := 581, sources := [303] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-4816bcc1a62784bd"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk115`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5279)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 401, sources := [582] }, { frame := 1, destination := 280, sources := [596] },
  { frame := 1, destination := 554, sources := [388] }, { frame := 1, destination := 537, sources := [299] },
  { frame := 1, destination := 538, sources := [270] }, { frame := 1, destination := 607, sources := [395] },
  { frame := 1, destination := 437, sources := [599] }, { frame := 1, destination := 346, sources := [602] },
  { frame := 1, destination := 362, sources := [566] }, { frame := 1, destination := 378, sources := [567] },
  { frame := 1, destination := 448, sources := [617] }, { frame := 1, destination := 343, sources := [540] },
  { frame := 1, destination := 379, sources := [605] }, { frame := 1, destination := 298, sources := [559] },
  { frame := 1, destination := 524, sources := [261] }, { frame := 1, destination := 544, sources := [285] },
  { frame := 1, destination := 562, sources := [440] }, { frame := 1, destination := 563, sources := [315] },
  { frame := 1, destination := 389, sources := [564] }, { frame := 1, destination := 268, sources := [553] },
  { frame := 1, destination := 612, sources := [431] }, { frame := 1, destination := 519, sources := [269] },
  { frame := 1, destination := 556, sources := [279] }, { frame := 1, destination := 557, sources := [442] },
  { frame := 1, destination := 427, sources := [584] }, { frame := 1, destination := 342, sources := [597] },
  { frame := 1, destination := 225, sources := [522] }, { frame := 1, destination := 492, sources := [523] },
  { frame := 1, destination := 487, sources := [528] }, { frame := 1, destination := 337, sources := [551] },
  { frame := 1, destination := 369, sources := [598] }, { frame := 1, destination := 296, sources := [531] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-115f7a933abb81f9"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk116`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5312)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 606, sources := [384] }, { frame := 1, destination := 526, sources := [508] },
  { frame := 1, destination := 561, sources := [355] }, { frame := 1, destination := 601, sources := [420] },
  { frame := 1, destination := 405, sources := [532] }, { frame := 1, destination := 274, sources := [533] },
  { frame := 1, destination := 518, sources := [497] }, { frame := 1, destination := 573, sources := [286] },
  { frame := 1, destination := 574, sources := [281] }, { frame := 1, destination := 521, sources := [515] },
  { frame := 1, destination := 482, sources := [569] }, { frame := 1, destination := 232, sources := [570] },
  { frame := 1, destination := 505, sources := [530] }, { frame := 1, destination := 251, sources := [541] },
  { frame := 1, destination := 363, sources := [546] }, { frame := 1, destination := 456, sources := [535] },
  { frame := 1, destination := 222, sources := [534] }, { frame := 1, destination := 500, sources := [549] },
  { frame := 1, destination := 595, sources := [265] }, { frame := 1, destination := 525, sources := [512] },
  { frame := 1, destination := 543, sources := [361] }, { frame := 1, destination := 600, sources := [309] },
  { frame := 1, destination := 253, sources := [550] }, { frame := 1, destination := 252, sources := [517] },
  { frame := 1, destination := 536, sources := [359] }, { frame := 1, destination := 555, sources := [348] },
  { frame := 1, destination := 520, sources := [313] }, { frame := 1, destination := 539, sources := [426] },
  { frame := 1, destination := 502, sources := [548] }, { frame := 1, destination := 320, sources := [356] },
  { frame := 1, destination := 494, sources := [264] }, { frame := 1, destination := 495, sources := [496] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-c5d8ddd86ecc27fa"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk117`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5345)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 336, sources := [514] }, { frame := 1, destination := 387, sources := [321] },
  { frame := 1, destination := 347, sources := [516] }, { frame := 1, destination := 324, sources := [354] },
  { frame := 1, destination := 491, sources := [506] }, { frame := 1, destination := 312, sources := [489] },
  { frame := 1, destination := 344, sources := [325] }, { frame := 1, destination := 305, sources := [380] },
  { frame := 1, destination := 341, sources := [364] }, { frame := 1, destination := 486, sources := [455] },
  { frame := 1, destination := 223, sources := [308] }, { frame := 1, destination := 272, sources := [242] },
  { frame := 1, destination := 246, sources := [421] }, { frame := 1, destination := 485, sources := [503] },
  { frame := 1, destination := 243, sources := [338] }, { frame := 1, destination := 511, sources := [493] },
  { frame := 1, destination := 432, sources := [402] }, { frame := 1, destination := 430, sources := [291] },
  { frame := 1, destination := 409, sources := [372] }, { frame := 1, destination := 323, sources := [366] },
  { frame := 1, destination := 373, sources := [498] }, { frame := 1, destination := 326, sources := [510] },
  { frame := 1, destination := 509, sources := [488] }, { frame := 1, destination := 400, sources := [507] },
  { frame := 1, destination := 256, sources := [490] }, { frame := 1, destination := 345, sources := [310] },
  { frame := 1, destination := 375, sources := [329] }, { frame := 1, destination := 504, sources := [499] },
  { frame := 1, destination := 240, sources := [417] }, { frame := 1, destination := 501, sources := [483] },
  { frame := 1, destination := 234, sources := [484] }, { frame := 1, destination := 235, sources := [403] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-6a35d68eb6edfc2d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk118`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5378)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 247, sources := [351] }, { frame := 1, destination := 588, sources := [547] },
  { frame := 1, destination := 615, sources := [588] }, { frame := 1, destination := 615, sources := [547] },
  { frame := 1, destination := 639, sources := [615] }, { frame := 1, destination := 639, sources := [588] },
  { frame := 1, destination := 639, sources := [547] }, { frame := 1, destination := 657, sources := [639] },
  { frame := 1, destination := 657, sources := [615] }, { frame := 1, destination := 657, sources := [597] },
  { frame := 1, destination := 657, sources := [588] }, { frame := 1, destination := 657, sources := [547] },
  { frame := 1, destination := 615, sources := [657] }, { frame := 1, destination := 597, sources := [657] },
  { frame := 1, destination := 597, sources := [639] }, { frame := 1, destination := 597, sources := [615] },
  { frame := 1, destination := 588, sources := [657] }, { frame := 1, destination := 547, sources := [657] },
  { frame := 1, destination := 547, sources := [639] }, { frame := 1, destination := 547, sources := [615] },
  { frame := 1, destination := 547, sources := [597] }, { frame := 1, destination := 616, sources := [552] },
  { frame := 1, destination := 640, sources := [616] }, { frame := 1, destination := 640, sources := [552] },
  { frame := 1, destination := 658, sources := [640] }, { frame := 1, destination := 658, sources := [616] },
  { frame := 1, destination := 658, sources := [598] }, { frame := 1, destination := 658, sources := [552] },
  { frame := 1, destination := 616, sources := [658] }, { frame := 1, destination := 598, sources := [658] },
  { frame := 1, destination := 598, sources := [640] }, { frame := 1, destination := 598, sources := [616] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-372b4ae072d58c08"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk119`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5411)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 583, sources := [658] }, { frame := 1, destination := 583, sources := [640] },
  { frame := 1, destination := 583, sources := [616] }, { frame := 1, destination := 583, sources := [598] },
  { frame := 1, destination := 552, sources := [640] }, { frame := 1, destination := 552, sources := [616] },
  { frame := 1, destination := 552, sources := [598] }, { frame := 1, destination := 552, sources := [583] },
  { frame := 1, destination := 578, sources := [542] }, { frame := 1, destination := 608, sources := [606] },
  { frame := 1, destination := 608, sources := [578] }, { frame := 1, destination := 608, sources := [542] },
  { frame := 1, destination := 629, sources := [606] }, { frame := 1, destination := 629, sources := [578] },
  { frame := 1, destination := 629, sources := [542] }, { frame := 1, destination := 649, sources := [578] },
  { frame := 1, destination := 649, sources := [542] }, { frame := 1, destination := 629, sources := [649] },
  { frame := 1, destination := 608, sources := [649] }, { frame := 1, destination := 606, sources := [649] },
  { frame := 1, destination := 606, sources := [629] }, { frame := 1, destination := 606, sources := [608] },
  { frame := 1, destination := 578, sources := [606] }, { frame := 1, destination := 542, sources := [649] },
  { frame := 1, destination := 542, sources := [629] }, { frame := 1, destination := 542, sources := [608] },
  { frame := 1, destination := 542, sources := [606] }, { frame := 1, destination := 611, sources := [545] },
  { frame := 1, destination := 626, sources := [545] }, { frame := 1, destination := 654, sources := [626] },
  { frame := 1, destination := 654, sources := [611] }, { frame := 1, destination := 654, sources := [601] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-9bbab2f93f7aa94f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk120`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5444)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 654, sources := [545] }, { frame := 1, destination := 626, sources := [654] },
  { frame := 1, destination := 611, sources := [654] }, { frame := 1, destination := 601, sources := [654] },
  { frame := 1, destination := 601, sources := [626] }, { frame := 1, destination := 601, sources := [611] },
  { frame := 1, destination := 581, sources := [654] }, { frame := 1, destination := 581, sources := [626] },
  { frame := 1, destination := 581, sources := [611] }, { frame := 1, destination := 581, sources := [601] },
  { frame := 1, destination := 545, sources := [626] }, { frame := 1, destination := 545, sources := [611] },
  { frame := 1, destination := 545, sources := [601] }, { frame := 1, destination := 545, sources := [581] },
  { frame := 1, destination := 590, sources := [573] }, { frame := 1, destination := 590, sources := [537] },
  { frame := 1, destination := 619, sources := [573] }, { frame := 1, destination := 619, sources := [537] },
  { frame := 1, destination := 636, sources := [590] }, { frame := 1, destination := 636, sources := [573] },
  { frame := 1, destination := 636, sources := [537] }, { frame := 1, destination := 647, sources := [619] },
  { frame := 1, destination := 647, sources := [573] }, { frame := 1, destination := 647, sources := [537] },
  { frame := 1, destination := 619, sources := [647] }, { frame := 1, destination := 619, sources := [636] },
  { frame := 1, destination := 590, sources := [647] }, { frame := 1, destination := 590, sources := [636] },
  { frame := 1, destination := 573, sources := [647] }, { frame := 1, destination := 573, sources := [636] },
  { frame := 1, destination := 573, sources := [619] }, { frame := 1, destination := 573, sources := [590] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-a2f84ab2d2367e66"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk121`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5477)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 537, sources := [647] }, { frame := 1, destination := 537, sources := [636] },
  { frame := 1, destination := 537, sources := [619] }, { frame := 1, destination := 537, sources := [590] },
  { frame := 1, destination := 593, sources := [574] }, { frame := 1, destination := 593, sources := [538] },
  { frame := 1, destination := 624, sources := [574] }, { frame := 1, destination := 624, sources := [538] },
  { frame := 1, destination := 631, sources := [593] }, { frame := 1, destination := 631, sources := [574] },
  { frame := 1, destination := 631, sources := [538] }, { frame := 1, destination := 644, sources := [624] },
  { frame := 1, destination := 644, sources := [593] }, { frame := 1, destination := 644, sources := [574] },
  { frame := 1, destination := 644, sources := [538] }, { frame := 1, destination := 624, sources := [631] },
  { frame := 1, destination := 593, sources := [644] }, { frame := 1, destination := 574, sources := [644] },
  { frame := 1, destination := 574, sources := [631] }, { frame := 1, destination := 574, sources := [624] },
  { frame := 1, destination := 574, sources := [593] }, { frame := 1, destination := 538, sources := [644] },
  { frame := 1, destination := 538, sources := [631] }, { frame := 1, destination := 538, sources := [624] },
  { frame := 1, destination := 538, sources := [593] }, { frame := 1, destination := 623, sources := [605] },
  { frame := 1, destination := 623, sources := [529] }, { frame := 1, destination := 635, sources := [605] },
  { frame := 1, destination := 635, sources := [529] }, { frame := 1, destination := 653, sources := [605] },
  { frame := 1, destination := 653, sources := [529] }, { frame := 1, destination := 635, sources := [653] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-ffe865a1e4bcf432"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk122`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5510)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 623, sources := [635] }, { frame := 1, destination := 605, sources := [653] },
  { frame := 1, destination := 605, sources := [635] }, { frame := 1, destination := 605, sources := [623] },
  { frame := 1, destination := 570, sources := [653] }, { frame := 1, destination := 570, sources := [635] },
  { frame := 1, destination := 570, sources := [623] }, { frame := 1, destination := 570, sources := [605] },
  { frame := 1, destination := 529, sources := [653] }, { frame := 1, destination := 529, sources := [635] },
  { frame := 1, destination := 529, sources := [623] }, { frame := 1, destination := 529, sources := [570] },
  { frame := 1, destination := 569, sources := [530] }, { frame := 1, destination := 571, sources := [569] },
  { frame := 1, destination := 571, sources := [530] }, { frame := 1, destination := 596, sources := [569] },
  { frame := 1, destination := 596, sources := [540] }, { frame := 1, destination := 596, sources := [530] },
  { frame := 1, destination := 656, sources := [571] }, { frame := 1, destination := 656, sources := [569] },
  { frame := 1, destination := 656, sources := [530] }, { frame := 1, destination := 596, sources := [656] },
  { frame := 1, destination := 571, sources := [596] }, { frame := 1, destination := 569, sources := [571] },
  { frame := 1, destination := 540, sources := [656] }, { frame := 1, destination := 540, sources := [596] },
  { frame := 1, destination := 540, sources := [571] }, { frame := 1, destination := 530, sources := [656] },
  { frame := 1, destination := 530, sources := [596] }, { frame := 1, destination := 530, sources := [571] },
  { frame := 1, destination := 530, sources := [540] }, { frame := 1, destination := 568, sources := [541] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-a2e374b70d617b29"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk123`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5543)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 568, sources := [531] }, { frame := 1, destination := 582, sources := [531] },
  { frame := 1, destination := 617, sources := [582] }, { frame := 1, destination := 617, sources := [541] },
  { frame := 1, destination := 617, sources := [531] }, { frame := 1, destination := 641, sources := [568] },
  { frame := 1, destination := 641, sources := [541] }, { frame := 1, destination := 641, sources := [531] },
  { frame := 1, destination := 617, sources := [641] }, { frame := 1, destination := 568, sources := [641] },
  { frame := 1, destination := 568, sources := [582] }, { frame := 1, destination := 541, sources := [641] },
  { frame := 1, destination := 541, sources := [617] }, { frame := 1, destination := 541, sources := [582] },
  { frame := 1, destination := 541, sources := [568] }, { frame := 1, destination := 531, sources := [641] },
  { frame := 1, destination := 531, sources := [617] }, { frame := 1, destination := 531, sources := [582] },
  { frame := 1, destination := 531, sources := [568] }, { frame := 1, destination := 567, sources := [532] },
  { frame := 1, destination := 577, sources := [532] }, { frame := 1, destination := 614, sources := [567] },
  { frame := 1, destination := 614, sources := [546] }, { frame := 1, destination := 614, sources := [532] },
  { frame := 1, destination := 638, sources := [577] }, { frame := 1, destination := 638, sources := [532] },
  { frame := 1, destination := 614, sources := [638] }, { frame := 1, destination := 577, sources := [638] },
  { frame := 1, destination := 577, sources := [614] }, { frame := 1, destination := 567, sources := [577] },
  { frame := 1, destination := 546, sources := [638] }, { frame := 1, destination := 546, sources := [614] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0a998881cbda4d80"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk124`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5576)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 546, sources := [577] }, { frame := 1, destination := 546, sources := [567] },
  { frame := 1, destination := 532, sources := [638] }, { frame := 1, destination := 532, sources := [614] },
  { frame := 1, destination := 532, sources := [567] }, { frame := 1, destination := 532, sources := [546] },
  { frame := 1, destination := 566, sources := [533] }, { frame := 1, destination := 576, sources := [533] },
  { frame := 1, destination := 599, sources := [535] }, { frame := 1, destination := 599, sources := [533] },
  { frame := 1, destination := 659, sources := [576] }, { frame := 1, destination := 659, sources := [533] },
  { frame := 1, destination := 599, sources := [659] }, { frame := 1, destination := 576, sources := [599] },
  { frame := 1, destination := 566, sources := [576] }, { frame := 1, destination := 535, sources := [659] },
  { frame := 1, destination := 535, sources := [599] }, { frame := 1, destination := 535, sources := [576] },
  { frame := 1, destination := 533, sources := [659] }, { frame := 1, destination := 533, sources := [599] },
  { frame := 1, destination := 533, sources := [566] }, { frame := 1, destination := 533, sources := [535] },
  { frame := 1, destination := 565, sources := [534] }, { frame := 1, destination := 620, sources := [565] },
  { frame := 1, destination := 620, sources := [534] }, { frame := 1, destination := 632, sources := [565] },
  { frame := 1, destination := 632, sources := [534] }, { frame := 1, destination := 650, sources := [632] },
  { frame := 1, destination := 650, sources := [620] }, { frame := 1, destination := 650, sources := [602] },
  { frame := 1, destination := 650, sources := [565] }, { frame := 1, destination := 650, sources := [534] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-4aa1a19bb110c715"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk125`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5609)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 632, sources := [650] }, { frame := 1, destination := 620, sources := [650] },
  { frame := 1, destination := 602, sources := [650] }, { frame := 1, destination := 602, sources := [632] },
  { frame := 1, destination := 602, sources := [620] }, { frame := 1, destination := 565, sources := [650] },
  { frame := 1, destination := 534, sources := [650] }, { frame := 1, destination := 534, sources := [632] },
  { frame := 1, destination := 534, sources := [620] }, { frame := 1, destination := 534, sources := [602] },
  { frame := 1, destination := 564, sources := [523] }, { frame := 1, destination := 586, sources := [523] },
  { frame := 1, destination := 621, sources := [549] }, { frame := 1, destination := 621, sources := [523] },
  { frame := 1, destination := 633, sources := [621] }, { frame := 1, destination := 633, sources := [586] },
  { frame := 1, destination := 633, sources := [523] }, { frame := 1, destination := 621, sources := [633] },
  { frame := 1, destination := 586, sources := [633] }, { frame := 1, destination := 564, sources := [586] },
  { frame := 1, destination := 549, sources := [633] }, { frame := 1, destination := 549, sources := [621] },
  { frame := 1, destination := 549, sources := [586] }, { frame := 1, destination := 523, sources := [633] },
  { frame := 1, destination := 523, sources := [621] }, { frame := 1, destination := 523, sources := [564] },
  { frame := 1, destination := 523, sources := [549] }, { frame := 1, destination := 560, sources := [524] },
  { frame := 1, destination := 609, sources := [595] }, { frame := 1, destination := 609, sources := [560] },
  { frame := 1, destination := 609, sources := [524] }, { frame := 1, destination := 628, sources := [609] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-31553c119a23f263"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk126`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5642)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 628, sources := [595] }, { frame := 1, destination := 628, sources := [560] },
  { frame := 1, destination := 628, sources := [524] }, { frame := 1, destination := 660, sources := [595] },
  { frame := 1, destination := 660, sources := [560] }, { frame := 1, destination := 660, sources := [524] },
  { frame := 1, destination := 628, sources := [660] }, { frame := 1, destination := 609, sources := [660] },
  { frame := 1, destination := 595, sources := [660] }, { frame := 1, destination := 595, sources := [628] },
  { frame := 1, destination := 595, sources := [609] }, { frame := 1, destination := 560, sources := [595] },
  { frame := 1, destination := 524, sources := [660] }, { frame := 1, destination := 524, sources := [628] },
  { frame := 1, destination := 524, sources := [609] }, { frame := 1, destination := 524, sources := [595] },
  { frame := 1, destination := 561, sources := [525] }, { frame := 1, destination := 580, sources := [561] },
  { frame := 1, destination := 580, sources := [525] }, { frame := 1, destination := 594, sources := [561] },
  { frame := 1, destination := 594, sources := [544] }, { frame := 1, destination := 594, sources := [525] },
  { frame := 1, destination := 643, sources := [594] }, { frame := 1, destination := 643, sources := [580] },
  { frame := 1, destination := 643, sources := [561] }, { frame := 1, destination := 643, sources := [525] },
  { frame := 1, destination := 594, sources := [643] }, { frame := 1, destination := 580, sources := [643] },
  { frame := 1, destination := 580, sources := [594] }, { frame := 1, destination := 561, sources := [580] },
  { frame := 1, destination := 544, sources := [643] }, { frame := 1, destination := 544, sources := [594] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-61c89f579075954a"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk127`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5675)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 544, sources := [580] }, { frame := 1, destination := 525, sources := [643] },
  { frame := 1, destination := 525, sources := [594] }, { frame := 1, destination := 525, sources := [580] },
  { frame := 1, destination := 525, sources := [544] }, { frame := 1, destination := 562, sources := [543] },
  { frame := 1, destination := 579, sources := [562] }, { frame := 1, destination := 579, sources := [543] },
  { frame := 1, destination := 579, sources := [526] }, { frame := 1, destination := 589, sources := [562] },
  { frame := 1, destination := 589, sources := [543] }, { frame := 1, destination := 589, sources := [526] },
  { frame := 1, destination := 648, sources := [589] }, { frame := 1, destination := 648, sources := [579] },
  { frame := 1, destination := 648, sources := [562] }, { frame := 1, destination := 648, sources := [543] },
  { frame := 1, destination := 648, sources := [526] }, { frame := 1, destination := 589, sources := [648] },
  { frame := 1, destination := 543, sources := [648] }, { frame := 1, destination := 543, sources := [589] },
  { frame := 1, destination := 543, sources := [579] }, { frame := 1, destination := 543, sources := [562] },
  { frame := 1, destination := 526, sources := [648] }, { frame := 1, destination := 526, sources := [589] },
  { frame := 1, destination := 526, sources := [579] }, { frame := 1, destination := 526, sources := [562] },
  { frame := 1, destination := 610, sources := [600] }, { frame := 1, destination := 610, sources := [527] },
  { frame := 1, destination := 627, sources := [600] }, { frame := 1, destination := 627, sources := [527] },
  { frame := 1, destination := 655, sources := [600] }, { frame := 1, destination := 655, sources := [527] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-cdf1e786ec244787"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk128`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5708)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 627, sources := [655] }, { frame := 1, destination := 610, sources := [627] },
  { frame := 1, destination := 600, sources := [655] }, { frame := 1, destination := 600, sources := [627] },
  { frame := 1, destination := 600, sources := [610] }, { frame := 1, destination := 563, sources := [655] },
  { frame := 1, destination := 563, sources := [627] }, { frame := 1, destination := 563, sources := [610] },
  { frame := 1, destination := 563, sources := [600] }, { frame := 1, destination := 527, sources := [655] },
  { frame := 1, destination := 527, sources := [627] }, { frame := 1, destination := 527, sources := [610] },
  { frame := 1, destination := 527, sources := [563] }, { frame := 1, destination := 559, sources := [550] },
  { frame := 1, destination := 559, sources := [528] }, { frame := 1, destination := 585, sources := [528] },
  { frame := 1, destination := 622, sources := [550] }, { frame := 1, destination := 622, sources := [528] },
  { frame := 1, destination := 634, sources := [550] }, { frame := 1, destination := 634, sources := [528] },
  { frame := 1, destination := 559, sources := [634] }, { frame := 1, destination := 559, sources := [622] },
  { frame := 1, destination := 550, sources := [634] }, { frame := 1, destination := 550, sources := [622] },
  { frame := 1, destination := 550, sources := [585] }, { frame := 1, destination := 528, sources := [634] },
  { frame := 1, destination := 528, sources := [622] }, { frame := 1, destination := 528, sources := [559] },
  { frame := 1, destination := 551, sources := [517] }, { frame := 1, destination := 558, sources := [517] },
  { frame := 1, destination := 584, sources := [551] }, { frame := 1, destination := 603, sources := [584] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-757e29d2b500e0e3"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk129`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5741)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 603, sources := [558] }, { frame := 1, destination := 603, sources := [517] },
  { frame := 1, destination := 651, sources := [584] }, { frame := 1, destination := 651, sources := [558] },
  { frame := 1, destination := 651, sources := [517] }, { frame := 1, destination := 584, sources := [651] },
  { frame := 1, destination := 584, sources := [603] }, { frame := 1, destination := 558, sources := [584] },
  { frame := 1, destination := 551, sources := [558] }, { frame := 1, destination := 517, sources := [651] },
  { frame := 1, destination := 517, sources := [603] }, { frame := 1, destination := 517, sources := [584] },
  { frame := 1, destination := 517, sources := [551] }, { frame := 1, destination := 554, sources := [536] },
  { frame := 1, destination := 554, sources := [518] }, { frame := 1, destination := 572, sources := [554] },
  { frame := 1, destination := 572, sources := [536] }, { frame := 1, destination := 572, sources := [518] },
  { frame := 1, destination := 612, sources := [536] }, { frame := 1, destination := 612, sources := [518] },
  { frame := 1, destination := 625, sources := [572] }, { frame := 1, destination := 625, sources := [554] },
  { frame := 1, destination := 625, sources := [536] }, { frame := 1, destination := 625, sources := [518] },
  { frame := 1, destination := 612, sources := [625] }, { frame := 1, destination := 572, sources := [625] },
  { frame := 1, destination := 572, sources := [612] }, { frame := 1, destination := 554, sources := [625] },
  { frame := 1, destination := 554, sources := [612] }, { frame := 1, destination := 554, sources := [572] },
  { frame := 1, destination := 536, sources := [625] }, { frame := 1, destination := 536, sources := [612] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-581ee69f51776460"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk130`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5774)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 536, sources := [572] }, { frame := 1, destination := 536, sources := [554] },
  { frame := 1, destination := 518, sources := [625] }, { frame := 1, destination := 518, sources := [612] },
  { frame := 1, destination := 518, sources := [554] }, { frame := 1, destination := 592, sources := [555] },
  { frame := 1, destination := 592, sources := [519] }, { frame := 1, destination := 613, sources := [555] },
  { frame := 1, destination := 613, sources := [519] }, { frame := 1, destination := 642, sources := [592] },
  { frame := 1, destination := 642, sources := [555] }, { frame := 1, destination := 642, sources := [519] },
  { frame := 1, destination := 645, sources := [613] }, { frame := 1, destination := 645, sources := [555] },
  { frame := 1, destination := 645, sources := [519] }, { frame := 1, destination := 613, sources := [645] },
  { frame := 1, destination := 613, sources := [642] }, { frame := 1, destination := 592, sources := [645] },
  { frame := 1, destination := 555, sources := [645] }, { frame := 1, destination := 555, sources := [642] },
  { frame := 1, destination := 555, sources := [613] }, { frame := 1, destination := 555, sources := [592] },
  { frame := 1, destination := 519, sources := [645] }, { frame := 1, destination := 519, sources := [642] },
  { frame := 1, destination := 519, sources := [613] }, { frame := 1, destination := 519, sources := [592] },
  { frame := 1, destination := 591, sources := [556] }, { frame := 1, destination := 591, sources := [520] },
  { frame := 1, destination := 618, sources := [556] }, { frame := 1, destination := 618, sources := [520] },
  { frame := 1, destination := 637, sources := [591] }, { frame := 1, destination := 637, sources := [556] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-f240335723a58a80"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk131`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5807)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 637, sources := [520] }, { frame := 1, destination := 646, sources := [618] },
  { frame := 1, destination := 646, sources := [591] }, { frame := 1, destination := 646, sources := [556] },
  { frame := 1, destination := 646, sources := [520] }, { frame := 1, destination := 618, sources := [637] },
  { frame := 1, destination := 591, sources := [646] }, { frame := 1, destination := 556, sources := [646] },
  { frame := 1, destination := 556, sources := [637] }, { frame := 1, destination := 556, sources := [618] },
  { frame := 1, destination := 556, sources := [591] }, { frame := 1, destination := 520, sources := [646] },
  { frame := 1, destination := 520, sources := [637] }, { frame := 1, destination := 520, sources := [618] },
  { frame := 1, destination := 520, sources := [591] }, { frame := 1, destination := 557, sources := [539] },
  { frame := 1, destination := 557, sources := [521] }, { frame := 1, destination := 575, sources := [539] },
  { frame := 1, destination := 575, sources := [521] }, { frame := 1, destination := 607, sources := [539] },
  { frame := 1, destination := 607, sources := [521] }, { frame := 1, destination := 630, sources := [607] },
  { frame := 1, destination := 630, sources := [575] }, { frame := 1, destination := 630, sources := [539] },
  { frame := 1, destination := 630, sources := [521] }, { frame := 1, destination := 607, sources := [630] },
  { frame := 1, destination := 557, sources := [630] }, { frame := 1, destination := 557, sources := [607] },
  { frame := 1, destination := 557, sources := [575] }, { frame := 1, destination := 539, sources := [630] },
  { frame := 1, destination := 539, sources := [607] }, { frame := 1, destination := 539, sources := [575] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-9562d27c919a9a4e"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk132`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5840)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 521, sources := [630] }, { frame := 1, destination := 521, sources := [607] },
  { frame := 1, destination := 521, sources := [575] }, { frame := 1, destination := 521, sources := [557] },
  { frame := 1, destination := 553, sources := [548] }, { frame := 1, destination := 587, sources := [548] },
  { frame := 1, destination := 587, sources := [522] }, { frame := 1, destination := 604, sources := [587] },
  { frame := 1, destination := 604, sources := [522] }, { frame := 1, destination := 652, sources := [587] },
  { frame := 1, destination := 652, sources := [522] }, { frame := 1, destination := 587, sources := [652] },
  { frame := 1, destination := 587, sources := [604] }, { frame := 1, destination := 548, sources := [652] },
  { frame := 1, destination := 548, sources := [604] }, { frame := 1, destination := 548, sources := [587] },
  { frame := 1, destination := 522, sources := [652] }, { frame := 1, destination := 522, sources := [604] },
  { frame := 1, destination := 522, sources := [553] }, { frame := 1, destination := 522, sources := [548] },
  { frame := 1, destination := 350, sources := [516] }, { frame := 1, destination := 350, sources := [493] },
  { frame := 1, destination := 363, sources := [516] }, { frame := 1, destination := 363, sources := [493] },
  { frame := 1, destination := 448, sources := [516] }, { frame := 1, destination := 448, sources := [493] },
  { frame := 1, destination := 450, sources := [448] }, { frame := 1, destination := 450, sources := [350] },
  { frame := 1, destination := 450, sources := [516] }, { frame := 1, destination := 450, sources := [493] },
  { frame := 1, destination := 448, sources := [450] }, { frame := 1, destination := 363, sources := [450] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-33cde646381e36ab"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk133`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5873)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 363, sources := [448] }, { frame := 1, destination := 350, sources := [448] },
  { frame := 1, destination := 350, sources := [363] }, { frame := 1, destination := 516, sources := [450] },
  { frame := 1, destination := 516, sources := [448] }, { frame := 1, destination := 516, sources := [363] },
  { frame := 1, destination := 516, sources := [350] }, { frame := 1, destination := 493, sources := [450] },
  { frame := 1, destination := 493, sources := [448] }, { frame := 1, destination := 493, sources := [363] },
  { frame := 1, destination := 493, sources := [350] }, { frame := 1, destination := 328, sources := [511] },
  { frame := 1, destination := 328, sources := [320] }, { frame := 1, destination := 330, sources := [328] },
  { frame := 1, destination := 330, sources := [511] }, { frame := 1, destination := 330, sources := [320] },
  { frame := 1, destination := 225, sources := [511] }, { frame := 1, destination := 225, sources := [320] },
  { frame := 1, destination := 458, sources := [330] }, { frame := 1, destination := 458, sources := [328] },
  { frame := 1, destination := 458, sources := [511] }, { frame := 1, destination := 458, sources := [320] },
  { frame := 1, destination := 225, sources := [458] }, { frame := 1, destination := 330, sources := [225] },
  { frame := 1, destination := 328, sources := [458] }, { frame := 1, destination := 328, sources := [225] },
  { frame := 1, destination := 511, sources := [458] }, { frame := 1, destination := 511, sources := [225] },
  { frame := 1, destination := 511, sources := [330] }, { frame := 1, destination := 511, sources := [328] },
  { frame := 1, destination := 320, sources := [458] }, { frame := 1, destination := 320, sources := [225] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-6df342a089b69a8d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk134`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5906)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 320, sources := [330] }, { frame := 1, destination := 320, sources := [328] },
  { frame := 1, destination := 512, sources := [494] }, { frame := 1, destination := 314, sources := [402] },
  { frame := 1, destination := 314, sources := [512] }, { frame := 1, destination := 314, sources := [494] },
  { frame := 1, destination := 440, sources := [402] }, { frame := 1, destination := 440, sources := [512] },
  { frame := 1, destination := 440, sources := [494] }, { frame := 1, destination := 262, sources := [440] },
  { frame := 1, destination := 262, sources := [314] }, { frame := 1, destination := 262, sources := [402] },
  { frame := 1, destination := 262, sources := [512] }, { frame := 1, destination := 262, sources := [494] },
  { frame := 1, destination := 440, sources := [262] }, { frame := 1, destination := 402, sources := [262] },
  { frame := 1, destination := 402, sources := [440] }, { frame := 1, destination := 402, sources := [314] },
  { frame := 1, destination := 512, sources := [402] }, { frame := 1, destination := 494, sources := [262] },
  { frame := 1, destination := 494, sources := [440] }, { frame := 1, destination := 494, sources := [314] },
  { frame := 1, destination := 494, sources := [402] }, { frame := 1, destination := 515, sources := [321] },
  { frame := 1, destination := 422, sources := [515] }, { frame := 1, destination := 422, sources := [321] },
  { frame := 1, destination := 388, sources := [432] }, { frame := 1, destination := 388, sources := [515] },
  { frame := 1, destination := 388, sources := [321] }, { frame := 1, destination := 301, sources := [422] },
  { frame := 1, destination := 301, sources := [515] }, { frame := 1, destination := 301, sources := [321] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-df83c98338c0edaf"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk135`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5939)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 388, sources := [301] }, { frame := 1, destination := 422, sources := [388] },
  { frame := 1, destination := 432, sources := [301] }, { frame := 1, destination := 432, sources := [388] },
  { frame := 1, destination := 432, sources := [422] }, { frame := 1, destination := 515, sources := [422] },
  { frame := 1, destination := 321, sources := [301] }, { frame := 1, destination := 321, sources := [388] },
  { frame := 1, destination := 321, sources := [422] }, { frame := 1, destination := 321, sources := [432] },
  { frame := 1, destination := 513, sources := [495] }, { frame := 1, destination := 438, sources := [513] },
  { frame := 1, destination := 438, sources := [495] }, { frame := 1, destination := 267, sources := [438] },
  { frame := 1, destination := 267, sources := [513] }, { frame := 1, destination := 267, sources := [495] },
  { frame := 1, destination := 317, sources := [267] }, { frame := 1, destination := 317, sources := [438] },
  { frame := 1, destination := 317, sources := [291] }, { frame := 1, destination := 317, sources := [513] },
  { frame := 1, destination := 317, sources := [495] }, { frame := 1, destination := 438, sources := [317] },
  { frame := 1, destination := 291, sources := [317] }, { frame := 1, destination := 291, sources := [267] },
  { frame := 1, destination := 291, sources := [438] }, { frame := 1, destination := 513, sources := [317] },
  { frame := 1, destination := 495, sources := [317] }, { frame := 1, destination := 495, sources := [267] },
  { frame := 1, destination := 495, sources := [438] }, { frame := 1, destination := 495, sources := [291] },
  { frame := 1, destination := 384, sources := [348] }, { frame := 1, destination := 279, sources := [384] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-f635a086cb1c15c7"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk136`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L5972)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 279, sources := [430] }, { frame := 1, destination := 279, sources := [348] },
  { frame := 1, destination := 303, sources := [384] }, { frame := 1, destination := 303, sources := [348] },
  { frame := 1, destination := 279, sources := [303] }, { frame := 1, destination := 384, sources := [279] },
  { frame := 1, destination := 430, sources := [303] }, { frame := 1, destination := 430, sources := [279] },
  { frame := 1, destination := 430, sources := [384] }, { frame := 1, destination := 514, sources := [303] },
  { frame := 1, destination := 514, sources := [279] }, { frame := 1, destination := 514, sources := [384] },
  { frame := 1, destination := 514, sources := [430] }, { frame := 1, destination := 348, sources := [303] },
  { frame := 1, destination := 348, sources := [384] }, { frame := 1, destination := 348, sources := [430] },
  { frame := 1, destination := 348, sources := [514] }, { frame := 1, destination := 420, sources := [372] },
  { frame := 1, destination := 420, sources := [496] }, { frame := 1, destination := 313, sources := [372] },
  { frame := 1, destination := 313, sources := [496] }, { frame := 1, destination := 269, sources := [313] },
  { frame := 1, destination := 269, sources := [420] }, { frame := 1, destination := 269, sources := [372] },
  { frame := 1, destination := 269, sources := [496] }, { frame := 1, destination := 292, sources := [420] },
  { frame := 1, destination := 292, sources := [372] }, { frame := 1, destination := 292, sources := [496] },
  { frame := 1, destination := 269, sources := [292] }, { frame := 1, destination := 313, sources := [292] },
  { frame := 1, destination := 420, sources := [292] }, { frame := 1, destination := 420, sources := [269] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-3128f8fdf18c384f"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk137`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6005)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 372, sources := [292] }, { frame := 1, destination := 372, sources := [269] },
  { frame := 1, destination := 372, sources := [313] }, { frame := 1, destination := 372, sources := [420] },
  { frame := 1, destination := 496, sources := [292] }, { frame := 1, destination := 496, sources := [269] },
  { frame := 1, destination := 496, sources := [313] }, { frame := 1, destination := 496, sources := [420] },
  { frame := 1, destination := 367, sources := [336] }, { frame := 1, destination := 282, sources := [409] },
  { frame := 1, destination := 282, sources := [367] }, { frame := 1, destination := 282, sources := [336] },
  { frame := 1, destination := 255, sources := [409] }, { frame := 1, destination := 255, sources := [367] },
  { frame := 1, destination := 255, sources := [336] }, { frame := 1, destination := 306, sources := [409] },
  { frame := 1, destination := 306, sources := [367] }, { frame := 1, destination := 306, sources := [336] },
  { frame := 1, destination := 255, sources := [306] }, { frame := 1, destination := 282, sources := [255] },
  { frame := 1, destination := 409, sources := [306] }, { frame := 1, destination := 409, sources := [255] },
  { frame := 1, destination := 409, sources := [282] }, { frame := 1, destination := 367, sources := [409] },
  { frame := 1, destination := 336, sources := [306] }, { frame := 1, destination := 336, sources := [255] },
  { frame := 1, destination := 336, sources := [282] }, { frame := 1, destination := 336, sources := [409] },
  { frame := 1, destination := 445, sources := [497] }, { frame := 1, destination := 395, sources := [264] },
  { frame := 1, destination := 395, sources := [497] }, { frame := 1, destination := 289, sources := [445] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-6c55d1415040314d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk138`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6038)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 289, sources := [497] }, { frame := 1, destination := 395, sources := [289] },
  { frame := 1, destination := 445, sources := [395] }, { frame := 1, destination := 264, sources := [289] },
  { frame := 1, destination := 264, sources := [395] }, { frame := 1, destination := 264, sources := [445] },
  { frame := 1, destination := 366, sources := [289] }, { frame := 1, destination := 366, sources := [395] },
  { frame := 1, destination := 366, sources := [445] }, { frame := 1, destination := 366, sources := [264] },
  { frame := 1, destination := 497, sources := [289] }, { frame := 1, destination := 497, sources := [395] },
  { frame := 1, destination := 497, sources := [264] }, { frame := 1, destination := 497, sources := [366] },
  { frame := 1, destination := 361, sources := [323] }, { frame := 1, destination := 406, sources := [361] },
  { frame := 1, destination := 406, sources := [323] }, { frame := 1, destination := 285, sources := [387] },
  { frame := 1, destination := 285, sources := [361] }, { frame := 1, destination := 285, sources := [323] },
  { frame := 1, destination := 424, sources := [285] }, { frame := 1, destination := 424, sources := [406] },
  { frame := 1, destination := 424, sources := [361] }, { frame := 1, destination := 424, sources := [323] },
  { frame := 1, destination := 285, sources := [424] }, { frame := 1, destination := 406, sources := [424] },
  { frame := 1, destination := 387, sources := [424] }, { frame := 1, destination := 387, sources := [285] },
  { frame := 1, destination := 387, sources := [406] }, { frame := 1, destination := 361, sources := [406] },
  { frame := 1, destination := 323, sources := [424] }, { frame := 1, destination := 323, sources := [285] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-dc0f97ca9ae29b9d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk139`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6071)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 323, sources := [406] }, { frame := 1, destination := 323, sources := [387] },
  { frame := 1, destination := 376, sources := [356] }, { frame := 1, destination := 376, sources := [498] },
  { frame := 1, destination := 378, sources := [356] }, { frame := 1, destination := 378, sources := [498] },
  { frame := 1, destination := 251, sources := [356] }, { frame := 1, destination := 251, sources := [498] },
  { frame := 1, destination := 460, sources := [251] }, { frame := 1, destination := 460, sources := [376] },
  { frame := 1, destination := 460, sources := [356] }, { frame := 1, destination := 460, sources := [498] },
  { frame := 1, destination := 251, sources := [460] }, { frame := 1, destination := 378, sources := [460] },
  { frame := 1, destination := 378, sources := [251] }, { frame := 1, destination := 376, sources := [251] },
  { frame := 1, destination := 376, sources := [378] }, { frame := 1, destination := 356, sources := [460] },
  { frame := 1, destination := 356, sources := [251] }, { frame := 1, destination := 356, sources := [378] },
  { frame := 1, destination := 356, sources := [376] }, { frame := 1, destination := 498, sources := [460] },
  { frame := 1, destination := 498, sources := [251] }, { frame := 1, destination := 498, sources := [378] },
  { frame := 1, destination := 498, sources := [376] }, { frame := 1, destination := 370, sources := [347] },
  { frame := 1, destination := 370, sources := [337] }, { frame := 1, destination := 453, sources := [347] },
  { frame := 1, destination := 453, sources := [337] }, { frame := 1, destination := 230, sources := [453] },
  { frame := 1, destination := 230, sources := [370] }, { frame := 1, destination := 230, sources := [347] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-4af9e3108fed5401"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk140`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6104)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 230, sources := [337] }, { frame := 1, destination := 453, sources := [230] },
  { frame := 1, destination := 347, sources := [230] }, { frame := 1, destination := 347, sources := [453] },
  { frame := 1, destination := 347, sources := [370] }, { frame := 1, destination := 373, sources := [230] },
  { frame := 1, destination := 373, sources := [453] }, { frame := 1, destination := 373, sources := [370] },
  { frame := 1, destination := 373, sources := [347] }, { frame := 1, destination := 337, sources := [230] },
  { frame := 1, destination := 337, sources := [453] }, { frame := 1, destination := 337, sources := [370] },
  { frame := 1, destination := 337, sources := [373] }, { frame := 1, destination := 335, sources := [364] },
  { frame := 1, destination := 335, sources := [487] }, { frame := 1, destination := 454, sources := [364] },
  { frame := 1, destination := 454, sources := [487] }, { frame := 1, destination := 239, sources := [454] },
  { frame := 1, destination := 239, sources := [335] }, { frame := 1, destination := 239, sources := [364] },
  { frame := 1, destination := 239, sources := [487] }, { frame := 1, destination := 454, sources := [239] },
  { frame := 1, destination := 364, sources := [239] }, { frame := 1, destination := 364, sources := [454] },
  { frame := 1, destination := 364, sources := [335] }, { frame := 1, destination := 510, sources := [239] },
  { frame := 1, destination := 510, sources := [454] }, { frame := 1, destination := 510, sources := [335] },
  { frame := 1, destination := 510, sources := [364] }, { frame := 1, destination := 487, sources := [239] },
  { frame := 1, destination := 487, sources := [454] }, { frame := 1, destination := 487, sources := [335] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-8ed67ae8e24d9d57"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk141`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6137)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 487, sources := [510] }, { frame := 1, destination := 505, sources := [324] },
  { frame := 1, destination := 362, sources := [505] }, { frame := 1, destination := 362, sources := [324] },
  { frame := 1, destination := 224, sources := [326] }, { frame := 1, destination := 224, sources := [505] },
  { frame := 1, destination := 224, sources := [324] }, { frame := 1, destination := 446, sources := [326] },
  { frame := 1, destination := 446, sources := [505] }, { frame := 1, destination := 446, sources := [324] },
  { frame := 1, destination := 326, sources := [446] }, { frame := 1, destination := 326, sources := [224] },
  { frame := 1, destination := 326, sources := [362] }, { frame := 1, destination := 505, sources := [362] },
  { frame := 1, destination := 505, sources := [326] }, { frame := 1, destination := 324, sources := [446] },
  { frame := 1, destination := 324, sources := [224] }, { frame := 1, destination := 324, sources := [362] },
  { frame := 1, destination := 324, sources := [326] }, { frame := 1, destination := 286, sources := [506] },
  { frame := 1, destination := 286, sources := [488] }, { frame := 1, destination := 265, sources := [506] },
  { frame := 1, destination := 265, sources := [488] }, { frame := 1, destination := 315, sources := [265] },
  { frame := 1, destination := 315, sources := [506] }, { frame := 1, destination := 315, sources := [488] },
  { frame := 1, destination := 270, sources := [315] }, { frame := 1, destination := 270, sources := [265] },
  { frame := 1, destination := 270, sources := [286] }, { frame := 1, destination := 270, sources := [506] },
  { frame := 1, destination := 270, sources := [488] }, { frame := 1, destination := 265, sources := [270] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-84dffae6de621ef8"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk142`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6170)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 265, sources := [315] }, { frame := 1, destination := 286, sources := [315] },
  { frame := 1, destination := 506, sources := [270] }, { frame := 1, destination := 506, sources := [315] },
  { frame := 1, destination := 506, sources := [265] }, { frame := 1, destination := 506, sources := [286] },
  { frame := 1, destination := 488, sources := [270] }, { frame := 1, destination := 488, sources := [315] },
  { frame := 1, destination := 488, sources := [265] }, { frame := 1, destination := 488, sources := [286] },
  { frame := 1, destination := 441, sources := [305] }, { frame := 1, destination := 441, sources := [318] },
  { frame := 1, destination := 414, sources := [441] }, { frame := 1, destination := 414, sources := [305] },
  { frame := 1, destination := 414, sources := [318] }, { frame := 1, destination := 300, sources := [305] },
  { frame := 1, destination := 300, sources := [318] }, { frame := 1, destination := 414, sources := [300] },
  { frame := 1, destination := 441, sources := [300] }, { frame := 1, destination := 305, sources := [300] },
  { frame := 1, destination := 305, sources := [414] }, { frame := 1, destination := 305, sources := [441] },
  { frame := 1, destination := 509, sources := [300] }, { frame := 1, destination := 509, sources := [414] },
  { frame := 1, destination := 509, sources := [441] }, { frame := 1, destination := 509, sources := [305] },
  { frame := 1, destination := 318, sources := [300] }, { frame := 1, destination := 318, sources := [414] },
  { frame := 1, destination := 318, sources := [441] }, { frame := 1, destination := 318, sources := [509] },
  { frame := 1, destination := 431, sources := [507] }, { frame := 1, destination := 431, sources := [489] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2d6f32f1488d6793"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk143`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6203)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 426, sources := [507] }, { frame := 1, destination := 426, sources := [489] },
  { frame := 1, destination := 408, sources := [426] }, { frame := 1, destination := 408, sources := [431] },
  { frame := 1, destination := 408, sources := [507] }, { frame := 1, destination := 408, sources := [489] },
  { frame := 1, destination := 383, sources := [426] }, { frame := 1, destination := 383, sources := [431] },
  { frame := 1, destination := 383, sources := [507] }, { frame := 1, destination := 383, sources := [489] },
  { frame := 1, destination := 426, sources := [383] }, { frame := 1, destination := 426, sources := [408] },
  { frame := 1, destination := 431, sources := [383] }, { frame := 1, destination := 431, sources := [408] },
  { frame := 1, destination := 507, sources := [383] }, { frame := 1, destination := 507, sources := [408] },
  { frame := 1, destination := 507, sources := [426] }, { frame := 1, destination := 507, sources := [431] },
  { frame := 1, destination := 489, sources := [383] }, { frame := 1, destination := 489, sources := [408] },
  { frame := 1, destination := 489, sources := [426] }, { frame := 1, destination := 489, sources := [431] },
  { frame := 1, destination := 508, sources := [344] }, { frame := 1, destination := 390, sources := [400] },
  { frame := 1, destination := 390, sources := [508] }, { frame := 1, destination := 390, sources := [344] },
  { frame := 1, destination := 283, sources := [400] }, { frame := 1, destination := 283, sources := [508] },
  { frame := 1, destination := 283, sources := [344] }, { frame := 1, destination := 418, sources := [400] },
  { frame := 1, destination := 418, sources := [508] }, { frame := 1, destination := 418, sources := [344] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0a37565cb573e76d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk144`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6236)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 390, sources := [418] }, { frame := 1, destination := 390, sources := [283] },
  { frame := 1, destination := 400, sources := [418] }, { frame := 1, destination := 400, sources := [283] },
  { frame := 1, destination := 400, sources := [390] }, { frame := 1, destination := 508, sources := [390] },
  { frame := 1, destination := 508, sources := [400] }, { frame := 1, destination := 344, sources := [418] },
  { frame := 1, destination := 344, sources := [283] }, { frame := 1, destination := 344, sources := [390] },
  { frame := 1, destination := 344, sources := [400] }, { frame := 1, destination := 355, sources := [490] },
  { frame := 1, destination := 412, sources := [355] }, { frame := 1, destination := 412, sources := [490] },
  { frame := 1, destination := 434, sources := [312] }, { frame := 1, destination := 434, sources := [355] },
  { frame := 1, destination := 434, sources := [490] }, { frame := 1, destination := 429, sources := [312] },
  { frame := 1, destination := 429, sources := [355] }, { frame := 1, destination := 429, sources := [490] },
  { frame := 1, destination := 312, sources := [429] }, { frame := 1, destination := 312, sources := [434] },
  { frame := 1, destination := 312, sources := [412] }, { frame := 1, destination := 355, sources := [412] },
  { frame := 1, destination := 355, sources := [312] }, { frame := 1, destination := 490, sources := [429] },
  { frame := 1, destination := 490, sources := [434] }, { frame := 1, destination := 490, sources := [412] },
  { frame := 1, destination := 490, sources := [312] }, { frame := 1, destination := 359, sources := [325] },
  { frame := 1, destination := 442, sources := [359] }, { frame := 1, destination := 442, sources := [325] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-23471a6e3ba45ed1"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk145`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6269)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 404, sources := [442] }, { frame := 1, destination := 404, sources := [256] },
  { frame := 1, destination := 404, sources := [359] }, { frame := 1, destination := 404, sources := [325] },
  { frame := 1, destination := 392, sources := [442] }, { frame := 1, destination := 392, sources := [256] },
  { frame := 1, destination := 392, sources := [359] }, { frame := 1, destination := 392, sources := [325] },
  { frame := 1, destination := 256, sources := [392] }, { frame := 1, destination := 256, sources := [404] },
  { frame := 1, destination := 256, sources := [442] }, { frame := 1, destination := 359, sources := [256] },
  { frame := 1, destination := 325, sources := [392] }, { frame := 1, destination := 325, sources := [404] },
  { frame := 1, destination := 325, sources := [442] }, { frame := 1, destination := 325, sources := [256] },
  { frame := 1, destination := 374, sources := [491] }, { frame := 1, destination := 275, sources := [310] },
  { frame := 1, destination := 275, sources := [374] }, { frame := 1, destination := 275, sources := [491] },
  { frame := 1, destination := 263, sources := [310] }, { frame := 1, destination := 263, sources := [374] },
  { frame := 1, destination := 263, sources := [491] }, { frame := 1, destination := 410, sources := [263] },
  { frame := 1, destination := 410, sources := [275] }, { frame := 1, destination := 410, sources := [310] },
  { frame := 1, destination := 410, sources := [374] }, { frame := 1, destination := 410, sources := [491] },
  { frame := 1, destination := 310, sources := [410] }, { frame := 1, destination := 310, sources := [263] },
  { frame := 1, destination := 310, sources := [275] }, { frame := 1, destination := 374, sources := [410] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-925a0b3f153adeed"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk146`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6302)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 374, sources := [310] }, { frame := 1, destination := 491, sources := [410] },
  { frame := 1, destination := 491, sources := [263] }, { frame := 1, destination := 491, sources := [275] },
  { frame := 1, destination := 491, sources := [310] }, { frame := 1, destination := 309, sources := [380] },
  { frame := 1, destination := 309, sources := [345] }, { frame := 1, destination := 281, sources := [309] },
  { frame := 1, destination := 281, sources := [380] }, { frame := 1, destination := 281, sources := [345] },
  { frame := 1, destination := 299, sources := [309] }, { frame := 1, destination := 299, sources := [380] },
  { frame := 1, destination := 299, sources := [345] }, { frame := 1, destination := 261, sources := [281] },
  { frame := 1, destination := 261, sources := [380] }, { frame := 1, destination := 261, sources := [345] },
  { frame := 1, destination := 299, sources := [261] }, { frame := 1, destination := 281, sources := [299] },
  { frame := 1, destination := 309, sources := [261] }, { frame := 1, destination := 309, sources := [281] },
  { frame := 1, destination := 380, sources := [261] }, { frame := 1, destination := 380, sources := [299] },
  { frame := 1, destination := 380, sources := [281] }, { frame := 1, destination := 380, sources := [309] },
  { frame := 1, destination := 345, sources := [261] }, { frame := 1, destination := 345, sources := [299] },
  { frame := 1, destination := 345, sources := [281] }, { frame := 1, destination := 345, sources := [309] },
  { frame := 1, destination := 331, sources := [329] }, { frame := 1, destination := 331, sources := [492] },
  { frame := 1, destination := 449, sources := [331] }, { frame := 1, destination := 449, sources := [492] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-a66c34a7481a4d7b"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk147`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6335)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 249, sources := [331] }, { frame := 1, destination := 249, sources := [492] },
  { frame := 1, destination := 331, sources := [249] }, { frame := 1, destination := 331, sources := [449] },
  { frame := 1, destination := 329, sources := [249] }, { frame := 1, destination := 329, sources := [449] },
  { frame := 1, destination := 329, sources := [331] }, { frame := 1, destination := 354, sources := [249] },
  { frame := 1, destination := 354, sources := [449] }, { frame := 1, destination := 354, sources := [331] },
  { frame := 1, destination := 354, sources := [329] }, { frame := 1, destination := 492, sources := [249] },
  { frame := 1, destination := 492, sources := [449] }, { frame := 1, destination := 492, sources := [329] },
  { frame := 1, destination := 492, sources := [354] }, { frame := 1, destination := 339, sources := [375] },
  { frame := 1, destination := 339, sources := [341] }, { frame := 1, destination := 343, sources := [375] },
  { frame := 1, destination := 343, sources := [341] }, { frame := 1, destination := 456, sources := [375] },
  { frame := 1, destination := 456, sources := [341] }, { frame := 1, destination := 231, sources := [339] },
  { frame := 1, destination := 231, sources := [375] }, { frame := 1, destination := 231, sources := [341] },
  { frame := 1, destination := 456, sources := [231] }, { frame := 1, destination := 343, sources := [231] },
  { frame := 1, destination := 343, sources := [456] }, { frame := 1, destination := 339, sources := [231] },
  { frame := 1, destination := 339, sources := [343] }, { frame := 1, destination := 375, sources := [231] },
  { frame := 1, destination := 375, sources := [456] }, { frame := 1, destination := 375, sources := [343] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-659fc05d86756e12"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk148`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6368)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 375, sources := [339] }, { frame := 1, destination := 341, sources := [231] },
  { frame := 1, destination := 341, sources := [456] }, { frame := 1, destination := 341, sources := [343] },
  { frame := 1, destination := 341, sources := [339] }, { frame := 1, destination := 457, sources := [481] },
  { frame := 1, destination := 447, sources := [481] }, { frame := 1, destination := 461, sources := [457] },
  { frame := 1, destination := 461, sources := [455] }, { frame := 1, destination := 461, sources := [481] },
  { frame := 1, destination := 447, sources := [461] }, { frame := 1, destination := 457, sources := [461] },
  { frame := 1, destination := 457, sources := [447] }, { frame := 1, destination := 455, sources := [461] },
  { frame := 1, destination := 455, sources := [447] }, { frame := 1, destination := 455, sources := [457] },
  { frame := 1, destination := 499, sources := [461] }, { frame := 1, destination := 499, sources := [447] },
  { frame := 1, destination := 499, sources := [457] }, { frame := 1, destination := 499, sources := [455] },
  { frame := 1, destination := 481, sources := [447] }, { frame := 1, destination := 481, sources := [457] },
  { frame := 1, destination := 481, sources := [455] }, { frame := 1, destination := 481, sources := [499] },
  { frame := 1, destination := 346, sources := [338] }, { frame := 1, destination := 346, sources := [232] },
  { frame := 1, destination := 342, sources := [232] }, { frame := 1, destination := 334, sources := [346] },
  { frame := 1, destination := 334, sources := [232] }, { frame := 1, destination := 342, sources := [334] },
  { frame := 1, destination := 346, sources := [334] }, { frame := 1, destination := 346, sources := [342] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2e51ea5bcfdd0cb6"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk149`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6401)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 338, sources := [334] }, { frame := 1, destination := 338, sources := [342] },
  { frame := 1, destination := 338, sources := [346] }, { frame := 1, destination := 504, sources := [334] },
  { frame := 1, destination := 504, sources := [342] }, { frame := 1, destination := 504, sources := [346] },
  { frame := 1, destination := 504, sources := [338] }, { frame := 1, destination := 232, sources := [334] },
  { frame := 1, destination := 232, sources := [346] }, { frame := 1, destination := 232, sources := [338] },
  { frame := 1, destination := 232, sources := [504] }, { frame := 1, destination := 423, sources := [482] },
  { frame := 1, destination := 437, sources := [417] }, { frame := 1, destination := 437, sources := [482] },
  { frame := 1, destination := 425, sources := [423] }, { frame := 1, destination := 425, sources := [482] },
  { frame := 1, destination := 437, sources := [425] }, { frame := 1, destination := 423, sources := [437] },
  { frame := 1, destination := 417, sources := [425] }, { frame := 1, destination := 417, sources := [437] },
  { frame := 1, destination := 417, sources := [423] }, { frame := 1, destination := 503, sources := [425] },
  { frame := 1, destination := 503, sources := [437] }, { frame := 1, destination := 503, sources := [423] },
  { frame := 1, destination := 503, sources := [417] }, { frame := 1, destination := 482, sources := [425] },
  { frame := 1, destination := 482, sources := [437] }, { frame := 1, destination := 482, sources := [417] },
  { frame := 1, destination := 482, sources := [503] }, { frame := 1, destination := 500, sources := [240] },
  { frame := 1, destination := 298, sources := [500] }, { frame := 1, destination := 298, sources := [240] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0d1124c06ae8e6c5"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk150`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6434)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 304, sources := [298] }, { frame := 1, destination := 304, sources := [308] },
  { frame := 1, destination := 304, sources := [500] }, { frame := 1, destination := 304, sources := [240] },
  { frame := 1, destination := 288, sources := [298] }, { frame := 1, destination := 288, sources := [308] },
  { frame := 1, destination := 288, sources := [500] }, { frame := 1, destination := 288, sources := [240] },
  { frame := 1, destination := 308, sources := [288] }, { frame := 1, destination := 308, sources := [304] },
  { frame := 1, destination := 308, sources := [298] }, { frame := 1, destination := 500, sources := [308] },
  { frame := 1, destination := 240, sources := [288] }, { frame := 1, destination := 240, sources := [304] },
  { frame := 1, destination := 240, sources := [298] }, { frame := 1, destination := 240, sources := [308] },
  { frame := 1, destination := 502, sources := [483] }, { frame := 1, destination := 427, sources := [502] },
  { frame := 1, destination := 427, sources := [483] }, { frame := 1, destination := 439, sources := [427] },
  { frame := 1, destination := 439, sources := [421] }, { frame := 1, destination := 439, sources := [502] },
  { frame := 1, destination := 439, sources := [483] }, { frame := 1, destination := 419, sources := [427] },
  { frame := 1, destination := 419, sources := [421] }, { frame := 1, destination := 419, sources := [502] },
  { frame := 1, destination := 419, sources := [483] }, { frame := 1, destination := 421, sources := [419] },
  { frame := 1, destination := 421, sources := [439] }, { frame := 1, destination := 421, sources := [427] },
  { frame := 1, destination := 502, sources := [421] }, { frame := 1, destination := 483, sources := [419] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2a179dc907125d5c"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk151`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6467)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 483, sources := [439] }, { frame := 1, destination := 483, sources := [427] },
  { frame := 1, destination := 483, sources := [421] }, { frame := 1, destination := 296, sources := [501] },
  { frame := 1, destination := 296, sources := [242] }, { frame := 1, destination := 302, sources := [296] },
  { frame := 1, destination := 302, sources := [501] }, { frame := 1, destination := 302, sources := [242] },
  { frame := 1, destination := 294, sources := [501] }, { frame := 1, destination := 294, sources := [242] },
  { frame := 1, destination := 316, sources := [302] }, { frame := 1, destination := 316, sources := [296] },
  { frame := 1, destination := 316, sources := [501] }, { frame := 1, destination := 316, sources := [242] },
  { frame := 1, destination := 294, sources := [316] }, { frame := 1, destination := 302, sources := [294] },
  { frame := 1, destination := 296, sources := [316] }, { frame := 1, destination := 296, sources := [294] },
  { frame := 1, destination := 501, sources := [316] }, { frame := 1, destination := 501, sources := [294] },
  { frame := 1, destination := 501, sources := [302] }, { frame := 1, destination := 501, sources := [296] },
  { frame := 1, destination := 242, sources := [316] }, { frame := 1, destination := 242, sources := [294] },
  { frame := 1, destination := 242, sources := [302] }, { frame := 1, destination := 242, sources := [296] },
  { frame := 1, destination := 401, sources := [246] }, { frame := 1, destination := 401, sources := [484] },
  { frame := 1, destination := 391, sources := [401] }, { frame := 1, destination := 391, sources := [246] },
  { frame := 1, destination := 391, sources := [484] }, { frame := 1, destination := 405, sources := [246] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2d2337682aa6e46e"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk152`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6500)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 405, sources := [484] }, { frame := 1, destination := 393, sources := [405] },
  { frame := 1, destination := 393, sources := [391] }, { frame := 1, destination := 393, sources := [401] },
  { frame := 1, destination := 393, sources := [246] }, { frame := 1, destination := 393, sources := [484] },
  { frame := 1, destination := 405, sources := [393] }, { frame := 1, destination := 391, sources := [393] },
  { frame := 1, destination := 391, sources := [405] }, { frame := 1, destination := 401, sources := [393] },
  { frame := 1, destination := 401, sources := [405] }, { frame := 1, destination := 246, sources := [393] },
  { frame := 1, destination := 246, sources := [405] }, { frame := 1, destination := 246, sources := [391] },
  { frame := 1, destination := 246, sources := [401] }, { frame := 1, destination := 484, sources := [393] },
  { frame := 1, destination := 484, sources := [405] }, { frame := 1, destination := 484, sources := [391] },
  { frame := 1, destination := 484, sources := [401] }, { frame := 1, destination := 252, sources := [234] },
  { frame := 1, destination := 268, sources := [252] }, { frame := 1, destination := 268, sources := [234] },
  { frame := 1, destination := 276, sources := [268] }, { frame := 1, destination := 276, sources := [272] },
  { frame := 1, destination := 276, sources := [252] }, { frame := 1, destination := 276, sources := [234] },
  { frame := 1, destination := 266, sources := [268] }, { frame := 1, destination := 266, sources := [272] },
  { frame := 1, destination := 266, sources := [252] }, { frame := 1, destination := 266, sources := [234] },
  { frame := 1, destination := 272, sources := [266] }, { frame := 1, destination := 272, sources := [276] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-cf12b5a2430ce278"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk153`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6533)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 272, sources := [268] }, { frame := 1, destination := 252, sources := [272] },
  { frame := 1, destination := 234, sources := [266] }, { frame := 1, destination := 234, sources := [276] },
  { frame := 1, destination := 234, sources := [268] }, { frame := 1, destination := 234, sources := [272] },
  { frame := 1, destination := 253, sources := [485] }, { frame := 1, destination := 397, sources := [403] },
  { frame := 1, destination := 397, sources := [253] }, { frame := 1, destination := 397, sources := [485] },
  { frame := 1, destination := 389, sources := [403] }, { frame := 1, destination := 389, sources := [253] },
  { frame := 1, destination := 389, sources := [485] }, { frame := 1, destination := 399, sources := [397] },
  { frame := 1, destination := 399, sources := [403] }, { frame := 1, destination := 399, sources := [253] },
  { frame := 1, destination := 399, sources := [485] }, { frame := 1, destination := 389, sources := [399] },
  { frame := 1, destination := 403, sources := [399] }, { frame := 1, destination := 403, sources := [389] },
  { frame := 1, destination := 403, sources := [397] }, { frame := 1, destination := 253, sources := [403] },
  { frame := 1, destination := 485, sources := [399] }, { frame := 1, destination := 485, sources := [389] },
  { frame := 1, destination := 485, sources := [397] }, { frame := 1, destination := 485, sources := [403] },
  { frame := 1, destination := 280, sources := [223] }, { frame := 1, destination := 280, sources := [235] },
  { frame := 1, destination := 260, sources := [280] }, { frame := 1, destination := 260, sources := [223] },
  { frame := 1, destination := 260, sources := [235] }, { frame := 1, destination := 274, sources := [223] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-82dfa467ba54b84e"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk154`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6566)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 274, sources := [235] }, { frame := 1, destination := 258, sources := [274] },
  { frame := 1, destination := 258, sources := [260] }, { frame := 1, destination := 258, sources := [280] },
  { frame := 1, destination := 258, sources := [223] }, { frame := 1, destination := 258, sources := [235] },
  { frame := 1, destination := 274, sources := [258] }, { frame := 1, destination := 260, sources := [258] },
  { frame := 1, destination := 260, sources := [274] }, { frame := 1, destination := 280, sources := [258] },
  { frame := 1, destination := 280, sources := [274] }, { frame := 1, destination := 223, sources := [258] },
  { frame := 1, destination := 223, sources := [274] }, { frame := 1, destination := 223, sources := [260] },
  { frame := 1, destination := 223, sources := [280] }, { frame := 1, destination := 235, sources := [258] },
  { frame := 1, destination := 235, sources := [274] }, { frame := 1, destination := 235, sources := [260] },
  { frame := 1, destination := 235, sources := [280] }, { frame := 1, destination := 222, sources := [486] },
  { frame := 1, destination := 369, sources := [351] }, { frame := 1, destination := 369, sources := [222] },
  { frame := 1, destination := 369, sources := [486] }, { frame := 1, destination := 379, sources := [369] },
  { frame := 1, destination := 379, sources := [351] }, { frame := 1, destination := 379, sources := [222] },
  { frame := 1, destination := 379, sources := [486] }, { frame := 1, destination := 353, sources := [351] },
  { frame := 1, destination := 353, sources := [222] }, { frame := 1, destination := 353, sources := [486] },
  { frame := 1, destination := 379, sources := [353] }, { frame := 1, destination := 351, sources := [353] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-ff8d753330e89f6b"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk155`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6599)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 351, sources := [379] }, { frame := 1, destination := 351, sources := [369] },
  { frame := 1, destination := 222, sources := [379] }, { frame := 1, destination := 222, sources := [351] },
  { frame := 1, destination := 486, sources := [353] }, { frame := 1, destination := 486, sources := [379] },
  { frame := 1, destination := 486, sources := [369] }, { frame := 1, destination := 486, sources := [351] },
  { frame := 1, destination := 244, sources := [247] }, { frame := 1, destination := 244, sources := [243] },
  { frame := 1, destination := 236, sources := [244] }, { frame := 1, destination := 236, sources := [247] },
  { frame := 1, destination := 236, sources := [243] }, { frame := 1, destination := 226, sources := [244] },
  { frame := 1, destination := 226, sources := [247] }, { frame := 1, destination := 226, sources := [243] },
  { frame := 1, destination := 238, sources := [226] }, { frame := 1, destination := 238, sources := [236] },
  { frame := 1, destination := 238, sources := [247] }, { frame := 1, destination := 238, sources := [243] },
  { frame := 1, destination := 226, sources := [238] }, { frame := 1, destination := 236, sources := [238] },
  { frame := 1, destination := 244, sources := [226] }, { frame := 1, destination := 244, sources := [236] },
  { frame := 1, destination := 247, sources := [238] }, { frame := 1, destination := 247, sources := [226] },
  { frame := 1, destination := 247, sources := [236] }, { frame := 1, destination := 247, sources := [244] },
  { frame := 1, destination := 243, sources := [238] }, { frame := 1, destination := 243, sources := [226] },
  { frame := 1, destination := 243, sources := [236] }, { frame := 1, destination := 243, sources := [244] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-a21885d370aa3e36"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk156`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6632)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 660, sources := [393] }, { frame := 1, destination := 393, sources := [73] },
  { frame := 1, destination := 659, sources := [317] }, { frame := 1, destination := 317, sources := [78] },
  { frame := 1, destination := 658, sources := [383] }, { frame := 1, destination := 383, sources := [45] },
  { frame := 1, destination := 657, sources := [392] }, { frame := 1, destination := 392, sources := [307] },
  { frame := 1, destination := 656, sources := [306] }, { frame := 1, destination := 306, sources := [382] },
  { frame := 1, destination := 655, sources := [316] }, { frame := 1, destination := 316, sources := [40] },
  { frame := 1, destination := 654, sources := [399] }, { frame := 1, destination := 399, sources := [86] },
  { frame := 1, destination := 653, sources := [301] }, { frame := 1, destination := 301, sources := [411] },
  { frame := 1, destination := 652, sources := [300] }, { frame := 1, destination := 300, sources := [81] },
  { frame := 1, destination := 651, sources := [410] }, { frame := 1, destination := 410, sources := [31] },
  { frame := 1, destination := 650, sources := [289] }, { frame := 1, destination := 289, sources := [398] },
  { frame := 1, destination := 649, sources := [288] }, { frame := 1, destination := 288, sources := [37] },
  { frame := 1, destination := 648, sources := [461] }, { frame := 1, destination := 461, sources := [451] },
  { frame := 1, destination := 647, sources := [460] }, { frame := 1, destination := 460, sources := [12] },
  { frame := 1, destination := 646, sources := [249] }, { frame := 1, destination := 249, sources := [105] },
  { frame := 1, destination := 645, sources := [239] }, { frame := 1, destination := 239, sources := [110] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-13ba5ac50d810ade"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk157`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6665)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 644, sources := [450] }, { frame := 1, destination := 450, sources := [8] },
  { frame := 1, destination := 643, sources := [238] }, { frame := 1, destination := 238, sources := [248] },
  { frame := 1, destination := 642, sources := [425] }, { frame := 1, destination := 425, sources := [88] },
  { frame := 1, destination := 641, sources := [263] }, { frame := 1, destination := 263, sources := [93] },
  { frame := 1, destination := 640, sources := [262] }, { frame := 1, destination := 262, sources := [415] },
  { frame := 1, destination := 639, sources := [424] }, { frame := 1, destination := 424, sources := [259] },
  { frame := 1, destination := 638, sources := [414] }, { frame := 1, destination := 414, sources := [16] },
  { frame := 1, destination := 637, sources := [258] }, { frame := 1, destination := 258, sources := [18] },
  { frame := 1, destination := 636, sources := [419] }, { frame := 1, destination := 419, sources := [95] },
  { frame := 1, destination := 635, sources := [429] }, { frame := 1, destination := 429, sources := [20] },
  { frame := 1, destination := 634, sources := [267] }, { frame := 1, destination := 267, sources := [90] },
  { frame := 1, destination := 633, sources := [255] }, { frame := 1, destination := 255, sources := [428] },
  { frame := 1, destination := 632, sources := [418] }, { frame := 1, destination := 418, sources := [254] },
  { frame := 1, destination := 631, sources := [266] }, { frame := 1, destination := 266, sources := [14] },
  { frame := 1, destination := 630, sources := [447] }, { frame := 1, destination := 447, sources := [109] },
  { frame := 1, destination := 629, sources := [231] }, { frame := 1, destination := 231, sources := [459] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2d4dfd4096a0540b"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk158`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6698)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 628, sources := [230] }, { frame := 1, destination := 230, sources := [103] },
  { frame := 1, destination := 627, sources := [458] }, { frame := 1, destination := 458, sources := [227] },
  { frame := 1, destination := 626, sources := [446] }, { frame := 1, destination := 446, sources := [2] },
  { frame := 1, destination := 625, sources := [226] }, { frame := 1, destination := 226, sources := [4] },
  { frame := 1, destination := 624, sources := [439] }, { frame := 1, destination := 439, sources := [98] },
  { frame := 1, destination := 623, sources := [283] }, { frame := 1, destination := 283, sources := [100] },
  { frame := 1, destination := 622, sources := [282] }, { frame := 1, destination := 282, sources := [435] },
  { frame := 1, destination := 621, sources := [438] }, { frame := 1, destination := 438, sources := [25] },
  { frame := 1, destination := 620, sources := [434] }, { frame := 1, destination := 434, sources := [277] },
  { frame := 1, destination := 619, sources := [276] }, { frame := 1, destination := 276, sources := [28] },
  { frame := 1, destination := 618, sources := [437] }, { frame := 1, destination := 437, sources := [101] },
  { frame := 1, destination := 617, sources := [441] }, { frame := 1, destination := 441, sources := [29] },
  { frame := 1, destination := 616, sources := [285] }, { frame := 1, destination := 285, sources := [436] },
  { frame := 1, destination := 615, sources := [440] }, { frame := 1, destination := 440, sources := [24] },
  { frame := 1, destination := 614, sources := [275] }, { frame := 1, destination := 275, sources := [99] },
  { frame := 1, destination := 613, sources := [274] }, { frame := 1, destination := 274, sources := [284] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-25660bc658ff2c65"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk159`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6731)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 612, sources := [457] }, { frame := 1, destination := 457, sources := [106] },
  { frame := 1, destination := 611, sources := [456] }, { frame := 1, destination := 456, sources := [237] },
  { frame := 1, destination := 610, sources := [453] }, { frame := 1, destination := 453, sources := [7] },
  { frame := 1, destination := 609, sources := [225] }, { frame := 1, destination := 225, sources := [108] },
  { frame := 1, destination := 608, sources := [224] }, { frame := 1, destination := 224, sources := [452] },
  { frame := 1, destination := 607, sources := [236] }, { frame := 1, destination := 236, sources := [1] },
  { frame := 1, destination := 606, sources := [389] }, { frame := 1, destination := 389, sources := [79] },
  { frame := 1, destination := 605, sources := [395] }, { frame := 1, destination := 395, sources := [311] },
  { frame := 1, destination := 604, sources := [310] }, { frame := 1, destination := 310, sources := [76] },
  { frame := 1, destination := 603, sources := [305] }, { frame := 1, destination := 305, sources := [394] },
  { frame := 1, destination := 602, sources := [388] }, { frame := 1, destination := 388, sources := [39] },
  { frame := 1, destination := 601, sources := [304] }, { frame := 1, destination := 304, sources := [42] },
  { frame := 1, destination := 600, sources := [405] }, { frame := 1, destination := 405, sources := [85] },
  { frame := 1, destination := 599, sources := [409] }, { frame := 1, destination := 409, sources := [34] },
  { frame := 1, destination := 598, sources := [404] }, { frame := 1, destination := 404, sources := [295] },
  { frame := 1, destination := 597, sources := [408] }, { frame := 1, destination := 408, sources := [32] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-ad1db89795b8fb9d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk160`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6764)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 596, sources := [291] }, { frame := 1, destination := 291, sources := [83] },
  { frame := 1, destination := 595, sources := [294] }, { frame := 1, destination := 294, sources := [290] },
  { frame := 1, destination := 594, sources := [455] }, { frame := 1, destination := 455, sources := [104] },
  { frame := 1, destination := 593, sources := [251] }, { frame := 1, destination := 251, sources := [107] },
  { frame := 1, destination := 592, sources := [449] }, { frame := 1, destination := 449, sources := [250] },
  { frame := 1, destination := 591, sources := [454] }, { frame := 1, destination := 454, sources := [245] },
  { frame := 1, destination := 590, sources := [448] }, { frame := 1, destination := 448, sources := [10] },
  { frame := 1, destination := 589, sources := [244] }, { frame := 1, destination := 244, sources := [13] },
  { frame := 1, destination := 588, sources := [353] }, { frame := 1, destination := 353, sources := [371] },
  { frame := 1, destination := 587, sources := [370] }, { frame := 1, destination := 586, sources := [335] },
  { frame := 1, destination := 335, sources := [60] }, { frame := 1, destination := 585, sources := [331] },
  { frame := 1, destination := 331, sources := [67] }, { frame := 1, destination := 584, sources := [330] },
  { frame := 1, destination := 330, sources := [352] }, { frame := 1, destination := 583, sources := [334] },
  { frame := 1, destination := 334, sources := [50] }, { frame := 1, destination := 582, sources := [391] },
  { frame := 1, destination := 391, sources := [413] }, { frame := 1, destination := 581, sources := [303] },
  { frame := 1, destination := 303, sources := [87] }, { frame := 1, destination := 580, sources := [390] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-10ea24e94ef253b2"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk161`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6797)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 390, sources := [38] }, { frame := 1, destination := 579, sources := [412] },
  { frame := 1, destination := 412, sources := [293] }, { frame := 1, destination := 578, sources := [292] },
  { frame := 1, destination := 292, sources := [77] }, { frame := 1, destination := 577, sources := [302] },
  { frame := 1, destination := 302, sources := [33] }, { frame := 1, destination := 576, sources := [423] },
  { frame := 1, destination := 575, sources := [445] }, { frame := 1, destination := 445, sources := [271] },
  { frame := 1, destination := 574, sources := [270] }, { frame := 1, destination := 270, sources := [92] },
  { frame := 1, destination := 573, sources := [261] }, { frame := 1, destination := 572, sources := [422] },
  { frame := 1, destination := 422, sources := [17] }, { frame := 1, destination := 571, sources := [260] },
  { frame := 1, destination := 260, sources := [22] }, { frame := 1, destination := 570, sources := [379] },
  { frame := 1, destination := 379, sources := [64] }, { frame := 1, destination := 569, sources := [343] },
  { frame := 1, destination := 343, sources := [71] }, { frame := 1, destination := 568, sources := [363] },
  { frame := 1, destination := 363, sources := [55] }, { frame := 1, destination := 567, sources := [378] },
  { frame := 1, destination := 378, sources := [51] }, { frame := 1, destination := 566, sources := [362] },
  { frame := 1, destination := 362, sources := [333] }, { frame := 1, destination := 565, sources := [342] },
  { frame := 1, destination := 342, sources := [332] }, { frame := 1, destination := 564, sources := [397] },
  { frame := 1, destination := 397, sources := [407] }, { frame := 1, destination := 563, sources := [315] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-ee50d479002f5650"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk162`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6830)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 315, sources := [84] }, { frame := 1, destination := 562, sources := [314] },
  { frame := 1, destination := 314, sources := [80] }, { frame := 1, destination := 561, sources := [406] },
  { frame := 1, destination := 406, sources := [36] }, { frame := 1, destination := 560, sources := [299] },
  { frame := 1, destination := 299, sources := [396] }, { frame := 1, destination := 559, sources := [298] },
  { frame := 1, destination := 298, sources := [44] }, { frame := 1, destination := 558, sources := [427] },
  { frame := 1, destination := 427, sources := [443] }, { frame := 1, destination := 557, sources := [442] },
  { frame := 1, destination := 442, sources := [26] }, { frame := 1, destination := 556, sources := [279] },
  { frame := 1, destination := 279, sources := [94] }, { frame := 1, destination := 555, sources := [269] },
  { frame := 1, destination := 269, sources := [102] }, { frame := 1, destination := 554, sources := [426] },
  { frame := 1, destination := 426, sources := [21] }, { frame := 1, destination := 553, sources := [268] },
  { frame := 1, destination := 268, sources := [278] }, { frame := 1, destination := 552, sources := [369] },
  { frame := 1, destination := 369, sources := [365] }, { frame := 1, destination := 551, sources := [347] },
  { frame := 1, destination := 347, sources := [368] }, { frame := 1, destination := 550, sources := [364] },
  { frame := 1, destination := 364, sources := [57] }, { frame := 1, destination := 549, sources := [329] },
  { frame := 1, destination := 329, sources := [66] }, { frame := 1, destination := 548, sources := [328] },
  { frame := 1, destination := 328, sources := [65] }, { frame := 1, destination := 547, sources := [346] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-cecb54a56db0acc0"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk163`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6863)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 546, sources := [401] }, { frame := 1, destination := 401, sources := [385] },
  { frame := 1, destination := 545, sources := [313] }, { frame := 1, destination := 544, sources := [312] },
  { frame := 1, destination := 312, sources := [74] }, { frame := 1, destination := 543, sources := [400] },
  { frame := 1, destination := 400, sources := [297] }, { frame := 1, destination := 542, sources := [384] },
  { frame := 1, destination := 384, sources := [35] }, { frame := 1, destination := 541, sources := [296] },
  { frame := 1, destination := 296, sources := [43] }, { frame := 1, destination := 540, sources := [417] },
  { frame := 1, destination := 417, sources := [433] }, { frame := 1, destination := 539, sources := [432] },
  { frame := 1, destination := 432, sources := [27] }, { frame := 1, destination := 538, sources := [281] },
  { frame := 1, destination := 281, sources := [89] }, { frame := 1, destination := 537, sources := [265] },
  { frame := 1, destination := 265, sources := [97] }, { frame := 1, destination := 536, sources := [264] },
  { frame := 1, destination := 264, sources := [416] }, { frame := 1, destination := 535, sources := [280] },
  { frame := 1, destination := 280, sources := [19] }, { frame := 1, destination := 534, sources := [351] },
  { frame := 1, destination := 351, sources := [377] }, { frame := 1, destination := 533, sources := [339] },
  { frame := 1, destination := 339, sources := [70] }, { frame := 1, destination := 532, sources := [350] },
  { frame := 1, destination := 350, sources := [53] }, { frame := 1, destination := 531, sources := [376] },
  { frame := 1, destination := 376, sources := [327] }, { frame := 1, destination := 530, sources := [326] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-c7933933e4ff1281"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk164`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6896)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 326, sources := [59] }, { frame := 1, destination := 529, sources := [338] },
  { frame := 1, destination := 338, sources := [49] }, { frame := 1, destination := 528, sources := [403] },
  { frame := 1, destination := 403, sources := [75] }, { frame := 1, destination := 527, sources := [309] },
  { frame := 1, destination := 309, sources := [82] }, { frame := 1, destination := 526, sources := [387] },
  { frame := 1, destination := 387, sources := [41] }, { frame := 1, destination := 525, sources := [402] },
  { frame := 1, destination := 402, sources := [287] }, { frame := 1, destination := 524, sources := [286] },
  { frame := 1, destination := 286, sources := [386] }, { frame := 1, destination := 523, sources := [308] },
  { frame := 1, destination := 308, sources := [30] }, { frame := 1, destination := 522, sources := [421] },
  { frame := 1, destination := 421, sources := [96] }, { frame := 1, destination := 521, sources := [431] },
  { frame := 1, destination := 431, sources := [273] }, { frame := 1, destination := 520, sources := [420] },
  { frame := 1, destination := 420, sources := [23] }, { frame := 1, destination := 519, sources := [430] },
  { frame := 1, destination := 430, sources := [257] }, { frame := 1, destination := 518, sources := [256] },
  { frame := 1, destination := 256, sources := [91] }, { frame := 1, destination := 517, sources := [272] },
  { frame := 1, destination := 272, sources := [15] }, { frame := 1, destination := 516, sources := [373] },
  { frame := 1, destination := 515, sources := [361] }, { frame := 1, destination := 361, sources := [68] },
  { frame := 1, destination := 514, sources := [367] }, { frame := 1, destination := 367, sources := [360] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-c097be525e852ab7"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk165`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6929)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 513, sources := [372] }, { frame := 1, destination := 372, sources := [357] },
  { frame := 1, destination := 512, sources := [366] }, { frame := 1, destination := 366, sources := [61] },
  { frame := 1, destination := 511, sources := [356] }, { frame := 1, destination := 356, sources := [63] },
  { frame := 1, destination := 510, sources := [375] }, { frame := 1, destination := 375, sources := [381] },
  { frame := 1, destination := 509, sources := [380] }, { frame := 1, destination := 380, sources := [62] },
  { frame := 1, destination := 508, sources := [359] }, { frame := 1, destination := 359, sources := [69] },
  { frame := 1, destination := 507, sources := [355] }, { frame := 1, destination := 355, sources := [72] },
  { frame := 1, destination := 506, sources := [374] }, { frame := 1, destination := 505, sources := [354] },
  { frame := 1, destination := 354, sources := [358] }, { frame := 1, destination := 504, sources := [247] },
  { frame := 1, destination := 503, sources := [253] }, { frame := 1, destination := 253, sources := [229] },
  { frame := 1, destination := 502, sources := [246] }, { frame := 1, destination := 246, sources := [3] },
  { frame := 1, destination := 501, sources := [252] }, { frame := 1, destination := 252, sources := [0] },
  { frame := 1, destination := 500, sources := [223] }, { frame := 1, destination := 223, sources := [11] },
  { frame := 1, destination := 499, sources := [222] }, { frame := 1, destination := 222, sources := [228] },
  { frame := 1, destination := 498, sources := [337] }, { frame := 1, destination := 337, sources := [58] },
  { frame := 1, destination := 497, sources := [323] }, { frame := 1, destination := 323, sources := [349] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-db6e952504288ef9"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk166`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6962)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 496, sources := [336] }, { frame := 1, destination := 336, sources := [322] },
  { frame := 1, destination := 495, sources := [348] }, { frame := 1, destination := 348, sources := [47] },
  { frame := 1, destination := 494, sources := [321] }, { frame := 1, destination := 321, sources := [52] },
  { frame := 1, destination := 493, sources := [320] }, { frame := 1, destination := 320, sources := [48] },
  { frame := 1, destination := 492, sources := [341] }, { frame := 1, destination := 341, sources := [56] },
  { frame := 1, destination := 491, sources := [345] }, { frame := 1, destination := 490, sources := [325] },
  { frame := 1, destination := 325, sources := [54] }, { frame := 1, destination := 489, sources := [344] },
  { frame := 1, destination := 344, sources := [319] }, { frame := 1, destination := 488, sources := [318] },
  { frame := 1, destination := 318, sources := [340] }, { frame := 1, destination := 487, sources := [324] },
  { frame := 1, destination := 324, sources := [46] }, { frame := 1, destination := 486, sources := [243] },
  { frame := 1, destination := 243, sources := [9] }, { frame := 1, destination := 485, sources := [235] },
  { frame := 1, destination := 484, sources := [234] }, { frame := 1, destination := 234, sources := [241] },
  { frame := 1, destination := 483, sources := [242] }, { frame := 1, destination := 242, sources := [233] },
  { frame := 1, destination := 482, sources := [240] }, { frame := 1, destination := 240, sources := [5] },
  { frame := 1, destination := 481, sources := [232] }, { frame := 1, destination := 232, sources := [6] },
  { frame := 1, destination := 480, sources := [17] }, { frame := 1, destination := 479, sources := [43] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-92a359d2c755b32c"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk167`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L6995)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 478, sources := [68] }, { frame := 1, destination := 477, sources := [69] },
  { frame := 1, destination := 476, sources := [67] }, { frame := 1, destination := 475, sources := [57] },
  { frame := 1, destination := 474, sources := [56] }, { frame := 1, destination := 473, sources := [11] },
  { frame := 1, destination := 472, sources := [6] }, { frame := 1, destination := 471, sources := [92] },
  { frame := 1, destination := 470, sources := [77] }, { frame := 1, destination := 469, sources := [50] },
  { frame := 1, destination := 468, sources := [38] }, { frame := 1, destination := 467, sources := [27] },
  { frame := 1, destination := 466, sources := [19] }, { frame := 1, destination := 465, sources := [0] },
  { frame := 1, destination := 464, sources := [54] }, { frame := 1, destination := 463, sources := [52] },
  { frame := 1, destination := 462, sources := [47] }, { frame := 1, destination := 461, sources := [110] },
  { frame := 1, destination := 460, sources := [110] }, { frame := 1, destination := 459, sources := [109] },
  { frame := 1, destination := 458, sources := [109] }, { frame := 1, destination := 457, sources := [108] },
  { frame := 1, destination := 456, sources := [108] }, { frame := 1, destination := 455, sources := [107] },
  { frame := 1, destination := 454, sources := [107] }, { frame := 1, destination := 453, sources := [106] },
  { frame := 1, destination := 452, sources := [106] }, { frame := 1, destination := 451, sources := [105] },
  { frame := 1, destination := 450, sources := [105] }, { frame := 1, destination := 449, sources := [104] },
  { frame := 1, destination := 448, sources := [104] }, { frame := 1, destination := 447, sources := [103] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-cf1419a5d0e42665"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk168`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L7028)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 446, sources := [103] }, { frame := 1, destination := 443, sources := [102] },
  { frame := 1, destination := 442, sources := [102] }, { frame := 1, destination := 441, sources := [101] },
  { frame := 1, destination := 440, sources := [101] }, { frame := 1, destination := 439, sources := [100] },
  { frame := 1, destination := 438, sources := [100] }, { frame := 1, destination := 437, sources := [99] },
  { frame := 1, destination := 436, sources := [99] }, { frame := 1, destination := 435, sources := [98] },
  { frame := 1, destination := 434, sources := [98] }, { frame := 1, destination := 433, sources := [97] },
  { frame := 1, destination := 432, sources := [97] }, { frame := 1, destination := 431, sources := [96] },
  { frame := 1, destination := 430, sources := [96] }, { frame := 1, destination := 429, sources := [95] },
  { frame := 1, destination := 428, sources := [95] }, { frame := 1, destination := 427, sources := [94] },
  { frame := 1, destination := 426, sources := [94] }, { frame := 1, destination := 425, sources := [93] },
  { frame := 1, destination := 424, sources := [93] }, { frame := 1, destination := 423, sources := [92] },
  { frame := 1, destination := 422, sources := [92] }, { frame := 1, destination := 421, sources := [91] },
  { frame := 1, destination := 420, sources := [91] }, { frame := 1, destination := 419, sources := [90] },
  { frame := 1, destination := 418, sources := [90] }, { frame := 1, destination := 417, sources := [89] },
  { frame := 1, destination := 416, sources := [89] }, { frame := 1, destination := 415, sources := [88] },
  { frame := 1, destination := 414, sources := [88] }, { frame := 1, destination := 413, sources := [87] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-927f3b35085d14a0"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk169`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L7061)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 412, sources := [87] }, { frame := 1, destination := 411, sources := [86] },
  { frame := 1, destination := 410, sources := [86] }, { frame := 1, destination := 409, sources := [85] },
  { frame := 1, destination := 408, sources := [85] }, { frame := 1, destination := 407, sources := [84] },
  { frame := 1, destination := 406, sources := [84] }, { frame := 1, destination := 405, sources := [83] },
  { frame := 1, destination := 404, sources := [83] }, { frame := 1, destination := 403, sources := [82] },
  { frame := 1, destination := 402, sources := [82] }, { frame := 1, destination := 399, sources := [81] },
  { frame := 1, destination := 398, sources := [81] }, { frame := 1, destination := 397, sources := [80] },
  { frame := 1, destination := 396, sources := [80] }, { frame := 1, destination := 395, sources := [79] },
  { frame := 1, destination := 394, sources := [79] }, { frame := 1, destination := 393, sources := [78] },
  { frame := 1, destination := 392, sources := [78] }, { frame := 1, destination := 391, sources := [77] },
  { frame := 1, destination := 390, sources := [77] }, { frame := 1, destination := 389, sources := [76] },
  { frame := 1, destination := 388, sources := [76] }, { frame := 1, destination := 387, sources := [75] },
  { frame := 1, destination := 386, sources := [75] }, { frame := 1, destination := 385, sources := [74] },
  { frame := 1, destination := 384, sources := [74] }, { frame := 1, destination := 383, sources := [73] },
  { frame := 1, destination := 382, sources := [73] }, { frame := 1, destination := 381, sources := [72] },
  { frame := 1, destination := 380, sources := [72] }, { frame := 1, destination := 379, sources := [71] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-2521ca98b53e6f7b"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk170`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L7094)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 378, sources := [71] }, { frame := 1, destination := 377, sources := [70] },
  { frame := 1, destination := 376, sources := [70] }, { frame := 1, destination := 375, sources := [69] },
  { frame := 1, destination := 374, sources := [69] }, { frame := 1, destination := 373, sources := [68] },
  { frame := 1, destination := 372, sources := [68] }, { frame := 1, destination := 371, sources := [67] },
  { frame := 1, destination := 370, sources := [67] }, { frame := 1, destination := 369, sources := [66] },
  { frame := 1, destination := 368, sources := [66] }, { frame := 1, destination := 365, sources := [65] },
  { frame := 1, destination := 364, sources := [65] }, { frame := 1, destination := 363, sources := [64] },
  { frame := 1, destination := 362, sources := [64] }, { frame := 1, destination := 361, sources := [63] },
  { frame := 1, destination := 360, sources := [63] }, { frame := 1, destination := 359, sources := [62] },
  { frame := 1, destination := 358, sources := [62] }, { frame := 1, destination := 357, sources := [61] },
  { frame := 1, destination := 356, sources := [61] }, { frame := 1, destination := 353, sources := [60] },
  { frame := 1, destination := 352, sources := [60] }, { frame := 1, destination := 351, sources := [59] },
  { frame := 1, destination := 350, sources := [59] }, { frame := 1, destination := 349, sources := [58] },
  { frame := 1, destination := 348, sources := [58] }, { frame := 1, destination := 347, sources := [57] },
  { frame := 1, destination := 346, sources := [57] }, { frame := 1, destination := 345, sources := [56] },
  { frame := 1, destination := 344, sources := [56] }, { frame := 1, destination := 343, sources := [55] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-30c780c5f0db7c51"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk171`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L7127)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 342, sources := [55] }, { frame := 1, destination := 341, sources := [54] },
  { frame := 1, destination := 340, sources := [54] }, { frame := 1, destination := 339, sources := [53] },
  { frame := 1, destination := 338, sources := [53] }, { frame := 1, destination := 337, sources := [52] },
  { frame := 1, destination := 336, sources := [52] }, { frame := 1, destination := 333, sources := [51] },
  { frame := 1, destination := 332, sources := [51] }, { frame := 1, destination := 331, sources := [50] },
  { frame := 1, destination := 330, sources := [50] }, { frame := 1, destination := 327, sources := [49] },
  { frame := 1, destination := 326, sources := [49] }, { frame := 1, destination := 323, sources := [48] },
  { frame := 1, destination := 322, sources := [48] }, { frame := 1, destination := 321, sources := [47] },
  { frame := 1, destination := 320, sources := [47] }, { frame := 1, destination := 319, sources := [46] },
  { frame := 1, destination := 318, sources := [46] }, { frame := 1, destination := 317, sources := [45] },
  { frame := 1, destination := 316, sources := [45] }, { frame := 1, destination := 315, sources := [44] },
  { frame := 1, destination := 314, sources := [44] }, { frame := 1, destination := 313, sources := [43] },
  { frame := 1, destination := 312, sources := [43] }, { frame := 1, destination := 311, sources := [42] },
  { frame := 1, destination := 310, sources := [42] }, { frame := 1, destination := 309, sources := [41] },
  { frame := 1, destination := 308, sources := [41] }, { frame := 1, destination := 307, sources := [40] },
  { frame := 1, destination := 306, sources := [40] }, { frame := 1, destination := 305, sources := [39] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-abb374585b16f3f5"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk172`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L7160)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 304, sources := [39] }, { frame := 1, destination := 303, sources := [38] },
  { frame := 1, destination := 302, sources := [38] }, { frame := 1, destination := 301, sources := [37] },
  { frame := 1, destination := 300, sources := [37] }, { frame := 1, destination := 299, sources := [36] },
  { frame := 1, destination := 298, sources := [36] }, { frame := 1, destination := 297, sources := [35] },
  { frame := 1, destination := 296, sources := [35] }, { frame := 1, destination := 295, sources := [34] },
  { frame := 1, destination := 294, sources := [34] }, { frame := 1, destination := 293, sources := [33] },
  { frame := 1, destination := 292, sources := [33] }, { frame := 1, destination := 291, sources := [32] },
  { frame := 1, destination := 290, sources := [32] }, { frame := 1, destination := 289, sources := [31] },
  { frame := 1, destination := 288, sources := [31] }, { frame := 1, destination := 287, sources := [30] },
  { frame := 1, destination := 286, sources := [30] }, { frame := 1, destination := 285, sources := [29] },
  { frame := 1, destination := 284, sources := [29] }, { frame := 1, destination := 283, sources := [28] },
  { frame := 1, destination := 282, sources := [28] }, { frame := 1, destination := 281, sources := [27] },
  { frame := 1, destination := 280, sources := [27] }, { frame := 1, destination := 279, sources := [26] },
  { frame := 1, destination := 278, sources := [26] }, { frame := 1, destination := 277, sources := [25] },
  { frame := 1, destination := 276, sources := [25] }, { frame := 1, destination := 275, sources := [24] },
  { frame := 1, destination := 274, sources := [24] }, { frame := 1, destination := 273, sources := [23] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-4b43b8ac4974248d"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk173`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L7193)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 272, sources := [23] }, { frame := 1, destination := 271, sources := [22] },
  { frame := 1, destination := 270, sources := [22] }, { frame := 1, destination := 269, sources := [21] },
  { frame := 1, destination := 268, sources := [21] }, { frame := 1, destination := 267, sources := [20] },
  { frame := 1, destination := 266, sources := [20] }, { frame := 1, destination := 265, sources := [19] },
  { frame := 1, destination := 264, sources := [19] }, { frame := 1, destination := 263, sources := [18] },
  { frame := 1, destination := 262, sources := [18] }, { frame := 1, destination := 261, sources := [17] },
  { frame := 1, destination := 260, sources := [17] }, { frame := 1, destination := 259, sources := [16] },
  { frame := 1, destination := 258, sources := [16] }, { frame := 1, destination := 257, sources := [15] },
  { frame := 1, destination := 256, sources := [15] }, { frame := 1, destination := 255, sources := [14] },
  { frame := 1, destination := 254, sources := [14] }, { frame := 1, destination := 251, sources := [13] },
  { frame := 1, destination := 250, sources := [13] }, { frame := 1, destination := 249, sources := [12] },
  { frame := 1, destination := 248, sources := [12] }, { frame := 1, destination := 247, sources := [11] },
  { frame := 1, destination := 246, sources := [11] }, { frame := 1, destination := 245, sources := [10] },
  { frame := 1, destination := 244, sources := [10] }, { frame := 1, destination := 241, sources := [9] },
  { frame := 1, destination := 240, sources := [9] }, { frame := 1, destination := 239, sources := [8] },
  { frame := 1, destination := 238, sources := [8] }, { frame := 1, destination := 237, sources := [7] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-0a08b9c9b6984793"></a>
## `CodedSorting.Construction.FiniteCertificate.gatesChunk174`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L7226)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
#[{ frame := 1, destination := 236, sources := [7] }, { frame := 1, destination := 235, sources := [6] },
  { frame := 1, destination := 234, sources := [6] }, { frame := 1, destination := 233, sources := [5] },
  { frame := 1, destination := 232, sources := [5] }, { frame := 1, destination := 231, sources := [4] },
  { frame := 1, destination := 230, sources := [4] }, { frame := 1, destination := 229, sources := [3] },
  { frame := 1, destination := 228, sources := [3] }, { frame := 1, destination := 227, sources := [2] },
  { frame := 1, destination := 226, sources := [2] }, { frame := 1, destination := 225, sources := [1] },
  { frame := 1, destination := 224, sources := [1] }, { frame := 1, destination := 223, sources := [0] },
  { frame := 1, destination := 222, sources := [0] }]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Gate.mk](../../Circuit/Local/FiniteTypes.definitions.md#def-7c9ac588cd2d0597)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-1b8de7a898d28b81"></a>
## `CodedSorting.Construction.FiniteCertificate.gates`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L7242)

**类型**

```lean
Array CodedSorting.Construction.FiniteCertificate.Gate
```

**定义**

```lean
Array.foldl (fun a b => a ++ b) #[]
  (let y :=
      let y :=
        let y :=
          let y :=
            let y :=
              [CodedSorting.Construction.FiniteCertificate.gatesChunk169,
                CodedSorting.Construction.FiniteCertificate.gatesChunk170,
                CodedSorting.Construction.FiniteCertificate.gatesChunk171,
                CodedSorting.Construction.FiniteCertificate.gatesChunk172,
                CodedSorting.Construction.FiniteCertificate.gatesChunk173,
                CodedSorting.Construction.FiniteCertificate.gatesChunk174];
            CodedSorting.Construction.FiniteCertificate.gatesChunk164 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk165 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk166 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk167 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk168 :: y;
          let y :=
            CodedSorting.Construction.FiniteCertificate.gatesChunk158 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk159 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk160 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk161 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk162 ::
                      CodedSorting.Construction.FiniteCertificate.gatesChunk163 :: y;
          CodedSorting.Construction.FiniteCertificate.gatesChunk153 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk154 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk155 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk156 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk157 :: y;
        let y :=
          let y :=
            CodedSorting.Construction.FiniteCertificate.gatesChunk147 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk148 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk149 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk150 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk151 ::
                      CodedSorting.Construction.FiniteCertificate.gatesChunk152 :: y;
          CodedSorting.Construction.FiniteCertificate.gatesChunk142 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk143 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk144 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk145 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk146 :: y;
        let y :=
          CodedSorting.Construction.FiniteCertificate.gatesChunk136 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk137 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk138 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk139 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk140 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk141 :: y;
        CodedSorting.Construction.FiniteCertificate.gatesChunk131 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk132 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk133 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk134 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk135 :: y;
      let y :=
        let y :=
          let y :=
            CodedSorting.Construction.FiniteCertificate.gatesChunk125 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk126 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk127 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk128 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk129 ::
                      CodedSorting.Construction.FiniteCertificate.gatesChunk130 :: y;
          CodedSorting.Construction.FiniteCertificate.gatesChunk120 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk121 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk122 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk123 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk124 :: y;
        let y :=
          CodedSorting.Construction.FiniteCertificate.gatesChunk114 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk115 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk116 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk117 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk118 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk119 :: y;
        CodedSorting.Construction.FiniteCertificate.gatesChunk109 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk110 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk111 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk112 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk113 :: y;
      let y :=
        let y :=
          CodedSorting.Construction.FiniteCertificate.gatesChunk103 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk104 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk105 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk106 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk107 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk108 :: y;
        CodedSorting.Construction.FiniteCertificate.gatesChunk98 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk99 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk100 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk101 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk102 :: y;
      let y :=
        CodedSorting.Construction.FiniteCertificate.gatesChunk92 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk93 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk94 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk95 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk96 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk97 :: y;
      CodedSorting.Construction.FiniteCertificate.gatesChunk87 ::
        CodedSorting.Construction.FiniteCertificate.gatesChunk88 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk89 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk90 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk91 :: y;
    let y :=
      let y :=
        let y :=
          let y :=
            CodedSorting.Construction.FiniteCertificate.gatesChunk81 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk82 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk83 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk84 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk85 ::
                      CodedSorting.Construction.FiniteCertificate.gatesChunk86 :: y;
          CodedSorting.Construction.FiniteCertificate.gatesChunk76 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk77 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk78 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk79 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk80 :: y;
        let y :=
          CodedSorting.Construction.FiniteCertificate.gatesChunk70 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk71 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk72 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk73 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk74 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk75 :: y;
        CodedSorting.Construction.FiniteCertificate.gatesChunk65 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk66 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk67 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk68 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk69 :: y;
      let y :=
        let y :=
          CodedSorting.Construction.FiniteCertificate.gatesChunk59 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk60 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk61 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk62 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk63 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk64 :: y;
        CodedSorting.Construction.FiniteCertificate.gatesChunk54 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk55 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk56 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk57 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk58 :: y;
      let y :=
        CodedSorting.Construction.FiniteCertificate.gatesChunk48 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk49 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk50 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk51 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk52 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk53 :: y;
      CodedSorting.Construction.FiniteCertificate.gatesChunk43 ::
        CodedSorting.Construction.FiniteCertificate.gatesChunk44 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk45 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk46 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk47 :: y;
    let y :=
      let y :=
        let y :=
          CodedSorting.Construction.FiniteCertificate.gatesChunk37 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk38 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk39 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk40 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk41 ::
                    CodedSorting.Construction.FiniteCertificate.gatesChunk42 :: y;
        CodedSorting.Construction.FiniteCertificate.gatesChunk32 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk33 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk34 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk35 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk36 :: y;
      let y :=
        CodedSorting.Construction.FiniteCertificate.gatesChunk26 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk27 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk28 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk29 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk30 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk31 :: y;
      CodedSorting.Construction.FiniteCertificate.gatesChunk21 ::
        CodedSorting.Construction.FiniteCertificate.gatesChunk22 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk23 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk24 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk25 :: y;
    let y :=
      let y :=
        CodedSorting.Construction.FiniteCertificate.gatesChunk15 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk16 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk17 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk18 ::
                CodedSorting.Construction.FiniteCertificate.gatesChunk19 ::
                  CodedSorting.Construction.FiniteCertificate.gatesChunk20 :: y;
      CodedSorting.Construction.FiniteCertificate.gatesChunk10 ::
        CodedSorting.Construction.FiniteCertificate.gatesChunk11 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk12 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk13 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk14 :: y;
    let y :=
      CodedSorting.Construction.FiniteCertificate.gatesChunk5 ::
        CodedSorting.Construction.FiniteCertificate.gatesChunk6 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk7 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk8 ::
              CodedSorting.Construction.FiniteCertificate.gatesChunk9 :: y;
    CodedSorting.Construction.FiniteCertificate.gatesChunk0 ::
      CodedSorting.Construction.FiniteCertificate.gatesChunk1 ::
        CodedSorting.Construction.FiniteCertificate.gatesChunk2 ::
          CodedSorting.Construction.FiniteCertificate.gatesChunk3 ::
            CodedSorting.Construction.FiniteCertificate.gatesChunk4 :: y).toArray
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.gatesChunk116](Data.definitions.md#def-115f7a933abb81f9)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk147](Data.definitions.md#def-a66c34a7481a4d7b)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk49](Data.definitions.md#def-7588c836c5c4d0cd)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk139](Data.definitions.md#def-dc0f97ca9ae29b9d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk39](Data.definitions.md#def-beca1c9883e0514a)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk129](Data.definitions.md#def-757e29d2b500e0e3)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk162](Data.definitions.md#def-ee50d479002f5650)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk63](Data.definitions.md#def-a24bf7d058a93099)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk79](Data.definitions.md#def-2d1df7296bf01edb)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk5](Data.definitions.md#def-78df6fcb58aadec5)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk56](Data.definitions.md#def-e0b5367d0fd7b5d6)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk89](Data.definitions.md#def-9c2296f8a748b87e)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk133](Data.definitions.md#def-33cde646381e36ab)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk75](Data.definitions.md#def-e37e5a7f1b0090f7)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk69](Data.definitions.md#def-339a59bb54a5cb46)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk8](Data.definitions.md#def-d2e9a6dc70c0180a)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk93](Data.definitions.md#def-849e7c322bbf01f6)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk165](Data.definitions.md#def-c097be525e852ab7)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk11](Data.definitions.md#def-105a4c5e4a1c6a8f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk22](Data.definitions.md#def-ce16eaa5e0ede74a)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk155](Data.definitions.md#def-ff8d753330e89f6b)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk82](Data.definitions.md#def-34ebbb4d38280cd1)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk121](Data.definitions.md#def-a2f84ab2d2367e66)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk66](Data.definitions.md#def-701043954c54178a)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk67](Data.definitions.md#def-3738122d3222df28)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk19](Data.definitions.md#def-479a251b5320a1e1)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk45](Data.definitions.md#def-b5376f1c1be0f0a7)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk114](Data.definitions.md#def-a74015e476e3ac55)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk123](Data.definitions.md#def-a2e374b70d617b29)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk58](Data.definitions.md#def-7f1cf0b76bded46a)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk17](Data.definitions.md#def-395573e15e2509e5)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk88](Data.definitions.md#def-4239d20278256caa)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk92](Data.definitions.md#def-0b2044c3cf0f35d4)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk6](Data.definitions.md#def-b04ab019858f0384)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk173](Data.definitions.md#def-4b43b8ac4974248d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk115](Data.definitions.md#def-4816bcc1a62784bd)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk48](Data.definitions.md#def-e3ccb218a607691f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk62](Data.definitions.md#def-cddade364a420928)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk171](Data.definitions.md#def-30c780c5f0db7c51)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk122](Data.definitions.md#def-ffe865a1e4bcf432)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk77](Data.definitions.md#def-5bba896070e4edac)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk107](Data.definitions.md#def-4efd61e9db3bac3f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk161](Data.definitions.md#def-10ea24e94ef253b2)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk136](Data.definitions.md#def-f635a086cb1c15c7)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk153](Data.definitions.md#def-cf12b5a2430ce278)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk70](Data.definitions.md#def-e58af66372143d50)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk134](Data.definitions.md#def-6df342a089b69a8d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk156](Data.definitions.md#def-a21885d370aa3e36)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk40](Data.definitions.md#def-7ab1f245e17f420d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk25](Data.definitions.md#def-9738dfffed20f9de)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk86](Data.definitions.md#def-0119a0c61e687104)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk97](Data.definitions.md#def-77ebd7287e16b5ae)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk87](Data.definitions.md#def-1549ea84e5c02310)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk60](Data.definitions.md#def-75215f0db58ba3bc)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk47](Data.definitions.md#def-e86a7151bf9e28fc)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk157](Data.definitions.md#def-13ba5ac50d810ade)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk106](Data.definitions.md#def-41d4550fd772a9cb)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk127](Data.definitions.md#def-61c89f579075954a)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk78](Data.definitions.md#def-3de77b7ff5a6bda1)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk117](Data.definitions.md#def-c5d8ddd86ecc27fa)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk1](Data.definitions.md#def-e8f13884dbf56437)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk36](Data.definitions.md#def-9244d70a8b0870ae)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk26](Data.definitions.md#def-263c5b213d0425d4)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk74](Data.definitions.md#def-67b009238f7f2bf7)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk14](Data.definitions.md#def-175848d5e3e72784)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk55](Data.definitions.md#def-0c7d6f25d7da4566)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk7](Data.definitions.md#def-58da97a0a4992d56)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk9](Data.definitions.md#def-294cf70c2cf864f1)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk54](Data.definitions.md#def-6cbfd3bfa7380bf5)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk31](Data.definitions.md#def-f5e2440dee830190)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk94](Data.definitions.md#def-7e7fe91bdcaa9824)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk59](Data.definitions.md#def-4bd43d195e9c490f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk104](Data.definitions.md#def-bf5cc2507274ab60)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk159](Data.definitions.md#def-25660bc658ff2c65)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk110](Data.definitions.md#def-f4f984f71ef51bf0)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk85](Data.definitions.md#def-6a10f6e454362d9c)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk16](Data.definitions.md#def-f991c791abb18e4d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk13](Data.definitions.md#def-8e5826d029b87bfe)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk28](Data.definitions.md#def-0a472cda28b58404)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk2](Data.definitions.md#def-965a813d6c9af834)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk80](Data.definitions.md#def-a126ebad80e58baf)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk140](Data.definitions.md#def-4af9e3108fed5401)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk53](Data.definitions.md#def-e4f6e83c6d928826)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk141](Data.definitions.md#def-8ed67ae8e24d9d57)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk109](Data.definitions.md#def-0694f6cd9e373dda)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk142](Data.definitions.md#def-84dffae6de621ef8)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk108](Data.definitions.md#def-b0262d2fefa53786)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk33](Data.definitions.md#def-5c3a26497320ede2)
- [CodedSorting.Construction.FiniteCertificate.Gate](../../Circuit/Local/FiniteTypes.definitions.md#def-050ce19ea890dc32)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk124](Data.definitions.md#def-0a998881cbda4d80)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk131](Data.definitions.md#def-f240335723a58a80)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk96](Data.definitions.md#def-474d7095ee8b039a)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk170](Data.definitions.md#def-2521ca98b53e6f7b)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk4](Data.definitions.md#def-b7c1f6812be49501)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk73](Data.definitions.md#def-1fbc617dd8aa190f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk138](Data.definitions.md#def-6c55d1415040314d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk57](Data.definitions.md#def-2171962bbfb4e0f1)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk27](Data.definitions.md#def-187709613b47ab18)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk149](Data.definitions.md#def-2e51ea5bcfdd0cb6)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk37](Data.definitions.md#def-fc32fe26c054fbe4)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk160](Data.definitions.md#def-ad1db89795b8fb9d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk126](Data.definitions.md#def-31553c119a23f263)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk148](Data.definitions.md#def-659fc05d86756e12)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk120](Data.definitions.md#def-9bbab2f93f7aa94f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk3](Data.definitions.md#def-77b62cd9919378bf)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk20](Data.definitions.md#def-d9f54cd7156076cb)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk83](Data.definitions.md#def-f07bccdfe5f044e7)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk29](Data.definitions.md#def-b528b0d2854eb091)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk46](Data.definitions.md#def-5e45c7676a164772)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk105](Data.definitions.md#def-3c6e71d5c44d97ff)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk50](Data.definitions.md#def-55e6c30cb17f43c3)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk163](Data.definitions.md#def-cecb54a56db0acc0)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk95](Data.definitions.md#def-e110db567ebe2b6d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk98](Data.definitions.md#def-5ecec1b4a23190d5)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk102](Data.definitions.md#def-8448f3dd32d26589)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk42](Data.definitions.md#def-7eba5658fe0ec801)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk44](Data.definitions.md#def-9f6ae63434d39d49)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk12](Data.definitions.md#def-09f95ff8239b0840)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk166](Data.definitions.md#def-db6e952504288ef9)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk71](Data.definitions.md#def-2fca826fb5616849)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk76](Data.definitions.md#def-3b87019b059b1a6f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk35](Data.definitions.md#def-557730a5838ff4f8)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk167](Data.definitions.md#def-92a359d2c755b32c)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk90](Data.definitions.md#def-3019a5aa1de72411)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk38](Data.definitions.md#def-c41d6870797e685e)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk21](Data.definitions.md#def-faec46b539e0ac5f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk158](Data.definitions.md#def-2d4dfd4096a0540b)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk145](Data.definitions.md#def-23471a6e3ba45ed1)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk72](Data.definitions.md#def-1a7135e11d09ec59)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk125](Data.definitions.md#def-4aa1a19bb110c715)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk23](Data.definitions.md#def-8f45a3bf2d30eb9d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk15](Data.definitions.md#def-67fd06da2416b50b)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk154](Data.definitions.md#def-82dfa467ba54b84e)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk132](Data.definitions.md#def-9562d27c919a9a4e)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk174](Data.definitions.md#def-0a08b9c9b6984793)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk41](Data.definitions.md#def-ff541d6f1ae9af96)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk65](Data.definitions.md#def-6f54a22d5083cca1)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk113](Data.definitions.md#def-5ec748a5905d3c3f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk99](Data.definitions.md#def-e2501750cfedf91b)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk34](Data.definitions.md#def-36c128df45445f1f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk61](Data.definitions.md#def-5165d8854b7bbc7b)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk91](Data.definitions.md#def-94ae544a78e339b2)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk146](Data.definitions.md#def-925a0b3f153adeed)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk137](Data.definitions.md#def-3128f8fdf18c384f)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk0](Data.definitions.md#def-981a72463683f667)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk81](Data.definitions.md#def-dbfc69df3a573764)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk144](Data.definitions.md#def-0a37565cb573e76d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk118](Data.definitions.md#def-6a35d68eb6edfc2d)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk112](Data.definitions.md#def-96f2ee959a95f5a8)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk151](Data.definitions.md#def-2a179dc907125d5c)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk103](Data.definitions.md#def-1294b1eafff69100)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk150](Data.definitions.md#def-0d1124c06ae8e6c5)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk143](Data.definitions.md#def-2d6f32f1488d6793)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk32](Data.definitions.md#def-2c73f9112e9cfebf)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk10](Data.definitions.md#def-874dbac41705c56a)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk164](Data.definitions.md#def-c7933933e4ff1281)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk52](Data.definitions.md#def-e8bafe79d2e6dd41)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk135](Data.definitions.md#def-df83c98338c0edaf)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk18](Data.definitions.md#def-48d4d45a349b3e2e)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk101](Data.definitions.md#def-b9146d34ad6fe8b7)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk128](Data.definitions.md#def-cdf1e786ec244787)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk43](Data.definitions.md#def-a2703010a56710b1)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk64](Data.definitions.md#def-eb823ed6c0976eae)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk30](Data.definitions.md#def-62dfa45edb796267)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk172](Data.definitions.md#def-abb374585b16f3f5)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk84](Data.definitions.md#def-bd7408ad51d0ad20)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk169](Data.definitions.md#def-927f3b35085d14a0)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk51](Data.definitions.md#def-d5c088e27a732e19)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk130](Data.definitions.md#def-581ee69f51776460)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk119](Data.definitions.md#def-372b4ae072d58c08)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk111](Data.definitions.md#def-aa94978b487d7769)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk152](Data.definitions.md#def-2d2337682aa6e46e)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk68](Data.definitions.md#def-80e8e42cfc7d5e1e)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk168](Data.definitions.md#def-cf1419a5d0e42665)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk100](Data.definitions.md#def-3cff84da5008fbcd)
- [CodedSorting.Construction.FiniteCertificate.gatesChunk24](Data.definitions.md#def-dd45cf550dc9f84b)

**基础库名称**

`Array.instAppend`, `instOfNatNat`, `List.toArray`, `Array.foldl`, `List.cons`, `Array`, `instHAppendOfAppend`, `List`, `Nat`, `OfNat.ofNat`, `Array.size`, `HAppend.hAppend`, `List.nil`

<a id="def-fead527ad283c2a5"></a>
## `CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk0`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L8838)

**类型**

```lean
Array ℕ
```

**定义**

```lean
#[91, 95, 80, 25, 45, 27, 68, 90, 107, 103, 100, 48, 102, 106, 65, 81, 104, 97, 110, 88, 51, 96, 92, 87, 101, 86, 89,
  79, 94, 105, 109, 63]
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-707f739c76b9422f"></a>
## `CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk1`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L8871)

**类型**

```lean
Array ℕ
```

**定义**

```lean
#[99, 74, 93, 67, 84, 82, 85, 69, 61, 98, 70, 75, 73, 3, 53, 77, 76, 108, 66, 83, 78, 59, 60, 46, 57, 71, 52, 58, 55,
  64, 72, 33]
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-170a618465b0487c"></a>
## `CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk2`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L8904)

**类型**

```lean
Array ℕ
```

**定义**

```lean
#[38, 50, 47, 35, 54, 37, 49, 39, 31, 62, 44, 36, 40, 34, 42, 41, 12, 23, 5, 43, 56, 32, 30, 28, 26, 19, 21, 13, 18, 29,
  24, 22]
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-41f271a22f7422e6"></a>
## `CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk3`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L8937)

**类型**

```lean
Array ℕ
```

**定义**

```lean
#[6, 20, 17, 15, 14, 0, 16, 11, 10, 9, 8, 7, 4, 2, 1]
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `List.toArray`, `List.cons`, `Array`, `Nat`, `OfNat.ofNat`, `List.nil`

<a id="def-e0d946baae644aca"></a>
## `CodedSorting.Construction.FiniteCertificate.orthogonalPartner`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L8953)

**类型**

```lean
Array ℕ
```

**定义**

```lean
Array.foldl (fun a b => a ++ b) #[]
  #[CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk0,
    CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk1,
    CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk2,
    CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk3]
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk1](Data.definitions.md#def-707f739c76b9422f)
- [CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk2](Data.definitions.md#def-170a618465b0487c)
- [CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk3](Data.definitions.md#def-41f271a22f7422e6)
- [CodedSorting.Construction.FiniteCertificate.orthogonalPartnerChunk0](Data.definitions.md#def-fead527ad283c2a5)

**基础库名称**

`Array.instAppend`, `instOfNatNat`, `List.toArray`, `Array.foldl`, `List.cons`, `Array`, `instHAppendOfAppend`, `Nat`, `OfNat.ofNat`, `Array.size`, `HAppend.hAppend`, `List.nil`

<a id="def-8594ece3c1c04e1b"></a>
## `CodedSorting.Construction.FiniteCertificate.beforeScatterCount`

这里保存固定电路的数据，或定义怎样读取这些数据。具体数值和读取方法见源码中的数组、整数及下标运算。

[源码位置](Data.lean#L8958)

**类型**

```lean
ℕ
```

**定义**

```lean
2186
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`
