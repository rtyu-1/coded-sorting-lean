# FiniteInterpretation 的定义

[源码](FiniteInterpretation.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-fb5bed89587c7f3a"></a>
## `CodedSorting.Construction.IntegerProjection.projectionOfInts`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteInterpretation.lean#L26)

**类型**

```lean
{I : Type u_1} → ℤ → Matrix I I ℤ → Matrix I I ℚ
```

**定义**

```lean
fun {I} denominator numerator i j => ↑(numerator i j) / ↑denominator
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Int.cast`, `instHDiv`, `Matrix`, `Rat`, `Rat.instIntCast`, `HDiv.hDiv`, `Int`, `Rat.instDiv`

<a id="def-1d9f5849aecb194d"></a>
## `CodedSorting.Construction.IntegerProjection.vectorOfInts`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteInterpretation.lean#L29)

**类型**

```lean
{I : Type u_1} → (I → ℤ) → I → ℚ
```

**定义**

```lean
fun {I} v i => ↑(v i)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Int.cast`, `Rat`, `Rat.instIntCast`, `Int`

<a id="def-99e092c80c9c68c0"></a>
## `CodedSorting.Construction.IntegerProjection.certificateNumerator`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteInterpretation.lean#L181)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Projection → Matrix (Fin 8) (Fin 8) ℤ
```

**定义**

```lean
fun p i j => p.numerator[8 * ↑i + ↑j]!
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.numerator](../Local/FiniteTypes.definitions.md#def-98d789a781723f22)

**基础库名称**

`Int.instInhabited`, `HMul.hMul`, `Matrix`, `instMulNat`, `instOfNatNat`, `Int`, `Fin.val`, `Array`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `GetElem?.getElem!`, `Array.size`, `instHMul`, `Array.instGetElem?NatLtSize`

<a id="def-bd328f0d6e991056"></a>
## `CodedSorting.Construction.IntegerProjection.certificateMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteInterpretation.lean#L185)

**类型**

```lean
CodedSorting.Construction.FiniteCertificate.Projection → Matrix (Fin 8) (Fin 8) ℚ
```

**定义**

```lean
fun p =>
  CodedSorting.Construction.IntegerProjection.projectionOfInts p.denominator
    (CodedSorting.Construction.IntegerProjection.certificateNumerator p)
```

**继续展开**

- [CodedSorting.Construction.FiniteCertificate.Projection](../Local/FiniteTypes.definitions.md#def-1cfe6fae6693f682)
- [CodedSorting.Construction.FiniteCertificate.Projection.denominator](../Local/FiniteTypes.definitions.md#def-fe61a69b89d86ced)
- [CodedSorting.Construction.IntegerProjection.projectionOfInts](FiniteInterpretation.definitions.md#def-fb5bed89587c7f3a)
- [CodedSorting.Construction.IntegerProjection.certificateNumerator](FiniteInterpretation.definitions.md#def-99e092c80c9c68c0)

**基础库名称**

`Matrix`, `Rat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`
