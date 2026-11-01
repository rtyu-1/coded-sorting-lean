# Program 的定义

[源码](Program.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-6e4d2d5f472e641f"></a>
## `CodedSorting.CommonLeafBatchProgram.extendDisk`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L32)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonLeafProgram.Disk q → CodedSorting.WordControl.BlockDisk q.block q.w
```

**定义**

```lean
fun q disk a => if h : a < q.N ^ q.exponent then disk ⟨a, h⟩ else fun x => 0
```

**继续展开**

- [CodedSorting.WordControl.BlockDisk](../../Words/WordConvention.definitions.md#def-4e32f87cad7924e3)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafProgram.Disk](../Leaf/Program.definitions.md#def-e343337119cf665f)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLeafBatchProgram.extendDisk._proof_1](Program.definitions.md#def-7f51d4aff981ab86)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `Fin.instOfNat`, `instOfNatNat`, `dite`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.decLt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`

<a id="def-7f51d4aff981ab86"></a>
## `CodedSorting.CommonLeafBatchProgram.extendDisk._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), NeZero (2 ^ q.w)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `OfNat.ofNat`, `MulZeroClass.toZero`
