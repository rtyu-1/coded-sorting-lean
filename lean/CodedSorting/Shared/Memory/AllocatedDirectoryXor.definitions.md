# AllocatedDirectoryXor 的定义

[源码](AllocatedDirectoryXor.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-add5104abba71517"></a>
## `CodedSorting.PhysicalFileHandlesXor.xorBlock`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllocatedDirectoryXor.lean#L411)

**类型**

```lean
{B w : ℕ} → CodedSorting.WordControl.Words B w → CodedSorting.WordControl.Words B w → CodedSorting.WordControl.Words B w
```

**定义**

```lean
fun {B w} a b =>
  (CodedSorting.BitWordPacking.blockBits B w).symm fun i =>
    (CodedSorting.BitWordPacking.blockBits B w) a i + (CodedSorting.BitWordPacking.blockBits B w) b i
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.BitWordPacking.blockBits](../Words/WordConvention.definitions.md#def-a9a13aad90fdf19b)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Equiv.instFunLike`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `CommRing.toNonUnitalCommRing`, `ZMod.commRing`, `Equiv`, `Distrib.toAdd`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `NonUnitalNonAssocSemiring.toDistrib`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`
