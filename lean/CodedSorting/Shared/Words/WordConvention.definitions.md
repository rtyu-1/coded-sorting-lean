# WordConvention 的定义

[源码](WordConvention.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-5ac34e3d8146967b"></a>
## `CodedSorting.WordControl.Word`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](WordConvention.lean#L18)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun w => Fin (2 ^ w)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-6ff0251bdd746fcb"></a>
## `CodedSorting.WordControl.Words`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](WordConvention.lean#L19)

**类型**

```lean
ℕ → ℕ → Type
```

**定义**

```lean
fun count w => Fin count → CodedSorting.WordControl.Word w
```

**继续展开**

- [CodedSorting.WordControl.Word](WordConvention.definitions.md#def-5ac34e3d8146967b)

**基础库名称**

`Nat`, `Fin`

<a id="def-11c782157f026c8c"></a>
## `CodedSorting.WordControl.decodeWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](WordConvention.lean#L39)

**类型**

```lean
{count w : ℕ} → CodedSorting.WordControl.Words count w → ℕ
```

**定义**

```lean
fun {count w} words => ↑(finFunctionFinEquiv words)
```

**继续展开**

- [CodedSorting.WordControl.Words](WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `finFunctionFinEquiv`, `Monoid.toNatPow`, `Equiv`, `instOfNatNat`, `Fin.val`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-4e32f87cad7924e3"></a>
## `CodedSorting.WordControl.BlockDisk`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](WordConvention.lean#L93)

**类型**

```lean
ℕ → ℕ → Type
```

**定义**

```lean
fun B w => ℕ → Fin B → CodedSorting.WordControl.Word w
```

**继续展开**

- [CodedSorting.WordControl.Word](WordConvention.definitions.md#def-5ac34e3d8146967b)

**基础库名称**

`Nat`, `Fin`

<a id="def-c2c9e554a7303927"></a>
## `CodedSorting.BitWordPacking.wordBits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](WordConvention.lean#L496)

**类型**

```lean
(w : ℕ) → CodedSorting.WordControl.Word w ≃ (Fin w → CodedSorting.Circuit.Bit)
```

**定义**

```lean
fun w => finFunctionFinEquiv.symm.trans (Equiv.piCongrRight fun x => (ZMod.finEquiv 2).toEquiv)
```

**继续展开**

- [CodedSorting.WordControl.Word](WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.BitWordPacking.wordBits._proof_18](WordConvention.definitions.md#def-8787b42ba17c4d8e)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `RingEquiv.toEquiv`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `ZMod.commRing`, `Equiv.trans`, `Nat.instMonoid`, `finFunctionFinEquiv`, `Monoid.toNatPow`, `Equiv`, `Distrib.toAdd`, `instOfNatNat`, `ZMod`, `HPow.hPow`, `Distrib.toMul`, `Fin.instMul`, `Nat`, `Equiv.piCongrRight`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `NonUnitalNonAssocSemiring.toDistrib`, `Fin.instAdd`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `ZMod.finEquiv`

<a id="def-a9a13aad90fdf19b"></a>
## `CodedSorting.BitWordPacking.blockBits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](WordConvention.lean#L501)

**类型**

```lean
(B w : ℕ) → (Fin B → CodedSorting.WordControl.Word w) ≃ (Fin (B * w) → CodedSorting.Circuit.Bit)
```

**定义**

```lean
fun B w =>
  {
    toFun := fun words i =>
      (CodedSorting.BitWordPacking.wordBits w) (words (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2,
    invFun := fun bits j => (CodedSorting.BitWordPacking.wordBits w).symm fun i => bits (finProdFinEquiv (j, i)),
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.BitWordPacking.blockBits._proof_19](WordConvention.definitions.md#def-dcbda7430ea16be1)
- [CodedSorting.WordControl.Word](WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.BitWordPacking.wordBits](WordConvention.definitions.md#def-c2c9e554a7303927)
- [CodedSorting.BitWordPacking.blockBits._proof_20](WordConvention.definitions.md#def-c76383ad3264da66)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv.mk`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-a9dbb84e85202da9"></a>
## `CodedSorting.WordConvention.Covers`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](WordConvention.lean#L660)

**类型**

```lean
ℕ → ℕ → ℕ → Prop
```

**定义**

```lean
fun N w c => Nat.clog 2 N ≤ c * w
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `Nat.clog`, `instHMul`

<a id="def-9628275071b9e991"></a>
## `CodedSorting.WordConvention.polynomial_capacity`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](WordConvention.lean#L682)

**类型**

```lean
∀ (N w c exponent : ℕ),
  2 ≤ N → CodedSorting.WordConvention.Covers N w c → N ^ exponent + 1 ≤ (2 ^ w) ^ (c * (exponent + 1))
```

**继续展开**

- [CodedSorting.WordConvention.Covers](WordConvention.definitions.md#def-a9dbb84e85202da9)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-b25382c90b106b24"></a>
## `CodedSorting.WordConvention.encode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](WordConvention.lean#L695)

**类型**

```lean
(N w c exponent : ℕ) →
  2 ≤ N →
    CodedSorting.WordConvention.Covers N w c →
      Fin (N ^ exponent + 1) → CodedSorting.WordControl.Words (c * (exponent + 1)) w
```

**定义**

```lean
fun N w c exponent hN h x => finFunctionFinEquiv.symm (Fin.castLE ⋯ x)
```

**继续展开**

- [CodedSorting.WordConvention.polynomial_capacity](WordConvention.definitions.md#def-9628275071b9e991)
- [CodedSorting.WordConvention.Covers](WordConvention.definitions.md#def-a9dbb84e85202da9)
- [CodedSorting.WordControl.Words](WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Fin.castLE`, `Nat.instMonoid`, `finFunctionFinEquiv`, `Monoid.toNatPow`, `Equiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-dcbda7430ea16be1"></a>
## `CodedSorting.BitWordPacking.blockBits._proof_19`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](WordConvention.lean)

**类型**

```lean
∀ (B w : ℕ) (words : Fin B → CodedSorting.WordControl.Word w),
  (fun j =>
      (CodedSorting.BitWordPacking.wordBits w).symm fun i =>
        (CodedSorting.BitWordPacking.wordBits w) (words (finProdFinEquiv.symm (finProdFinEquiv (j, i))).1)
          (finProdFinEquiv.symm (finProdFinEquiv (j, i))).2) =
    words
```

**继续展开**

- [CodedSorting.WordControl.Word](WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.BitWordPacking.wordBits](WordConvention.definitions.md#def-c2c9e554a7303927)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-c76383ad3264da66"></a>
## `CodedSorting.BitWordPacking.blockBits._proof_20`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](WordConvention.lean)

**类型**

```lean
∀ (B w : ℕ) (bits : Fin (B * w) → CodedSorting.Circuit.Bit),
  (fun i =>
      (CodedSorting.BitWordPacking.wordBits w)
        ((CodedSorting.BitWordPacking.wordBits w).symm fun i_1 =>
          bits (finProdFinEquiv ((finProdFinEquiv.symm i).1, i_1)))
        (finProdFinEquiv.symm i).2) =
    bits
```

**继续展开**

- [CodedSorting.WordControl.Word](WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.BitWordPacking.wordBits](WordConvention.definitions.md#def-c2c9e554a7303927)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-8787b42ba17c4d8e"></a>
## `CodedSorting.BitWordPacking.wordBits._proof_18`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](WordConvention.lean)

**类型**

```lean
NeZero (1 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`
