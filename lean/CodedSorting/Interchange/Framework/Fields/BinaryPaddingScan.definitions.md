# BinaryPaddingScan 的定义

[源码](BinaryPaddingScan.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-c8fa626af923b445"></a>
## `CodedSorting.SingleCoordinate.Before`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L23)

**类型**

```lean
{I : Type u_1} → [inst : LinearOrder I] → I → Type (max 0 u_1)
```

**定义**

```lean
fun {I} [LinearOrder I] i => { k // k < i }
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `LinearOrder`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Subtype`, `LT.lt`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-61b672af3baaa6b5"></a>
## `CodedSorting.SingleCoordinate.After`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L24)

**类型**

```lean
{I : Type u_1} → [inst : LinearOrder I] → I → Type (max 0 u_1)
```

**定义**

```lean
fun {I} [LinearOrder I] i => { k // i < k }
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `LinearOrder`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Subtype`, `LT.lt`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-c357815ca160da97"></a>
## `CodedSorting.SingleCoordinate.modifySelected`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L80)

**类型**

```lean
{I : Type u_1} →
  {R : Type u_2} →
    {Prefix : Type u_3} →
      {Gap : Type u_4} →
        {Suffix : Type u_5} →
          [inst : LinearOrder I] →
            I →
              I →
                (R × R → R × R) →
                  CodedSorting.Address.FullAddress Prefix (I → R) Gap Suffix →
                    CodedSorting.Address.FullAddress Prefix (I → R) Gap Suffix
```

**定义**

```lean
fun {I} {R} {Prefix} {Gap} {Suffix} [LinearOrder I] i j op a =>
  let result := op (a.high i, a.low j);
  { prefixCoord := a.prefixCoord, high := Function.update a.high i result.1, gap := a.gap,
    low := Function.update a.low j result.2, suffix := a.suffix }
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Function.update`, `LinearOrder.toDecidableEq`, `LinearOrder`, `Prod.mk`, `Prod.fst`, `Prod`, `Prod.snd`

<a id="def-945a2a92a6f3df83"></a>
## `CodedSorting.SingleCoordinate.shortExchange`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L110)

**类型**

```lean
{I : Type u_1} →
  {R : Type u_2} →
    {Prefix : Type u_3} →
      {Gap : Type u_4} →
        {Suffix : Type u_5} →
          [inst : LinearOrder I] → I → I → Equiv.Perm (CodedSorting.Address.FullAddress Prefix (I → R) Gap Suffix)
```

**定义**

```lean
fun {I} {R} {Prefix} {Gap} {Suffix} [LinearOrder I] i j =>
  { toFun := CodedSorting.SingleCoordinate.modifySelected i j Prod.swap,
    invFun := CodedSorting.SingleCoordinate.modifySelected i j Prod.swap, left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.SingleCoordinate.shortExchange._proof_9](BinaryPaddingScan.definitions.md#def-e3934f82dce57c48)
- [CodedSorting.SingleCoordinate.modifySelected](BinaryPaddingScan.definitions.md#def-c357815ca160da97)

**基础库名称**

`LinearOrder`, `Equiv.mk`, `Equiv.Perm`, `Prod.swap`

<a id="def-27613a35b25c74be"></a>
## `CodedSorting.CoordinateScans.lowLayout`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L260)

**类型**

```lean
{P Q G S : ℕ} → CodedSorting.Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin S) ≃ Fin (P * (Q * G) * (Q * S))
```

**定义**

```lean
fun {P Q G S} =>
  {
    toFun := fun a =>
      CodedSorting.TriangularStreams.tripleEncode
        (CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.high, a.gap), a.low, a.suffix),
    invFun := fun x =>
      let outer := CodedSorting.TriangularStreams.tripleEncode.symm x;
      let pre := CodedSorting.TriangularStreams.tripleEncode.symm outer.1;
      { prefixCoord := pre.1, high := pre.2.1, gap := pre.2.2, low := outer.2.1, suffix := outer.2.2 },
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.CoordinateScans.lowLayout._proof_12](BinaryPaddingScan.definitions.md#def-669d68d5df4088b1)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.CoordinateScans.lowLayout._proof_11](BinaryPaddingScan.definitions.md#def-0f2a59252d4b1934)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv.mk`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-9f78c58eb260cdb3"></a>
## `CodedSorting.BinaryPadding.Volume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L458)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun P Q G S => P * (Q * G) * (Q * S)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-88da4e0529453272"></a>
## `CodedSorting.BinaryPadding.Addr`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L459)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun P Q G S => CodedSorting.Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)

**基础库名称**

`Nat`, `Fin`

<a id="def-e31dbc0d4258590d"></a>
## `CodedSorting.BinaryPadding.embed`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L461)

**类型**

```lean
{P G S n m : ℕ} → n ≤ m → CodedSorting.BinaryPadding.Addr P n G S → CodedSorting.BinaryPadding.Addr P m G S
```

**定义**

```lean
fun {P G S n m} h a =>
  { prefixCoord := a.prefixCoord, high := Fin.castLE h a.high, gap := a.gap, low := Fin.castLE h a.low,
    suffix := a.suffix }
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.BinaryPadding.Addr](BinaryPaddingScan.definitions.md#def-88da4e0529453272)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Fin.castLE`, `LE.le`, `instLENat`, `Nat`, `Fin`

<a id="def-55a103c70c916359"></a>
## `CodedSorting.BinaryPadding.physicalEmbed`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L503)

**类型**

```lean
{P G S n m : ℕ} →
  n ≤ m → Fin (CodedSorting.BinaryPadding.Volume P n G S) → Fin (CodedSorting.BinaryPadding.Volume P m G S)
```

**定义**

```lean
fun {P G S n m} h x =>
  CodedSorting.CoordinateScans.lowLayout
    (CodedSorting.BinaryPadding.embed h (CodedSorting.CoordinateScans.lowLayout.symm x))
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.CoordinateScans.lowLayout](BinaryPaddingScan.definitions.md#def-27613a35b25c74be)
- [CodedSorting.BinaryPadding.embed](BinaryPaddingScan.definitions.md#def-e31dbc0d4258590d)
- [CodedSorting.BinaryPadding.Volume](BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `LE.le`, `instLENat`, `Nat`, `Equiv.symm`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-910a2c4f95254734"></a>
## `CodedSorting.BinaryPadding.physicalEmbed_strictMono`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BinaryPaddingScan.lean#L517)

**类型**

```lean
∀ {P G S n m : ℕ} (h : n ≤ m), StrictMono (CodedSorting.BinaryPadding.physicalEmbed h)
```

**继续展开**

- [CodedSorting.BinaryPadding.physicalEmbed](BinaryPaddingScan.definitions.md#def-55a103c70c916359)
- [CodedSorting.BinaryPadding.Volume](BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`StrictMono`, `PartialOrder.toPreorder`, `LE.le`, `instLENat`, `Fin.instPartialOrder`, `Nat`, `Fin`

<a id="def-2592e6a8b528ee13"></a>
## `CodedSorting.BinaryPadding.exponent`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BinaryPaddingScan.lean#L549)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun q u => Nat.clog q (2 ^ u)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Nat.clog`

<a id="def-0f2a59252d4b1934"></a>
## `CodedSorting.CoordinateScans.lowLayout._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BinaryPaddingScan.lean)

**类型**

```lean
∀ {P Q G S : ℕ} (a : CodedSorting.Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)),
  {
      prefixCoord :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
            (CodedSorting.TriangularStreams.tripleEncode.symm
                (CodedSorting.TriangularStreams.tripleEncode
                  (CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.high, a.gap), a.low, a.suffix))).1).1,
      high :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (CodedSorting.TriangularStreams.tripleEncode.symm
                  (CodedSorting.TriangularStreams.tripleEncode
                    (CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.high, a.gap), a.low,
                      a.suffix))).1).2.1,
      gap :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (CodedSorting.TriangularStreams.tripleEncode.symm
                  (CodedSorting.TriangularStreams.tripleEncode
                    (CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.high, a.gap), a.low,
                      a.suffix))).1).2.2,
      low :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (CodedSorting.TriangularStreams.tripleEncode
                (CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.high, a.gap), a.low, a.suffix))).2.1,
      suffix :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (CodedSorting.TriangularStreams.tripleEncode
                (CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.high, a.gap), a.low, a.suffix))).2.2 } =
    a
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-669d68d5df4088b1"></a>
## `CodedSorting.CoordinateScans.lowLayout._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BinaryPaddingScan.lean)

**类型**

```lean
∀ {P Q G S : ℕ} (x : Fin (P * (Q * G) * (Q * S))),
  CodedSorting.TriangularStreams.tripleEncode
      (CodedSorting.TriangularStreams.tripleEncode
          ((CodedSorting.TriangularStreams.tripleEncode.symm (CodedSorting.TriangularStreams.tripleEncode.symm x).1).1,
            (CodedSorting.TriangularStreams.tripleEncode.symm
                  (CodedSorting.TriangularStreams.tripleEncode.symm x).1).2.1,
            (CodedSorting.TriangularStreams.tripleEncode.symm
                  (CodedSorting.TriangularStreams.tripleEncode.symm x).1).2.2),
        (CodedSorting.TriangularStreams.tripleEncode.symm x).2.1,
        (CodedSorting.TriangularStreams.tripleEncode.symm x).2.2) =
    x
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-e3934f82dce57c48"></a>
## `CodedSorting.SingleCoordinate.shortExchange._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BinaryPaddingScan.lean)

**类型**

```lean
∀ {I : Type u_2} {R : Type u_3} {Prefix : Type u_1} {Gap : Type u_4} {Suffix : Type u_5} [inst : LinearOrder I]
  (i j : I) (a : CodedSorting.Address.FullAddress Prefix (I → R) Gap Suffix),
  CodedSorting.SingleCoordinate.modifySelected i j Prod.swap
      (CodedSorting.SingleCoordinate.modifySelected i j Prod.swap a) =
    a
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.SingleCoordinate.modifySelected](BinaryPaddingScan.definitions.md#def-c357815ca160da97)

**基础库名称**

`LinearOrder`, `Prod.swap`, `Eq`
