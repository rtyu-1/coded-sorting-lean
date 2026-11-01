# AddressLayout 的定义

[源码](AddressLayout.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-1d9d3db74e54f41b"></a>
## `CodedSorting.CommonAddressLayout.FieldCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L15)

**类型**

```lean
(I : Type u_2) → [inst : Fintype I] → ℕ → ℕ
```

**定义**

```lean
fun I [Fintype I] Q => Q ^ Fintype.card I
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fintype.card`, `Fintype`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-2ac21fef4723d861"></a>
## `CodedSorting.CommonAddressLayout.BeforeCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L16)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → ℕ → I → ℕ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] Q i => Q ^ Fintype.card (CodedSorting.SingleCoordinate.Before i)
```

**继续展开**

- [CodedSorting.SingleCoordinate.Before](../Fields/BinaryPaddingScan.definitions.md#def-c8fa626af923b445)

**基础库名称**

`Preorder.toLT`, `Nat.instMonoid`, `LinearOrder`, `PartialOrder.toPreorder`, `Subtype.fintype`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fintype.card`, `Fintype`, `HPow.hPow`, `LinearOrder.toDecidableLT`, `Nat`, `LT.lt`, `instHPow`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-4b7e6b3ce2936ed7"></a>
## `CodedSorting.CommonAddressLayout.AfterCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L17)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → ℕ → I → ℕ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] Q i => Q ^ Fintype.card (CodedSorting.SingleCoordinate.After i)
```

**继续展开**

- [CodedSorting.SingleCoordinate.After](../Fields/BinaryPaddingScan.definitions.md#def-61b672af3baaa6b5)

**基础库名称**

`Preorder.toLT`, `Nat.instMonoid`, `LinearOrder`, `PartialOrder.toPreorder`, `Subtype.fintype`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fintype.card`, `Fintype`, `HPow.hPow`, `LinearOrder.toDecidableLT`, `Nat`, `LT.lt`, `instHPow`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-78d3be525d0e72fe"></a>
## `CodedSorting.CommonAddressLayout.shape`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L87)

**类型**

```lean
{A : Type u_2} →
  {B : Type u_3} →
    {C : Type u_4} →
      {D : Type u_5} →
        {A' : Type u_6} →
          {B' : Type u_7} →
            {C' : Type u_8} →
              {D' : Type u_9} →
                A ≃ A' →
                  B ≃ B' →
                    C ≃ C' →
                      D ≃ D' → CodedSorting.Address.FullAddress A B C D ≃ CodedSorting.Address.FullAddress A' B' C' D'
```

**定义**

```lean
fun {A} {B} {C} {D} {A'} {B'} {C'} {D'} ep eh eg es =>
  {
    toFun := fun a =>
      { prefixCoord := ep a.prefixCoord, high := eh a.high, gap := eg a.gap, low := eh a.low, suffix := es a.suffix },
    invFun := fun a =>
      { prefixCoord := ep.symm a.prefixCoord, high := eh.symm a.high, gap := eg.symm a.gap, low := eh.symm a.low,
        suffix := es.symm a.suffix },
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.CommonAddressLayout.shape._proof_4](AddressLayout.definitions.md#def-a4ab7df8c70637bc)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)
- [CodedSorting.CommonAddressLayout.shape._proof_3](AddressLayout.definitions.md#def-c02b192ab4522c9b)

**基础库名称**

`Equiv.instFunLike`, `Equiv.mk`, `Equiv`, `Equiv.symm`, `DFunLike.coe`

<a id="def-b3dff48de4627bef"></a>
## `CodedSorting.CommonAddressLayout.Volume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L96)

**类型**

```lean
(I : Type u_2) → [inst : Fintype I] → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun I [Fintype I] P Q G S =>
  P * (CodedSorting.CommonAddressLayout.FieldCount I Q * G) * (CodedSorting.CommonAddressLayout.FieldCount I Q * S)
```

**继续展开**

- [CodedSorting.CommonAddressLayout.FieldCount](AddressLayout.definitions.md#def-1d9d3db74e54f41b)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fintype`, `Nat`, `instHMul`

<a id="def-6ebf2402101b2f28"></a>
## `CodedSorting.CommonAddressLayout.longLayout`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L99)

**类型**

```lean
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : LinearOrder I] →
      [inst_2 : WellFoundedLT I] →
        {P Q G S : ℕ} →
          CodedSorting.Address.FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S) ≃
            Fin (CodedSorting.CommonAddressLayout.Volume I P Q G S)
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] [WellFoundedLT I] {P Q G S} =>
  (CodedSorting.CommonAddressLayout.shape (Equiv.refl (Fin P)) CodedSorting.LexBlocks.subvectorEncode
        (Equiv.refl (Fin G)) (Equiv.refl (Fin S))).trans
    CodedSorting.CoordinateScans.lowLayout
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.CommonAddressLayout.shape](AddressLayout.definitions.md#def-78d3be525d0e72fe)
- [CodedSorting.CoordinateScans.lowLayout](../Fields/BinaryPaddingScan.definitions.md#def-27613a35b25c74be)
- [CodedSorting.LexBlocks.subvectorEncode](../../../Shared/Indexing/LexBlocks.definitions.md#def-3bfb2af662c69a76)
- [CodedSorting.CommonAddressLayout.Volume](AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Preorder.toLT`, `Equiv.trans`, `Nat.instMonoid`, `LinearOrder`, `WellFoundedLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fintype.card`, `Equiv`, `Fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Equiv.refl`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-5c09851b2e77598f"></a>
## `CodedSorting.CommonAddressLayout.ChildPrefix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L108)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → ℕ → ℕ → I → ℕ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] P Q i => P * CodedSorting.CommonAddressLayout.BeforeCount Q i
```

**继续展开**

- [CodedSorting.CommonAddressLayout.BeforeCount](AddressLayout.definitions.md#def-2ac21fef4723d861)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `instMulNat`, `Fintype`, `Nat`, `instHMul`

<a id="def-92585e8addd446c8"></a>
## `CodedSorting.CommonAddressLayout.ChildGap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L109)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → ℕ → ℕ → I → I → ℕ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] G Q i j =>
  CodedSorting.CommonAddressLayout.AfterCount Q i * (G * CodedSorting.CommonAddressLayout.BeforeCount Q j)
```

**继续展开**

- [CodedSorting.CommonAddressLayout.BeforeCount](AddressLayout.definitions.md#def-2ac21fef4723d861)
- [CodedSorting.CommonAddressLayout.AfterCount](AddressLayout.definitions.md#def-4b7e6b3ce2936ed7)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `instMulNat`, `Fintype`, `Nat`, `instHMul`

<a id="def-a65f392f1717518d"></a>
## `CodedSorting.CommonAddressLayout.ChildSuffix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AddressLayout.lean#L110)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → ℕ → ℕ → I → ℕ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] S Q j => CodedSorting.CommonAddressLayout.AfterCount Q j * S
```

**继续展开**

- [CodedSorting.CommonAddressLayout.AfterCount](AddressLayout.definitions.md#def-4b7e6b3ce2936ed7)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `instMulNat`, `Fintype`, `Nat`, `instHMul`

<a id="def-c02b192ab4522c9b"></a>
## `CodedSorting.CommonAddressLayout.shape._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AddressLayout.lean)

**类型**

```lean
∀ {A : Type u_1} {B : Type u_2} {C : Type u_3} {D : Type u_4} {A' : Type u_5} {B' : Type u_6} {C' : Type u_7}
  {D' : Type u_8} (ep : A ≃ A') (eh : B ≃ B') (eg : C ≃ C') (es : D ≃ D')
  (a : CodedSorting.Address.FullAddress A B C D),
  {
      prefixCoord :=
        ep.symm
          { prefixCoord := ep a.prefixCoord, high := eh a.high, gap := eg a.gap, low := eh a.low,
              suffix := es a.suffix }.prefixCoord,
      high :=
        eh.symm
          { prefixCoord := ep a.prefixCoord, high := eh a.high, gap := eg a.gap, low := eh a.low,
              suffix := es a.suffix }.high,
      gap :=
        eg.symm
          { prefixCoord := ep a.prefixCoord, high := eh a.high, gap := eg a.gap, low := eh a.low,
              suffix := es a.suffix }.gap,
      low :=
        eh.symm
          { prefixCoord := ep a.prefixCoord, high := eh a.high, gap := eg a.gap, low := eh a.low,
              suffix := es a.suffix }.low,
      suffix :=
        es.symm
          { prefixCoord := ep a.prefixCoord, high := eh a.high, gap := eg a.gap, low := eh a.low,
              suffix := es a.suffix }.suffix } =
    a
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

`Equiv.instFunLike`, `Equiv`, `Equiv.symm`, `Eq`, `DFunLike.coe`

<a id="def-a4ab7df8c70637bc"></a>
## `CodedSorting.CommonAddressLayout.shape._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](AddressLayout.lean)

**类型**

```lean
∀ {A : Type u_5} {B : Type u_6} {C : Type u_7} {D : Type u_8} {A' : Type u_1} {B' : Type u_2} {C' : Type u_3}
  {D' : Type u_4} (ep : A ≃ A') (eh : B ≃ B') (eg : C ≃ C') (es : D ≃ D')
  (a : CodedSorting.Address.FullAddress A' B' C' D'),
  {
      prefixCoord :=
        ep
          { prefixCoord := ep.symm a.prefixCoord, high := eh.symm a.high, gap := eg.symm a.gap, low := eh.symm a.low,
              suffix := es.symm a.suffix }.prefixCoord,
      high :=
        eh
          { prefixCoord := ep.symm a.prefixCoord, high := eh.symm a.high, gap := eg.symm a.gap, low := eh.symm a.low,
              suffix := es.symm a.suffix }.high,
      gap :=
        eg
          { prefixCoord := ep.symm a.prefixCoord, high := eh.symm a.high, gap := eg.symm a.gap, low := eh.symm a.low,
              suffix := es.symm a.suffix }.gap,
      low :=
        eh
          { prefixCoord := ep.symm a.prefixCoord, high := eh.symm a.high, gap := eg.symm a.gap, low := eh.symm a.low,
              suffix := es.symm a.suffix }.low,
      suffix :=
        es
          { prefixCoord := ep.symm a.prefixCoord, high := eh.symm a.high, gap := eg.symm a.gap, low := eh.symm a.low,
              suffix := es.symm a.suffix }.suffix } =
    a
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

`Equiv.instFunLike`, `Equiv`, `Equiv.symm`, `Eq`, `DFunLike.coe`
