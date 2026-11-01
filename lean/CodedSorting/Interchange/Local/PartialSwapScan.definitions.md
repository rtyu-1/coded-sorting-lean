# PartialSwapScan 的定义

[源码](PartialSwapScan.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-63b4f15890df9b8c"></a>
## `CodedSorting.Construction.PartialSwapScan.Addr`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L27)

**类型**

```lean
Type u_2 → ℕ → ℕ → ℕ → ℕ → Type (max 0 u_2)
```

**定义**

```lean
fun I P Q G S => CodedSorting.Address.FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)

**基础库名称**

`Nat`, `Fin`

<a id="def-5874ab1dce22ad43"></a>
## `CodedSorting.Construction.PartialSwapScan.LowPrefixSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L34)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → ℕ → ℕ → ℕ → I → ℕ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] P Q G i =>
  P * (CodedSorting.CommonAddressLayout.FieldCount I Q * G) * CodedSorting.CommonAddressLayout.BeforeCount Q i
```

**继续展开**

- [CodedSorting.CommonAddressLayout.FieldCount](../Framework/Memory/AddressLayout.definitions.md#def-1d9d3db74e54f41b)
- [CodedSorting.CommonAddressLayout.BeforeCount](../Framework/Memory/AddressLayout.definitions.md#def-2ac21fef4723d861)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `instMulNat`, `Fintype`, `Nat`, `instHMul`

<a id="def-ea6f90212307da45"></a>
## `CodedSorting.Construction.PartialSwapScan.LowSuffixSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L36)

**类型**

```lean
{I : Type u_1} → [inst : Fintype I] → [inst : LinearOrder I] → ℕ → ℕ → I → ℕ
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] Q S i => CodedSorting.CommonAddressLayout.AfterCount Q i * S
```

**继续展开**

- [CodedSorting.CommonAddressLayout.AfterCount](../Framework/Memory/AddressLayout.definitions.md#def-4b7e6b3ce2936ed7)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `instMulNat`, `Fintype`, `Nat`, `instHMul`

<a id="def-fbc0d981ae52984e"></a>
## `CodedSorting.Construction.PartialSwapScan.lowVolume`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapScan.lean#L60)

**类型**

```lean
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : LinearOrder I] [inst_2 : WellFoundedLT I] {P Q G S : ℕ} (i : I),
  CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i *
      (Q * CodedSorting.Construction.PartialSwapScan.LowSuffixSize Q S i) =
    CodedSorting.CommonAddressLayout.Volume I P Q G S
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.LowPrefixSize](PartialSwapScan.definitions.md#def-5874ab1dce22ad43)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.PartialSwapScan.LowSuffixSize](PartialSwapScan.definitions.md#def-ea6f90212307da45)

**基础库名称**

`Preorder.toLT`, `HMul.hMul`, `LinearOrder`, `WellFoundedLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `instMulNat`, `Fintype`, `Nat`, `Eq`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-261e254dd597819b"></a>
## `CodedSorting.Construction.PartialSwapScan.castPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L144)

**类型**

```lean
{V W : ℕ} → V = W → CodedSorting.ScanProgram.Pass V → CodedSorting.ScanProgram.Pass W
```

**定义**

```lean
fun {V W} h p => h ▸ p
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Eq.rec`, `Nat`, `Eq`

<a id="def-3be07712259809d7"></a>
## `CodedSorting.Construction.PartialSwapScan.slotPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L157)

**类型**

```lean
{Q K V A C : ℕ} →
  A * (Q * C) = V →
    (e : Fin A → Equiv.Perm (Fin Q)) →
      (key : Fin A → Fin Q → Fin K) →
        (∀ (p : Fin A) (x y : Fin Q), x < y → key p x = key p y → (e p) x < (e p) y) → CodedSorting.ScanProgram.Pass V
```

**定义**

```lean
fun {Q K V A C} h e key hinc =>
  CodedSorting.Construction.PartialSwapScan.castPass h
    (CodedSorting.ScanProgram.Pass.streams K (CodedSorting.TriangularStreams.globalFieldEquiv e)
      (CodedSorting.TriangularStreams.globalKey key) ⋯)
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.castPass](PartialSwapScan.definitions.md#def-261e254dd597819b)
- [CodedSorting.ScanProgram.Pass.streams](../../Shared/Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.TriangularStreams.globalKey](../../Circuit/Framework/TriangularStreams.definitions.md#def-f272f59e3f07df97)
- [CodedSorting.TriangularStreams.global_increasing_streams](../../Circuit/Framework/TriangularStreams.definitions.md#def-fef164089f463635)
- [CodedSorting.TriangularStreams.globalFieldEquiv](../../Circuit/Framework/TriangularStreams.definitions.md#def-512e9a6065bbe891)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-0f65ee37729dd571"></a>
## `CodedSorting.Construction.PartialSwapScan.lowPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L188)

**类型**

```lean
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : LinearOrder I] →
      [inst_2 : WellFoundedLT I] →
        {P Q G S K : ℕ} →
          (i : I) →
            (e : Fin (CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i) → Equiv.Perm (Fin Q)) →
              (key : Fin (CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i) → Fin Q → Fin K) →
                (∀ (p : Fin (CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i)) (x y : Fin Q),
                    x < y → key p x = key p y → (e p) x < (e p) y) →
                  CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume I P Q G S)
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] [WellFoundedLT I] {P Q G S K} i e key hinc =>
  CodedSorting.Construction.PartialSwapScan.slotPass ⋯ e key hinc
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.lowVolume](PartialSwapScan.definitions.md#def-fbc0d981ae52984e)
- [CodedSorting.Construction.PartialSwapScan.LowPrefixSize](PartialSwapScan.definitions.md#def-5874ab1dce22ad43)
- [CodedSorting.Construction.PartialSwapScan.slotPass](PartialSwapScan.definitions.md#def-3be07712259809d7)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.PartialSwapScan.LowSuffixSize](PartialSwapScan.definitions.md#def-ea6f90212307da45)

**基础库名称**

`Equiv.instFunLike`, `Preorder.toLT`, `LinearOrder`, `WellFoundedLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fintype`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`, `DFunLike.coe`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-6bb2f91bba5a1c84"></a>
## `CodedSorting.Construction.PartialSwapScan.lowAdd`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L246)

**类型**

```lean
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : LinearOrder I] →
      [inst_2 : WellFoundedLT I] →
        {P Q G S : ℕ} →
          (i : I) →
            (Fin (CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i) → Fin Q) →
              CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume I P Q G S)
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] [WellFoundedLT I] {P Q G S} i offset =>
  CodedSorting.Construction.PartialSwapScan.lowPass i (fun p => CodedSorting.AffineStreams.additionEquiv (offset p))
    (fun p => CodedSorting.SequentialArithmetic.additionRun (offset p)) ⋯
```

**继续展开**

- [CodedSorting.SequentialArithmetic.additionRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-4958ad02f45d9028)
- [CodedSorting.Construction.PartialSwapScan.LowPrefixSize](PartialSwapScan.definitions.md#def-5874ab1dce22ad43)
- [CodedSorting.Construction.PartialSwapScan.lowPass](PartialSwapScan.definitions.md#def-0f65ee37729dd571)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.Construction.PartialSwapScan.lowAdd._proof_4](PartialSwapScan.definitions.md#def-96ca251ecb714658)
- [CodedSorting.AffineStreams.additionEquiv](../../Circuit/Framework/AffineStreams.definitions.md#def-7c94b054256195c1)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Preorder.toLT`, `LinearOrder`, `WellFoundedLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `instOfNatNat`, `Fintype`, `Nat`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-269fb4187d8bdda4"></a>
## `CodedSorting.Construction.PartialSwapScan.highFromLowPrefix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L321)

**类型**

```lean
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : LinearOrder I] →
      [inst_2 : WellFoundedLT I] →
        {P Q G : ℕ} → (i : I) → Fin (CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i) → I → Fin Q
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] [WellFoundedLT I] {P Q G} i p =>
  CodedSorting.LexBlocks.subvectorEncode.symm
    (CodedSorting.TriangularStreams.tripleEncode.symm (finProdFinEquiv.symm p).1).2.1
```

**继续展开**

- [CodedSorting.CommonAddressLayout.FieldCount](../Framework/Memory/AddressLayout.definitions.md#def-1d9d3db74e54f41b)
- [CodedSorting.CommonAddressLayout.BeforeCount](../Framework/Memory/AddressLayout.definitions.md#def-2ac21fef4723d861)
- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Construction.PartialSwapScan.LowPrefixSize](PartialSwapScan.definitions.md#def-5874ab1dce22ad43)
- [CodedSorting.TriangularStreams.tripleEncode](../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.LexBlocks.subvectorEncode](../../Shared/Indexing/LexBlocks.definitions.md#def-3bfb2af662c69a76)

**基础库名称**

`Equiv.instFunLike`, `Preorder.toLT`, `HMul.hMul`, `Nat.instMonoid`, `LinearOrder`, `WellFoundedLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fintype.card`, `Equiv`, `instMulNat`, `Prod.fst`, `Fintype`, `HPow.hPow`, `Nat`, `finProdFinEquiv`, `instHPow`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-0c60fb9053685036"></a>
## `CodedSorting.Construction.PartialSwapScan.crossOffset`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L331)

**类型**

```lean
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : LinearOrder I] →
      [inst_2 : WellFoundedLT I] →
        {P Q G : ℕ} →
          [inst_3 : NeZero Q] →
            Matrix I I (Fin Q) → (i : I) → Fin (CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i) → Fin Q
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] [WellFoundedLT I] {P Q G} [NeZero Q] C i p =>
  C.mulVec (CodedSorting.Construction.PartialSwapScan.highFromLowPrefix i p) i
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.highFromLowPrefix](PartialSwapScan.definitions.md#def-269fb4187d8bdda4)
- [CodedSorting.Construction.PartialSwapScan.LowPrefixSize](PartialSwapScan.definitions.md#def-5874ab1dce22ad43)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Nat.instMulZeroClass`, `Preorder.toLT`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `Fin.instCommRing`, `Matrix`, `LinearOrder`, `WellFoundedLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fintype`, `Nat`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `NeZero`, `Fin`, `Matrix.mulVec`, `instDistribLatticeOfLinearOrder`, `MulZeroClass.toZero`, `Lattice.toSemilatticeInf`

<a id="def-7a773ebdafc35463"></a>
## `CodedSorting.Construction.PartialSwapScan.crossPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L335)

**类型**

```lean
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : LinearOrder I] →
      [inst_2 : WellFoundedLT I] →
        {P Q G S : ℕ} →
          [inst_3 : NeZero Q] →
            Matrix I I (Fin Q) → I → CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume I P Q G S)
```

**定义**

```lean
fun {I} [Fintype I] [LinearOrder I] [WellFoundedLT I] {P Q G S} [NeZero Q] C i =>
  CodedSorting.Construction.PartialSwapScan.lowAdd i (CodedSorting.Construction.PartialSwapScan.crossOffset C i)
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.crossOffset](PartialSwapScan.definitions.md#def-0c60fb9053685036)
- [CodedSorting.Construction.PartialSwapScan.lowAdd](PartialSwapScan.definitions.md#def-6bb2f91bba5a1c84)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Nat.instMulZeroClass`, `Preorder.toLT`, `Matrix`, `LinearOrder`, `WellFoundedLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fintype`, `Nat`, `NeZero`, `Fin`, `instDistribLatticeOfLinearOrder`, `MulZeroClass.toZero`, `Lattice.toSemilatticeInf`

<a id="def-b42192232c56dca0"></a>
## `CodedSorting.Construction.PartialSwapScan.crossProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapScan.lean#L351)

**类型**

```lean
{P Q G S : ℕ} →
  [inst : NeZero Q] →
    {m : ℕ} →
      Matrix (Fin m) (Fin m) (Fin Q) →
        (n : ℕ) → n ≤ m → List (CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume (Fin m) P Q G S))
```

**定义**

```lean
fun {P Q G S} [NeZero Q] {m} C x x_1 =>
  Nat.brecOn (motive := fun x =>
    x ≤ m → List (CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume (Fin m) P Q G S))) x
    (fun x f x_2 =>
      (match (motive :=
          (x : ℕ) →
            x ≤ m →
              Nat.below (motive := fun x =>
                  x ≤ m →
                    List (CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume (Fin m) P Q G S)))
                  x →
                List (CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume (Fin m) P Q G S)))
          x, x_2 with
        | 0, x => fun x => []
        | n.succ, hn => fun x => CodedSorting.Construction.PartialSwapScan.crossPass C ⟨n, ⋯⟩ :: x.1 ⋯)
        f)
    x_1
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.crossProgram._proof_12](PartialSwapScan.definitions.md#def-468170da90f73f75)
- [CodedSorting.Construction.PartialSwapScan.crossProgram._proof_11](PartialSwapScan.definitions.md#def-c95fc9b923971a84)
- [CodedSorting.Construction.PartialSwapScan.crossPass](PartialSwapScan.definitions.md#def-7a773ebdafc35463)
- [CodedSorting.Construction.PartialSwapScan.crossProgram._proof_13](PartialSwapScan.definitions.md#def-ce0166f44bd2088f)
- [CodedSorting.Construction.PartialSwapScan.crossProgram.match_1](PartialSwapScan.definitions.md#def-3a03e94e56b12469)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Nat.instMulZeroClass`, `Matrix`, `Fin.mk`, `Nat.brecOn`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.fintype`, `List.cons`, `Nat.below`, `List`, `instHAdd`, `Fin.instLinearOrder`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `MulZeroClass.toZero`, `List.nil`

<a id="def-c95fc9b923971a84"></a>
## `CodedSorting.Construction.PartialSwapScan.crossProgram._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapScan.lean)

**类型**

```lean
∀ {m : ℕ}, IsWellFounded (Fin m) fun x1 x2 => x1 < x2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.instLinearOrder`, `Nat`, `LT.lt`, `Fin`, `IsWellFounded`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-468170da90f73f75"></a>
## `CodedSorting.Construction.PartialSwapScan.crossProgram._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapScan.lean)

**类型**

```lean
∀ {m : ℕ} (n : ℕ), n + 1 ≤ m → n < m
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-ce0166f44bd2088f"></a>
## `CodedSorting.Construction.PartialSwapScan.crossProgram._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapScan.lean)

**类型**

```lean
∀ {m : ℕ} (n : ℕ), n + 1 ≤ m → n ≤ m
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-3a03e94e56b12469"></a>
## `CodedSorting.Construction.PartialSwapScan.crossProgram.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PartialSwapScan.lean)

**类型**

```lean
{m : ℕ} →
  (motive : (x : ℕ) → x ≤ m → Sort u_1) →
    (x : ℕ) →
      (x_1 : x ≤ m) → ((x : 0 ≤ m) → motive 0 x) → ((n : ℕ) → (hn : n + 1 ≤ m) → motive n.succ hn) → motive x x_1
```

**定义**

```lean
fun {m} motive x x_1 h_1 h_2 =>
  Nat.casesOn (motive := fun x => (x_2 : x ≤ m) → motive x x_2) x (fun x => h_1 x) (fun n x => h_2 n x) x_1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Nat.zero`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-96ca251ecb714658"></a>
## `CodedSorting.Construction.PartialSwapScan.lowAdd._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapScan.lean)

**类型**

```lean
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : LinearOrder I] {P Q G : ℕ} (i : I)
  (offset : Fin (CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i) → Fin Q)
  (p : Fin (CodedSorting.Construction.PartialSwapScan.LowPrefixSize P Q G i)) (x y : Fin Q),
  x < y →
    CodedSorting.SequentialArithmetic.additionRun (offset p) x =
        CodedSorting.SequentialArithmetic.additionRun (offset p) y →
      CodedSorting.SequentialArithmetic.addOffset (offset p) x <
        CodedSorting.SequentialArithmetic.addOffset (offset p) y
```

**继续展开**

- [CodedSorting.SequentialArithmetic.additionRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-4958ad02f45d9028)
- [CodedSorting.Construction.PartialSwapScan.LowPrefixSize](PartialSwapScan.definitions.md#def-5874ab1dce22ad43)
- [CodedSorting.SequentialArithmetic.addOffset](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-1af292012b811a2b)

**基础库名称**

`LinearOrder`, `instOfNatNat`, `Fintype`, `Nat`, `LT.lt`, `instLTFin`, `OfNat.ofNat`, `Fin`, `Eq`
