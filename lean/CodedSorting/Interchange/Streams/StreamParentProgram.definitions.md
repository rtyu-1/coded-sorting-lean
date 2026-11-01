# StreamParentProgram 的定义

[源码](StreamParentProgram.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-aeb1e7cda7cfeb0e"></a>
## `CodedSorting.Construction.StreamSplitLayout.transposeTriples`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L21)

**类型**

```lean
(rows W L : ℕ) →
  CodedSorting.TriangularStreams.TripleAddress rows W L ≃ CodedSorting.TriangularStreams.TripleAddress W rows L
```

**定义**

```lean
fun rows W L =>
  { toFun := fun a => (a.2.1, a.1, a.2.2), invFun := fun a => (a.2.1, a.1, a.2.2), left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Construction.StreamSplitLayout.transposeTriples._proof_2](StreamParentProgram.definitions.md#def-ec0e02c125a43530)
- [CodedSorting.Construction.StreamSplitLayout.transposeTriples._proof_1](StreamParentProgram.definitions.md#def-1c3028c1249d5e5f)

**基础库名称**

`Equiv.mk`, `Equiv`, `Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Prod.snd`

<a id="def-199ddd565ec93625"></a>
## `CodedSorting.Construction.StreamSplitLayout.transposeCard`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean#L27)

**类型**

```lean
∀ (rows W L : ℕ), W * (rows * L) = rows * (W * L)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`

<a id="def-cd1378469d1a29a8"></a>
## `CodedSorting.Construction.StreamSplitLayout.cyclicPermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L29)

**类型**

```lean
(rows W L : ℕ) → Equiv.Perm (Fin (rows * (W * L)))
```

**定义**

```lean
fun rows W L =>
  CodedSorting.TriangularStreams.tripleEncode.symm.trans
    ((CodedSorting.Construction.StreamSplitLayout.transposeTriples rows W L).trans
      (CodedSorting.TriangularStreams.tripleEncode.trans (finCongr ⋯)))
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.transposeTriples](StreamParentProgram.definitions.md#def-aeb1e7cda7cfeb0e)
- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Construction.StreamSplitLayout.transposeCard](StreamParentProgram.definitions.md#def-199ddd565ec93625)
- [CodedSorting.TriangularStreams.tripleEncode](../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `finCongr`, `instMulNat`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `instHMul`

<a id="def-9e841628d71c4df4"></a>
## `CodedSorting.Construction.StreamSplitLayout.cyclicKey`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L33)

**类型**

```lean
(rows W L : ℕ) → Fin (rows * (W * L)) → Fin W
```

**定义**

```lean
fun rows W L x => (CodedSorting.TriangularStreams.tripleEncode.symm x).2.1
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.tripleEncode](../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Prod.fst`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-4a1c9d8308750d21"></a>
## `CodedSorting.Construction.StreamSplitLayout.cyclic_increasing`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean#L42)

**类型**

```lean
∀ (rows W L : ℕ) (x y : Fin (rows * (W * L))),
  x < y →
    CodedSorting.Construction.StreamSplitLayout.cyclicKey rows W L x =
        CodedSorting.Construction.StreamSplitLayout.cyclicKey rows W L y →
      (CodedSorting.Construction.StreamSplitLayout.cyclicPermutation rows W L) x <
        (CodedSorting.Construction.StreamSplitLayout.cyclicPermutation rows W L) y
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.cyclicKey](StreamParentProgram.definitions.md#def-9e841628d71c4df4)
- [CodedSorting.Construction.StreamSplitLayout.cyclicPermutation](StreamParentProgram.definitions.md#def-cd1378469d1a29a8)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-279922b6ca339a3c"></a>
## `CodedSorting.Construction.StreamSplitLayout.rawSplitPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L58)

**类型**

```lean
(rows W L : ℕ) → CodedSorting.ScanProgram.Pass (rows * (W * L))
```

**定义**

```lean
fun rows W L =>
  CodedSorting.ScanProgram.Pass.streams W (CodedSorting.Construction.StreamSplitLayout.cyclicPermutation rows W L)
    (CodedSorting.Construction.StreamSplitLayout.cyclicKey rows W L) ⋯
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.cyclic_increasing](StreamParentProgram.definitions.md#def-4a1c9d8308750d21)
- [CodedSorting.Construction.StreamSplitLayout.cyclicKey](StreamParentProgram.definitions.md#def-9e841628d71c4df4)
- [CodedSorting.Construction.StreamSplitLayout.cyclicPermutation](StreamParentProgram.definitions.md#def-cd1378469d1a29a8)
- [CodedSorting.ScanProgram.Pass.streams](../../Shared/Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-718aba9c32058879"></a>
## `CodedSorting.Construction.StreamSplitLayout.gatherKey`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L63)

**类型**

```lean
(rows W L : ℕ) → Fin (rows * (W * L)) → Fin W
```

**定义**

```lean
fun rows W L x => (CodedSorting.TriangularStreams.tripleEncode.symm ((finCongr ⋯).symm x)).1
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Construction.StreamSplitLayout.transposeCard](StreamParentProgram.definitions.md#def-199ddd565ec93625)
- [CodedSorting.TriangularStreams.tripleEncode](../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `finCongr`, `Equiv`, `instMulNat`, `Prod.fst`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-eeb8f5b751fb7da6"></a>
## `CodedSorting.Construction.StreamSplitLayout.gather_increasing`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean#L71)

**类型**

```lean
∀ (rows W L : ℕ) (x y : Fin (rows * (W * L))),
  x < y →
    CodedSorting.Construction.StreamSplitLayout.gatherKey rows W L x =
        CodedSorting.Construction.StreamSplitLayout.gatherKey rows W L y →
      (Equiv.symm (CodedSorting.Construction.StreamSplitLayout.cyclicPermutation rows W L)) x <
        (Equiv.symm (CodedSorting.Construction.StreamSplitLayout.cyclicPermutation rows W L)) y
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.cyclicPermutation](StreamParentProgram.definitions.md#def-cd1378469d1a29a8)
- [CodedSorting.Construction.StreamSplitLayout.gatherKey](StreamParentProgram.definitions.md#def-718aba9c32058879)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Nat`, `LT.lt`, `instLTFin`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-bdf551f86c40f882"></a>
## `CodedSorting.Construction.StreamSplitLayout.rawGatherPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L89)

**类型**

```lean
(rows W L : ℕ) → CodedSorting.ScanProgram.Pass (rows * (W * L))
```

**定义**

```lean
fun rows W L =>
  CodedSorting.ScanProgram.Pass.streams W
    (Equiv.symm (CodedSorting.Construction.StreamSplitLayout.cyclicPermutation rows W L))
    (CodedSorting.Construction.StreamSplitLayout.gatherKey rows W L) ⋯
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.gather_increasing](StreamParentProgram.definitions.md#def-eeb8f5b751fb7da6)
- [CodedSorting.Construction.StreamSplitLayout.cyclicPermutation](StreamParentProgram.definitions.md#def-cd1378469d1a29a8)
- [CodedSorting.ScanProgram.Pass.streams](../../Shared/Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.Construction.StreamSplitLayout.gatherKey](StreamParentProgram.definitions.md#def-718aba9c32058879)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Equiv.symm`, `Fin`, `instHMul`

<a id="def-028004f74b6d3b80"></a>
## `CodedSorting.Construction.StreamSplitLayout.SegmentCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L99)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun m Q G S =>
  CodedSorting.CommonAddressLayout.FieldCount (Fin m) Q * G *
    (CodedSorting.CommonAddressLayout.FieldCount (Fin m) Q * S)
```

**继续展开**

- [CodedSorting.CommonAddressLayout.FieldCount](../Framework/Memory/AddressLayout.definitions.md#def-1d9d3db74e54f41b)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `Nat`, `Fin`, `instHMul`

<a id="def-1a1a4b4b3a0dba18"></a>
## `CodedSorting.Construction.StreamSplitLayout.distributionVolume`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean#L117)

**类型**

```lean
∀ (m Q rows W G S : ℕ),
  rows * (W * CodedSorting.Construction.StreamSplitLayout.SegmentCount m Q G S) =
    CodedSorting.CommonAddressLayout.Volume (Fin m) (rows * W) Q G S
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.SegmentCount](StreamParentProgram.definitions.md#def-028004f74b6d3b80)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `Nat`, `Fin`, `Eq`, `instHMul`

<a id="def-4aaa0f4dbba50342"></a>
## `CodedSorting.Construction.StreamSplitLayout.splitPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L145)

**类型**

```lean
(m Q rows W G S : ℕ) → CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume (Fin m) (rows * W) Q G S)
```

**定义**

```lean
fun m Q rows W G S =>
  CodedSorting.Construction.PartialSwapScan.castPass ⋯
    (CodedSorting.Construction.StreamSplitLayout.rawSplitPass rows W
      (CodedSorting.Construction.StreamSplitLayout.SegmentCount m Q G S))
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.castPass](../Local/PartialSwapScan.definitions.md#def-261e254dd597819b)
- [CodedSorting.Construction.StreamSplitLayout.rawSplitPass](StreamParentProgram.definitions.md#def-279922b6ca339a3c)
- [CodedSorting.Construction.StreamSplitLayout.SegmentCount](StreamParentProgram.definitions.md#def-028004f74b6d3b80)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.StreamSplitLayout.distributionVolume](StreamParentProgram.definitions.md#def-1a1a4b4b3a0dba18)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `Nat`, `Fin`, `instHMul`

<a id="def-2dfcd3bb769f4642"></a>
## `CodedSorting.Construction.StreamSplitLayout.gatherPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L148)

**类型**

```lean
(m Q rows W G S : ℕ) → CodedSorting.ScanProgram.Pass (CodedSorting.CommonAddressLayout.Volume (Fin m) (rows * W) Q G S)
```

**定义**

```lean
fun m Q rows W G S =>
  CodedSorting.Construction.PartialSwapScan.castPass ⋯
    (CodedSorting.Construction.StreamSplitLayout.rawGatherPass rows W
      (CodedSorting.Construction.StreamSplitLayout.SegmentCount m Q G S))
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.rawGatherPass](StreamParentProgram.definitions.md#def-bdf551f86c40f882)
- [CodedSorting.Construction.PartialSwapScan.castPass](../Local/PartialSwapScan.definitions.md#def-261e254dd597819b)
- [CodedSorting.Construction.StreamSplitLayout.SegmentCount](StreamParentProgram.definitions.md#def-028004f74b6d3b80)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.StreamSplitLayout.distributionVolume](StreamParentProgram.definitions.md#def-1a1a4b4b3a0dba18)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `Nat`, `Fin`, `instHMul`

<a id="def-dcc489e2f022255b"></a>
## `CodedSorting.Construction.StreamSplitLayout.selectedCall`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L303)

**类型**

```lean
ℕ → (m : ℕ) → ℕ → ℕ → ℕ → ℕ → Fin m → Fin m → ℕ → ℕ → ℕ → CodedSorting.Construction.ExchangeInterface.Call
```

**定义**

```lean
fun radix m f Pref G S i j source buffer limit =>
  { fieldWidth := f, prefixCount := CodedSorting.CommonAddressLayout.ChildPrefix Pref (radix ^ f) i,
    gap := CodedSorting.CommonAddressLayout.ChildGap G (radix ^ f) i j,
    suffix := CodedSorting.CommonAddressLayout.ChildSuffix S (radix ^ f) j, source := source, buffer := buffer,
    limit := limit }
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.mk](../Bounds/ExchangeInterface.definitions.md#def-88d363c434138873)
- [CodedSorting.CommonAddressLayout.ChildPrefix](../Framework/Memory/AddressLayout.definitions.md#def-5c09851b2e77598f)
- [CodedSorting.CommonAddressLayout.ChildGap](../Framework/Memory/AddressLayout.definitions.md#def-92585e8addd446c8)
- [CodedSorting.CommonAddressLayout.ChildSuffix](../Framework/Memory/AddressLayout.definitions.md#def-a65f392f1717518d)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.fintype`, `Fin.instLinearOrder`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-df1a2ebcd842733d"></a>
## `CodedSorting.Construction.StreamSplitLayout.selectedCall_volume`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean#L308)

**类型**

```lean
∀ (radix m f Pref G S : ℕ) (i j : Fin m) (source buffer limit : ℕ),
  CodedSorting.Construction.ExchangeInterface.volume radix
      (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit) =
    CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.selectedCall](StreamParentProgram.definitions.md#def-dcc489e2f022255b)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`

<a id="def-00a3279ded565a44"></a>
## `CodedSorting.Construction.StreamSplitLayout.selectedChildProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L357)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (radix m f Pref G S : ℕ) →
    (i j : Fin m) →
      (source buffer limit : ℕ) →
        CodedSorting.Construction.ExchangeInterface.Program q radix
            (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit) →
          CodedSorting.CommonFinitePermutation.Program q
            (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S) source buffer limit
            (CodedSorting.CommonAddressLayout.longLayout.symm.trans
              (Equiv.trans (CodedSorting.SingleCoordinate.shortExchange i j)
                CodedSorting.CommonAddressLayout.longLayout))
```

**定义**

```lean
fun q radix m f Pref G S i j source buffer limit child =>
  let p := CodedSorting.CommonFinitePermutation.Program.castVolume child ⋯;
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_7](StreamParentProgram.definitions.md#def-986adcb5737b826a)
- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3](StreamParentProgram.definitions.md#def-951268f3101df86e)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_5](StreamParentProgram.definitions.md#def-7e3a7f39547133fe)
- [CodedSorting.SingleCoordinate.shortExchange](../Framework/Fields/BinaryPaddingScan.definitions.md#def-945a2a92a6f3df83)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_4](StreamParentProgram.definitions.md#def-e32c66e731e7418b)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall](StreamParentProgram.definitions.md#def-dcc489e2f022255b)
- [CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_6](StreamParentProgram.definitions.md#def-7557a6c801d36295)
- [CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_8](StreamParentProgram.definitions.md#def-b53aa6b8d1e57aeb)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.castVolume](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-011d8c0416a63718)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall_volume](StreamParentProgram.definitions.md#def-df1a2ebcd842733d)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`Preorder.toLT`, `Equiv.trans`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `finCongr`, `Fin.Lt.isWellOrder`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fin.fintype`, `Fin.instLinearOrder`, `HPow.hPow`, `IsWellOrder.toIsWellFounded`, `Nat`, `LT.lt`, `instHPow`, `Equiv.symm`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-7dbb0b09af6bbfe2"></a>
## `CodedSorting.Construction.StreamSplitMachine.transposeCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L424)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader m Q rows W G S source target =>
  CodedSorting.CommonScanProgram.passCode q reader
    (CodedSorting.Construction.StreamSplitLayout.splitPass m Q rows W G S) source target
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.StreamSplitLayout.splitPass](StreamParentProgram.definitions.md#def-4aaa0f4dbba50342)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonScanProgram.passCode](../../Shared/Memory/ScanProgram.definitions.md#def-a3f8f7609a0933eb)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `List`, `Nat`, `Fin`, `instHMul`

<a id="def-497560896f7bd52b"></a>
## `CodedSorting.Construction.StreamSplitMachine.inverseCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L428)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader m Q rows W G S source target =>
  CodedSorting.CommonScanProgram.passCode q reader
    (CodedSorting.Construction.StreamSplitLayout.gatherPass m Q rows W G S) source target
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.StreamSplitLayout.gatherPass](StreamParentProgram.definitions.md#def-2dfcd3bb769f4642)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonScanProgram.passCode](../../Shared/Memory/ScanProgram.definitions.md#def-a3f8f7609a0933eb)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `List`, `Nat`, `Fin`, `instHMul`

<a id="def-2de8638d376413a2"></a>
## `CodedSorting.Construction.StreamSplitMachine.Slabs`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](StreamParentProgram.lean#L512)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.Construction.StreamSplitMachine.Slabs.mk](StreamParentProgram.definitions.md#def-76d03a46edbf6b1d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-76d03a46edbf6b1d"></a>
## `CodedSorting.Construction.StreamSplitMachine.Slabs.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](StreamParentProgram.lean#L514)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {W n : ℕ} →
    (base : Fin W → ℕ) →
      (address : ℕ → Fin (q.N ^ q.exponent)) →
        (∀ (c : Fin W),
            ∀ k < CodedSorting.PhysicalStreamCursor.blockCount q.block n,
              address (↑c * CodedSorting.PhysicalStreamCursor.blockCount q.block n + k) =
                CodedSorting.CommonColumnSplit.address q (base c) k) →
          (∀ p < W * CodedSorting.PhysicalStreamCursor.blockCount q.block n,
              ∀ j < W * CodedSorting.PhysicalStreamCursor.blockCount q.block n, address p = address j → p = j) →
            CodedSorting.Construction.StreamSplitMachine.Slabs q W n
```

**继续展开**

- [CodedSorting.Construction.StreamSplitMachine.Slabs](StreamParentProgram.definitions.md#def-2de8638d376413a2)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonColumnSplit.address](../Framework/Columns/ColumnOperations.definitions.md#def-72d3a9464453bd7c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `instHMul`

<a id="def-46614c4f7c20a64f"></a>
## `CodedSorting.Construction.StreamSplitMachine.Slabs.address`

读取 `CodedSorting.Construction.StreamSplitMachine.Slabs` 的 `address` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](StreamParentProgram.lean#L516)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {W n : ℕ} → CodedSorting.Construction.StreamSplitMachine.Slabs q W n → ℕ → Fin (q.N ^ q.exponent)
```

**定义**

```lean
fun q W n self => self.2
```

**继续展开**

- [CodedSorting.Construction.StreamSplitMachine.Slabs](StreamParentProgram.definitions.md#def-2de8638d376413a2)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-e1c0bc276acbb398"></a>
## `CodedSorting.Construction.StreamSplitMachine.slotMap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L522)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {W K : ℕ} → ℕ → ℕ → ℕ → (Fin W → Fin K) → ℕ → Fin (q.N ^ q.exponent)
```

**定义**

```lean
fun q {W K} workspace stride live slot k =>
  if h : k / live < W then
    CodedSorting.CommonColumnSplit.address q (workspace + ↑(slot ⟨k / live, h⟩) * stride) (k % live)
  else CodedSorting.CommonColumnSplit.address q 0 0
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonColumnSplit.address](../Framework/Columns/ColumnOperations.definitions.md#def-72d3a9464453bd7c)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `instOfNatNat`, `Fin.val`, `dite`, `instHAdd`, `HMod.hMod`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-7dd58b8187823e96"></a>
## `CodedSorting.Construction.StreamSplitMachine.allocatedSlabs`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L605)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {W K : ℕ} →
    (n workspace stride : ℕ) →
      (slot : Fin W → Fin K) →
        Function.Injective slot →
          CodedSorting.PhysicalStreamCursor.blockCount q.block n ≤ stride →
            workspace + K * stride ≤ q.N ^ q.exponent → CodedSorting.Construction.StreamSplitMachine.Slabs q W n
```

**定义**

```lean
fun q {W K} n workspace stride slot hinj hle hfit =>
  { base := fun c => workspace + ↑(slot c) * stride,
    address :=
      CodedSorting.Construction.StreamSplitMachine.slotMap q workspace stride
        (CodedSorting.PhysicalStreamCursor.blockCount q.block n) slot,
    map_at := ⋯, injective := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.StreamSplitMachine.Slabs](StreamParentProgram.definitions.md#def-2de8638d376413a2)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.StreamSplitMachine.allocatedSlabs._proof_10](StreamParentProgram.definitions.md#def-351a2c26419237ca)
- [CodedSorting.Construction.StreamSplitMachine.slotMap](StreamParentProgram.definitions.md#def-e1c0bc276acbb398)
- [CodedSorting.Construction.StreamSplitMachine.Slabs.mk](StreamParentProgram.definitions.md#def-76d03a46edbf6b1d)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.StreamSplitMachine.allocatedSlabs._proof_9](StreamParentProgram.definitions.md#def-19fb4b5100e68e83)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Function.Injective`, `Fin`, `instHMul`

<a id="def-191e2647e0d0fa34"></a>
## `CodedSorting.Construction.StreamSplitMachine.scatterCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L637)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (m Q rows W G S : ℕ) →
      ℕ →
        ℕ →
          CodedSorting.Construction.StreamSplitMachine.Slabs q W
              (CodedSorting.CommonAddressLayout.Volume (Fin m) rows Q G S) →
            List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader m Q rows W G S source temporary slabs =>
  CodedSorting.Construction.StreamSplitMachine.transposeCode q reader m Q rows W G (S * q.w) source temporary ++
    CodedSorting.CommonStaticSlabSplit.code q reader W (CodedSorting.CommonAddressLayout.Volume (Fin m) rows Q G S)
      temporary slabs.address
```

**继续展开**

- [CodedSorting.Construction.StreamSplitMachine.Slabs](StreamParentProgram.definitions.md#def-2de8638d376413a2)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.StreamSplitMachine.transposeCode](StreamParentProgram.definitions.md#def-7dbb0b09af6bbfe2)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.StreamSplitMachine.Slabs.address](StreamParentProgram.definitions.md#def-46614c4f7c20a64f)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSlabSplit.code](../../Shared/Programs/Static/SlabSplit.definitions.md#def-70924b7f561a7e35)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `Fin`, `HAppend.hAppend`, `instHMul`

<a id="def-73904b67bd0e52df"></a>
## `CodedSorting.Construction.StreamSplitMachine.gatherCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L642)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (m Q rows W G S : ℕ) →
      ℕ →
        ℕ →
          CodedSorting.Construction.StreamSplitMachine.Slabs q W
              (CodedSorting.CommonAddressLayout.Volume (Fin m) rows Q G S) →
            List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader m Q rows W G S source temporary slabs =>
  CodedSorting.CommonStaticSlabJoinMapped.code q reader (CodedSorting.CommonAddressLayout.Volume (Fin m) rows Q G S) W
      temporary slabs.address ++
    CodedSorting.Construction.StreamSplitMachine.inverseCode q reader m Q rows W G (S * q.w) temporary source
```

**继续展开**

- [CodedSorting.Construction.StreamSplitMachine.Slabs](StreamParentProgram.definitions.md#def-2de8638d376413a2)
- [CodedSorting.CommonStaticSlabJoinMapped.code](../../Shared/Programs/Static/SlabJoinMappedMath.definitions.md#def-3e50765d291b2bd7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.StreamSplitMachine.inverseCode](StreamParentProgram.definitions.md#def-497560896f7bd52b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.StreamSplitMachine.Slabs.address](StreamParentProgram.definitions.md#def-46614c4f7c20a64f)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `Fin`, `HAppend.hAppend`, `instHMul`

<a id="def-8ea9c03ba6fdcc48"></a>
## `CodedSorting.Construction.StreamSplitMachine.distributionCharge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L647)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q m Q rows W G S =>
  3 * (2 * W + 6) *
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.CommonAddressLayout.Volume (Fin m) (rows * W) Q G (S * q.w)) +
    6 *
      (W *
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.CommonAddressLayout.Volume (Fin m) rows Q G (S * q.w)))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.fintype`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-5b6d25cf4d2885eb"></a>
## `CodedSorting.Construction.StreamParentProgram.parentCall`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L810)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → CodedSorting.Construction.ExchangeInterface.Call
```

**定义**

```lean
fun m f Pref G S source buffer limit =>
  { fieldWidth := m * f, prefixCount := Pref, gap := G, suffix := S, source := source, buffer := buffer,
    limit := limit }
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.mk](../Bounds/ExchangeInterface.definitions.md#def-88d363c434138873)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-75a80ebc49d33ab7"></a>
## `CodedSorting.Construction.StreamParentProgram.parentProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StreamParentProgram.lean#L819)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (radix m f Pref G S source buffer limit : ℕ) →
    CodedSorting.CommonFinitePermutation.Program q
        (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S) source buffer limit
        (CodedSorting.CommonAddressLayout.longLayout.symm.trans
          (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CommonAddressLayout.longLayout)) →
      CodedSorting.Construction.ExchangeInterface.Program q radix
        (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit)
```

**定义**

```lean
fun q radix m f Pref G S source buffer limit p =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3](StreamParentProgram.definitions.md#def-951268f3101df86e)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.StreamParentProgram.parentProgram._proof_12](StreamParentProgram.definitions.md#def-7734a266257d50b6)
- [CodedSorting.Construction.StreamParentProgram.parentProgram._proof_11](StreamParentProgram.definitions.md#def-80e6c95a50ba408d)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.Construction.StreamParentProgram.parentProgram._proof_13](StreamParentProgram.definitions.md#def-9e0c993be0932c01)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Address.exchangeEquiv](../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)
- [CodedSorting.Construction.StreamParentProgram.parentProgram._proof_15](StreamParentProgram.definitions.md#def-4d28152a39dad316)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.StreamParentProgram.parentCall](StreamParentProgram.definitions.md#def-5b6d25cf4d2885eb)
- [CodedSorting.Construction.StreamParentProgram.parentProgram._proof_14](StreamParentProgram.definitions.md#def-5801c672c2117417)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`Preorder.toLT`, `Equiv.trans`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `Fin.Lt.isWellOrder`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fin.fintype`, `Fin.instLinearOrder`, `HPow.hPow`, `IsWellOrder.toIsWellFounded`, `Nat`, `LT.lt`, `instHPow`, `Equiv.symm`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-80e6c95a50ba408d"></a>
## `CodedSorting.Construction.StreamParentProgram.parentProgram._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S) source buffer limit
      (CodedSorting.CommonAddressLayout.longLayout.symm.trans
        (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CommonAddressLayout.longLayout)))
  (state : CodedSorting.CommonLeafProgram.Machine q)
  (y :
    Fin
      (CodedSorting.Construction.ExchangeInterface.volume radix
        (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit))),
  CodedSorting.CommonPermutationPairs.readBit q
      (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions state).1.disk
      (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit).source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q state.disk
      (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit).source
      ↑((CodedSorting.Construction.ExchangeInterface.permutation radix
            (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit))
          y)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3](StreamParentProgram.definitions.md#def-951268f3101df86e)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Address.exchangeEquiv](../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.StreamParentProgram.parentCall](StreamParentProgram.definitions.md#def-5b6d25cf4d2885eb)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.val`, `Prod.fst`, `Fin.fintype`, `Fin.instLinearOrder`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-7734a266257d50b6"></a>
## `CodedSorting.Construction.StreamParentProgram.parentProgram._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S) source buffer limit
      (CodedSorting.CommonAddressLayout.longLayout.symm.trans
        (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CommonAddressLayout.longLayout)))
  (state : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit).source ∨
      (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit).source +
          CodedSorting.CommonPermutationPairs.count q
            (CodedSorting.Construction.ExchangeInterface.volume radix
              (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit)) ≤
        ↑a →
    ↑a < (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit).buffer ∨
        (CodedSorting.Construction.StreamParentProgram.parentCall m f Pref G S source buffer limit).limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions state).1.disk a = state.disk a
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3](StreamParentProgram.definitions.md#def-951268f3101df86e)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Address.exchangeEquiv](../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.StreamParentProgram.parentCall](StreamParentProgram.definitions.md#def-5b6d25cf4d2885eb)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `Fin.fintype`, `instHAdd`, `Fin.instLinearOrder`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Equiv.symm`, `Fin`, `Eq`

<a id="def-9e0c993be0932c01"></a>
## `CodedSorting.Construction.StreamParentProgram.parentProgram._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S) source buffer limit
      (CodedSorting.CommonAddressLayout.longLayout.symm.trans
        (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CommonAddressLayout.longLayout))),
  ∀ i ∈ p.instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3](StreamParentProgram.definitions.md#def-951268f3101df86e)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Address.exchangeEquiv](../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `Fin.fintype`, `List`, `Fin.instLinearOrder`, `HPow.hPow`, `List.instMembership`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`

<a id="def-5801c672c2117417"></a>
## `CodedSorting.Construction.StreamParentProgram.parentProgram._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S) source buffer limit
      (CodedSorting.CommonAddressLayout.longLayout.symm.trans
        (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CommonAddressLayout.longLayout))),
  CodedSorting.CommonStaticSchedule.cost q p.instructions ≤ p.charge
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3](StreamParentProgram.definitions.md#def-951268f3101df86e)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Address.exchangeEquiv](../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.fintype`, `Fin.instLinearOrder`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`

<a id="def-4d28152a39dad316"></a>
## `CodedSorting.Construction.StreamParentProgram.parentProgram._proof_15`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S) source buffer limit
      (CodedSorting.CommonAddressLayout.longLayout.symm.trans
        (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CommonAddressLayout.longLayout))),
  p.instructions.length ≤ p.charge
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3](StreamParentProgram.definitions.md#def-951268f3101df86e)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Address.exchangeEquiv](../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.fintype`, `Fin.instLinearOrder`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `List.length`

<a id="def-951268f3101df86e"></a>
## `CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ {m : ℕ}, IsWellFounded (Fin m) fun x1 x2 => x1 < x2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.instLinearOrder`, `Nat`, `LT.lt`, `Fin`, `IsWellFounded`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-e32c66e731e7418b"></a>
## `CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S : ℕ) (i j : Fin m)
  (source buffer limit : ℕ)
  (child :
    CodedSorting.Construction.ExchangeInterface.Program q radix
      (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit))
  (state : CodedSorting.CommonLeafProgram.Machine q)
  (y : Fin (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S)),
  CodedSorting.CommonPermutationPairs.readBit q
      (CodedSorting.CommonStaticSchedule.executeRaw q
            (CodedSorting.CommonFinitePermutation.Program.castVolume child ⋯).instructions state).1.disk
      source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q state.disk source
      ↑((CodedSorting.CommonAddressLayout.longLayout.symm.trans
            (Equiv.trans (CodedSorting.SingleCoordinate.shortExchange i j) CodedSorting.CommonAddressLayout.longLayout))
          y)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.StreamSplitLayout.bodyCode._proof_3](StreamParentProgram.definitions.md#def-951268f3101df86e)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SingleCoordinate.shortExchange](../Framework/Fields/BinaryPaddingScan.definitions.md#def-945a2a92a6f3df83)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall](StreamParentProgram.definitions.md#def-dcc489e2f022255b)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.castVolume](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-011d8c0416a63718)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall_volume](StreamParentProgram.definitions.md#def-df1a2ebcd842733d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Equiv.trans`, `Nat.instMonoid`, `finCongr`, `Monoid.toNatPow`, `Fin.val`, `Prod.fst`, `Fin.fintype`, `Fin.instLinearOrder`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-7e3a7f39547133fe"></a>
## `CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S : ℕ) (i j : Fin m)
  (source buffer limit : ℕ)
  (child :
    CodedSorting.Construction.ExchangeInterface.Program q radix
      (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit))
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit).source ∨
      (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit).source +
          CodedSorting.CommonPermutationPairs.count q
            (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (radix ^ f) G S) ≤
        ↑a →
    ↑a < (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit).buffer ∨
        (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit).limit ≤
          ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.CommonFinitePermutation.Program.castVolume child ⋯).instructions s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall](StreamParentProgram.definitions.md#def-dcc489e2f022255b)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonFinitePermutation.Program.castVolume](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-011d8c0416a63718)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall_volume](StreamParentProgram.definitions.md#def-df1a2ebcd842733d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `finCongr`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `Fin.fintype`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Equiv.symm`, `Fin`, `Eq`

<a id="def-7557a6c801d36295"></a>
## `CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S : ℕ) (i j : Fin m)
  (source buffer limit : ℕ)
  (child :
    CodedSorting.Construction.ExchangeInterface.Program q radix
      (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit)),
  ∀ i_1 ∈ (CodedSorting.CommonFinitePermutation.Program.castVolume child ⋯).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i_1
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall](StreamParentProgram.definitions.md#def-dcc489e2f022255b)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.castVolume](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-011d8c0416a63718)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall_volume](StreamParentProgram.definitions.md#def-df1a2ebcd842733d)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `finCongr`, `Membership.mem`, `Monoid.toNatPow`, `Fin.fintype`, `List`, `HPow.hPow`, `List.instMembership`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`

<a id="def-986adcb5737b826a"></a>
## `CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S : ℕ) (i j : Fin m)
  (source buffer limit : ℕ)
  (child :
    CodedSorting.Construction.ExchangeInterface.Program q radix
      (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit)),
  CodedSorting.CommonStaticSchedule.cost q
      (CodedSorting.CommonFinitePermutation.Program.castVolume child ⋯).instructions ≤
    (CodedSorting.CommonFinitePermutation.Program.castVolume child ⋯).charge
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall](StreamParentProgram.definitions.md#def-dcc489e2f022255b)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.castVolume](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-011d8c0416a63718)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall_volume](StreamParentProgram.definitions.md#def-df1a2ebcd842733d)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `finCongr`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`

<a id="def-b53aa6b8d1e57aeb"></a>
## `CodedSorting.Construction.StreamSplitLayout.selectedChildProgram._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (radix m f Pref G S : ℕ) (i j : Fin m)
  (source buffer limit : ℕ)
  (child :
    CodedSorting.Construction.ExchangeInterface.Program q radix
      (CodedSorting.Construction.StreamSplitLayout.selectedCall radix m f Pref G S i j source buffer limit)),
  (CodedSorting.CommonFinitePermutation.Program.castVolume child ⋯).instructions.length ≤
    (CodedSorting.CommonFinitePermutation.Program.castVolume child ⋯).charge
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall](StreamParentProgram.definitions.md#def-dcc489e2f022255b)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.ExchangeInterface.permutation](../Bounds/ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.castVolume](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-011d8c0416a63718)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall_volume](StreamParentProgram.definitions.md#def-df1a2ebcd842733d)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `finCongr`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `List.length`

<a id="def-1c3028c1249d5e5f"></a>
## `CodedSorting.Construction.StreamSplitLayout.transposeTriples._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (rows W L : ℕ) (a : CodedSorting.TriangularStreams.TripleAddress rows W L),
  ((a.2.1, a.1, a.2.2).2.1, (a.2.1, a.1, a.2.2).1, (a.2.1, a.1, a.2.2).2.2) = a
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Eq`, `Prod.snd`

<a id="def-ec0e02c125a43530"></a>
## `CodedSorting.Construction.StreamSplitLayout.transposeTriples._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (rows W L : ℕ) (a : CodedSorting.TriangularStreams.TripleAddress W rows L),
  ((a.2.1, a.1, a.2.2).2.1, (a.2.1, a.1, a.2.2).1, (a.2.1, a.1, a.2.2).2.2) = a
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Eq`, `Prod.snd`

<a id="def-351a2c26419237ca"></a>
## `CodedSorting.Construction.StreamSplitMachine.allocatedSlabs._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {W K : ℕ} (n workspace stride : ℕ) (slot : Fin W → Fin K),
  Function.Injective slot →
    CodedSorting.PhysicalStreamCursor.blockCount q.block n ≤ stride →
      workspace + K * stride ≤ q.N ^ q.exponent →
        ∀ p < W * CodedSorting.PhysicalStreamCursor.blockCount q.block n,
          ∀ k < W * CodedSorting.PhysicalStreamCursor.blockCount q.block n,
            CodedSorting.Construction.StreamSplitMachine.slotMap q workspace stride
                  (CodedSorting.PhysicalStreamCursor.blockCount q.block n) slot p =
                CodedSorting.Construction.StreamSplitMachine.slotMap q workspace stride
                  (CodedSorting.PhysicalStreamCursor.blockCount q.block n) slot k →
              p = k
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.StreamSplitMachine.slotMap](StreamParentProgram.definitions.md#def-e1c0bc276acbb398)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `Function.Injective`, `instLTNat`, `Fin`, `Eq`, `instHMul`

<a id="def-19fb4b5100e68e83"></a>
## `CodedSorting.Construction.StreamSplitMachine.allocatedSlabs._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StreamParentProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {W K : ℕ} (n workspace stride : ℕ) (slot : Fin W → Fin K)
  (c : Fin W),
  ∀ k < CodedSorting.PhysicalStreamCursor.blockCount q.block n,
    CodedSorting.Construction.StreamSplitMachine.slotMap q workspace stride
        (CodedSorting.PhysicalStreamCursor.blockCount q.block n) slot
        (↑c * CodedSorting.PhysicalStreamCursor.blockCount q.block n + k) =
      CodedSorting.CommonColumnSplit.address q (workspace + ↑(slot c) * stride) k
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.StreamSplitMachine.slotMap](StreamParentProgram.definitions.md#def-e1c0bc276acbb398)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonColumnSplit.address](../Framework/Columns/ColumnOperations.definitions.md#def-72d3a9464453bd7c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `instHMul`
