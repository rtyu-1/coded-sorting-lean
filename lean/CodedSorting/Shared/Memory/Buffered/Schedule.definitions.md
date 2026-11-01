# Schedule 的定义

[源码](Schedule.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-ab652a1f6edc68d1"></a>
## `CodedSorting.CommonBufferedBaseLayout.Volume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Schedule.lean#L17)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
CodedSorting.BaseExchangeProgram.Volume
```

**继续展开**

- [CodedSorting.BaseExchangeProgram.Volume](../../../Interchange/Framework/Memory/BaseExchangeProgram.definitions.md#def-1a2dfaef9959ff0a)

**基础库名称**

`Nat`

<a id="def-94a32c197b95bcbc"></a>
## `CodedSorting.CommonBufferedBaseLayout.bucketSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Schedule.lean#L18)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun P G S => P * (G * S)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-582b01189486d6fe"></a>
## `CodedSorting.CommonBufferedBaseLayout.addressEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Schedule.lean#L20)

**类型**

```lean
(P Q G S : ℕ) →
  CodedSorting.Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin S) ≃
    Fin (Q * Q) × Fin (CodedSorting.CommonBufferedBaseLayout.bucketSize P G S)
```

**定义**

```lean
fun P Q G S =>
  {
    toFun := fun a =>
      (finProdFinEquiv (a.high, a.low), CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.gap, a.suffix)),
    invFun := fun x =>
      let hd := finProdFinEquiv.symm x.1;
      let pgs := CodedSorting.TriangularStreams.tripleEncode.symm x.2;
      { prefixCoord := pgs.1, high := hd.1, gap := pgs.2.1, low := hd.2, suffix := pgs.2.2 },
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Address.FullAddress](../Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.FullAddress.low](../Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.CommonBufferedBaseLayout.addressEquiv._proof_1](Schedule.definitions.md#def-508dec0b06766509)
- [CodedSorting.Address.FullAddress.mk](../Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](Schedule.definitions.md#def-94a32c197b95bcbc)
- [CodedSorting.Address.FullAddress.gap](../Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.CommonBufferedBaseLayout.addressEquiv._proof_2](Schedule.definitions.md#def-70b7b6c3d69357a3)
- [CodedSorting.Address.FullAddress.suffix](../Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv.mk`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-d2a7034dd8a02f65"></a>
## `CodedSorting.CommonBufferedBaseLayout.indexEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Schedule.lean#L33)

**类型**

```lean
(P Q G S : ℕ) →
  Fin (CodedSorting.CommonBufferedBaseLayout.Volume P Q G S) ≃
    Fin (Q * Q) × Fin (CodedSorting.CommonBufferedBaseLayout.bucketSize P G S)
```

**定义**

```lean
fun P Q G S =>
  CodedSorting.CoordinateScans.lowLayout.symm.trans (CodedSorting.CommonBufferedBaseLayout.addressEquiv P Q G S)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.CommonBufferedBaseLayout.addressEquiv](Schedule.definitions.md#def-582b01189486d6fe)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](Schedule.definitions.md#def-94a32c197b95bcbc)
- [CodedSorting.CoordinateScans.lowLayout](../../../Interchange/Framework/Fields/BinaryPaddingScan.definitions.md#def-27613a35b25c74be)
- [CodedSorting.CommonBufferedBaseLayout.Volume](Schedule.definitions.md#def-ab652a1f6edc68d1)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Equiv`, `instMulNat`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `instHMul`

<a id="def-274883a4b214c632"></a>
## `CodedSorting.CommonBufferedBaseLayout.outputIndexEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Schedule.lean#L142)

**类型**

```lean
(P Q G S : ℕ) →
  Fin (CodedSorting.CommonBufferedBaseLayout.Volume P Q G S) ≃
    Fin (Q * Q) × Fin (CodedSorting.CommonBufferedBaseLayout.bucketSize P G S)
```

**定义**

```lean
fun P Q G S =>
  (Equiv.symm CodedSorting.BaseExchangeProgram.permutation).trans
    (CodedSorting.CommonBufferedBaseLayout.indexEquiv P Q G S)
```

**继续展开**

- [CodedSorting.BaseExchangeProgram.permutation](../../../Interchange/Framework/Memory/BaseExchangeProgram.definitions.md#def-c68cf3aa9259828f)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](Schedule.definitions.md#def-94a32c197b95bcbc)
- [CodedSorting.BaseExchangeProgram.Volume](../../../Interchange/Framework/Memory/BaseExchangeProgram.definitions.md#def-1a2dfaef9959ff0a)
- [CodedSorting.CommonBufferedBaseLayout.indexEquiv](Schedule.definitions.md#def-d2a7034dd8a02f65)
- [CodedSorting.CommonBufferedBaseLayout.Volume](Schedule.definitions.md#def-ab652a1f6edc68d1)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Equiv`, `instMulNat`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `instHMul`

<a id="def-508dec0b06766509"></a>
## `CodedSorting.CommonBufferedBaseLayout.addressEquiv._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Schedule.lean)

**类型**

```lean
∀ (P Q G S : ℕ) (a : CodedSorting.Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)),
  {
      prefixCoord :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
            (finProdFinEquiv (a.high, a.low),
                CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.gap, a.suffix)).2).1,
      high :=
        (finProdFinEquiv.symm
            (finProdFinEquiv (a.high, a.low),
                CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.gap, a.suffix)).1).1,
      gap :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (finProdFinEquiv (a.high, a.low),
                  CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.gap, a.suffix)).2).2.1,
      low :=
        (finProdFinEquiv.symm
            (finProdFinEquiv (a.high, a.low),
                CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.gap, a.suffix)).1).2,
      suffix :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (finProdFinEquiv (a.high, a.low),
                  CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord, a.gap, a.suffix)).2).2.2 } =
    a
```

**继续展开**

- [CodedSorting.Address.FullAddress](../Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.FullAddress.low](../Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](Schedule.definitions.md#def-94a32c197b95bcbc)
- [CodedSorting.Address.FullAddress.gap](../Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-70b7b6c3d69357a3"></a>
## `CodedSorting.CommonBufferedBaseLayout.addressEquiv._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Schedule.lean)

**类型**

```lean
∀ (P Q G S : ℕ) (x : Fin (Q * Q) × Fin (CodedSorting.CommonBufferedBaseLayout.bucketSize P G S)),
  (finProdFinEquiv ((finProdFinEquiv.symm x.1).1, (finProdFinEquiv.symm x.1).2),
      CodedSorting.TriangularStreams.tripleEncode
        ((CodedSorting.TriangularStreams.tripleEncode.symm x.2).1,
          (CodedSorting.TriangularStreams.tripleEncode.symm x.2).2.1,
          (CodedSorting.TriangularStreams.tripleEncode.symm x.2).2.2)) =
    x
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.CommonBufferedBaseLayout.bucketSize](Schedule.definitions.md#def-94a32c197b95bcbc)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`
