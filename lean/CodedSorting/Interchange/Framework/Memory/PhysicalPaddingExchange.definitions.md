# PhysicalPaddingExchange 的定义

[源码](PhysicalPaddingExchange.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-5ddf64b0d20708fd"></a>
## `CodedSorting.BorrowScan.Orig`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L12)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun O H L G S => CodedSorting.ArbitraryShapes.Original
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](../Recursion/ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)

**基础库名称**

`Nat`, `Fin`

<a id="def-c171eb153972cd02"></a>
## `CodedSorting.BorrowScan.Borrow`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L14)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun O H L G S => CodedSorting.ArbitraryShapes.Borrowed
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Borrowed](../Recursion/ArbitrarySchedule.definitions.md#def-be433f720c8f210a)

**基础库名称**

`Nat`, `Fin`

<a id="def-947bc1534a4ad3ac"></a>
## `CodedSorting.BorrowScan.volume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L17)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun O H L G S => O * (H * (L * G) * (H * (L * S)))
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-dcab73ead65179bc"></a>
## `CodedSorting.BorrowScan.originalGroup`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L19)

**类型**

```lean
(O H L G S : ℕ) →
  CodedSorting.BorrowScan.Orig O H L G S ≃ Fin O × CodedSorting.TriangularStreams.TripleAddress (H * (L * G)) H (L * S)
```

**定义**

```lean
fun O H L G S =>
  {
    toFun := fun a =>
      (a.prefixCoord, CodedSorting.TriangularStreams.tripleEncode (a.high.1, a.high.2, a.gap), a.low.1,
        finProdFinEquiv (a.low.2, a.suffix)),
    invFun := fun x =>
      let hlg := CodedSorting.TriangularStreams.tripleEncode.symm x.2.1;
      let ls := finProdFinEquiv.symm x.2.2.2;
      { prefixCoord := x.1, high := (hlg.1, hlg.2.1), gap := hlg.2.2, low := (x.2.2.1, ls.1), suffix := ls.2 },
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.BorrowScan.originalGroup._proof_2](PhysicalPaddingExchange.definitions.md#def-234f88b8544987eb)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.BorrowScan.originalGroup._proof_1](PhysicalPaddingExchange.definitions.md#def-de574e61c3d44b87)
- [CodedSorting.BorrowScan.Orig](PhysicalPaddingExchange.definitions.md#def-5ddf64b0d20708fd)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv.mk`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-ad2afe17ebf3eb2b"></a>
## `CodedSorting.BorrowScan.borrowedGroup`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L35)

**类型**

```lean
(O H L G S : ℕ) →
  CodedSorting.BorrowScan.Borrow O H L G S ≃
    Fin O × CodedSorting.TriangularStreams.TripleAddress H (H * (L * G)) (L * S)
```

**定义**

```lean
fun O H L G S =>
  {
    toFun := fun a =>
      (a.prefixCoord.1, a.prefixCoord.2.1,
        CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord.2.2, a.high, a.gap),
        finProdFinEquiv (a.low, a.suffix)),
    invFun := fun x =>
      let hlg := CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1;
      let ls := finProdFinEquiv.symm x.2.2.2;
      { prefixCoord := (x.1, x.2.1, hlg.1), high := hlg.2.1, gap := hlg.2.2, low := ls.1, suffix := ls.2 },
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.BorrowScan.Borrow](PhysicalPaddingExchange.definitions.md#def-c171eb153972cd02)
- [CodedSorting.BorrowScan.borrowedGroup._proof_3](PhysicalPaddingExchange.definitions.md#def-b60511fe0c96417c)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)
- [CodedSorting.BorrowScan.borrowedGroup._proof_4](PhysicalPaddingExchange.definitions.md#def-6f7a90505982bdd7)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv.mk`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-fc39eedea80f3e3e"></a>
## `CodedSorting.BorrowScan.fourCodec`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L50)

**类型**

```lean
(O P H S : ℕ) → Fin O × CodedSorting.TriangularStreams.TripleAddress P H S ≃ Fin (O * (P * (H * S)))
```

**定义**

```lean
fun O P H S => ((Equiv.refl (Fin O)).prodCongr CodedSorting.TriangularStreams.tripleEncode).trans finProdFinEquiv
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Equiv`, `instMulNat`, `Nat`, `finProdFinEquiv`, `Prod`, `Equiv.prodCongr`, `Fin`, `Equiv.refl`, `instHMul`

<a id="def-056ea8ef9896a898"></a>
## `CodedSorting.BorrowScan.originalCodec`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L53)

**类型**

```lean
(O H L G S : ℕ) → CodedSorting.BorrowScan.Orig O H L G S ≃ Fin (CodedSorting.BorrowScan.volume O H L G S)
```

**定义**

```lean
fun O H L G S =>
  (CodedSorting.BorrowScan.originalGroup O H L G S).trans (CodedSorting.BorrowScan.fourCodec O (H * (L * G)) H (L * S))
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.BorrowScan.fourCodec](PhysicalPaddingExchange.definitions.md#def-fc39eedea80f3e3e)
- [CodedSorting.BorrowScan.Orig](PhysicalPaddingExchange.definitions.md#def-5ddf64b0d20708fd)
- [CodedSorting.BorrowScan.originalGroup](PhysicalPaddingExchange.definitions.md#def-dcab73ead65179bc)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Equiv`, `instMulNat`, `Nat`, `Prod`, `Fin`, `instHMul`

<a id="def-4e071e47cd293dcd"></a>
## `CodedSorting.BorrowScan.borrowedCodec`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L56)

**类型**

```lean
(O H L G S : ℕ) → CodedSorting.BorrowScan.Borrow O H L G S ≃ Fin (CodedSorting.BorrowScan.volume O H L G S)
```

**定义**

```lean
fun O H L G S =>
  (CodedSorting.BorrowScan.borrowedGroup O H L G S).trans
    ((CodedSorting.BorrowScan.fourCodec O H (H * (L * G)) (L * S)).trans (finCongr ⋯))
```

**继续展开**

- [CodedSorting.BorrowScan.borrowedCodec._proof_5](PhysicalPaddingExchange.definitions.md#def-cd4d33737843e8a2)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.BorrowScan.fourCodec](PhysicalPaddingExchange.definitions.md#def-fc39eedea80f3e3e)
- [CodedSorting.BorrowScan.Borrow](PhysicalPaddingExchange.definitions.md#def-c171eb153972cd02)
- [CodedSorting.BorrowScan.borrowedGroup](PhysicalPaddingExchange.definitions.md#def-ad2afe17ebf3eb2b)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `finCongr`, `Equiv`, `instMulNat`, `Nat`, `Prod`, `Fin`, `instHMul`

<a id="def-5b07642e3db0adc2"></a>
## `CodedSorting.BorrowScan.borrowProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L72)

**类型**

```lean
(O q ρ L G S : ℕ) → List (CodedSorting.ScanProgram.Pass (CodedSorting.BorrowScan.volume O (q ^ ρ) L G S))
```

**定义**

```lean
fun O q ρ L G S => CodedSorting.BlockDigitMove.program O (q ^ ρ * (L * G)) q (L * S) ρ
```

**继续展开**

- [CodedSorting.BlockDigitMove.program](../../../Shared/Memory/BlockDigitMove.definitions.md#def-750c71c1cda4fe46)
- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `instHMul`

<a id="def-342db2eba4fb8963"></a>
## `CodedSorting.BorrowScan.finishProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L75)

**类型**

```lean
(O q ρ L G S : ℕ) → List (CodedSorting.ScanProgram.Pass (CodedSorting.BorrowScan.volume O (q ^ ρ) L G S))
```

**定义**

```lean
fun O q ρ L G S =>
  CodedSorting.BlockDigitMove.castProgram ⋯
    (CodedSorting.BlockDigitMove.inverseProgram (CodedSorting.BlockDigitMove.program (O * q ^ ρ) (L * G) q (L * S) ρ))
```

**继续展开**

- [CodedSorting.BlockDigitMove.program](../../../Shared/Memory/BlockDigitMove.definitions.md#def-750c71c1cda4fe46)
- [CodedSorting.BlockDigitMove.castProgram](../../../Shared/Memory/BlockDigitMove.definitions.md#def-a3f79c8b1137cbb3)
- [CodedSorting.BlockDigitMove.inverseProgram](../../../Shared/Memory/BlockDigitMove.definitions.md#def-1c938335a9d18c4c)
- [CodedSorting.BorrowScan.finishProgram._proof_6](PhysicalPaddingExchange.definitions.md#def-0e23fb80d8971c96)
- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `instHMul`

<a id="def-18059f387df670ea"></a>
## `CodedSorting.BorrowScan.borrowPermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L120)

**类型**

```lean
(O H L G S : ℕ) → Equiv.Perm (Fin (CodedSorting.BorrowScan.volume O H L G S))
```

**定义**

```lean
fun O H L G S =>
  (CodedSorting.BorrowScan.originalCodec O H L G S).symm.trans
    (CodedSorting.ArbitraryShapes.borrowEquiv.trans (CodedSorting.BorrowScan.borrowedCodec O H L G S))
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](../Recursion/ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.BorrowScan.originalCodec](PhysicalPaddingExchange.definitions.md#def-056ea8ef9896a898)
- [CodedSorting.ArbitraryShapes.borrowEquiv](../Recursion/ArbitrarySchedule.definitions.md#def-4c1609a8168de062)
- [CodedSorting.BorrowScan.borrowedCodec](PhysicalPaddingExchange.definitions.md#def-4e071e47cd293dcd)
- [CodedSorting.ArbitraryShapes.Borrowed](../Recursion/ArbitrarySchedule.definitions.md#def-be433f720c8f210a)
- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.BorrowScan.Orig](PhysicalPaddingExchange.definitions.md#def-5ddf64b0d20708fd)

**基础库名称**

`Equiv.trans`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`

<a id="def-b4db3b622c021400"></a>
## `CodedSorting.BorrowScan.finishPermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalPaddingExchange.lean#L123)

**类型**

```lean
(O H L G S : ℕ) → Equiv.Perm (Fin (CodedSorting.BorrowScan.volume O H L G S))
```

**定义**

```lean
fun O H L G S =>
  (CodedSorting.BorrowScan.borrowedCodec O H L G S).symm.trans
    (CodedSorting.ArbitraryShapes.finishEquiv.trans (CodedSorting.BorrowScan.originalCodec O H L G S))
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](../Recursion/ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.BorrowScan.originalCodec](PhysicalPaddingExchange.definitions.md#def-056ea8ef9896a898)
- [CodedSorting.ArbitraryShapes.finishEquiv](../Recursion/ArbitrarySchedule.definitions.md#def-55b9cc97d955c742)
- [CodedSorting.BorrowScan.borrowedCodec](PhysicalPaddingExchange.definitions.md#def-4e071e47cd293dcd)
- [CodedSorting.ArbitraryShapes.Borrowed](../Recursion/ArbitrarySchedule.definitions.md#def-be433f720c8f210a)
- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.BorrowScan.Borrow](PhysicalPaddingExchange.definitions.md#def-c171eb153972cd02)

**基础库名称**

`Equiv.trans`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`

<a id="def-fd27de74d690c2aa"></a>
## `CodedSorting.PhysicalBorrowLayout.original_volume`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalPaddingExchange.lean#L598)

**类型**

```lean
∀ (O H L G S : ℕ), CodedSorting.BinaryPadding.Volume O (H * L) G S = CodedSorting.BorrowScan.volume O H L G S
```

**继续展开**

- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`

<a id="def-c92516d3f96291cc"></a>
## `CodedSorting.PhysicalBorrowLayout.borrowed_volume`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalPaddingExchange.lean#L642)

**类型**

```lean
∀ (O H L G S : ℕ), CodedSorting.BinaryPadding.Volume (O * (H * H)) L G S = CodedSorting.BorrowScan.volume O H L G S
```

**继续展开**

- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`

<a id="def-cd4d33737843e8a2"></a>
## `CodedSorting.BorrowScan.borrowedCodec._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalPaddingExchange.lean)

**类型**

```lean
∀ (O H L G S : ℕ), O * (H * (H * (L * G) * (L * S))) = CodedSorting.BorrowScan.volume O H L G S
```

**继续展开**

- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`

<a id="def-b60511fe0c96417c"></a>
## `CodedSorting.BorrowScan.borrowedGroup._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalPaddingExchange.lean)

**类型**

```lean
∀ (O H L G S : ℕ) (a : CodedSorting.BorrowScan.Borrow O H L G S),
  {
      prefixCoord :=
        ((a.prefixCoord.1, a.prefixCoord.2.1,
              CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord.2.2, a.high, a.gap),
              finProdFinEquiv (a.low, a.suffix)).1,
          (a.prefixCoord.1, a.prefixCoord.2.1,
                CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord.2.2, a.high, a.gap),
                finProdFinEquiv (a.low, a.suffix)).2.1,
          (CodedSorting.TriangularStreams.tripleEncode.symm
              (a.prefixCoord.1, a.prefixCoord.2.1,
                      CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord.2.2, a.high, a.gap),
                      finProdFinEquiv (a.low, a.suffix)).2.2.1).1),
      high :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (a.prefixCoord.1, a.prefixCoord.2.1,
                      CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord.2.2, a.high, a.gap),
                      finProdFinEquiv (a.low, a.suffix)).2.2.1).2.1,
      gap :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (a.prefixCoord.1, a.prefixCoord.2.1,
                      CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord.2.2, a.high, a.gap),
                      finProdFinEquiv (a.low, a.suffix)).2.2.1).2.2,
      low :=
        (finProdFinEquiv.symm
            (a.prefixCoord.1, a.prefixCoord.2.1,
                    CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord.2.2, a.high, a.gap),
                    finProdFinEquiv (a.low, a.suffix)).2.2.2).1,
      suffix :=
        (finProdFinEquiv.symm
            (a.prefixCoord.1, a.prefixCoord.2.1,
                    CodedSorting.TriangularStreams.tripleEncode (a.prefixCoord.2.2, a.high, a.gap),
                    finProdFinEquiv (a.low, a.suffix)).2.2.2).2 } =
    a
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.BorrowScan.Borrow](PhysicalPaddingExchange.definitions.md#def-c171eb153972cd02)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-6f7a90505982bdd7"></a>
## `CodedSorting.BorrowScan.borrowedGroup._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalPaddingExchange.lean)

**类型**

```lean
∀ (O H L G S : ℕ) (x : Fin O × CodedSorting.TriangularStreams.TripleAddress H (H * (L * G)) (L * S)),
  ({ prefixCoord := (x.1, x.2.1, (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).1),
            high := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.1,
            gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.2,
            low := (finProdFinEquiv.symm x.2.2.2).1, suffix := (finProdFinEquiv.symm x.2.2.2).2 }.prefixCoord.1,
      { prefixCoord := (x.1, x.2.1, (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).1),
              high := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.1,
              gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.2,
              low := (finProdFinEquiv.symm x.2.2.2).1, suffix := (finProdFinEquiv.symm x.2.2.2).2 }.prefixCoord.2.1,
      CodedSorting.TriangularStreams.tripleEncode
        ({ prefixCoord := (x.1, x.2.1, (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).1),
                  high := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.1,
                  gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.2,
                  low := (finProdFinEquiv.symm x.2.2.2).1, suffix := (finProdFinEquiv.symm x.2.2.2).2 }.prefixCoord.2.2,
          { prefixCoord := (x.1, x.2.1, (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).1),
              high := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.1,
              gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.2,
              low := (finProdFinEquiv.symm x.2.2.2).1, suffix := (finProdFinEquiv.symm x.2.2.2).2 }.high,
          { prefixCoord := (x.1, x.2.1, (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).1),
              high := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.1,
              gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.2,
              low := (finProdFinEquiv.symm x.2.2.2).1, suffix := (finProdFinEquiv.symm x.2.2.2).2 }.gap),
      finProdFinEquiv
        ({ prefixCoord := (x.1, x.2.1, (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).1),
              high := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.1,
              gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.2,
              low := (finProdFinEquiv.symm x.2.2.2).1, suffix := (finProdFinEquiv.symm x.2.2.2).2 }.low,
          { prefixCoord := (x.1, x.2.1, (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).1),
              high := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.1,
              gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.2.1).2.2,
              low := (finProdFinEquiv.symm x.2.2.2).1, suffix := (finProdFinEquiv.symm x.2.2.2).2 }.suffix)) =
    x
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-0e23fb80d8971c96"></a>
## `CodedSorting.BorrowScan.finishProgram._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalPaddingExchange.lean)

**类型**

```lean
∀ (O q ρ L G S : ℕ), O * q ^ ρ * (L * G * (q ^ ρ * (L * S))) = CodedSorting.BorrowScan.volume O (q ^ ρ) L G S
```

**继续展开**

- [CodedSorting.BorrowScan.volume](PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `HPow.hPow`, `Nat`, `instHPow`, `Eq`, `instHMul`

<a id="def-de574e61c3d44b87"></a>
## `CodedSorting.BorrowScan.originalGroup._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalPaddingExchange.lean)

**类型**

```lean
∀ (O H L G S : ℕ) (a : CodedSorting.BorrowScan.Orig O H L G S),
  {
      prefixCoord :=
        (a.prefixCoord, CodedSorting.TriangularStreams.tripleEncode (a.high.1, a.high.2, a.gap), a.low.1,
            finProdFinEquiv (a.low.2, a.suffix)).1,
      high :=
        ((CodedSorting.TriangularStreams.tripleEncode.symm
              (a.prefixCoord, CodedSorting.TriangularStreams.tripleEncode (a.high.1, a.high.2, a.gap), a.low.1,
                    finProdFinEquiv (a.low.2, a.suffix)).2.1).1,
          (CodedSorting.TriangularStreams.tripleEncode.symm
                (a.prefixCoord, CodedSorting.TriangularStreams.tripleEncode (a.high.1, a.high.2, a.gap), a.low.1,
                      finProdFinEquiv (a.low.2, a.suffix)).2.1).2.1),
      gap :=
        (CodedSorting.TriangularStreams.tripleEncode.symm
              (a.prefixCoord, CodedSorting.TriangularStreams.tripleEncode (a.high.1, a.high.2, a.gap), a.low.1,
                    finProdFinEquiv (a.low.2, a.suffix)).2.1).2.2,
      low :=
        ((a.prefixCoord, CodedSorting.TriangularStreams.tripleEncode (a.high.1, a.high.2, a.gap), a.low.1,
                  finProdFinEquiv (a.low.2, a.suffix)).2.2.1,
          (finProdFinEquiv.symm
              (a.prefixCoord, CodedSorting.TriangularStreams.tripleEncode (a.high.1, a.high.2, a.gap), a.low.1,
                      finProdFinEquiv (a.low.2, a.suffix)).2.2.2).1),
      suffix :=
        (finProdFinEquiv.symm
            (a.prefixCoord, CodedSorting.TriangularStreams.tripleEncode (a.high.1, a.high.2, a.gap), a.low.1,
                    finProdFinEquiv (a.low.2, a.suffix)).2.2.2).2 } =
    a
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.BorrowScan.Orig](PhysicalPaddingExchange.definitions.md#def-5ddf64b0d20708fd)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-234f88b8544987eb"></a>
## `CodedSorting.BorrowScan.originalGroup._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalPaddingExchange.lean)

**类型**

```lean
∀ (O H L G S : ℕ) (x : Fin O × CodedSorting.TriangularStreams.TripleAddress (H * (L * G)) H (L * S)),
  ({ prefixCoord := x.1,
          high :=
            ((CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).1,
              (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.1),
          gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.2,
          low := (x.2.2.1, (finProdFinEquiv.symm x.2.2.2).1), suffix := (finProdFinEquiv.symm x.2.2.2).2 }.prefixCoord,
      CodedSorting.TriangularStreams.tripleEncode
        ({ prefixCoord := x.1,
                high :=
                  ((CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).1,
                    (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.1),
                gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.2,
                low := (x.2.2.1, (finProdFinEquiv.symm x.2.2.2).1), suffix := (finProdFinEquiv.symm x.2.2.2).2 }.high.1,
          { prefixCoord := x.1,
                high :=
                  ((CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).1,
                    (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.1),
                gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.2,
                low := (x.2.2.1, (finProdFinEquiv.symm x.2.2.2).1), suffix := (finProdFinEquiv.symm x.2.2.2).2 }.high.2,
          { prefixCoord := x.1,
              high :=
                ((CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).1,
                  (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.1),
              gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.2,
              low := (x.2.2.1, (finProdFinEquiv.symm x.2.2.2).1), suffix := (finProdFinEquiv.symm x.2.2.2).2 }.gap),
      { prefixCoord := x.1,
            high :=
              ((CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).1,
                (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.1),
            gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.2,
            low := (x.2.2.1, (finProdFinEquiv.symm x.2.2.2).1), suffix := (finProdFinEquiv.symm x.2.2.2).2 }.low.1,
      finProdFinEquiv
        ({ prefixCoord := x.1,
                high :=
                  ((CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).1,
                    (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.1),
                gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.2,
                low := (x.2.2.1, (finProdFinEquiv.symm x.2.2.2).1), suffix := (finProdFinEquiv.symm x.2.2.2).2 }.low.2,
          { prefixCoord := x.1,
              high :=
                ((CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).1,
                  (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.1),
              gap := (CodedSorting.TriangularStreams.tripleEncode.symm x.2.1).2.2,
              low := (x.2.2.1, (finProdFinEquiv.symm x.2.2.2).1),
              suffix := (finProdFinEquiv.symm x.2.2.2).2 }.suffix)) =
    x
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.TriangularStreams.TripleAddress](../../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.TriangularStreams.tripleEncode](../../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`
