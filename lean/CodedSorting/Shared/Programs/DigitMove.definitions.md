# DigitMove 的定义

[源码](DigitMove.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-926d0f0a0b42a610"></a>
## `CodedSorting.DigitMove.swapLeading`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DigitMove.lean#L12)

**类型**

```lean
(P q S : ℕ) → CodedSorting.TriangularStreams.TripleAddress P q S ≃ CodedSorting.TriangularStreams.TripleAddress q P S
```

**定义**

```lean
fun P q S =>
  { toFun := fun x => (x.2.1, x.1, x.2.2), invFun := fun x => (x.2.1, x.1, x.2.2), left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.DigitMove.swapLeading._proof_2](DigitMove.definitions.md#def-3543c2385993759a)
- [CodedSorting.DigitMove.swapLeading._proof_1](DigitMove.definitions.md#def-9c2c550fbad57733)

**基础库名称**

`Equiv.mk`, `Equiv`, `Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Prod.snd`

<a id="def-ea03d4a818f18346"></a>
## `CodedSorting.DigitMove.toFront`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DigitMove.lean#L18)

**类型**

```lean
(P q S : ℕ) → Equiv.Perm (Fin (P * (q * S)))
```

**定义**

```lean
fun P q S =>
  CodedSorting.TriangularStreams.tripleEncode.symm.trans
    ((CodedSorting.DigitMove.swapLeading P q S).trans (CodedSorting.TriangularStreams.tripleEncode.trans (finCongr ⋯)))
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.tripleEncode](../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)
- [CodedSorting.DigitMove.swapLeading](DigitMove.definitions.md#def-926d0f0a0b42a610)
- [CodedSorting.DigitMove.toFront._proof_3](DigitMove.definitions.md#def-9a6bd7ce5bab490e)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `finCongr`, `instMulNat`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `instHMul`

<a id="def-984e35d17e9ce4ac"></a>
## `CodedSorting.DigitMove.digitKey`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DigitMove.lean#L22)

**类型**

```lean
(P q S : ℕ) → Fin (P * (q * S)) → Fin q
```

**定义**

```lean
fun P q S x => (CodedSorting.TriangularStreams.tripleEncode.symm x).2.1
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.tripleEncode](../../Circuit/Framework/TriangularStreams.definitions.md#def-d528c449fb733c38)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Prod.fst`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-9388cc212aa85359"></a>
## `CodedSorting.DigitMove.insidePrefix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DigitMove.lean#L79)

**类型**

```lean
(Outer P q S : ℕ) → Equiv.Perm (Fin (Outer * (P * (q * S))))
```

**定义**

```lean
fun Outer P q S =>
  finProdFinEquiv.symm.trans
    (((Equiv.refl (Fin Outer)).prodCongr (CodedSorting.DigitMove.toFront P q S)).trans finProdFinEquiv)
```

**继续展开**

- [CodedSorting.DigitMove.toFront](DigitMove.definitions.md#def-ea03d4a818f18346)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `instMulNat`, `Equiv.Perm`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Equiv.prodCongr`, `Fin`, `Equiv.refl`, `instHMul`

<a id="def-48aa15b586e4acde"></a>
## `CodedSorting.DigitMove.insideKey`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](DigitMove.lean#L85)

**类型**

```lean
(Outer P q S : ℕ) → Fin (Outer * (P * (q * S))) → Fin q
```

**定义**

```lean
fun Outer P q S x => CodedSorting.DigitMove.digitKey P q S (finProdFinEquiv.symm x).2
```

**继续展开**

- [CodedSorting.DigitMove.digitKey](DigitMove.definitions.md#def-984e35d17e9ce4ac)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-29d68fd962bf0a88"></a>
## `CodedSorting.DigitMove.insidePrefix_increasing`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](DigitMove.lean#L94)

**类型**

```lean
∀ (Outer P q S : ℕ) (x y : Fin (Outer * (P * (q * S)))),
  x < y →
    CodedSorting.DigitMove.insideKey Outer P q S x = CodedSorting.DigitMove.insideKey Outer P q S y →
      (CodedSorting.DigitMove.insidePrefix Outer P q S) x < (CodedSorting.DigitMove.insidePrefix Outer P q S) y
```

**继续展开**

- [CodedSorting.DigitMove.insidePrefix](DigitMove.definitions.md#def-9388cc212aa85359)
- [CodedSorting.DigitMove.insideKey](DigitMove.definitions.md#def-48aa15b586e4acde)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-9c2c550fbad57733"></a>
## `CodedSorting.DigitMove.swapLeading._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](DigitMove.lean)

**类型**

```lean
∀ (P q S : ℕ) (x : CodedSorting.TriangularStreams.TripleAddress P q S),
  ((x.2.1, x.1, x.2.2).2.1, (x.2.1, x.1, x.2.2).1, (x.2.1, x.1, x.2.2).2.2) =
    ((x.2.1, x.1, x.2.2).2.1, (x.2.1, x.1, x.2.2).1, (x.2.1, x.1, x.2.2).2.2)
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Eq`, `Prod.snd`

<a id="def-3543c2385993759a"></a>
## `CodedSorting.DigitMove.swapLeading._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](DigitMove.lean)

**类型**

```lean
∀ (P q S : ℕ) (x : CodedSorting.TriangularStreams.TripleAddress q P S),
  ((x.2.1, x.1, x.2.2).2.1, (x.2.1, x.1, x.2.2).1, (x.2.1, x.1, x.2.2).2.2) =
    ((x.2.1, x.1, x.2.2).2.1, (x.2.1, x.1, x.2.2).1, (x.2.1, x.1, x.2.2).2.2)
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](../../Circuit/Framework/TriangularStreams.definitions.md#def-11a69ce135db048a)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Eq`, `Prod.snd`

<a id="def-9a6bd7ce5bab490e"></a>
## `CodedSorting.DigitMove.toFront._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](DigitMove.lean)

**类型**

```lean
∀ (P q S : ℕ), q * (P * S) = P * (q * S)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`
