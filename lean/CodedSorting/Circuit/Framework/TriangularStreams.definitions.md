# TriangularStreams 的定义

[源码](TriangularStreams.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-11a69ce135db048a"></a>
## `CodedSorting.TriangularStreams.TripleAddress`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L107)

**类型**

```lean
ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun P Q S => Fin P × Fin Q × Fin S
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`, `Prod`, `Fin`

<a id="def-d528c449fb733c38"></a>
## `CodedSorting.TriangularStreams.tripleEncode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L109)

**类型**

```lean
{P Q S : ℕ} → CodedSorting.TriangularStreams.TripleAddress P Q S ≃ Fin (P * (Q * S))
```

**定义**

```lean
fun {P Q S} => ((Equiv.refl (Fin P)).prodCongr finProdFinEquiv).trans finProdFinEquiv
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](TriangularStreams.definitions.md#def-11a69ce135db048a)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Equiv`, `instMulNat`, `Nat`, `finProdFinEquiv`, `Prod`, `Equiv.prodCongr`, `Fin`, `Equiv.refl`, `instHMul`

<a id="def-906fc1953048b868"></a>
## `CodedSorting.TriangularStreams.fieldEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L150)

**类型**

```lean
{P Q S : ℕ} → (Fin P → Equiv.Perm (Fin Q)) → Equiv.Perm (CodedSorting.TriangularStreams.TripleAddress P Q S)
```

**定义**

```lean
fun {P Q S} e =>
  { toFun := fun x => (x.1, (e x.1) x.2.1, x.2.2), invFun := fun x => (x.1, (Equiv.symm (e x.1)) x.2.1, x.2.2),
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.TriangularStreams.fieldEquiv._proof_6](TriangularStreams.definitions.md#def-b0498e8f33693919)
- [CodedSorting.TriangularStreams.TripleAddress](TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.fieldEquiv._proof_5](TriangularStreams.definitions.md#def-d64da95ddb6a100e)

**基础库名称**

`Equiv.instFunLike`, `Equiv.mk`, `Equiv`, `Prod.mk`, `Prod.fst`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`

<a id="def-512e9a6065bbe891"></a>
## `CodedSorting.TriangularStreams.globalFieldEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L156)

**类型**

```lean
{P Q S : ℕ} → (Fin P → Equiv.Perm (Fin Q)) → Equiv.Perm (Fin (P * (Q * S)))
```

**定义**

```lean
fun {P Q S} e =>
  CodedSorting.TriangularStreams.tripleEncode.symm.trans
    (Equiv.trans (CodedSorting.TriangularStreams.fieldEquiv e) CodedSorting.TriangularStreams.tripleEncode)
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.fieldEquiv](TriangularStreams.definitions.md#def-906fc1953048b868)
- [CodedSorting.TriangularStreams.tripleEncode](TriangularStreams.definitions.md#def-d528c449fb733c38)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `instMulNat`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `instHMul`

<a id="def-f272f59e3f07df97"></a>
## `CodedSorting.TriangularStreams.globalKey`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L160)

**类型**

```lean
{P Q S K : ℕ} → (Fin P → Fin Q → Fin K) → Fin (P * (Q * S)) → Fin K
```

**定义**

```lean
fun {P Q S K} key x =>
  key (CodedSorting.TriangularStreams.tripleEncode.symm x).1 (CodedSorting.TriangularStreams.tripleEncode.symm x).2.1
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](TriangularStreams.definitions.md#def-11a69ce135db048a)
- [CodedSorting.TriangularStreams.tripleEncode](TriangularStreams.definitions.md#def-d528c449fb733c38)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Prod.fst`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-fef164089f463635"></a>
## `CodedSorting.TriangularStreams.global_increasing_streams`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularStreams.lean#L172)

**类型**

```lean
∀ {P Q S K : ℕ} (e : Fin P → Equiv.Perm (Fin Q)) (key : Fin P → Fin Q → Fin K),
  (∀ (p : Fin P) (x y : Fin Q), x < y → key p x = key p y → (e p) x < (e p) y) →
    ∀ (x y : Fin (P * (Q * S))),
      x < y →
        CodedSorting.TriangularStreams.globalKey key x = CodedSorting.TriangularStreams.globalKey key y →
          (CodedSorting.TriangularStreams.globalFieldEquiv e) x < (CodedSorting.TriangularStreams.globalFieldEquiv e) y
```

**继续展开**

- [CodedSorting.TriangularStreams.globalKey](TriangularStreams.definitions.md#def-f272f59e3f07df97)
- [CodedSorting.TriangularStreams.globalFieldEquiv](TriangularStreams.definitions.md#def-512e9a6065bbe891)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-639e80a4a83a6692"></a>
## `CodedSorting.TriangularStreams.lexLayout`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L277)

**类型**

```lean
{Q m : ℕ} → (Fin m → Fin Q) ≃ Fin (Q ^ m)
```

**定义**

```lean
fun {Q m} => toLex.trans (Fintype.orderIsoFinOfCardEq (Lex (Fin m → Fin Q)) ⋯).symm.toEquiv
```

**继续展开**

- [CodedSorting.TriangularStreams.lexLayout._proof_7](TriangularStreams.definitions.md#def-966f6db7761d131f)
- [CodedSorting.TriangularStreams.lexLayout._proof_8](TriangularStreams.definitions.md#def-069a1fe6c85a3aeb)

**基础库名称**

`Lex.fintype`, `Pi.instLinearOrderLexForallOfWellFoundedLT`, `Equiv.trans`, `Lex`, `Nat.instMonoid`, `PartialOrder.toPreorder`, `instDecidableEqFin`, `Pi.instFintype`, `Fintype.orderIsoFinOfCardEq`, `Preorder.toLE`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Equiv`, `LE.le`, `OrderIso.symm`, `instLEFin`, `Fin.fintype`, `Fin.instLinearOrder`, `HPow.hPow`, `Nat`, `instHPow`, `RelIso.toEquiv`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `toLex`

<a id="def-d875f44a4522e0e7"></a>
## `CodedSorting.TriangularStreams.PrefixDependent`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L287)

**类型**

```lean
{Q m : ℕ} → {α : Type u_1} → Fin m → ((Fin m → Fin Q) → α) → Prop
```

**定义**

```lean
fun {Q m} {α} i f => ∀ (x y : Fin m → Fin Q), (∀ j < i, x j = y j) → f x = f y
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`

<a id="def-41e93f18fb27aa44"></a>
## `CodedSorting.TriangularStreams.coordinateEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L298)

**类型**

```lean
{Q m : ℕ} →
  (i : Fin m) →
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) →
      CodedSorting.TriangularStreams.PrefixDependent i e → Equiv.Perm (Fin m → Fin Q)
```

**定义**

```lean
fun {Q m} i e he =>
  { toFun := fun x => Function.update x i ((e x) (x i)),
    invFun := fun x => Function.update x i ((Equiv.symm (e x)) (x i)), left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.TriangularStreams.coordinateEquiv._proof_10](TriangularStreams.definitions.md#def-9a97bb2f09bb59b2)
- [CodedSorting.TriangularStreams.coordinateEquiv._proof_11](TriangularStreams.definitions.md#def-d68495c6ce30ddea)
- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)

**基础库名称**

`Equiv.instFunLike`, `Function.update`, `instDecidableEqFin`, `Equiv.mk`, `Equiv`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `DFunLike.coe`

<a id="def-34a101f0f3e629b3"></a>
## `CodedSorting.TriangularStreams.coordinatePermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L355)

**类型**

```lean
{Q m : ℕ} →
  (i : Fin m) →
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) →
      CodedSorting.TriangularStreams.PrefixDependent i e → Equiv.Perm (Fin (Q ^ m))
```

**定义**

```lean
fun {Q m} i e he =>
  CodedSorting.TriangularStreams.lexLayout.symm.trans
    (Equiv.trans (CodedSorting.TriangularStreams.coordinateEquiv i e he) CodedSorting.TriangularStreams.lexLayout)
```

**继续展开**

- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)
- [CodedSorting.TriangularStreams.lexLayout](TriangularStreams.definitions.md#def-639e80a4a83a6692)
- [CodedSorting.TriangularStreams.coordinateEquiv](TriangularStreams.definitions.md#def-41e93f18fb27aa44)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`

<a id="def-048bf20e84e68307"></a>
## `CodedSorting.TriangularStreams.coordinateKey`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L360)

**类型**

```lean
{Q K m : ℕ} → Fin m → ((Fin m → Fin Q) → Fin Q → Fin K) → Fin (Q ^ m) → Fin K
```

**定义**

```lean
fun {Q K m} i key a =>
  key (CodedSorting.TriangularStreams.lexLayout.symm a) (CodedSorting.TriangularStreams.lexLayout.symm a i)
```

**继续展开**

- [CodedSorting.TriangularStreams.lexLayout](TriangularStreams.definitions.md#def-639e80a4a83a6692)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `DFunLike.coe`

<a id="def-373a4acc1944f70d"></a>
## `CodedSorting.TriangularStreams.coordinatePermutation_increasing`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularStreams.lean#L364)

**类型**

```lean
∀ {Q K m : ℕ} (i : Fin m) (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q))
  (he : CodedSorting.TriangularStreams.PrefixDependent i e) (key : (Fin m → Fin Q) → Fin Q → Fin K),
  CodedSorting.TriangularStreams.PrefixDependent i key →
    (∀ (x : Fin m → Fin Q) (a b : Fin Q), a < b → key x a = key x b → (e x) a < (e x) b) →
      ∀ (x y : Fin (Q ^ m)),
        x < y →
          CodedSorting.TriangularStreams.coordinateKey i key x = CodedSorting.TriangularStreams.coordinateKey i key y →
            (CodedSorting.TriangularStreams.coordinatePermutation i e he) x <
              (CodedSorting.TriangularStreams.coordinatePermutation i e he) y
```

**继续展开**

- [CodedSorting.TriangularStreams.coordinatePermutation](TriangularStreams.definitions.md#def-34a101f0f3e629b3)
- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)
- [CodedSorting.TriangularStreams.coordinateKey](TriangularStreams.definitions.md#def-048bf20e84e68307)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instHPow`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-e0fb3e34cf712661"></a>
## `CodedSorting.TriangularStreams.prefixOffset`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularStreams.lean#L472)

**类型**

```lean
{R : Type u_1} → [inst : CommRing R] → {m : ℕ} → Matrix (Fin m) (Fin m) R → Fin m → (Fin m → R) → R
```

**定义**

```lean
fun {R} [CommRing R] {m} A i x => ∑ j, if j < i then A i j * x j else 0
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `CommRing`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `CommRing.toNonUnitalCommRing`, `Finset.univ`, `Matrix`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Fin.fintype`, `NonUnitalNonAssocSemiring.toAddCommMonoid`, `Fin.decLt`, `Distrib.toMul`, `Nat`, `LT.lt`, `instLTFin`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `NonUnitalNonAssocSemiring.toDistrib`, `Zero.toOfNat0`, `OfNat.ofNat`, `Fin`, `Finset.sum`, `MulZeroClass.toZero`, `instHMul`, `ite`

<a id="def-9a97bb2f09bb59b2"></a>
## `CodedSorting.TriangularStreams.coordinateEquiv._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularStreams.lean)

**类型**

```lean
∀ {Q m : ℕ} (i : Fin m) (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)),
  CodedSorting.TriangularStreams.PrefixDependent i e →
    ∀ (x : Fin m → Fin Q),
      Function.update (Function.update x i ((e x) (x i))) i
          ((Equiv.symm (e (Function.update x i ((e x) (x i))))) (Function.update x i ((e x) (x i)) i)) =
        x
```

**继续展开**

- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)

**基础库名称**

`Equiv.instFunLike`, `Function.update`, `instDecidableEqFin`, `Equiv`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-d68495c6ce30ddea"></a>
## `CodedSorting.TriangularStreams.coordinateEquiv._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularStreams.lean)

**类型**

```lean
∀ {Q m : ℕ} (i : Fin m) (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)),
  CodedSorting.TriangularStreams.PrefixDependent i e →
    ∀ (x : Fin m → Fin Q),
      Function.update (Function.update x i ((Equiv.symm (e x)) (x i))) i
          ((e (Function.update x i ((Equiv.symm (e x)) (x i)))) (Function.update x i ((Equiv.symm (e x)) (x i)) i)) =
        x
```

**继续展开**

- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)

**基础库名称**

`Equiv.instFunLike`, `Function.update`, `instDecidableEqFin`, `Equiv`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-d64da95ddb6a100e"></a>
## `CodedSorting.TriangularStreams.fieldEquiv._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularStreams.lean)

**类型**

```lean
∀ {P Q S : ℕ} (e : Fin P → Equiv.Perm (Fin Q)) (x : CodedSorting.TriangularStreams.TripleAddress P Q S),
  (x.1, (Equiv.symm (e x.1)) ((e x.1) x.2.1), x.2.2) = x
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](TriangularStreams.definitions.md#def-11a69ce135db048a)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Prod.mk`, `Prod.fst`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`

<a id="def-b0498e8f33693919"></a>
## `CodedSorting.TriangularStreams.fieldEquiv._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularStreams.lean)

**类型**

```lean
∀ {P Q S : ℕ} (e : Fin P → Equiv.Perm (Fin Q)) (x : CodedSorting.TriangularStreams.TripleAddress P Q S),
  (x.1, (e x.1) ((Equiv.symm (e x.1)) x.2.1), x.2.2) = x
```

**继续展开**

- [CodedSorting.TriangularStreams.TripleAddress](TriangularStreams.definitions.md#def-11a69ce135db048a)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Prod.mk`, `Prod.fst`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Prod`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`

<a id="def-966f6db7761d131f"></a>
## `CodedSorting.TriangularStreams.lexLayout._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularStreams.lean)

**类型**

```lean
∀ {m : ℕ}, IsWellFounded (Fin m) fun x1 x2 => x1 < x2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.instLinearOrder`, `Nat`, `LT.lt`, `Fin`, `IsWellFounded`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-069a1fe6c85a3aeb"></a>
## `CodedSorting.TriangularStreams.lexLayout._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularStreams.lean)

**类型**

```lean
∀ {Q m : ℕ}, Fintype.card (Fin m → Fin Q) = Q ^ m
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `instDecidableEqFin`, `Pi.instFintype`, `Monoid.toNatPow`, `Fintype.card`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`
