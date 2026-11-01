# MatrixFactorization 的定义

[源码](MatrixFactorization.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e9cbc2b8599469e0"></a>
## `CodedSorting.MatrixFactorization.CoeffRing`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MatrixFactorization.lean#L25)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun D => Localization.Away ↑D
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Int.instCommMonoid`, `Localization.Away`, `Int`, `Nat.cast`, `Nat`, `instNatCastInt`

<a id="def-d272b606b69bdb75"></a>
## `CodedSorting.MatrixFactorization.intoRat`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MatrixFactorization.lean#L27)

**类型**

```lean
(D : ℕ) → D ≠ 0 → CodedSorting.MatrixFactorization.CoeffRing D →+* ℚ
```

**定义**

```lean
fun D hD => Localization.awayLift (Int.castRingHom ℚ) ↑D ⋯
```

**继续展开**

- [CodedSorting.MatrixFactorization.intoRat._proof_1](MatrixFactorization.definitions.md#def-ee5dafd3e4ea6a53)
- [CodedSorting.MatrixFactorization.CoeffRing](MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)

**基础库名称**

`Int.instCommMonoid`, `Ring.toNonAssocRing`, `Rat`, `RingHom`, `Rat.commSemiring`, `Rat.instDivisionRing`, `Ne`, `DivisionRing.toRing`, `instOfNatNat`, `Int`, `Localization.awayLift`, `Nat.cast`, `OreLocalization.oreSetComm`, `CommMonoid.toMonoid`, `Int.castRingHom`, `Nat`, `Submonoid.powers`, `instNatCastInt`, `Int.instCommSemiring`, `OfNat.ofNat`, `OreLocalization.instSemiring`, `Semiring.toNonAssocSemiring`, `Rat.semiring`, `Int.instSemiring`

<a id="def-17e2256f378fb954"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](MatrixFactorization.lean#L115)

**类型**

```lean
{K : Type u_1} → {I : Type u_2} → [inst : Fintype I] → [inst : DecidableEq I] → (K → Matrix I I ℚ) → Type (max u_1 u_2)
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.mk](MatrixFactorization.definitions.md#def-c4afcc9d2e786cd7)

**基础库名称**

`Matrix`, `Rat`, `Fintype`, `DecidableEq`

<a id="def-c4afcc9d2e786cd7"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](MatrixFactorization.lean#L119)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    [inst : Fintype I] →
      [inst_1 : DecidableEq I] →
        {A : K → Matrix I I ℚ} →
          (denominator : ℕ) →
            (denominator_ne_zero : denominator ≠ 0) →
              (prime : ℕ) →
                Nat.Prime prime →
                  Odd prime →
                    (coefficients : K → Matrix I I (CodedSorting.MatrixFactorization.CoeffRing denominator)) →
                      (∀ (k : K),
                          (CodedSorting.MatrixFactorization.intoRat denominator denominator_ne_zero).mapMatrix
                              (coefficients k) =
                            A k) →
                        (inverse_coefficients :
                            K → Matrix I I (CodedSorting.MatrixFactorization.CoeffRing denominator)) →
                          (∀ (k : K) (i j : I),
                              (CodedSorting.MatrixFactorization.intoRat denominator denominator_ne_zero)
                                  (inverse_coefficients k i j) =
                                (A k i j)⁻¹) →
                            ((f : ℕ) → CodedSorting.MatrixFactorization.CoeffRing denominator →+* ZMod (prime ^ f)) →
                              CodedSorting.MatrixFactorization.SpecializedFamily A
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.CoeffRing](MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)
- [CodedSorting.MatrixFactorization.intoRat](MatrixFactorization.definitions.md#def-d272b606b69bdb75)

**基础库名称**

`Int.instCommMonoid`, `Nat.Prime`, `ZMod.commRing`, `CommSemiring.toSemiring`, `Matrix`, `Nat.instMonoid`, `Rat`, `Odd`, `RingHom`, `Monoid.toNatPow`, `Ne`, `instOfNatNat`, `Int`, `Nat.cast`, `ZMod`, `Matrix.nonAssocSemiring`, `CommRing.toCommSemiring`, `RingHom.instFunLike`, `OreLocalization.oreSetComm`, `Inv.inv`, `Fintype`, `HPow.hPow`, `RingHom.mapMatrix`, `CommMonoid.toMonoid`, `Nat`, `Rat.instInv`, `Submonoid.powers`, `Nat.instSemiring`, `instNatCastInt`, `instHPow`, `OfNat.ofNat`, `OreLocalization.instSemiring`, `Semiring.toNonAssocSemiring`, `Eq`, `DFunLike.coe`, `Rat.semiring`, `Int.instSemiring`, `DecidableEq`

<a id="def-c8f7b01edbba36a1"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.denominator`

读取 `CodedSorting.MatrixFactorization.SpecializedFamily` 的 `denominator` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MatrixFactorization.lean#L120)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    [inst : Fintype I] →
      [inst_1 : DecidableEq I] → {A : K → Matrix I I ℚ} → CodedSorting.MatrixFactorization.SpecializedFamily A → ℕ
```

**定义**

```lean
fun K I [Fintype I] [DecidableEq I] A self => self.1
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)

**基础库名称**

`Matrix`, `Rat`, `Fintype`, `Nat`, `DecidableEq`

<a id="def-c270dd6ee4179f7f"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.denominator_ne_zero`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MatrixFactorization.lean#L121)

**类型**

```lean
∀ {K : Type u_1} {I : Type u_2} [inst : Fintype I] [inst_1 : DecidableEq I] {A : K → Matrix I I ℚ}
  (self : CodedSorting.MatrixFactorization.SpecializedFamily A), self.denominator ≠ 0
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator](MatrixFactorization.definitions.md#def-c8f7b01edbba36a1)
- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)

**基础库名称**

`Matrix`, `Rat`, `Ne`, `instOfNatNat`, `Fintype`, `Nat`, `OfNat.ofNat`, `DecidableEq`

<a id="def-5af30279750b8d0f"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.prime`

读取 `CodedSorting.MatrixFactorization.SpecializedFamily` 的 `prime` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MatrixFactorization.lean#L122)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    [inst : Fintype I] →
      [inst_1 : DecidableEq I] → {A : K → Matrix I I ℚ} → CodedSorting.MatrixFactorization.SpecializedFamily A → ℕ
```

**定义**

```lean
fun K I [Fintype I] [DecidableEq I] A self => self.3
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)

**基础库名称**

`Matrix`, `Rat`, `Fintype`, `Nat`, `DecidableEq`

<a id="def-21e7f386e3db1cd1"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.prime_is_prime`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MatrixFactorization.lean#L123)

**类型**

```lean
∀ {K : Type u_1} {I : Type u_2} [inst : Fintype I] [inst_1 : DecidableEq I] {A : K → Matrix I I ℚ}
  (self : CodedSorting.MatrixFactorization.SpecializedFamily A), Nat.Prime self.prime
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Nat.Prime`, `Matrix`, `Rat`, `Fintype`, `DecidableEq`

<a id="def-8948f2da419b2745"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.prime_is_odd`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MatrixFactorization.lean#L124)

**类型**

```lean
∀ {K : Type u_1} {I : Type u_2} [inst : Fintype I] [inst_1 : DecidableEq I] {A : K → Matrix I I ℚ}
  (self : CodedSorting.MatrixFactorization.SpecializedFamily A), Odd self.prime
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Matrix`, `Rat`, `Odd`, `Fintype`, `Nat`, `Nat.instSemiring`, `DecidableEq`

<a id="def-b80b2d775e5a9597"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.coefficients`

读取 `CodedSorting.MatrixFactorization.SpecializedFamily` 的 `coefficients` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MatrixFactorization.lean#L125)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    [inst : Fintype I] →
      [inst_1 : DecidableEq I] →
        {A : K → Matrix I I ℚ} →
          (self : CodedSorting.MatrixFactorization.SpecializedFamily A) →
            K → Matrix I I (CodedSorting.MatrixFactorization.CoeffRing self.denominator)
```

**定义**

```lean
fun K I [Fintype I] [DecidableEq I] A self => self.6
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator](MatrixFactorization.definitions.md#def-c8f7b01edbba36a1)
- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.CoeffRing](MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)

**基础库名称**

`Matrix`, `Rat`, `Fintype`, `DecidableEq`

<a id="def-8ee4f8292c25d037"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.inverse_coefficients`

读取 `CodedSorting.MatrixFactorization.SpecializedFamily` 的 `inverse_coefficients` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MatrixFactorization.lean#L128)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    [inst : Fintype I] →
      [inst_1 : DecidableEq I] →
        {A : K → Matrix I I ℚ} →
          (self : CodedSorting.MatrixFactorization.SpecializedFamily A) →
            K → Matrix I I (CodedSorting.MatrixFactorization.CoeffRing self.denominator)
```

**定义**

```lean
fun K I [Fintype I] [DecidableEq I] A self => self.8
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator](MatrixFactorization.definitions.md#def-c8f7b01edbba36a1)
- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.CoeffRing](MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)

**基础库名称**

`Matrix`, `Rat`, `Fintype`, `DecidableEq`

<a id="def-4b7ddd070394b3a3"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.reduce`

读取 `CodedSorting.MatrixFactorization.SpecializedFamily` 的 `reduce` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MatrixFactorization.lean#L131)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    [inst : Fintype I] →
      [inst_1 : DecidableEq I] →
        {A : K → Matrix I I ℚ} →
          (self : CodedSorting.MatrixFactorization.SpecializedFamily A) →
            (f : ℕ) → CodedSorting.MatrixFactorization.CoeffRing self.denominator →+* ZMod (self.prime ^ f)
```

**定义**

```lean
fun K I [Fintype I] [DecidableEq I] A self => self.10
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator](MatrixFactorization.definitions.md#def-c8f7b01edbba36a1)
- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.CoeffRing](MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Int.instCommMonoid`, `ZMod.commRing`, `CommSemiring.toSemiring`, `Matrix`, `Nat.instMonoid`, `Rat`, `RingHom`, `Monoid.toNatPow`, `Int`, `Nat.cast`, `ZMod`, `CommRing.toCommSemiring`, `OreLocalization.oreSetComm`, `Fintype`, `HPow.hPow`, `CommMonoid.toMonoid`, `Nat`, `Submonoid.powers`, `instNatCastInt`, `instHPow`, `OreLocalization.instSemiring`, `Semiring.toNonAssocSemiring`, `Int.instSemiring`, `DecidableEq`

<a id="def-6501610d878a69b1"></a>
## `CodedSorting.MatrixFactorization.specializeFamily`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MatrixFactorization.lean#L133)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    [inst : Fintype K] →
      [inst : Fintype I] →
        [inst_1 : DecidableEq I] → (A : K → Matrix I I ℚ) → CodedSorting.MatrixFactorization.SpecializedFamily A
```

**定义**

```lean
fun {K} {I} [Fintype K] [Fintype I] [DecidableEq I] A => Classical.choice ⋯
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.specializeFamily._proof_2](MatrixFactorization.definitions.md#def-2878d2745b2b846f)

**基础库名称**

`Matrix`, `Rat`, `Classical.choice`, `Fintype`, `DecidableEq`

<a id="def-cd4372c7ca4d7efd"></a>
## `CodedSorting.MatrixFactorization.SpecializedFamily.matrix`

读取 `CodedSorting.MatrixFactorization.SpecializedFamily` 的 `matrix` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MatrixFactorization.lean#L162)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    [inst : Fintype I] →
      [inst_1 : DecidableEq I] →
        {A : K → Matrix I I ℚ} →
          (F : CodedSorting.MatrixFactorization.SpecializedFamily A) → (f : ℕ) → K → Matrix I I (ZMod (F.prime ^ f))
```

**定义**

```lean
fun {K} {I} [Fintype I] [DecidableEq I] {A} F f k => (F.reduce f).mapMatrix (F.coefficients k)
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator](MatrixFactorization.definitions.md#def-c8f7b01edbba36a1)
- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.reduce](MatrixFactorization.definitions.md#def-4b7ddd070394b3a3)
- [CodedSorting.MatrixFactorization.CoeffRing](MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.MatrixFactorization.SpecializedFamily.coefficients](MatrixFactorization.definitions.md#def-b80b2d775e5a9597)

**基础库名称**

`Int.instCommMonoid`, `ZMod.commRing`, `CommSemiring.toSemiring`, `Matrix`, `Nat.instMonoid`, `Rat`, `RingHom`, `Monoid.toNatPow`, `Int`, `Nat.cast`, `ZMod`, `Matrix.nonAssocSemiring`, `CommRing.toCommSemiring`, `RingHom.instFunLike`, `OreLocalization.oreSetComm`, `Fintype`, `HPow.hPow`, `RingHom.mapMatrix`, `CommMonoid.toMonoid`, `Nat`, `Submonoid.powers`, `instNatCastInt`, `instHPow`, `OreLocalization.instSemiring`, `Semiring.toNonAssocSemiring`, `DFunLike.coe`, `Int.instSemiring`, `DecidableEq`

<a id="def-ee5dafd3e4ea6a53"></a>
## `CodedSorting.MatrixFactorization.intoRat._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MatrixFactorization.lean)

**类型**

```lean
∀ (D : ℕ), D ≠ 0 → IsUnit ((Int.castRingHom ℚ) ↑D)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`GroupWithZero.toMonoidWithZero`, `Ring.toNonAssocRing`, `CommSemiring.toSemiring`, `Rat`, `IsUnit`, `DivisionSemiring.toGroupWithZero`, `RingHom`, `Rat.commSemiring`, `Rat.instDivisionRing`, `Ne`, `DivisionRing.toRing`, `instOfNatNat`, `Int`, `Nat.cast`, `Field.toSemifield`, `RingHom.instFunLike`, `Semifield.toDivisionSemiring`, `Rat.instField`, `Int.castRingHom`, `Nat`, `instNatCastInt`, `Int.instCommSemiring`, `OfNat.ofNat`, `Semiring.toNonAssocSemiring`, `DFunLike.coe`, `MonoidWithZero.toMonoid`

<a id="def-2878d2745b2b846f"></a>
## `CodedSorting.MatrixFactorization.specializeFamily._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MatrixFactorization.lean)

**类型**

```lean
∀ {K : Type u_1} {I : Type u_2} [inst : Fintype K] [inst : Fintype I] [inst_1 : DecidableEq I] (A : K → Matrix I I ℚ),
  Nonempty (CodedSorting.MatrixFactorization.SpecializedFamily A)
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)

**基础库名称**

`Matrix`, `Rat`, `Fintype`, `Nonempty`, `DecidableEq`
