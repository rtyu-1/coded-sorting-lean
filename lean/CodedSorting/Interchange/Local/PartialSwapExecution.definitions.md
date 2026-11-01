# PartialSwapExecution 的定义

[源码](PartialSwapExecution.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-d9dcea7b7c12220f"></a>
## `CodedSorting.Construction.PartialSwapExecution.restrictFamily`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L22)

**类型**

```lean
{K : Type u_1} →
  {I : Type u_2} →
    {J : Type u_3} →
      {T : Type u_4} →
        [inst : Fintype K] →
          [inst : Fintype I] →
            [inst_1 : DecidableEq I] →
              [inst_2 : Fintype J] →
                [inst_3 : DecidableEq J] →
                  {A : K → Matrix I I ℚ} →
                    CodedSorting.MatrixFactorization.SpecializedFamily A →
                      (select : T → K) →
                        (row col : T → J → I) →
                          CodedSorting.MatrixFactorization.SpecializedFamily fun t =>
                            (A (select t)).submatrix (row t) (col t)
```

**定义**

```lean
fun {K} {I} {J} {T} [Fintype K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {A} F select row col =>
  { denominator := F.denominator, denominator_ne_zero := ⋯, prime := F.prime, prime_is_prime := ⋯, prime_is_odd := ⋯,
    coefficients := fun t => (F.coefficients (select t)).submatrix (row t) (col t), lift_correct := ⋯,
    inverse_coefficients := fun t => (F.inverse_coefficients (select t)).submatrix (row t) (col t),
    inverse_lift_correct := ⋯, reduce := F.reduce }
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator_ne_zero](../../Circuit/Framework/MatrixFactorization.definitions.md#def-c270dd6ee4179f7f)
- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator](../../Circuit/Framework/MatrixFactorization.definitions.md#def-c8f7b01edbba36a1)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime_is_prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-21e7f386e3db1cd1)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.mk](../../Circuit/Framework/MatrixFactorization.definitions.md#def-c4afcc9d2e786cd7)
- [CodedSorting.MatrixFactorization.SpecializedFamily.reduce](../../Circuit/Framework/MatrixFactorization.definitions.md#def-4b7ddd070394b3a3)
- [CodedSorting.MatrixFactorization.SpecializedFamily.inverse_coefficients](../../Circuit/Framework/MatrixFactorization.definitions.md#def-8ee4f8292c25d037)
- [CodedSorting.Construction.PartialSwapExecution.restrictFamily._proof_1](PartialSwapExecution.definitions.md#def-2cf6dc39f1d89787)
- [CodedSorting.MatrixFactorization.CoeffRing](../../Circuit/Framework/MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime_is_odd](../../Circuit/Framework/MatrixFactorization.definitions.md#def-8948f2da419b2745)
- [CodedSorting.Construction.PartialSwapExecution.restrictFamily._proof_2](PartialSwapExecution.definitions.md#def-0fdd0f393f24e7d8)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.MatrixFactorization.SpecializedFamily.coefficients](../../Circuit/Framework/MatrixFactorization.definitions.md#def-b80b2d775e5a9597)

**基础库名称**

`Matrix.submatrix`, `Matrix`, `Rat`, `Fintype`, `DecidableEq`

<a id="def-3fd518ed2d2e0124"></a>
## `CodedSorting.Construction.PartialSwapExecution.castProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L70)

**类型**

```lean
{V W : ℕ} → V = W → List (CodedSorting.ScanProgram.Pass V) → List (CodedSorting.ScanProgram.Pass W)
```

**定义**

```lean
fun {V W} h ps => h ▸ ps
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Eq.rec`, `List`, `Nat`, `Eq`

<a id="def-8a8756861dcfeeca"></a>
## `CodedSorting.Construction.PartialSwapExecution.highProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L118)

**类型**

```lean
{K : Type u_1} →
  [inst : Fintype K] →
    {m : ℕ} →
      {A : K → Matrix (Fin m) (Fin m) ℚ} →
        (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
          (f : ℕ) →
            (k : K) →
              (∀ (i : Fin m), A k i i ≠ 0) →
                (P G S : ℕ) →
                  0 < G →
                    0 < S →
                      List
                        (CodedSorting.ScanProgram.Pass
                          (CodedSorting.CommonAddressLayout.Volume (Fin m) P (F.prime ^ f) G S))
```

**定义**

```lean
fun {K} [Fintype K] {m} {A} F f k hdiag P G S hG hS =>
  CodedSorting.Construction.PartialSwapExecution.castProgram ⋯
    (CodedSorting.GlobalTriangular.program F f k hdiag P (G * ((F.prime ^ f) ^ m * S)) ⋯)
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.castProgram](PartialSwapExecution.definitions.md#def-3fd518ed2d2e0124)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.GlobalTriangular.program](../../Circuit/Framework/TriangularProgramBounds.definitions.md#def-3de4dcc6b330feb7)
- [CodedSorting.Construction.PartialSwapExecution.highProgram._proof_4](PartialSwapExecution.definitions.md#def-d93a26d0efd1b64a)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.Construction.PartialSwapExecution.highProgram._proof_3](PartialSwapExecution.definitions.md#def-30a322c7f059a40b)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Rat.instOfNat`, `HMul.hMul`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `Ne`, `instMulNat`, `instOfNatNat`, `Fin.fintype`, `List`, `Fintype`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-b51a6ecbac9c9bdf"></a>
## `CodedSorting.Construction.PartialSwapExecution.lowProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L125)

**类型**

```lean
{K : Type u_1} →
  [inst : Fintype K] →
    {m : ℕ} →
      {A : K → Matrix (Fin m) (Fin m) ℚ} →
        (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
          (f : ℕ) →
            (k : K) →
              (∀ (i : Fin m), A k i i ≠ 0) →
                (P G S : ℕ) →
                  0 < S →
                    List
                      (CodedSorting.ScanProgram.Pass
                        (CodedSorting.CommonAddressLayout.Volume (Fin m) P (F.prime ^ f) G S))
```

**定义**

```lean
fun {K} [Fintype K] {m} {A} F f k hdiag P G S hS =>
  CodedSorting.Construction.PartialSwapExecution.castProgram ⋯
    (CodedSorting.GlobalTriangular.program F f k hdiag (P * ((F.prime ^ f) ^ m * G)) S hS)
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.castProgram](PartialSwapExecution.definitions.md#def-3fd518ed2d2e0124)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.GlobalTriangular.program](../../Circuit/Framework/TriangularProgramBounds.definitions.md#def-3de4dcc6b330feb7)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.Construction.PartialSwapExecution.lowProgram._proof_5](PartialSwapExecution.definitions.md#def-6f6e41dad4431433)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Rat.instOfNat`, `HMul.hMul`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `Ne`, `instMulNat`, `instOfNatNat`, `Fin.fintype`, `List`, `Fintype`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-77d37a75a4e2b6fe"></a>
## `CodedSorting.Construction.PartialSwapExecution.doubledDecEq`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L168)

**类型**

```lean
{m : ℕ} → DecidableEq (Lex (Fin m ⊕ Fin m))
```

**定义**

```lean
fun {m} => LinearOrder.toDecidableEq
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`LinearOrder.toDecidableEq`, `Lex`, `LinearOrder`, `inferInstance`, `Sum`, `Fin.instLinearOrder`, `Nat`, `Sum.Lex.linearOrder`, `Fin`, `DecidableEq`

<a id="def-f2d6ac286c64e8c7"></a>
## `CodedSorting.Construction.PartialSwapExecution.instNeZeroNatHPowPrimeLexSumFin`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapExecution.lean#L173)

**类型**

```lean
∀ {K : Type u_1} {m : ℕ} {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ}
  (F : CodedSorting.MatrixFactorization.SpecializedFamily A) (f : ℕ), NeZero (F.prime ^ f)
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Lex.fintype`, `Nat.instMulZeroClass`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Monoid.toNatPow`, `Sum`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `Fin`, `MulZeroClass.toZero`

<a id="def-59ad1ad63b80fd72"></a>
## `CodedSorting.Construction.PartialSwapExecution.highFamily`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L175)

**类型**

```lean
{K : Type u_1} →
  [inst : Fintype K] →
    {m : ℕ} →
      {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ} →
        CodedSorting.MatrixFactorization.SpecializedFamily A →
          CodedSorting.MatrixFactorization.SpecializedFamily fun k =>
            CodedSorting.Construction.TriangularConjugacy.highBlock (A k)
```

**定义**

```lean
fun {K} [Fintype K] {m} {A} F =>
  CodedSorting.Construction.PartialSwapExecution.restrictFamily F id (fun x => ⇑toLex ∘ Sum.inl) fun x =>
    ⇑toLex ∘ Sum.inl
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.TriangularConjugacy.highBlock](../../Circuit/Local/TriangularConjugacy.definitions.md#def-13d5a5e633c1a11d)
- [CodedSorting.Construction.PartialSwapExecution.restrictFamily](PartialSwapExecution.definitions.md#def-d9dcea7b7c12220f)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Equiv.instFunLike`, `Matrix`, `Lex`, `Rat`, `instDecidableEqFin`, `Function.comp`, `Sum`, `id`, `Equiv`, `Sum.inl`, `Fin.fintype`, `Fintype`, `Nat`, `Fin`, `DFunLike.coe`, `toLex`

<a id="def-578100a5d9b90c2f"></a>
## `CodedSorting.Construction.PartialSwapExecution.lowFamily`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L178)

**类型**

```lean
{K : Type u_1} →
  [inst : Fintype K] →
    {m : ℕ} →
      {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ} →
        CodedSorting.MatrixFactorization.SpecializedFamily A →
          CodedSorting.MatrixFactorization.SpecializedFamily fun k =>
            CodedSorting.Construction.TriangularConjugacy.lowBlock (A k)
```

**定义**

```lean
fun {K} [Fintype K] {m} {A} F =>
  CodedSorting.Construction.PartialSwapExecution.restrictFamily F id (fun x => ⇑toLex ∘ Sum.inr) fun x =>
    ⇑toLex ∘ Sum.inr
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.PartialSwapExecution.restrictFamily](PartialSwapExecution.definitions.md#def-d9dcea7b7c12220f)
- [CodedSorting.Construction.TriangularConjugacy.lowBlock](../../Circuit/Local/TriangularConjugacy.definitions.md#def-d23ebe8dba4d6e83)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Equiv.instFunLike`, `Matrix`, `Lex`, `Rat`, `instDecidableEqFin`, `Function.comp`, `Sum`, `id`, `Equiv`, `Fin.fintype`, `Fintype`, `Sum.inr`, `Nat`, `Fin`, `DFunLike.coe`, `toLex`

<a id="def-dc198e292b23529a"></a>
## `CodedSorting.Construction.PartialSwapExecution.fullFinMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L181)

**类型**

```lean
{K : Type u_1} →
  {m : ℕ} →
    {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ} →
      (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
        (f : ℕ) → K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) (Fin (F.prime ^ f))
```

**定义**

```lean
fun {K} {m} {A} F f k => (F.matrix f k).map ⇑(ZMod.finEquiv (F.prime ^ f)).symm
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.matrix](../../Circuit/Framework/MatrixFactorization.definitions.md#def-cd4372c7ca4d7efd)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.PartialSwapExecution.instNeZeroNatHPowPrimeLexSumFin](PartialSwapExecution.definitions.md#def-f2d6ac286c64e8c7)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Lex.fintype`, `instFintypeSum`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `ZMod.commRing`, `Matrix`, `RingEquiv.instEquivLike`, `Lex`, `Nat.instMonoid`, `Rat`, `Monoid.toNatPow`, `Sum`, `Distrib.toAdd`, `ZMod`, `Fin.fintype`, `HPow.hPow`, `Distrib.toMul`, `Fin.instMul`, `Nat`, `Matrix.map`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `NonUnitalNonAssocSemiring.toDistrib`, `Fin.instAdd`, `instHPow`, `RingEquiv`, `Fin`, `DFunLike.coe`, `ZMod.finEquiv`, `RingEquiv.symm`, `EquivLike.toFunLike`

<a id="def-7eebdc457592be2a"></a>
## `CodedSorting.Construction.PartialSwapExecution.crossFinMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L185)

**类型**

```lean
{K : Type u_1} →
  {m : ℕ} →
    {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ} →
      (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
        (f : ℕ) → K → Matrix (Fin m) (Fin m) (Fin (F.prime ^ f))
```

**定义**

```lean
fun {K} {m} {A} F f k =>
  (CodedSorting.Construction.PartialSwapExecution.fullFinMatrix F f k).submatrix (⇑toLex ∘ Sum.inr) (⇑toLex ∘ Sum.inl)
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.PartialSwapExecution.fullFinMatrix](PartialSwapExecution.definitions.md#def-dc198e292b23529a)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Equiv.instFunLike`, `Matrix.submatrix`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Function.comp`, `Monoid.toNatPow`, `Sum`, `Equiv`, `Sum.inl`, `Fin.fintype`, `HPow.hPow`, `Sum.inr`, `Nat`, `instHPow`, `Fin`, `DFunLike.coe`, `toLex`

<a id="def-e621fc38304292d7"></a>
## `CodedSorting.Construction.PartialSwapExecution.highDiagonal`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapExecution.lean#L203)

**类型**

```lean
∀ {K : Type u_1} {m : ℕ} {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ} (k : K),
  CodedSorting.Construction.TriangularConjugacy.LowerTriangular (A k) →
    IsUnit (A k) → ∀ (i : Fin m), CodedSorting.Construction.TriangularConjugacy.highBlock (A k) i i ≠ 0
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.LowerTriangular](../../Circuit/Local/TriangularConjugacy.definitions.md#def-01d2ddb2f4fb32f9)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.TriangularConjugacy.highBlock](../../Circuit/Local/TriangularConjugacy.definitions.md#def-13d5a5e633c1a11d)

**基础库名称**

`Rat.instOfNat`, `Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Rat`, `IsUnit`, `Sum`, `Ne`, `Fin.fintype`, `Fin.instLinearOrder`, `Nat`, `Sum.Lex.linearOrder`, `Matrix.semiring`, `OfNat.ofNat`, `Fin`, `Rat.semiring`, `MonoidWithZero.toMonoid`, `Semiring.toMonoidWithZero`

<a id="def-c0c59805916d185e"></a>
## `CodedSorting.Construction.PartialSwapExecution.lowDiagonal`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapExecution.lean#L208)

**类型**

```lean
∀ {K : Type u_1} {m : ℕ} {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ} (k : K),
  CodedSorting.Construction.TriangularConjugacy.LowerTriangular (A k) →
    IsUnit (A k) → ∀ (i : Fin m), CodedSorting.Construction.TriangularConjugacy.lowBlock (A k) i i ≠ 0
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.LowerTriangular](../../Circuit/Local/TriangularConjugacy.definitions.md#def-01d2ddb2f4fb32f9)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.TriangularConjugacy.lowBlock](../../Circuit/Local/TriangularConjugacy.definitions.md#def-d23ebe8dba4d6e83)

**基础库名称**

`Rat.instOfNat`, `Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Rat`, `IsUnit`, `Sum`, `Ne`, `Fin.fintype`, `Fin.instLinearOrder`, `Nat`, `Sum.Lex.linearOrder`, `Matrix.semiring`, `OfNat.ofNat`, `Fin`, `Rat.semiring`, `MonoidWithZero.toMonoid`, `Semiring.toMonoidWithZero`

<a id="def-9b614eccb086203b"></a>
## `CodedSorting.Construction.PartialSwapExecution.lowerProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L212)

**类型**

```lean
{K : Type u_1} →
  [inst : Fintype K] →
    {m : ℕ} →
      {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ} →
        (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
          (f : ℕ) →
            (k : K) →
              CodedSorting.Construction.TriangularConjugacy.LowerTriangular (A k) →
                IsUnit (A k) →
                  (P G S : ℕ) →
                    0 < G →
                      0 < S →
                        List
                          (CodedSorting.ScanProgram.Pass
                            (CodedSorting.CommonAddressLayout.Volume (Fin m) P (F.prime ^ f) G S))
```

**定义**

```lean
fun {K} [Fintype K] {m} {A} F f k hA hu P G S hG hS =>
  CodedSorting.Construction.PartialSwapExecution.lowProgram (CodedSorting.Construction.PartialSwapExecution.lowFamily F)
        f k ⋯ P G S hS ++
      CodedSorting.Construction.PartialSwapScan.crossProgram
        (CodedSorting.Construction.PartialSwapExecution.crossFinMatrix F f k) m ⋯ ++
    CodedSorting.Construction.PartialSwapExecution.highProgram
      (CodedSorting.Construction.PartialSwapExecution.highFamily F) f k ⋯ P G S hG hS
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.lowDiagonal](PartialSwapExecution.definitions.md#def-c0c59805916d185e)
- [CodedSorting.Construction.PartialSwapExecution.lowFamily](PartialSwapExecution.definitions.md#def-578100a5d9b90c2f)
- [CodedSorting.Construction.TriangularConjugacy.LowerTriangular](../../Circuit/Local/TriangularConjugacy.definitions.md#def-01d2ddb2f4fb32f9)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.PartialSwapExecution.instNeZeroNatHPowPrimeLexSumFin](PartialSwapExecution.definitions.md#def-f2d6ac286c64e8c7)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.PartialSwapExecution.highFamily](PartialSwapExecution.definitions.md#def-59ad1ad63b80fd72)
- [CodedSorting.Construction.PartialSwapExecution.crossFinMatrix](PartialSwapExecution.definitions.md#def-7eebdc457592be2a)
- [CodedSorting.Construction.TriangularConjugacy.highBlock](../../Circuit/Local/TriangularConjugacy.definitions.md#def-13d5a5e633c1a11d)
- [CodedSorting.Construction.PartialSwapExecution.highDiagonal](PartialSwapExecution.definitions.md#def-e621fc38304292d7)
- [CodedSorting.Construction.PartialSwapExecution.highProgram](PartialSwapExecution.definitions.md#def-8a8756861dcfeeca)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.Construction.PartialSwapExecution.lowProgram](PartialSwapExecution.definitions.md#def-b51a6ecbac9c9bdf)
- [CodedSorting.Construction.PartialSwapScan.crossProgram](PartialSwapScan.definitions.md#def-b42192232c56dca0)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.TriangularConjugacy.lowBlock](../../Circuit/Local/TriangularConjugacy.definitions.md#def-d23ebe8dba4d6e83)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Nat.le_refl`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `IsUnit`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.fintype`, `instHAppendOfAppend`, `List`, `Fin.instLinearOrder`, `Fintype`, `HPow.hPow`, `Nat`, `LT.lt`, `Sum.Lex.linearOrder`, `instHPow`, `Matrix.semiring`, `instLTNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `Rat.semiring`, `HAppend.hAppend`, `MonoidWithZero.toMonoid`, `Semiring.toMonoidWithZero`

<a id="def-ed93fd05bc478dda"></a>
## `CodedSorting.Construction.PartialSwapExecution.joinedVector`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L219)

**类型**

```lean
{m Q P G S : ℕ} → CodedSorting.Construction.PartialSwapScan.Addr (Fin m) P Q G S → Lex (Fin m ⊕ Fin m) → Fin Q
```

**定义**

```lean
fun {m Q P G S} a => Sum.elim a.high a.low
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.Construction.PartialSwapScan.Addr](PartialSwapScan.definitions.md#def-63b4f15890df9b8c)
- [CodedSorting.Address.FullAddress.high](../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)

**基础库名称**

`Lex`, `Sum`, `Nat`, `Fin`, `Sum.elim`

<a id="def-89a9d06537ce0b1a"></a>
## `CodedSorting.Construction.PartialSwapExecution.matrixAddress`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L222)

**类型**

```lean
{m Q P G S : ℕ} →
  [inst : NeZero Q] →
    Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) (Fin Q) →
      CodedSorting.Construction.PartialSwapScan.Addr (Fin m) P Q G S →
        CodedSorting.Construction.PartialSwapScan.Addr (Fin m) P Q G S
```

**定义**

```lean
fun {m Q P G S} [NeZero Q] M a =>
  { prefixCoord := a.prefixCoord,
    high := fun i => M.mulVec (CodedSorting.Construction.PartialSwapExecution.joinedVector a) (toLex (Sum.inl i)),
    gap := a.gap,
    low := fun i => M.mulVec (CodedSorting.Construction.PartialSwapExecution.joinedVector a) (toLex (Sum.inr i)),
    suffix := a.suffix }
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.joinedVector](PartialSwapExecution.definitions.md#def-ed93fd05bc478dda)
- [CodedSorting.Construction.PartialSwapScan.Addr](PartialSwapScan.definitions.md#def-63b4f15890df9b8c)
- [CodedSorting.Address.FullAddress.mk](../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.Address.FullAddress.gap](../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Lex.fintype`, `Nat.instMulZeroClass`, `instFintypeSum`, `Equiv.instFunLike`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `Fin.instCommRing`, `Matrix`, `Lex`, `Sum`, `Equiv`, `Sum.inl`, `Fin.fintype`, `Sum.inr`, `Nat`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `NeZero`, `Fin`, `Matrix.mulVec`, `DFunLike.coe`, `MulZeroClass.toZero`, `toLex`

<a id="def-aa59e176a33f08d2"></a>
## `CodedSorting.Construction.PartialSwapExecution.lowerConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L250)

**类型**

```lean
{K : Type u_1} → {m : ℕ} → {A : K → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ} → K → ℕ
```

**定义**

```lean
fun {K} {m} {A} k =>
  2 * CodedSorting.SpecializedTriangular.fixedConstant k + 10 * m +
    2 * CodedSorting.SpecializedTriangular.fixedConstant k
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.highBlock](../../Circuit/Local/TriangularConjugacy.definitions.md#def-13d5a5e633c1a11d)
- [CodedSorting.SpecializedTriangular.fixedConstant](../../Circuit/Framework/TriangularProgramBounds.definitions.md#def-e4a1228e15e962f1)
- [CodedSorting.Construction.TriangularConjugacy.lowBlock](../../Circuit/Local/TriangularConjugacy.definitions.md#def-d23ebe8dba4d6e83)

**基础库名称**

`HMul.hMul`, `Matrix`, `Lex`, `Rat`, `Sum`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-6092f2bfca4476da"></a>
## `CodedSorting.Construction.PartialSwapExecution.doubledDecEqLine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L458)

**类型**

```lean
{m : ℕ} → DecidableEq (Lex (Fin m ⊕ Fin m))
```

**定义**

```lean
fun {m} => LinearOrder.toDecidableEq
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`LinearOrder.toDecidableEq`, `Lex`, `LinearOrder`, `inferInstance`, `Sum`, `Fin.instLinearOrder`, `Nat`, `Sum.Lex.linearOrder`, `Fin`, `DecidableEq`

<a id="def-38196eb5ed8d031c"></a>
## `CodedSorting.Construction.PartialSwapExecution.lineFamily`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PartialSwapExecution.lean#L461)

**类型**

```lean
{m : ℕ} → (Fin m → ℚ) → Fin m → Fin m → Bool × Bool → Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ
```

**定义**

```lean
fun {m} u s t x =>
  match x with
  | (false, false) =>
    CodedSorting.Construction.TriangularConjugacy.partialSwap
      (CodedSorting.Construction.TriangularConjugacy.lineProjection u)
  | (false, true) =>
    CodedSorting.Construction.TriangularConjugacy.factor (CodedSorting.Construction.TriangularConjugacy.doubleVec u)
      (toLex (Sum.inl s)) (toLex (Sum.inr t))
  | (true, false) => CodedSorting.Construction.TriangularConjugacy.swapMatrix (toLex (Sum.inl s)) (toLex (Sum.inr t))
  | (true, true) =>
    (CodedSorting.Construction.TriangularConjugacy.factor (CodedSorting.Construction.TriangularConjugacy.doubleVec u)
        (toLex (Sum.inl s)) (toLex (Sum.inr t)))⁻¹
```

**继续展开**

- [CodedSorting.Construction.PartialSwapExecution.lineFamily.match_1](PartialSwapExecution.definitions.md#def-abd04f0bb246182c)
- [CodedSorting.Construction.TriangularConjugacy.lineProjection](../../Circuit/Local/TriangularConjugacy.definitions.md#def-56ff2fa744d2ab0a)
- [CodedSorting.Construction.TriangularConjugacy.swapMatrix](../../Circuit/Local/TriangularConjugacy.definitions.md#def-b9e629dd477b8571)
- [CodedSorting.Construction.TriangularConjugacy.factor](../../Circuit/Local/TriangularConjugacy.definitions.md#def-dfa2b1c860991762)
- [CodedSorting.Construction.TriangularConjugacy.partialSwap](../../Circuit/Local/TriangularConjugacy.definitions.md#def-d19b70aac67a1997)
- [CodedSorting.Construction.TriangularConjugacy.doubleVec](../../Circuit/Local/TriangularConjugacy.definitions.md#def-2729b8a2a2991d4c)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEqLine](PartialSwapExecution.definitions.md#def-6092f2bfca4476da)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Equiv.instFunLike`, `Matrix`, `Lex`, `Rat`, `Sum`, `Equiv`, `Sum.inl`, `Fin.fintype`, `Matrix.inv`, `Fin.instLinearOrder`, `Unit`, `Inv.inv`, `Sum.inr`, `Nat`, `Bool`, `Sum.Lex.linearOrder`, `Prod`, `Fin`, `DFunLike.coe`, `Rat.commRing`, `toLex`

<a id="def-30a322c7f059a40b"></a>
## `CodedSorting.Construction.PartialSwapExecution.highProgram._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapExecution.lean)

**类型**

```lean
∀ {K : Type u_1} {m : ℕ} {A : K → Matrix (Fin m) (Fin m) ℚ} (F : CodedSorting.MatrixFactorization.SpecializedFamily A)
  (f P G S : ℕ),
  P * ((F.prime ^ f) ^ m * (G * ((F.prime ^ f) ^ m * S))) =
    CodedSorting.CommonAddressLayout.Volume (Fin m) P (F.prime ^ f) G S
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`HMul.hMul`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `instMulNat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`, `instHMul`

<a id="def-d93a26d0efd1b64a"></a>
## `CodedSorting.Construction.PartialSwapExecution.highProgram._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapExecution.lean)

**类型**

```lean
∀ {K : Type u_1} {m : ℕ} {A : K → Matrix (Fin m) (Fin m) ℚ} (F : CodedSorting.MatrixFactorization.SpecializedFamily A)
  (f G S : ℕ), 0 < G → 0 < S → G * ((F.prime ^ f) ^ m * S) > 0
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`HMul.hMul`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `Fin.fintype`, `GT.gt`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-abd04f0bb246182c"></a>
## `CodedSorting.Construction.PartialSwapExecution.lineFamily.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PartialSwapExecution.lean)

**类型**

```lean
(motive : Bool × Bool → Sort u_1) →
  (x : Bool × Bool) →
    (Unit → motive (false, false)) →
      (Unit → motive (false, true)) → (Unit → motive (true, false)) → (Unit → motive (true, true)) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 h_4 =>
  Prod.casesOn x fun fst snd =>
    Bool.casesOn fst (Bool.casesOn snd (h_1 ()) (h_2 ())) (Bool.casesOn snd (h_3 ()) (h_4 ()))
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `Prod.mk`, `Bool.true`, `Unit`, `Bool.casesOn`, `Bool`, `Prod`, `Prod.casesOn`, `Bool.false`

<a id="def-6f6e41dad4431433"></a>
## `CodedSorting.Construction.PartialSwapExecution.lowProgram._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapExecution.lean)

**类型**

```lean
∀ {K : Type u_1} {m : ℕ} {A : K → Matrix (Fin m) (Fin m) ℚ} (F : CodedSorting.MatrixFactorization.SpecializedFamily A)
  (f P G S : ℕ),
  P * ((F.prime ^ f) ^ m * G) * ((F.prime ^ f) ^ m * S) =
    CodedSorting.CommonAddressLayout.Volume (Fin m) P (F.prime ^ f) G S
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`HMul.hMul`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `instMulNat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`, `instHMul`

<a id="def-2cf6dc39f1d89787"></a>
## `CodedSorting.Construction.PartialSwapExecution.restrictFamily._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapExecution.lean)

**类型**

```lean
∀ {K : Type u_2} {I : Type u_3} {J : Type u_1} {T : Type u_4} [inst : Fintype K] [inst : Fintype I]
  [inst_1 : DecidableEq I] [inst_2 : Fintype J] [inst_3 : DecidableEq J] {A : K → Matrix I I ℚ}
  (F : CodedSorting.MatrixFactorization.SpecializedFamily A) (select : T → K) (row col : T → J → I) (t : T),
  (CodedSorting.MatrixFactorization.intoRat F.denominator ⋯).mapMatrix
      ((F.coefficients (select t)).submatrix (row t) (col t)) =
    (A (select t)).submatrix (row t) (col t)
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator_ne_zero](../../Circuit/Framework/MatrixFactorization.definitions.md#def-c270dd6ee4179f7f)
- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator](../../Circuit/Framework/MatrixFactorization.definitions.md#def-c8f7b01edbba36a1)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.CoeffRing](../../Circuit/Framework/MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)
- [CodedSorting.MatrixFactorization.intoRat](../../Circuit/Framework/MatrixFactorization.definitions.md#def-d272b606b69bdb75)
- [CodedSorting.MatrixFactorization.SpecializedFamily.coefficients](../../Circuit/Framework/MatrixFactorization.definitions.md#def-b80b2d775e5a9597)

**基础库名称**

`Int.instCommMonoid`, `Matrix.submatrix`, `Matrix`, `Rat`, `RingHom`, `Int`, `Nat.cast`, `Matrix.nonAssocSemiring`, `RingHom.instFunLike`, `OreLocalization.oreSetComm`, `Fintype`, `RingHom.mapMatrix`, `CommMonoid.toMonoid`, `Submonoid.powers`, `instNatCastInt`, `OreLocalization.instSemiring`, `Semiring.toNonAssocSemiring`, `Eq`, `DFunLike.coe`, `Rat.semiring`, `Int.instSemiring`, `DecidableEq`

<a id="def-0fdd0f393f24e7d8"></a>
## `CodedSorting.Construction.PartialSwapExecution.restrictFamily._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PartialSwapExecution.lean)

**类型**

```lean
∀ {K : Type u_1} {I : Type u_2} {J : Type u_4} {T : Type u_3} [inst : Fintype I] [inst_1 : DecidableEq I]
  {A : K → Matrix I I ℚ} (F : CodedSorting.MatrixFactorization.SpecializedFamily A) (select : T → K)
  (row col : T → J → I) (t : T) (i j : J),
  (CodedSorting.MatrixFactorization.intoRat F.denominator ⋯) (F.inverse_coefficients (select t) (row t i) (col t j)) =
    (A (select t) (row t i) (col t j))⁻¹
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator_ne_zero](../../Circuit/Framework/MatrixFactorization.definitions.md#def-c270dd6ee4179f7f)
- [CodedSorting.MatrixFactorization.SpecializedFamily.denominator](../../Circuit/Framework/MatrixFactorization.definitions.md#def-c8f7b01edbba36a1)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.inverse_coefficients](../../Circuit/Framework/MatrixFactorization.definitions.md#def-8ee4f8292c25d037)
- [CodedSorting.MatrixFactorization.CoeffRing](../../Circuit/Framework/MatrixFactorization.definitions.md#def-e9cbc2b8599469e0)
- [CodedSorting.MatrixFactorization.intoRat](../../Circuit/Framework/MatrixFactorization.definitions.md#def-d272b606b69bdb75)

**基础库名称**

`Int.instCommMonoid`, `Matrix`, `Rat`, `RingHom`, `Int`, `Nat.cast`, `RingHom.instFunLike`, `OreLocalization.oreSetComm`, `Inv.inv`, `Fintype`, `CommMonoid.toMonoid`, `Rat.instInv`, `Submonoid.powers`, `instNatCastInt`, `OreLocalization.instSemiring`, `Semiring.toNonAssocSemiring`, `Eq`, `DFunLike.coe`, `Rat.semiring`, `Int.instSemiring`, `DecidableEq`
