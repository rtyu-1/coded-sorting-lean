# ExchangeFramePermutation 的定义

[源码](ExchangeFramePermutation.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-90b3744c8186dcc8"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.CallBlock`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ExchangeFramePermutation.lean#L135)

**类型**

```lean
Type u_1 → ℕ → Type u_1
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.mk](ExchangeFramePermutation.definitions.md#def-a34e8d9728d27970)

**基础库名称**

`Nat`

<a id="def-a34e8d9728d27970"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.CallBlock.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ExchangeFramePermutation.lean#L137)

**类型**

```lean
{J : Type u_1} →
  {V : ℕ} →
    List (CodedSorting.ScanProgram.Pass V) →
      J → List (CodedSorting.ScanProgram.Pass V) → CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List`, `Nat`

<a id="def-e3e5bf868096e1b2"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.CallBlock.before`

读取 `CodedSorting.Construction.RankPartialSwapExecution.CallBlock` 的 `before` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeFramePermutation.lean#L138)

**类型**

```lean
{J : Type u_1} →
  {V : ℕ} → CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V → List (CodedSorting.ScanProgram.Pass V)
```

**定义**

```lean
fun J V self => self.1
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List`, `Nat`

<a id="def-2365622cd8ec6ede"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.CallBlock.childIndex`

读取 `CodedSorting.Construction.RankPartialSwapExecution.CallBlock` 的 `childIndex` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeFramePermutation.lean#L139)

**类型**

```lean
{J : Type u_1} → {V : ℕ} → CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V → J
```

**定义**

```lean
fun J V self => self.2
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)

**基础库名称**

`Nat`

<a id="def-d2265b7196bff313"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.CallBlock.after`

读取 `CodedSorting.Construction.RankPartialSwapExecution.CallBlock` 的 `after` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeFramePermutation.lean#L140)

**类型**

```lean
{J : Type u_1} →
  {V : ℕ} → CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V → List (CodedSorting.ScanProgram.Pass V)
```

**定义**

```lean
fun J V self => self.3
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List`, `Nat`

<a id="def-a1665841158d3145"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.doubledDecEq`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L147)

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

<a id="def-77f703f0f9bf4b19"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.Support`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ExchangeFramePermutation.lean#L150)

**类型**

```lean
{m : ℕ} → (Fin m → ℚ) → Type
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.Support.mk](ExchangeFramePermutation.definitions.md#def-1a5785a5f5b6b444)

**基础库名称**

`Rat`, `Nat`, `Fin`

<a id="def-1a5785a5f5b6b444"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.Support.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ExchangeFramePermutation.lean#L150)

**类型**

```lean
{m : ℕ} →
  {u : Fin m → ℚ} →
    (first last : Fin m) →
      u first ≠ 0 →
        u last ≠ 0 →
          (∀ r < first, u r = 0) →
            (∀ (r : Fin m), last < r → u r = 0) → CodedSorting.Construction.RankPartialSwapExecution.Support u
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.Support](ExchangeFramePermutation.definitions.md#def-77f703f0f9bf4b19)

**基础库名称**

`Rat.instOfNat`, `Rat`, `Ne`, `Nat`, `LT.lt`, `instLTFin`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-02149a90db5345cd"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.Support.first`

读取 `CodedSorting.Construction.RankPartialSwapExecution.Support` 的 `first` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeFramePermutation.lean#L151)

**类型**

```lean
{m : ℕ} → {u : Fin m → ℚ} → CodedSorting.Construction.RankPartialSwapExecution.Support u → Fin m
```

**定义**

```lean
fun m u self => self.1
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.Support](ExchangeFramePermutation.definitions.md#def-77f703f0f9bf4b19)

**基础库名称**

`Rat`, `Nat`, `Fin`

<a id="def-4b353d14d6766402"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.Support.last`

读取 `CodedSorting.Construction.RankPartialSwapExecution.Support` 的 `last` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeFramePermutation.lean#L152)

**类型**

```lean
{m : ℕ} → {u : Fin m → ℚ} → CodedSorting.Construction.RankPartialSwapExecution.Support u → Fin m
```

**定义**

```lean
fun m u self => self.2
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.Support](ExchangeFramePermutation.definitions.md#def-77f703f0f9bf4b19)

**基础库名称**

`Rat`, `Nat`, `Fin`

<a id="def-fd9ce5e6cdf77ee0"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.support`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L158)

**类型**

```lean
{m : ℕ} → (u : Fin m → ℚ) → u ≠ 0 → CodedSorting.Construction.RankPartialSwapExecution.Support u
```

**定义**

```lean
fun {m} u hu => Classical.choice ⋯
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.support._proof_1](ExchangeFramePermutation.definitions.md#def-58f0b5f02e89e502)
- [CodedSorting.Construction.RankPartialSwapExecution.Support](ExchangeFramePermutation.definitions.md#def-77f703f0f9bf4b19)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `Rat`, `Classical.choice`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Pi.instZero`, `Ne`, `Nat`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Zero.toOfNat0`, `OfNat.ofNat`, `Fin`, `Rat.commRing`, `MulZeroClass.toZero`

<a id="def-f9dfb60db9c80af6"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.supports`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L165)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      (i : Fin P.rank) → CodedSorting.Construction.RankPartialSwapExecution.Support (d.vectors i)
```

**定义**

```lean
fun {m} {P} d i => CodedSorting.Construction.RankPartialSwapExecution.support (d.vectors i) ⋯
```

**继续展开**

- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.RankPartialSwapExecution.support](ExchangeFramePermutation.definitions.md#def-fd9ce5e6cdf77ee0)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.Support](ExchangeFramePermutation.definitions.md#def-77f703f0f9bf4b19)
- [CodedSorting.Construction.RankPartialSwapExecution.supports._proof_2](ExchangeFramePermutation.definitions.md#def-9adab355ae296dfe)

**基础库名称**

`Matrix`, `Rat`, `Matrix.rank`, `Fin.fintype`, `Nat`, `Fin`, `Rat.commRing`

<a id="def-bf27693c91d0e533"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L167)

**类型**

```lean
{m : ℕ} → Matrix (Fin m) (Fin m) ℚ → Type
```

**定义**

```lean
fun {m} P => Option (Fin P.rank × Bool × Bool)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Matrix`, `Rat`, `Matrix.rank`, `Fin.fintype`, `Nat`, `Bool`, `Prod`, `Fin`, `Rat.commRing`, `Option`

<a id="def-ca2fed603e447af0"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.family`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L169)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P →
      CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex P →
        Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) ℚ
```

**定义**

```lean
fun {m} {P} d x =>
  match x with
  | none => CodedSorting.Construction.TriangularConjugacy.partialSwap P
  | some (i, tag) =>
    CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last tag
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family.match_1](ExchangeFramePermutation.definitions.md#def-cc739f4c2300bf80)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.TriangularConjugacy.partialSwap](../../Circuit/Local/TriangularConjugacy.definitions.md#def-d19b70aac67a1997)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)

**基础库名称**

`Matrix`, `Lex`, `Rat`, `Matrix.rank`, `Sum`, `Fin.fintype`, `Fin.instLinearOrder`, `Unit`, `Nat`, `Bool`, `Prod`, `Fin`, `Rat.commRing`

<a id="def-8c442cf28e468aa7"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.instNeZeroNatHPowPrimeFamilyIndexLexSumFin`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean#L176)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (F : CodedSorting.MatrixFactorization.SpecializedFamily (CodedSorting.Construction.RankPartialSwapExecution.family d))
  (f : ℕ), NeZero (F.prime ^ f)
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.RankPartialSwapExecution.doubledDecEq](ExchangeFramePermutation.definitions.md#def-a1665841158d3145)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Lex.fintype`, `Nat.instMulZeroClass`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Monoid.toNatPow`, `Sum`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `Fin`, `MulZeroClass.toZero`

<a id="def-d6fae6a386f28d49"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.componentFamily`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L178)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      CodedSorting.MatrixFactorization.SpecializedFamily (CodedSorting.Construction.RankPartialSwapExecution.family d) →
        (i : Fin P.rank) →
          CodedSorting.MatrixFactorization.SpecializedFamily
            (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
              (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
              (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last)
```

**定义**

```lean
fun {m} {P} d F i =>
  CodedSorting.Construction.PartialSwapExecution.restrictFamily F (fun tag => some (i, tag)) (fun x => id) fun x => id
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)
- [CodedSorting.Construction.PartialSwapExecution.restrictFamily](PartialSwapExecution.definitions.md#def-d9dcea7b7c12220f)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.RankPartialSwapExecution.doubledDecEq](ExchangeFramePermutation.definitions.md#def-a1665841158d3145)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Bool.fintype`, `Matrix`, `Lex`, `Rat`, `Option.some`, `Matrix.rank`, `Sum`, `id`, `Prod.mk`, `Fin.fintype`, `Nat`, `Bool`, `instFintypeOption`, `instFintypeProd`, `Prod`, `Fin`, `Rat.commRing`

<a id="def-bbc9505cf7bd851f"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.finite_target_square`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean#L203)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (F : CodedSorting.MatrixFactorization.SpecializedFamily (CodedSorting.Construction.RankPartialSwapExecution.family d))
  (f : ℕ),
  CodedSorting.Construction.PartialSwapExecution.fullFinMatrix F f none *
      CodedSorting.Construction.PartialSwapExecution.fullFinMatrix F f none =
    1
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.PartialSwapExecution.fullFinMatrix](PartialSwapExecution.definitions.md#def-dc198e292b23529a)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.instNeZeroNatHPowPrimeFamilyIndexLexSumFin](ExchangeFramePermutation.definitions.md#def-8c442cf28e468aa7)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.RankPartialSwapExecution.doubledDecEq](ExchangeFramePermutation.definitions.md#def-a1665841158d3145)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Lex.fintype`, `instFintypeSum`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `CommRing.toNonUnitalCommRing`, `Fin.instCommRing`, `Matrix`, `Lex`, `Nat.instMonoid`, `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`, `Rat`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `Fin.instAddMonoidWithOne`, `Fin.fintype`, `AddMonoidWithOne.toOne`, `Option.none`, `HPow.hPow`, `Fin.instMul`, `Nat`, `Bool`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Fin.addCommMonoid`, `instHPow`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Rat.commRing`, `MulZeroClass.toZero`

<a id="def-b56bcf06b89ff137"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.componentPlan`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L232)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      (F :
          CodedSorting.MatrixFactorization.SpecializedFamily
            (CodedSorting.Construction.RankPartialSwapExecution.family d)) →
        (f Pref G S : ℕ) →
          0 < G →
            0 < S →
              Fin P.rank →
                CodedSorting.Construction.RankPartialSwapExecution.CallBlock (Fin P.rank)
                  (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (F.prime ^ f) G S)
```

**定义**

```lean
fun {m} {P} d F f Pref G S hG hS i =>
  let h := ⋯;
  {
    before :=
      CodedSorting.Construction.PartialSwapExecution.lowerProgram
        (CodedSorting.Construction.RankPartialSwapExecution.componentFamily d F i) f (true, true) ⋯ ⋯ Pref G S hG hS,
    childIndex := i,
    after :=
      CodedSorting.Construction.PartialSwapExecution.lowerProgram
        (CodedSorting.Construction.RankPartialSwapExecution.componentFamily d F i) f (false, true) ⋯ ⋯ Pref G S hG hS }
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.Construction.RankPartialSwapExecution.componentFamily](ExchangeFramePermutation.definitions.md#def-d6fae6a386f28d49)
- [CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_9](ExchangeFramePermutation.definitions.md#def-542baef1e7293269)
- [CodedSorting.Construction.TriangularConjugacy.LowerTriangular](../../Circuit/Local/TriangularConjugacy.definitions.md#def-01d2ddb2f4fb32f9)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.PartialSwapExecution.lowerProgram](PartialSwapExecution.definitions.md#def-9b614eccb086203b)
- [CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_10](ExchangeFramePermutation.definitions.md#def-9164e8e75a5097d1)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.mk](ExchangeFramePermutation.definitions.md#def-a34e8d9728d27970)
- [CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_7](ExchangeFramePermutation.definitions.md#def-1a65a9e15bacb828)
- [CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_11](ExchangeFramePermutation.definitions.md#def-31f641e10cb5cf09)
- [CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_8](ExchangeFramePermutation.definitions.md#def-dbf57dd31b5f4d09)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEqLine](PartialSwapExecution.definitions.md#def-6092f2bfca4476da)
- [CodedSorting.Construction.RankPartialSwapExecution.doubledDecEq](ExchangeFramePermutation.definitions.md#def-a1665841158d3145)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Rat.addCommMonoid`, `Lex.fintype`, `Rat.instMul`, `instFintypeSum`, `Bool.fintype`, `HMul.hMul`, `Matrix`, `Lex`, `Nat.instMonoid`, `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`, `Rat`, `IsUnit`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `Prod.mk`, `instOfNatNat`, `Fin.fintype`, `Bool.true`, `And`, `Fin.instLinearOrder`, `HPow.hPow`, `Nat`, `LT.lt`, `Bool`, `instFintypeProd`, `Sum.Lex.linearOrder`, `instHPow`, `Matrix.semiring`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Bool.false`, `Fin`, `Eq`, `Rat.semiring`, `Rat.commRing`, `MonoidWithZero.toMonoid`, `Semiring.toMonoidWithZero`

<a id="def-1c2051f11bfc2726"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.plan`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L239)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      (F :
          CodedSorting.MatrixFactorization.SpecializedFamily
            (CodedSorting.Construction.RankPartialSwapExecution.family d)) →
        (f Pref G S : ℕ) →
          0 < G →
            0 < S →
              List
                (CodedSorting.Construction.RankPartialSwapExecution.CallBlock (Fin P.rank)
                  (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (F.prime ^ f) G S))
```

**定义**

```lean
fun {m} {P} d F f Pref G S hG hS =>
  List.map (CodedSorting.Construction.RankPartialSwapExecution.componentPlan d F f Pref G S hG hS)
    (List.finRange P.rank)
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.RankPartialSwapExecution.componentPlan](ExchangeFramePermutation.definitions.md#def-b56bcf06b89ff137)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.Construction.RankPartialSwapExecution.doubledDecEq](ExchangeFramePermutation.definitions.md#def-a1665841158d3145)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `List.map`, `Nat.instMonoid`, `Rat`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.fintype`, `List`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `List.finRange`, `Rat.commRing`

<a id="def-1bf4ceb3dbfbad35"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.componentConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L293)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P → Fin P.rank → ℕ
```

**定义**

```lean
fun {m} {P} d i =>
  CodedSorting.Construction.PartialSwapExecution.lowerConstant (true, true) +
    CodedSorting.Construction.PartialSwapExecution.lowerConstant (false, true)
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lowerConstant](PartialSwapExecution.definitions.md#def-aa59e176a33f08d2)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)

**基础库名称**

`Matrix`, `Rat`, `Matrix.rank`, `Prod.mk`, `Fin.fintype`, `Bool.true`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Bool`, `instAddNat`, `Prod`, `Bool.false`, `Fin`, `Rat.commRing`

<a id="def-13d6b020c5190aa2"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.fixedConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L297)

**类型**

```lean
{m : ℕ} → {P : Matrix (Fin m) (Fin m) ℚ} → CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P → ℕ
```

**定义**

```lean
fun {m} {P} d => ∑ i, CodedSorting.Construction.RankPartialSwapExecution.componentConstant d i
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.componentConstant](ExchangeFramePermutation.definitions.md#def-1bf4ceb3dbfbad35)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)

**基础库名称**

`Finset.univ`, `Matrix`, `Rat`, `Matrix.rank`, `Fin.fintype`, `Nat`, `Nat.instAddCommMonoid`, `Fin`, `Finset.sum`, `Rat.commRing`

<a id="def-a2a5f7fc393358f5"></a>
## `CodedSorting.Construction.ExchangeFramePermutation.doubledDecEq`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L357)

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

<a id="def-9a5da047ee14d5a7"></a>
## `CodedSorting.Construction.ExchangeFramePermutation.Mat`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L360)

**类型**

```lean
ℕ → ℕ → Type
```

**定义**

```lean
fun m Q => Matrix (Lex (Fin m ⊕ Fin m)) (Lex (Fin m ⊕ Fin m)) (Fin Q)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Matrix`, `Lex`, `Sum`, `Nat`, `Fin`

<a id="def-1815218d41b0092b"></a>
## `CodedSorting.Construction.ExchangeFramePermutation.addressPerm`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L362)

**类型**

```lean
{m Q : ℕ} →
  [inst : NeZero Q] →
    (M : CodedSorting.Construction.ExchangeFramePermutation.Mat m Q) →
      M * M = 1 → (Pref G S : ℕ) → Equiv.Perm (CodedSorting.Construction.PartialSwapScan.Addr (Fin m) Pref Q G S)
```

**定义**

```lean
fun {m Q} [NeZero Q] M hM Pref G S =>
  { toFun := CodedSorting.Construction.PartialSwapExecution.matrixAddress M,
    invFun := CodedSorting.Construction.PartialSwapExecution.matrixAddress M, left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.Addr](PartialSwapScan.definitions.md#def-63b4f15890df9b8c)
- [CodedSorting.Construction.ExchangeFramePermutation.addressPerm._proof_12](ExchangeFramePermutation.definitions.md#def-5d9b793c1d618377)
- [CodedSorting.Construction.ExchangeFramePermutation.doubledDecEq](ExchangeFramePermutation.definitions.md#def-a2a5f7fc393358f5)
- [CodedSorting.Construction.ExchangeFramePermutation.Mat](ExchangeFramePermutation.definitions.md#def-9a5da047ee14d5a7)
- [CodedSorting.Construction.PartialSwapExecution.matrixAddress](PartialSwapExecution.definitions.md#def-89a9d06537ce0b1a)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Lex.fintype`, `Nat.instMulZeroClass`, `instFintypeSum`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `CommRing.toNonUnitalCommRing`, `Fin.instCommRing`, `Matrix`, `Lex`, `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Equiv.mk`, `Sum`, `Fin.instAddMonoidWithOne`, `Fin.fintype`, `AddMonoidWithOne.toOne`, `Equiv.Perm`, `Fin.instMul`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Fin.addCommMonoid`, `NeZero`, `OfNat.ofNat`, `Fin`, `Eq`, `MulZeroClass.toZero`

<a id="def-d5b41a60c5233f49"></a>
## `CodedSorting.Construction.ExchangeFramePermutation.numericPerm`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L375)

**类型**

```lean
{m Q : ℕ} →
  [inst : NeZero Q] →
    (M : CodedSorting.Construction.ExchangeFramePermutation.Mat m Q) →
      M * M = 1 → (Pref G S : ℕ) → Equiv.Perm (Fin (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref Q G S))
```

**定义**

```lean
fun {m Q} [NeZero Q] M hM Pref G S =>
  CodedSorting.CommonAddressLayout.longLayout.symm.trans
    (Equiv.trans (CodedSorting.Construction.ExchangeFramePermutation.addressPerm M hM Pref G S)
      CodedSorting.CommonAddressLayout.longLayout)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.PartialSwapScan.Addr](PartialSwapScan.definitions.md#def-63b4f15890df9b8c)
- [CodedSorting.Construction.ExchangeFramePermutation.addressPerm](ExchangeFramePermutation.definitions.md#def-1815218d41b0092b)
- [CodedSorting.Construction.ExchangeFramePermutation.doubledDecEq](ExchangeFramePermutation.definitions.md#def-a2a5f7fc393358f5)
- [CodedSorting.Construction.ExchangeFramePermutation.numericPerm._proof_13](ExchangeFramePermutation.definitions.md#def-5dfb5a2abf8e88a1)
- [CodedSorting.Construction.ExchangeFramePermutation.Mat](ExchangeFramePermutation.definitions.md#def-9a5da047ee14d5a7)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Lex.fintype`, `Nat.instMulZeroClass`, `instFintypeSum`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `CommRing.toNonUnitalCommRing`, `Fin.instCommRing`, `Equiv.trans`, `Matrix`, `Lex`, `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Sum`, `Fin.instAddMonoidWithOne`, `Fin.fintype`, `AddMonoidWithOne.toOne`, `Fin.instLinearOrder`, `Equiv.Perm`, `Fin.instMul`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Fin.addCommMonoid`, `Equiv.symm`, `NeZero`, `OfNat.ofNat`, `Fin`, `Eq`, `MulZeroClass.toZero`

<a id="def-04231f8608859801"></a>
## `CodedSorting.Construction.ExchangeFramePermutation.numericExchange`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeFramePermutation.lean#L422)

**类型**

```lean
{m Q : ℕ} → (Pref G S : ℕ) → Equiv.Perm (Fin (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref Q G S))
```

**定义**

```lean
fun {m Q} Pref G S =>
  CodedSorting.CommonAddressLayout.longLayout.symm.trans
    (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CommonAddressLayout.longLayout)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.ExchangeFramePermutation.numericPerm._proof_13](ExchangeFramePermutation.definitions.md#def-5dfb5a2abf8e88a1)
- [CodedSorting.Address.exchangeEquiv](../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Equiv.trans`, `Fin.fintype`, `Fin.instLinearOrder`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`

<a id="def-5d9b793c1d618377"></a>
## `CodedSorting.Construction.ExchangeFramePermutation.addressPerm._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m Q : ℕ} [inst : NeZero Q] (M : CodedSorting.Construction.ExchangeFramePermutation.Mat m Q),
  M * M = 1 →
    ∀ (Pref G S : ℕ) (a : CodedSorting.Construction.PartialSwapScan.Addr (Fin m) Pref Q G S),
      CodedSorting.Construction.PartialSwapExecution.matrixAddress M
          (CodedSorting.Construction.PartialSwapExecution.matrixAddress M a) =
        a
```

**继续展开**

- [CodedSorting.Construction.PartialSwapScan.Addr](PartialSwapScan.definitions.md#def-63b4f15890df9b8c)
- [CodedSorting.Construction.ExchangeFramePermutation.doubledDecEq](ExchangeFramePermutation.definitions.md#def-a2a5f7fc393358f5)
- [CodedSorting.Construction.ExchangeFramePermutation.Mat](ExchangeFramePermutation.definitions.md#def-9a5da047ee14d5a7)
- [CodedSorting.Construction.PartialSwapExecution.matrixAddress](PartialSwapExecution.definitions.md#def-89a9d06537ce0b1a)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `Lex.fintype`, `Nat.instMulZeroClass`, `instFintypeSum`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `CommRing.toNonUnitalCommRing`, `Fin.instCommRing`, `Matrix`, `Lex`, `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Sum`, `Fin.instAddMonoidWithOne`, `Fin.fintype`, `AddMonoidWithOne.toOne`, `Fin.instMul`, `Nat`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Matrix.one`, `Fin.addCommMonoid`, `NeZero`, `OfNat.ofNat`, `Fin`, `Eq`, `MulZeroClass.toZero`

<a id="def-5dfb5a2abf8e88a1"></a>
## `CodedSorting.Construction.ExchangeFramePermutation.numericPerm._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m : ℕ}, IsWellFounded (Fin m) fun x1 x2 => x1 < x2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.instLinearOrder`, `Nat`, `LT.lt`, `Fin`, `IsWellFounded`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-9164e8e75a5097d1"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (i : Fin P.rank),
  CodedSorting.Construction.TriangularConjugacy.LowerTriangular
    (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (false, true))
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.LowerTriangular](../../Circuit/Local/TriangularConjugacy.definitions.md#def-01d2ddb2f4fb32f9)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)

**基础库名称**

`Matrix`, `Lex`, `Rat`, `Matrix.rank`, `Sum`, `Prod.mk`, `Fin.fintype`, `Bool.true`, `Fin.instLinearOrder`, `Nat`, `Bool`, `Sum.Lex.linearOrder`, `Bool.false`, `Fin`, `Rat.commRing`

<a id="def-31f641e10cb5cf09"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (i : Fin P.rank),
  IsUnit
    (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (false, true))
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEqLine](PartialSwapExecution.definitions.md#def-6092f2bfca4476da)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Rat`, `IsUnit`, `Matrix.rank`, `Sum`, `Prod.mk`, `Fin.fintype`, `Bool.true`, `Nat`, `Bool`, `Matrix.semiring`, `Bool.false`, `Fin`, `Rat.semiring`, `Rat.commRing`, `MonoidWithZero.toMonoid`, `Semiring.toMonoidWithZero`

<a id="def-1a65a9e15bacb828"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (i : Fin P.rank),
  CodedSorting.Construction.TriangularConjugacy.LowerTriangular
      (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
        (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
        (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (false, true)) ∧
    IsUnit
        (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
          (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
          (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (false, true)) ∧
      CodedSorting.Construction.TriangularConjugacy.LowerTriangular
          (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
            (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
            (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (true, true)) ∧
        IsUnit
            (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
              (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
              (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (true, true)) ∧
          CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
              (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
              (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (false, false) =
            CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
                  (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
                  (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (false, true) *
                CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
                  (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
                  (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (true, false) *
              CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
                (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
                (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (true, true)
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.LowerTriangular](../../Circuit/Local/TriangularConjugacy.definitions.md#def-01d2ddb2f4fb32f9)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEqLine](PartialSwapExecution.definitions.md#def-6092f2bfca4476da)

**基础库名称**

`Rat.addCommMonoid`, `Lex.fintype`, `Rat.instMul`, `instFintypeSum`, `HMul.hMul`, `Matrix`, `Lex`, `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`, `Rat`, `IsUnit`, `Matrix.rank`, `Sum`, `Prod.mk`, `Fin.fintype`, `Bool.true`, `And`, `Fin.instLinearOrder`, `Nat`, `Bool`, `Sum.Lex.linearOrder`, `Matrix.semiring`, `Bool.false`, `Fin`, `Eq`, `Rat.semiring`, `Rat.commRing`, `MonoidWithZero.toMonoid`, `Semiring.toMonoidWithZero`

<a id="def-dbf57dd31b5f4d09"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (i : Fin P.rank),
  CodedSorting.Construction.TriangularConjugacy.LowerTriangular
    (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (true, true))
```

**继续展开**

- [CodedSorting.Construction.TriangularConjugacy.LowerTriangular](../../Circuit/Local/TriangularConjugacy.definitions.md#def-01d2ddb2f4fb32f9)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)

**基础库名称**

`Matrix`, `Lex`, `Rat`, `Matrix.rank`, `Sum`, `Prod.mk`, `Fin.fintype`, `Bool.true`, `Fin.instLinearOrder`, `Nat`, `Bool`, `Sum.Lex.linearOrder`, `Fin`, `Rat.commRing`

<a id="def-542baef1e7293269"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.componentPlan._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (i : Fin P.rank),
  IsUnit
    (CodedSorting.Construction.PartialSwapExecution.lineFamily (d.vectors i)
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
      (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last (true, true))
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.PartialSwapExecution.lineFamily](PartialSwapExecution.definitions.md#def-38196eb5ed8d031c)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEqLine](PartialSwapExecution.definitions.md#def-6092f2bfca4476da)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Rat`, `IsUnit`, `Matrix.rank`, `Sum`, `Prod.mk`, `Fin.fintype`, `Bool.true`, `Nat`, `Bool`, `Matrix.semiring`, `Fin`, `Rat.semiring`, `Rat.commRing`, `MonoidWithZero.toMonoid`, `Semiring.toMonoidWithZero`

<a id="def-cc739f4c2300bf80"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.family.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (motive : CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex P → Sort u_1) →
      (x : CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex P) →
        (Unit → motive none) → ((i : Fin P.rank) → (tag : Bool × Bool) → motive (some (i, tag))) → motive x
```

**定义**

```lean
fun {m} {P} motive x h_1 h_2 => Option.casesOn x (h_1 ()) fun val => Prod.casesOn val fun fst snd => h_2 fst snd
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)

**基础库名称**

`Unit.unit`, `Matrix`, `Rat`, `Option.casesOn`, `Option.some`, `Matrix.rank`, `Prod.mk`, `Fin.fintype`, `Option.none`, `Unit`, `Nat`, `Bool`, `Prod`, `Prod.casesOn`, `Fin`, `Rat.commRing`

<a id="def-58f0b5f02e89e502"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.support._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m : ℕ} (u : Fin m → ℚ), u ≠ 0 → Nonempty (CodedSorting.Construction.RankPartialSwapExecution.Support u)
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.Support](ExchangeFramePermutation.definitions.md#def-77f703f0f9bf4b19)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `Rat`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Pi.instZero`, `Ne`, `Nat`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Nonempty`, `Zero.toOfNat0`, `OfNat.ofNat`, `Fin`, `Rat.commRing`, `MulZeroClass.toZero`

<a id="def-9adab355ae296dfe"></a>
## `CodedSorting.Construction.RankPartialSwapExecution.supports._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeFramePermutation.lean)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (i : Fin P.rank), d.vectors i ≠ 0
```

**继续展开**

- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `Matrix`, `Rat`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `Matrix.rank`, `Pi.instZero`, `Ne`, `Fin.fintype`, `Nat`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `Zero.toOfNat0`, `OfNat.ofNat`, `Fin`, `Rat.commRing`, `MulZeroClass.toZero`
