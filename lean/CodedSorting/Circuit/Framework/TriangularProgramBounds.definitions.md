# TriangularProgramBounds 的定义

[源码](TriangularProgramBounds.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-82cadd74fa2460b2"></a>
## `CodedSorting.TriangularRealization.coordinatePass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L16)

**类型**

```lean
{m Q K : ℕ} →
  (i : Fin m) →
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) →
      CodedSorting.TriangularStreams.PrefixDependent i e →
        (key : (Fin m → Fin Q) → Fin Q → Fin K) →
          CodedSorting.TriangularStreams.PrefixDependent i key →
            (∀ (x : Fin m → Fin Q) (a b : Fin Q), a < b → key x a = key x b → (e x) a < (e x) b) →
              CodedSorting.ScanProgram.Pass (Q ^ m)
```

**定义**

```lean
fun {m Q K} i e he key hk hinc =>
  CodedSorting.ScanProgram.Pass.streams K (CodedSorting.TriangularStreams.coordinatePermutation i e he)
    (CodedSorting.TriangularStreams.coordinateKey i key) ⋯
```

**继续展开**

- [CodedSorting.TriangularStreams.coordinatePermutation](TriangularStreams.definitions.md#def-34a101f0f3e629b3)
- [CodedSorting.TriangularStreams.coordinatePermutation_increasing](TriangularStreams.definitions.md#def-373a4acc1944f70d)
- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)
- [CodedSorting.ScanProgram.Pass.streams](../../Shared/Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.TriangularStreams.coordinateKey](TriangularStreams.definitions.md#def-048bf20e84e68307)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instHPow`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-4ea3fff73450b608"></a>
## `CodedSorting.TriangularRealization.multiplyPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L23)

**类型**

```lean
{m Q a : ℕ} → 0 < a → 0 < Q → a.Coprime Q → Fin m → CodedSorting.ScanProgram.Pass (Q ^ m)
```

**定义**

```lean
fun {m Q a} ha hQ hc i =>
  CodedSorting.TriangularRealization.coordinatePass i
    (fun x => CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc) ⋯
    (fun x => CodedSorting.SequentialArithmetic.multiplicationRun ha hQ) ⋯ ⋯
```

**继续展开**

- [CodedSorting.TriangularRealization.multiplyPass._proof_1](TriangularProgramBounds.definitions.md#def-f890774d66232700)
- [CodedSorting.SequentialArithmetic.multiplicationEquiv](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-347eea4112933180)
- [CodedSorting.SequentialArithmetic.multiplicationRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-90e6aa00b76f15a7)
- [CodedSorting.TriangularRealization.coordinatePass](TriangularProgramBounds.definitions.md#def-82cadd74fa2460b2)
- [CodedSorting.SequentialArithmetic.multiplication_increasing_in_run](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-c03a22fa254d24ac)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.TriangularRealization.multiplyPass._proof_2](TriangularProgramBounds.definitions.md#def-7a2609d565e41245)

**基础库名称**

`Nat.Coprime`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instLTFin`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-825cc54438db3843"></a>
## `CodedSorting.TriangularRealization.inverseMultiplyPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L29)

**类型**

```lean
{m Q a : ℕ} → 0 < a → 0 < Q → a.Coprime Q → Fin m → CodedSorting.ScanProgram.Pass (Q ^ m)
```

**定义**

```lean
fun {m Q a} ha hQ hc i =>
  CodedSorting.TriangularRealization.coordinatePass i
    (fun x => Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)) ⋯
    (fun x x =>
      CodedSorting.SequentialArithmetic.multiplicationRun ha hQ
        ((Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)) x))
    ⋯ ⋯
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiplicationEquiv](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-347eea4112933180)
- [CodedSorting.SequentialArithmetic.multiplicationRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-90e6aa00b76f15a7)
- [CodedSorting.TriangularRealization.inverseMultiplyPass._proof_5](TriangularProgramBounds.definitions.md#def-781fd5f72d8077a1)
- [CodedSorting.TriangularRealization.coordinatePass](TriangularProgramBounds.definitions.md#def-82cadd74fa2460b2)
- [CodedSorting.TriangularRealization.inverseMultiplyPass._proof_4](TriangularProgramBounds.definitions.md#def-fcddb57ad7d3786d)
- [CodedSorting.TriangularRealization.inverseMultiplyPass._proof_3](TriangularProgramBounds.definitions.md#def-d6a48b8d00c48d64)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Nat.Coprime`, `Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instOfNatNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-0b94aa71029a074f"></a>
## `CodedSorting.TriangularRealization.addPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L37)

**类型**

```lean
{m Q : ℕ} →
  (i : Fin m) →
    (offset : (Fin m → Fin Q) → Fin Q) →
      CodedSorting.TriangularStreams.PrefixDependent i offset → CodedSorting.ScanProgram.Pass (Q ^ m)
```

**定义**

```lean
fun {m Q} i offset ho =>
  CodedSorting.TriangularRealization.coordinatePass i (fun x => CodedSorting.AffineStreams.additionEquiv (offset x)) ⋯
    (fun x => CodedSorting.SequentialArithmetic.additionRun (offset x)) ⋯ ⋯
```

**继续展开**

- [CodedSorting.TriangularRealization.addPass._proof_6](TriangularProgramBounds.definitions.md#def-0ac2f985e1849e14)
- [CodedSorting.TriangularRealization.addPass._proof_7](TriangularProgramBounds.definitions.md#def-98b2da83309dc2e6)
- [CodedSorting.TriangularRealization.coordinatePass](TriangularProgramBounds.definitions.md#def-82cadd74fa2460b2)
- [CodedSorting.SequentialArithmetic.additionRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-4958ad02f45d9028)
- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.TriangularRealization.addPass._proof_8](TriangularProgramBounds.definitions.md#def-578fdc9844347671)
- [CodedSorting.AffineStreams.additionEquiv](AffineStreams.definitions.md#def-7c94b054256195c1)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-56632df6c4ffa05c"></a>
## `CodedSorting.TriangularRealization.reflectionPasses`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L45)

**类型**

```lean
{m Q : ℕ} → Fin m → 0 < Q → List (CodedSorting.ScanProgram.Pass (Q ^ m))
```

**定义**

```lean
fun {m Q} i hQ =>
  [CodedSorting.ScanProgram.Pass.reverse (CodedSorting.LexBlocks.PrefixCount Q i)
      (Q * CodedSorting.LexBlocks.SuffixCount Q i) ⋯ ⋯,
    CodedSorting.ScanProgram.Pass.reverse (CodedSorting.LexBlocks.PrefixCount Q i * Q)
      (CodedSorting.LexBlocks.SuffixCount Q i) ⋯ ⋯]
```

**继续展开**

- [CodedSorting.LexBlocks.PrefixCount](../../Shared/Indexing/LexBlocks.definitions.md#def-b5dc0c1da80a1119)
- [CodedSorting.LexBlocks.blockCard](../../Shared/Indexing/LexBlocks.definitions.md#def-26d7d10a5c2062e8)
- [CodedSorting.LexBlocks.SuffixCount](../../Shared/Indexing/LexBlocks.definitions.md#def-b586bdb106d39599)
- [CodedSorting.TriangularRealization.reflectionPasses._proof_11](TriangularProgramBounds.definitions.md#def-476bf3c343a2fa1d)
- [CodedSorting.TriangularRealization.reflectionPasses._proof_10](TriangularProgramBounds.definitions.md#def-2e290fb271cf455e)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.TriangularRealization.reflectionPasses._proof_9](TriangularProgramBounds.definitions.md#def-d5df8e3fbd687495)
- [CodedSorting.ScanProgram.Pass.reverse](../../Shared/Programs/ScanProgramLift.definitions.md#def-b047d60fca52cebe)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `List.cons`, `List`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`, `List.nil`

<a id="def-fca117e931dca1f8"></a>
## `CodedSorting.TriangularRealization.negationPasses`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L101)

**类型**

```lean
{m Q : ℕ} → [inst : NeZero Q] → Fin m → 0 < Q → List (CodedSorting.ScanProgram.Pass (Q ^ m))
```

**定义**

```lean
fun {m Q} [NeZero Q] i hQ =>
  CodedSorting.TriangularRealization.reflectionPasses i hQ ++
    [CodedSorting.TriangularRealization.addPass i (fun x => 1) ⋯]
```

**继续展开**

- [CodedSorting.TriangularRealization.addPass](TriangularProgramBounds.definitions.md#def-0b94aa71029a074f)
- [CodedSorting.TriangularRealization.negationPasses._proof_12](TriangularProgramBounds.definitions.md#def-6aa0361c440772bc)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.TriangularRealization.reflectionPasses](TriangularProgramBounds.definitions.md#def-56632df6c4ffa05c)

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.instOfNat`, `instOfNatNat`, `List.cons`, `instHAppendOfAppend`, `List`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `List.instAppend`, `NeZero`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `MulZeroClass.toZero`, `List.nil`

<a id="def-a9188c7255798315"></a>
## `CodedSorting.TriangularRealization.signedMultiplyPasses`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L122)

**类型**

```lean
{m Q : ℕ} →
  [inst : NeZero Q] →
    (z : ℤ) → z ≠ 0 → z.natAbs.Coprime Q → Fin m → 0 < Q → List (CodedSorting.ScanProgram.Pass (Q ^ m))
```

**定义**

```lean
fun {m Q} [NeZero Q] z hz hc i hQ =>
  [CodedSorting.TriangularRealization.multiplyPass ⋯ hQ hc i] ++
    if 0 ≤ z then [] else CodedSorting.TriangularRealization.negationPasses i hQ
```

**继续展开**

- [CodedSorting.TriangularRealization.signedMultiplyPasses._proof_13](TriangularProgramBounds.definitions.md#def-8838d14287988789)
- [CodedSorting.TriangularRealization.negationPasses](TriangularProgramBounds.definitions.md#def-fca117e931dca1f8)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.TriangularRealization.multiplyPass](TriangularProgramBounds.definitions.md#def-4ea3fff73450b608)

**基础库名称**

`Nat.Coprime`, `Nat.instMulZeroClass`, `Nat.instMonoid`, `Int.decLe`, `Monoid.toNatPow`, `Ne`, `instOfNatNat`, `Int`, `LE.le`, `List.cons`, `instHAppendOfAppend`, `List`, `HPow.hPow`, `instOfNat`, `Nat`, `LT.lt`, `Int.natAbs`, `instHPow`, `instLTNat`, `List.instAppend`, `NeZero`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `Int.instLEInt`, `MulZeroClass.toZero`, `List.nil`, `ite`

<a id="def-79fa41febc46eceb"></a>
## `CodedSorting.TriangularRealization.DiagonalFractions`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](TriangularProgramBounds.lean#L168)

**类型**

```lean
{m Q : ℕ} → [inst : NeZero Q] → Matrix (Fin m) (Fin m) (Fin Q) → Type
```

**继续展开**

- [CodedSorting.TriangularRealization.DiagonalFractions.mk](TriangularProgramBounds.definitions.md#def-1a8c8ae4b2260864)

**基础库名称**

`Nat.instMulZeroClass`, `Matrix`, `Nat`, `NeZero`, `Fin`, `MulZeroClass.toZero`

<a id="def-1a8c8ae4b2260864"></a>
## `CodedSorting.TriangularRealization.DiagonalFractions.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](TriangularProgramBounds.lean#L169)

**类型**

```lean
{m Q : ℕ} →
  [inst : NeZero Q] →
    {A : Matrix (Fin m) (Fin m) (Fin Q)} →
      (numerator : Fin m → ℤ) →
        (denominator : Fin m → ℕ) →
          (∀ (i : Fin m), numerator i ≠ 0) →
            (∀ (i : Fin m), 0 < denominator i) →
              (∀ (i : Fin m), (numerator i).natAbs.Coprime Q) →
                (∀ (i : Fin m), (denominator i).Coprime Q) →
                  (∀ (i : Fin m), ↑(denominator i) * A i i = ↑(numerator i)) →
                    CodedSorting.TriangularRealization.DiagonalFractions A
```

**继续展开**

- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)

**基础库名称**

`Int.cast`, `Fin.instNatCast`, `Nat.Coprime`, `Nat.instMulZeroClass`, `HMul.hMul`, `Fin.instCommRing`, `Matrix`, `Ne`, `instOfNatNat`, `Int`, `AddGroupWithOne.toIntCast`, `Nat.cast`, `instOfNat`, `Fin.instMul`, `Nat`, `LT.lt`, `Int.natAbs`, `instLTNat`, `CommRing.toRing`, `NeZero`, `OfNat.ofNat`, `Fin`, `Eq`, `Ring.toAddGroupWithOne`, `MulZeroClass.toZero`, `instHMul`

<a id="def-bb53b9a17ea63021"></a>
## `CodedSorting.TriangularRealization.DiagonalFractions.numerator`

读取 `CodedSorting.TriangularRealization.DiagonalFractions` 的 `numerator` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](TriangularProgramBounds.lean#L170)

**类型**

```lean
{m Q : ℕ} →
  [inst : NeZero Q] →
    {A : Matrix (Fin m) (Fin m) (Fin Q)} → CodedSorting.TriangularRealization.DiagonalFractions A → Fin m → ℤ
```

**定义**

```lean
fun m Q [NeZero Q] A self => self.1
```

**继续展开**

- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)

**基础库名称**

`Nat.instMulZeroClass`, `Matrix`, `Int`, `Nat`, `NeZero`, `Fin`, `MulZeroClass.toZero`

<a id="def-1a1edbf696cb7d7d"></a>
## `CodedSorting.TriangularRealization.DiagonalFractions.denominator`

读取 `CodedSorting.TriangularRealization.DiagonalFractions` 的 `denominator` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](TriangularProgramBounds.lean#L171)

**类型**

```lean
{m Q : ℕ} →
  [inst : NeZero Q] →
    {A : Matrix (Fin m) (Fin m) (Fin Q)} → CodedSorting.TriangularRealization.DiagonalFractions A → Fin m → ℕ
```

**定义**

```lean
fun m Q [NeZero Q] A self => self.2
```

**继续展开**

- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)

**基础库名称**

`Nat.instMulZeroClass`, `Matrix`, `Nat`, `NeZero`, `Fin`, `MulZeroClass.toZero`

<a id="def-54d0ab6dcbf324c5"></a>
## `CodedSorting.TriangularRealization.DiagonalFractions.numerator_ne_zero`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean#L172)

**类型**

```lean
∀ {m Q : ℕ} [inst : NeZero Q] {A : Matrix (Fin m) (Fin m) (Fin Q)}
  (self : CodedSorting.TriangularRealization.DiagonalFractions A) (i : Fin m), self.numerator i ≠ 0
```

**继续展开**

- [CodedSorting.TriangularRealization.DiagonalFractions.numerator](TriangularProgramBounds.definitions.md#def-bb53b9a17ea63021)
- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)

**基础库名称**

`Nat.instMulZeroClass`, `Matrix`, `Ne`, `Int`, `instOfNat`, `Nat`, `NeZero`, `OfNat.ofNat`, `Fin`, `MulZeroClass.toZero`

<a id="def-738ddaac010ab449"></a>
## `CodedSorting.TriangularRealization.DiagonalFractions.denominator_pos`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean#L173)

**类型**

```lean
∀ {m Q : ℕ} [inst : NeZero Q] {A : Matrix (Fin m) (Fin m) (Fin Q)}
  (self : CodedSorting.TriangularRealization.DiagonalFractions A) (i : Fin m), 0 < self.denominator i
```

**继续展开**

- [CodedSorting.TriangularRealization.DiagonalFractions.denominator](TriangularProgramBounds.definitions.md#def-1a1edbf696cb7d7d)
- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)

**基础库名称**

`Nat.instMulZeroClass`, `Matrix`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `NeZero`, `OfNat.ofNat`, `Fin`, `MulZeroClass.toZero`

<a id="def-a2c39aa337e3e31c"></a>
## `CodedSorting.TriangularRealization.DiagonalFractions.numerator_coprime`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean#L174)

**类型**

```lean
∀ {m Q : ℕ} [inst : NeZero Q] {A : Matrix (Fin m) (Fin m) (Fin Q)}
  (self : CodedSorting.TriangularRealization.DiagonalFractions A) (i : Fin m), (self.numerator i).natAbs.Coprime Q
```

**继续展开**

- [CodedSorting.TriangularRealization.DiagonalFractions.numerator](TriangularProgramBounds.definitions.md#def-bb53b9a17ea63021)
- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)

**基础库名称**

`Nat.Coprime`, `Nat.instMulZeroClass`, `Matrix`, `Nat`, `Int.natAbs`, `NeZero`, `Fin`, `MulZeroClass.toZero`

<a id="def-b91acb0f38c6dce8"></a>
## `CodedSorting.TriangularRealization.DiagonalFractions.denominator_coprime`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean#L175)

**类型**

```lean
∀ {m Q : ℕ} [inst : NeZero Q] {A : Matrix (Fin m) (Fin m) (Fin Q)}
  (self : CodedSorting.TriangularRealization.DiagonalFractions A) (i : Fin m), (self.denominator i).Coprime Q
```

**继续展开**

- [CodedSorting.TriangularRealization.DiagonalFractions.denominator](TriangularProgramBounds.definitions.md#def-1a1edbf696cb7d7d)
- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)

**基础库名称**

`Nat.Coprime`, `Nat.instMulZeroClass`, `Matrix`, `Nat`, `NeZero`, `Fin`, `MulZeroClass.toZero`

<a id="def-bfe592e32d3bed9c"></a>
## `CodedSorting.TriangularRealization.rowPasses`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L178)

**类型**

```lean
{m Q : ℕ} →
  [inst : NeZero Q] →
    (A : Matrix (Fin m) (Fin m) (Fin Q)) →
      CodedSorting.TriangularRealization.DiagonalFractions A →
        Fin m → 0 < Q → List (CodedSorting.ScanProgram.Pass (Q ^ m))
```

**定义**

```lean
fun {m Q} [NeZero Q] A D i hQ =>
  CodedSorting.TriangularRealization.signedMultiplyPasses (D.numerator i) ⋯ ⋯ i hQ ++
      [CodedSorting.TriangularRealization.inverseMultiplyPass ⋯ hQ ⋯ i] ++
    [CodedSorting.TriangularRealization.addPass i (CodedSorting.TriangularStreams.prefixOffset A i) ⋯]
```

**继续展开**

- [CodedSorting.TriangularRealization.addPass](TriangularProgramBounds.definitions.md#def-0b94aa71029a074f)
- [CodedSorting.TriangularRealization.DiagonalFractions.numerator](TriangularProgramBounds.definitions.md#def-bb53b9a17ea63021)
- [CodedSorting.TriangularRealization.signedMultiplyPasses](TriangularProgramBounds.definitions.md#def-a9188c7255798315)
- [CodedSorting.TriangularRealization.DiagonalFractions.numerator_coprime](TriangularProgramBounds.definitions.md#def-a2c39aa337e3e31c)
- [CodedSorting.TriangularRealization.DiagonalFractions.numerator_ne_zero](TriangularProgramBounds.definitions.md#def-54d0ab6dcbf324c5)
- [CodedSorting.TriangularRealization.DiagonalFractions.denominator_coprime](TriangularProgramBounds.definitions.md#def-b91acb0f38c6dce8)
- [CodedSorting.TriangularRealization.DiagonalFractions.denominator](TriangularProgramBounds.definitions.md#def-1a1edbf696cb7d7d)
- [CodedSorting.TriangularRealization.rowPasses._proof_14](TriangularProgramBounds.definitions.md#def-0f9fbf37703e1551)
- [CodedSorting.TriangularRealization.inverseMultiplyPass](TriangularProgramBounds.definitions.md#def-825cc54438db3843)
- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)
- [CodedSorting.TriangularRealization.DiagonalFractions.denominator_pos](TriangularProgramBounds.definitions.md#def-738ddaac010ab449)
- [CodedSorting.TriangularStreams.prefixOffset](TriangularStreams.definitions.md#def-e0fb3e34cf712661)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Nat.instMulZeroClass`, `Fin.instCommRing`, `Matrix`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `List.cons`, `instHAppendOfAppend`, `List`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `List.instAppend`, `NeZero`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `MulZeroClass.toZero`, `List.nil`

<a id="def-8c352dae51e9ba3c"></a>
## `CodedSorting.TriangularRealization.descendingPasses`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L200)

**类型**

```lean
{m Q : ℕ} →
  [inst : NeZero Q] →
    (A : Matrix (Fin m) (Fin m) (Fin Q)) →
      CodedSorting.TriangularRealization.DiagonalFractions A →
        0 < Q → (n : ℕ) → n ≤ m → List (CodedSorting.ScanProgram.Pass (Q ^ m))
```

**定义**

```lean
fun {m Q} [NeZero Q] A D hQ x x_1 =>
  Nat.brecOn (motive := fun x => x ≤ m → List (CodedSorting.ScanProgram.Pass (Q ^ m))) x
    (fun x f x_2 =>
      (match (motive :=
          (x : ℕ) →
            x ≤ m →
              Nat.below (motive := fun x => x ≤ m → List (CodedSorting.ScanProgram.Pass (Q ^ m))) x →
                List (CodedSorting.ScanProgram.Pass (Q ^ m)))
          x, x_2 with
        | 0, x => fun x => []
        | n.succ, hn => fun x => CodedSorting.TriangularRealization.rowPasses A D ⟨n, ⋯⟩ hQ ++ x.1 ⋯)
        f)
    x_1
```

**继续展开**

- [CodedSorting.TriangularRealization.rowPasses](TriangularProgramBounds.definitions.md#def-bfe592e32d3bed9c)
- [CodedSorting.TriangularRealization.descendingPasses.match_1](TriangularProgramBounds.definitions.md#def-3152216ad6759484)
- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.TriangularRealization.descendingPasses._proof_18](TriangularProgramBounds.definitions.md#def-03b012757a1e8220)
- [CodedSorting.TriangularRealization.descendingPasses._proof_17](TriangularProgramBounds.definitions.md#def-5b75aae844104c97)

**基础库名称**

`Nat.instMulZeroClass`, `Matrix`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `Nat.brecOn`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `instHAppendOfAppend`, `List`, `instHAdd`, `PProd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `List.instAppend`, `NeZero`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `HAppend.hAppend`, `MulZeroClass.toZero`, `List.nil`

<a id="def-ea5bc2ef5a27174c"></a>
## `CodedSorting.SpecializedTriangular.instNeZeroNatHPowPrimeFin`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean#L297)

**类型**

```lean
∀ {Family : Type u_1} {m : ℕ} {A : Family → Matrix (Fin m) (Fin m) ℚ}
  (F : CodedSorting.MatrixFactorization.SpecializedFamily A) (f : ℕ), NeZero (F.prime ^ f)
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Nat.instMulZeroClass`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `Fin`, `MulZeroClass.toZero`

<a id="def-511dea50e5de3486"></a>
## `CodedSorting.SpecializedTriangular.finMatrix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L299)

**类型**

```lean
{Family : Type u_1} →
  {m : ℕ} →
    {A : Family → Matrix (Fin m) (Fin m) ℚ} →
      (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
        (f : ℕ) → Family → Matrix (Fin m) (Fin m) (Fin (F.prime ^ f))
```

**定义**

```lean
fun {Family} {m} {A} F f k => (F.matrix f k).map ⇑(ZMod.finEquiv (F.prime ^ f)).symm
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily.matrix](MatrixFactorization.definitions.md#def-cd4372c7ca4d7efd)
- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.SpecializedTriangular.instNeZeroNatHPowPrimeFin](TriangularProgramBounds.definitions.md#def-ea5bc2ef5a27174c)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `CommRing.toNonUnitalCommRing`, `ZMod.commRing`, `Matrix`, `RingEquiv.instEquivLike`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `Distrib.toAdd`, `ZMod`, `Fin.fintype`, `HPow.hPow`, `Distrib.toMul`, `Fin.instMul`, `Nat`, `Matrix.map`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `NonUnitalNonAssocSemiring.toDistrib`, `Fin.instAdd`, `instHPow`, `RingEquiv`, `Fin`, `DFunLike.coe`, `ZMod.finEquiv`, `RingEquiv.symm`, `EquivLike.toFunLike`

<a id="def-bac7c07fc28705ba"></a>
## `CodedSorting.SpecializedTriangular.diagonalData`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L302)

**类型**

```lean
{Family : Type u_1} →
  [inst : Fintype Family] →
    {m : ℕ} →
      {A : Family → Matrix (Fin m) (Fin m) ℚ} →
        (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
          (f : ℕ) →
            (k : Family) →
              (∀ (i : Fin m), A k i i ≠ 0) →
                CodedSorting.TriangularRealization.DiagonalFractions
                  (CodedSorting.SpecializedTriangular.finMatrix F f k)
```

**定义**

```lean
fun {Family} [Fintype Family] {m} {A} F f k hdiag =>
  { numerator := fun i => (A k i i).num, denominator := fun i => (A k i i).den, numerator_ne_zero := ⋯,
    denominator_pos := ⋯, numerator_coprime := ⋯, denominator_coprime := ⋯, fraction := ⋯ }
```

**继续展开**

- [CodedSorting.SpecializedTriangular.diagonalData._proof_22](TriangularProgramBounds.definitions.md#def-d9e3738ef8fb090c)
- [CodedSorting.SpecializedTriangular.diagonalData._proof_19](TriangularProgramBounds.definitions.md#def-f93a12601bbb0e39)
- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.TriangularRealization.DiagonalFractions](TriangularProgramBounds.definitions.md#def-79fa41febc46eceb)
- [CodedSorting.SpecializedTriangular.finMatrix](TriangularProgramBounds.definitions.md#def-511dea50e5de3486)
- [CodedSorting.SpecializedTriangular.diagonalData._proof_20](TriangularProgramBounds.definitions.md#def-b75842e8d5f9a003)
- [CodedSorting.SpecializedTriangular.diagonalData._proof_23](TriangularProgramBounds.definitions.md#def-12bbb509600b9c0e)
- [CodedSorting.TriangularRealization.DiagonalFractions.mk](TriangularProgramBounds.definitions.md#def-1a8c8ae4b2260864)
- [CodedSorting.SpecializedTriangular.diagonalData._proof_21](TriangularProgramBounds.definitions.md#def-365fe971f7f64540)
- [CodedSorting.SpecializedTriangular.instNeZeroNatHPowPrimeFin](TriangularProgramBounds.definitions.md#def-ea5bc2ef5a27174c)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Rat.instOfNat`, `Rat.num`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Rat.den`, `Monoid.toNatPow`, `Ne`, `Fin.fintype`, `Fintype`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-acd6502a53466c8f"></a>
## `CodedSorting.SpecializedTriangular.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L332)

**类型**

```lean
{Family : Type u_1} →
  [inst : Fintype Family] →
    {m : ℕ} →
      {A : Family → Matrix (Fin m) (Fin m) ℚ} →
        (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
          (f : ℕ) →
            (k : Family) → (∀ (i : Fin m), A k i i ≠ 0) → List (CodedSorting.ScanProgram.Pass ((F.prime ^ f) ^ m))
```

**定义**

```lean
fun {Family} [Fintype Family] {m} {A} F f k hdiag =>
  CodedSorting.TriangularRealization.descendingPasses (CodedSorting.SpecializedTriangular.finMatrix F f k)
    (CodedSorting.SpecializedTriangular.diagonalData F f k hdiag) ⋯ m ⋯
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.SpecializedTriangular.program._proof_24](TriangularProgramBounds.definitions.md#def-71f8b08d5c9fda2d)
- [CodedSorting.TriangularRealization.descendingPasses](TriangularProgramBounds.definitions.md#def-8c352dae51e9ba3c)
- [CodedSorting.SpecializedTriangular.finMatrix](TriangularProgramBounds.definitions.md#def-511dea50e5de3486)
- [CodedSorting.SpecializedTriangular.diagonalData](TriangularProgramBounds.definitions.md#def-bac7c07fc28705ba)
- [CodedSorting.SpecializedTriangular.instNeZeroNatHPowPrimeFin](TriangularProgramBounds.definitions.md#def-ea5bc2ef5a27174c)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Rat.instOfNat`, `Nat.le_refl`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `Ne`, `Fin.fintype`, `List`, `Fintype`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-e4a1228e15e962f1"></a>
## `CodedSorting.SpecializedTriangular.fixedConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L337)

**类型**

```lean
{Family : Type u_1} → {m : ℕ} → {A : Family → Matrix (Fin m) (Fin m) ℚ} → Family → ℕ
```

**定义**

```lean
fun {Family} {m} {A} k => m * ∑ i, (2 * (A k i i).num.natAbs + 2 * (A k i i).den + 42)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Rat.num`, `HMul.hMul`, `Finset.univ`, `Matrix`, `Rat`, `Rat.den`, `instMulNat`, `instOfNatNat`, `Fin.fintype`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Int.natAbs`, `instAddNat`, `Nat.instAddCommMonoid`, `OfNat.ofNat`, `Fin`, `Finset.sum`, `instHMul`

<a id="def-3de4dcc6b330feb7"></a>
## `CodedSorting.GlobalTriangular.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TriangularProgramBounds.lean#L387)

**类型**

```lean
{Family : Type u_1} →
  [inst : Fintype Family] →
    {m : ℕ} →
      {A : Family → Matrix (Fin m) (Fin m) ℚ} →
        (F : CodedSorting.MatrixFactorization.SpecializedFamily A) →
          (f : ℕ) →
            (k : Family) →
              (∀ (i : Fin m), A k i i ≠ 0) →
                (P S : ℕ) → 0 < S → List (CodedSorting.ScanProgram.Pass (P * ((F.prime ^ f) ^ m * S)))
```

**定义**

```lean
fun {Family} [Fintype Family] {m} {A} F f k hdiag P S hS =>
  CodedSorting.ScanProgramLift.liftProgram P S hS (CodedSorting.SpecializedTriangular.program F f k hdiag)
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.ScanProgramLift.liftProgram](../../Shared/Programs/ScanProgramLift.definitions.md#def-08274d7795e99cb8)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.SpecializedTriangular.program](TriangularProgramBounds.definitions.md#def-acd6502a53466c8f)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Rat.instOfNat`, `HMul.hMul`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `Ne`, `instMulNat`, `instOfNatNat`, `Fin.fintype`, `List`, `Fintype`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-f93a12601bbb0e39"></a>
## `CodedSorting.SpecializedTriangular.diagonalData._proof_19`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {Family : Type u_1} {m : ℕ} {A : Family → Matrix (Fin m) (Fin m) ℚ} (k : Family),
  (∀ (i : Fin m), A k i i ≠ 0) → ∀ (i : Fin m), (A k i i).num ≠ 0
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Rat.instOfNat`, `Rat.num`, `Matrix`, `Rat`, `Ne`, `Int`, `instOfNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-b75842e8d5f9a003"></a>
## `CodedSorting.SpecializedTriangular.diagonalData._proof_20`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {Family : Type u_1} {m : ℕ} {A : Family → Matrix (Fin m) (Fin m) ℚ} (k : Family) (i : Fin m), 0 < (A k i i).den
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Matrix`, `Rat`, `Rat.den`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-365fe971f7f64540"></a>
## `CodedSorting.SpecializedTriangular.diagonalData._proof_21`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {Family : Type u_1} [inst : Fintype Family] {m : ℕ} {A : Family → Matrix (Fin m) (Fin m) ℚ}
  (F : CodedSorting.MatrixFactorization.SpecializedFamily A) (f : ℕ) (k : Family),
  (∀ (i : Fin m), A k i i ≠ 0) → ∀ (i : Fin m), (A k i i).num.natAbs.Coprime (F.prime ^ f)
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Rat.instOfNat`, `Nat.Coprime`, `Rat.num`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Monoid.toNatPow`, `Ne`, `Fin.fintype`, `Fintype`, `HPow.hPow`, `Nat`, `Int.natAbs`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-d9e3738ef8fb090c"></a>
## `CodedSorting.SpecializedTriangular.diagonalData._proof_22`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {Family : Type u_1} [inst : Fintype Family] {m : ℕ} {A : Family → Matrix (Fin m) (Fin m) ℚ}
  (F : CodedSorting.MatrixFactorization.SpecializedFamily A) (f : ℕ) (k : Family) (i : Fin m),
  (A k i i).den.Coprime (F.prime ^ f)
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Nat.Coprime`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Rat.den`, `Monoid.toNatPow`, `Fin.fintype`, `Fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-12bbb509600b9c0e"></a>
## `CodedSorting.SpecializedTriangular.diagonalData._proof_23`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {Family : Type u_1} [inst : Fintype Family] {m : ℕ} {A : Family → Matrix (Fin m) (Fin m) ℚ}
  (F : CodedSorting.MatrixFactorization.SpecializedFamily A) (f : ℕ) (k : Family) (i : Fin m),
  ↑(A k i i).den * CodedSorting.SpecializedTriangular.finMatrix F f k i i = ↑(A k i i).num
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.SpecializedTriangular.finMatrix](TriangularProgramBounds.definitions.md#def-511dea50e5de3486)
- [CodedSorting.SpecializedTriangular.instNeZeroNatHPowPrimeFin](TriangularProgramBounds.definitions.md#def-ea5bc2ef5a27174c)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Int.cast`, `Fin.instNatCast`, `Rat.num`, `HMul.hMul`, `Fin.instCommRing`, `Matrix`, `Nat.instMonoid`, `Rat`, `instDecidableEqFin`, `Rat.den`, `Monoid.toNatPow`, `AddGroupWithOne.toIntCast`, `Nat.cast`, `Fin.fintype`, `Fintype`, `HPow.hPow`, `Fin.instMul`, `Nat`, `instHPow`, `CommRing.toRing`, `Fin`, `Eq`, `Ring.toAddGroupWithOne`, `instHMul`

<a id="def-71f8b08d5c9fda2d"></a>
## `CodedSorting.SpecializedTriangular.program._proof_24`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {Family : Type u_1} {m : ℕ} {A : Family → Matrix (Fin m) (Fin m) ℚ}
  (F : CodedSorting.MatrixFactorization.SpecializedFamily A) (f : ℕ), 0 < F.prime ^ f
```

**继续展开**

- [CodedSorting.MatrixFactorization.SpecializedFamily](MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](MatrixFactorization.definitions.md#def-5af30279750b8d0f)

**基础库名称**

`Preorder.toLT`, `Matrix`, `Rat`, `PartialOrder.toPreorder`, `instDecidableEqFin`, `Monoid.toNatPow`, `Fin.fintype`, `Nat.instMonoidWithZero`, `MonoidWithZero.toMulZeroOneClass`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instPartialOrder`, `Zero.toOfNat0`, `instHPow`, `MulZeroOneClass.toMulZeroClass`, `OfNat.ofNat`, `Fin`, `MonoidWithZero.toMonoid`, `MulZeroClass.toZero`

<a id="def-0ac2f985e1849e14"></a>
## `CodedSorting.TriangularRealization.addPass._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q : ℕ} (i : Fin m) (offset : (Fin m → Fin Q) → Fin Q),
  CodedSorting.TriangularStreams.PrefixDependent i offset →
    ∀ (x y : Fin m → Fin Q),
      (∀ j < i, x j = y j) →
        CodedSorting.AffineStreams.additionEquiv (offset x) = CodedSorting.AffineStreams.additionEquiv (offset y)
```

**继续展开**

- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)
- [CodedSorting.AffineStreams.additionEquiv](AffineStreams.definitions.md#def-7c94b054256195c1)

**基础库名称**

`Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`

<a id="def-98b2da83309dc2e6"></a>
## `CodedSorting.TriangularRealization.addPass._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q : ℕ} (i : Fin m) (offset : (Fin m → Fin Q) → Fin Q),
  CodedSorting.TriangularStreams.PrefixDependent i offset →
    ∀ (x y : Fin m → Fin Q),
      (∀ j < i, x j = y j) →
        CodedSorting.SequentialArithmetic.additionRun (offset x) =
          CodedSorting.SequentialArithmetic.additionRun (offset y)
```

**继续展开**

- [CodedSorting.SequentialArithmetic.additionRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-4958ad02f45d9028)
- [CodedSorting.TriangularStreams.PrefixDependent](TriangularStreams.definitions.md#def-d875f44a4522e0e7)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTFin`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-578fdc9844347671"></a>
## `CodedSorting.TriangularRealization.addPass._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q : ℕ} (offset : (Fin m → Fin Q) → Fin Q) (x : Fin m → Fin Q) (a b : Fin Q),
  a < b →
    CodedSorting.SequentialArithmetic.additionRun (offset x) a =
        CodedSorting.SequentialArithmetic.additionRun (offset x) b →
      CodedSorting.SequentialArithmetic.addOffset (offset x) a <
        CodedSorting.SequentialArithmetic.addOffset (offset x) b
```

**继续展开**

- [CodedSorting.SequentialArithmetic.additionRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-4958ad02f45d9028)
- [CodedSorting.SequentialArithmetic.addOffset](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-1af292012b811a2b)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTFin`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-5b75aae844104c97"></a>
## `CodedSorting.TriangularRealization.descendingPasses._proof_17`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m : ℕ} {Q : ℕ} (n : ℕ), n + 1 ≤ m → n < m
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-03b012757a1e8220"></a>
## `CodedSorting.TriangularRealization.descendingPasses._proof_18`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m : ℕ} {Q : ℕ} (n : ℕ), n + 1 ≤ m → n ≤ m
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-3152216ad6759484"></a>
## `CodedSorting.TriangularRealization.descendingPasses.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TriangularProgramBounds.lean)

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

<a id="def-d6a48b8d00c48d64"></a>
## `CodedSorting.TriangularRealization.inverseMultiplyPass._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q a : ℕ} (hQ : 0 < Q) (hc : a.Coprime Q) (i : Fin m) (x x_1 : Fin m → Fin Q),
  (∀ j < i, x j = x_1 j) →
    Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc) =
      Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiplicationEquiv](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-347eea4112933180)

**基础库名称**

`Nat.Coprime`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-fcddb57ad7d3786d"></a>
## `CodedSorting.TriangularRealization.inverseMultiplyPass._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q a : ℕ} (ha : 0 < a) (hQ : 0 < Q) (hc : a.Coprime Q) (i : Fin m) (x x_1 : Fin m → Fin Q),
  (∀ j < i, x j = x_1 j) →
    (fun x =>
        CodedSorting.SequentialArithmetic.multiplicationRun ha hQ
          ((Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)) x)) =
      fun x =>
      CodedSorting.SequentialArithmetic.multiplicationRun ha hQ
        ((Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)) x)
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiplicationEquiv](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-347eea4112933180)
- [CodedSorting.SequentialArithmetic.multiplicationRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-90e6aa00b76f15a7)

**基础库名称**

`Nat.Coprime`, `Equiv.instFunLike`, `Equiv`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-781fd5f72d8077a1"></a>
## `CodedSorting.TriangularRealization.inverseMultiplyPass._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q a : ℕ} (ha : 0 < a) (hQ : 0 < Q) (hc : a.Coprime Q),
  (Fin m → Fin Q) →
    ∀ (x y : Fin Q),
      x < y →
        CodedSorting.SequentialArithmetic.multiplicationRun ha hQ
              ((Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)) x) =
            CodedSorting.SequentialArithmetic.multiplicationRun ha hQ
              ((Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)) y) →
          (Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)) x <
            (Equiv.symm (CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc)) y
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiplicationEquiv](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-347eea4112933180)
- [CodedSorting.SequentialArithmetic.multiplicationRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-90e6aa00b76f15a7)

**基础库名称**

`Nat.Coprime`, `Equiv.instFunLike`, `Equiv`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-f890774d66232700"></a>
## `CodedSorting.TriangularRealization.multiplyPass._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q a : ℕ} (hQ : 0 < Q) (hc : a.Coprime Q) (i : Fin m) (x x_1 : Fin m → Fin Q),
  (∀ j < i, x j = x_1 j) →
    CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc =
      CodedSorting.SequentialArithmetic.multiplicationEquiv hQ hc
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiplicationEquiv](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-347eea4112933180)

**基础库名称**

`Nat.Coprime`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-7a2609d565e41245"></a>
## `CodedSorting.TriangularRealization.multiplyPass._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q a : ℕ} (ha : 0 < a) (hQ : 0 < Q) (i : Fin m) (x x_1 : Fin m → Fin Q),
  (∀ j < i, x j = x_1 j) →
    CodedSorting.SequentialArithmetic.multiplicationRun ha hQ =
      CodedSorting.SequentialArithmetic.multiplicationRun ha hQ
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiplicationRun](../../Shared/Indexing/SequentialArithmetic.definitions.md#def-90e6aa00b76f15a7)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-6aa0361c440772bc"></a>
## `CodedSorting.TriangularRealization.negationPasses._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q : ℕ} [inst : NeZero Q] (i : Fin m) (x x_1 : Fin m → Fin Q), (∀ j < i, x j = x_1 j) → 1 = 1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMulZeroClass`, `Fin.instOfNat`, `Nat`, `LT.lt`, `instLTFin`, `NeZero`, `OfNat.ofNat`, `Fin`, `Eq`, `MulZeroClass.toZero`

<a id="def-2e290fb271cf455e"></a>
## `CodedSorting.TriangularRealization.reflectionPasses._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q : ℕ} (i : Fin m), 0 < Q → 0 < Q ^ Fintype.card (CodedSorting.SingleCoordinate.After i)
```

**继续展开**

- [CodedSorting.SingleCoordinate.After](../../Interchange/Framework/Fields/BinaryPaddingScan.definitions.md#def-61b672af3baaa6b5)

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `Subtype.fintype`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Fintype.card`, `instOfNatNat`, `Fin.fintype`, `Nat.instMonoidWithZero`, `Fin.instLinearOrder`, `Fin.decLt`, `MonoidWithZero.toMulZeroOneClass`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instPartialOrder`, `Zero.toOfNat0`, `instHPow`, `instLTNat`, `MulZeroOneClass.toMulZeroClass`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `MonoidWithZero.toMonoid`, `MulZeroClass.toZero`, `Lattice.toSemilatticeInf`

<a id="def-476bf3c343a2fa1d"></a>
## `CodedSorting.TriangularRealization.reflectionPasses._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q : ℕ} (i : Fin m), CodedSorting.LexBlocks.PrefixCount Q i * Q * CodedSorting.LexBlocks.SuffixCount Q i = Q ^ m
```

**继续展开**

- [CodedSorting.LexBlocks.PrefixCount](../../Shared/Indexing/LexBlocks.definitions.md#def-b5dc0c1da80a1119)
- [CodedSorting.LexBlocks.SuffixCount](../../Shared/Indexing/LexBlocks.definitions.md#def-b586bdb106d39599)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`, `instHMul`

<a id="def-d5df8e3fbd687495"></a>
## `CodedSorting.TriangularRealization.reflectionPasses._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q : ℕ} (i : Fin m), 0 < Q → Q * CodedSorting.LexBlocks.SuffixCount Q i > 0
```

**继续展开**

- [CodedSorting.LexBlocks.SuffixCount](../../Shared/Indexing/LexBlocks.definitions.md#def-b586bdb106d39599)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `GT.gt`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-0f9fbf37703e1551"></a>
## `CodedSorting.TriangularRealization.rowPasses._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ {m Q : ℕ} [inst : NeZero Q] (A : Matrix (Fin m) (Fin m) (Fin Q)) (i : Fin m) (x y : Fin m → Fin Q),
  (∀ j < i, x j = y j) →
    CodedSorting.TriangularStreams.prefixOffset A i x = CodedSorting.TriangularStreams.prefixOffset A i y
```

**继续展开**

- [CodedSorting.TriangularStreams.prefixOffset](TriangularStreams.definitions.md#def-e0fb3e34cf712661)

**基础库名称**

`Nat.instMulZeroClass`, `Fin.instCommRing`, `Matrix`, `Nat`, `LT.lt`, `instLTFin`, `NeZero`, `Fin`, `Eq`, `MulZeroClass.toZero`

<a id="def-8838d14287988789"></a>
## `CodedSorting.TriangularRealization.signedMultiplyPasses._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TriangularProgramBounds.lean)

**类型**

```lean
∀ (z : ℤ), z ≠ 0 → 0 < z.natAbs
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Ne`, `instOfNatNat`, `Int`, `instOfNat`, `Nat`, `LT.lt`, `Int.natAbs`, `instLTNat`, `OfNat.ofNat`
