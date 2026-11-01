# RecordOperations 的定义

[源码](RecordOperations.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-cf0936beb1051bd4"></a>
## `CodedSorting.KeyRecordBits.recordBot`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L17)

**类型**

```lean
(w : ℕ) → OrderBot (CodedSorting.KeyRecordWords.Record w)
```

**定义**

```lean
fun w => { bot := CodedSorting.KeyRecordWords.Record.bottom, bot_le := ⋯ }
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.KeyRecordBits.recordBot._proof_1](RecordOperations.definitions.md#def-ff3b875631471c93)

**基础库名称**

`PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `OrderBot.mk`, `Nat`, `Bot.mk`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-d046cc432bab29e0"></a>
## `CodedSorting.KeyRecordBits.recordTop`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L23)

**类型**

```lean
(w : ℕ) → OrderTop (CodedSorting.KeyRecordWords.Record w)
```

**定义**

```lean
fun w => { top := CodedSorting.KeyRecordWords.Record.top, le_top := ⋯ }
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordTop._proof_2](RecordOperations.definitions.md#def-86536345184338d1)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.top](KeyRecordWords.definitions.md#def-dfff22d085934d4b)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)

**基础库名称**

`PartialOrder.toPreorder`, `Preorder.toLE`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Top.mk`, `OrderTop.mk`, `OrderTop`, `Nat`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-2f019ca7cff46224"></a>
## `CodedSorting.KeyRecordBits.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L29)

**类型**

```lean
(w : ℕ) → 2 ≤ w → CodedSorting.KeyRecordWords.Record w → Fin (3 * w) → CodedSorting.Circuit.Bit
```

**定义**

```lean
fun w hw r => (CodedSorting.BitWordPacking.blockBits 3 w) (CodedSorting.KeyRecordWords.encode w hw r)
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.BitWordPacking.blockBits](../Words/WordConvention.definitions.md#def-a9a13aad90fdf19b)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.KeyRecordWords.encode](KeyRecordWords.definitions.md#def-db8b85b6def9e34c)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-d97d98eb7adcb603"></a>
## `CodedSorting.CommonRecordProgram.Records`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L85)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → Type
```

**定义**

```lean
fun q n => Fin n → CodedSorting.KeyRecordWords.Record q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`, `Fin`

<a id="def-82da314eef6ab4d1"></a>
## `CodedSorting.CommonRecordProgram.bits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L87)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {n : ℕ} → CodedSorting.CommonRecordProgram.Records q n → Fin (n * (3 * q.w)) → CodedSorting.Circuit.Bit
```

**定义**

```lean
fun q {n} f i => CodedSorting.KeyRecordBits.code q.w ⋯ (f (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2
```

**继续展开**

- [CodedSorting.CommonRecordProgram.bits._proof_4](RecordOperations.definitions.md#def-46221c734e9f680d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.KeyRecordBits.code](RecordOperations.definitions.md#def-2f019ca7cff46224)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `instOfNatNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-f604a7bec7bf567e"></a>
## `CodedSorting.CommonRecordProgram.Encoded`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L96)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {n : ℕ} → CodedSorting.CommonLeafProgram.Disk q → ℕ → CodedSorting.CommonRecordProgram.Records q n → Prop
```

**定义**

```lean
fun q {n} disk base f =>
  ∀ (i : Fin (n * (3 * q.w))),
    CodedSorting.CommonPermutationPairs.readBit q disk base ↑i = CodedSorting.CommonRecordProgram.bits q f i
```

**继续展开**

- [CodedSorting.CommonRecordProgram.bits](RecordOperations.definitions.md#def-82da314eef6ab4d1)
- [CodedSorting.CommonLeafProgram.Disk](../Memory/Leaf/Program.definitions.md#def-e343337119cf665f)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonPermutationPairs.readBit](../../Interchange/Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Nat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-ea265f1c6d0c5e70"></a>
## `CodedSorting.CommonRecordProgram.recordBlocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L111)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n => CodedSorting.CommonPermutationPairs.count q (n * (3 * q.w))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-a99dc947411e91e2"></a>
## `CodedSorting.CommonRecordProgram.Program`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](RecordOperations.lean#L113)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) →
    ℕ → ℕ → ℕ → (CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n) → Type
```

**继续展开**

- [CodedSorting.CommonRecordProgram.Program.mk](RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Nat`

<a id="def-887b49862da8c4f3"></a>
## `CodedSorting.CommonRecordProgram.Program.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](RecordOperations.lean#L113)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n source buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      (instructions : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
        (charge : ℕ) →
          (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
              CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
                CodedSorting.CommonRecordProgram.Encoded q
                  (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk source (F f)) →
            (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
                ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
                  ↑a < buffer ∨ limit ≤ ↑a →
                    (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk a = s.disk a) →
              (∀ i ∈ instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
                CodedSorting.CommonStaticSchedule.cost q instructions ≤ charge →
                  instructions.length ≤ charge → CodedSorting.CommonRecordProgram.Program q n source buffer limit F
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `List.length`

<a id="def-32d1da6b9bab0871"></a>
## `CodedSorting.CommonRecordProgram.Program.instructions`

读取 `CodedSorting.CommonRecordProgram.Program` 的 `instructions` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](RecordOperations.lean#L115)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n source buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      CodedSorting.CommonRecordProgram.Program q n source buffer limit F →
        List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q n source buffer limit F self => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`List`, `Nat`

<a id="def-ab509acf69c03316"></a>
## `CodedSorting.CommonRecordProgram.Program.charge`

读取 `CodedSorting.CommonRecordProgram.Program` 的 `charge` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](RecordOperations.lean#L116)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n source buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      CodedSorting.CommonRecordProgram.Program q n source buffer limit F → ℕ
```

**定义**

```lean
fun q n source buffer limit F self => self.2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Nat`

<a id="def-35824ef4d996ed98"></a>
## `CodedSorting.CommonRecordProgram.Program.correct`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean#L117)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n source buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (self : CodedSorting.CommonRecordProgram.Program q n source buffer limit F)
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    CodedSorting.CommonRecordProgram.Encoded q
      (CodedSorting.CommonStaticSchedule.executeRaw q self.instructions s).1.disk source (F f)
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Prod.fst`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-93f4dfd4226a6f19"></a>
## `CodedSorting.CommonRecordProgram.Program.safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean#L123)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n source buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (self : CodedSorting.CommonRecordProgram.Program q n source buffer limit F),
  ∀ i ∈ self.instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`

<a id="def-755ba98c8833d7fa"></a>
## `CodedSorting.CommonRecordProgram.Program.cost_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean#L124)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n source buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (self : CodedSorting.CommonRecordProgram.Program q n source buffer limit F),
  CodedSorting.CommonStaticSchedule.cost q self.instructions ≤ self.charge
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-7d40c8596cace851"></a>
## `CodedSorting.CommonRecordProgram.Program.length_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean#L125)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n source buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (self : CodedSorting.CommonRecordProgram.Program q n source buffer limit F), self.instructions.length ≤ self.charge
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`LE.le`, `instLENat`, `Nat`, `List.length`

<a id="def-92edf0926ce9eb39"></a>
## `CodedSorting.CommonRecordProgram.Program.changeFunction`

读取 `CodedSorting.CommonRecordProgram.Program` 的 `changeFunction` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](RecordOperations.lean#L164)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n source buffer limit : ℕ} →
    {F G : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      CodedSorting.CommonRecordProgram.Program q n source buffer limit F →
        F = G → CodedSorting.CommonRecordProgram.Program q n source buffer limit G
```

**定义**

```lean
fun {q} {n source buffer limit} {F G} p h => h ▸ p
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Eq.rec`, `Nat`, `Eq`

<a id="def-6080eee98895ec90"></a>
## `CodedSorting.CommonRecordPrefix.extendBottom`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L274)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m : ℕ} → CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m
```

**定义**

```lean
fun {q} {n m} f i => if hi : ↑i < n then f ⟨↑i, hi⟩ else CodedSorting.KeyRecordWords.Record.bottom
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.KeyRecordWords.Record.bottom](KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Fin.mk`, `Fin.val`, `dite`, `Nat`, `LT.lt`, `Nat.decLt`, `instLTNat`, `Fin`, `Not`

<a id="def-1ff13236813def56"></a>
## `CodedSorting.CommonRecordPrefix.restrictOutput`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L315)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m : ℕ} →
    n ≤ m →
      (CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m) →
        CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n
```

**定义**

```lean
fun {q} {n m} h F f i => F (CodedSorting.CommonRecordPrefix.extendBottom f) (Fin.castLE h i)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordPrefix.extendBottom](RecordOperations.definitions.md#def-6080eee98895ec90)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Fin.castLE`, `LE.le`, `instLENat`, `Nat`, `Fin`

<a id="def-ee3cf67e053976c4"></a>
## `CodedSorting.CommonRecordPrefix.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L319)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  Fin q.inventory.readers →
    {n : ℕ} →
      {m : ℕ} →
        {source : ℕ} →
          {buffer work limit : ℕ} →
            {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} →
              CodedSorting.CommonRecordProgram.Program q m buffer work limit F →
                List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} reader {n m source buffer work limit} {F} p =>
  CodedSorting.CommonFinitePadding.prefixCode q reader (n * (3 * q.w)) (m * (3 * q.w)) source buffer ++
      p.instructions ++
    CodedSorting.CommonRecursiveExchange.copyCode q reader (n * (3 * q.w)) buffer source
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecursiveExchange.copyCode](../../Interchange/Framework/Recursion/OuterCopyFrame.definitions.md#def-654a82544fb518ba)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonFinitePadding.prefixCode](../../Interchange/Framework/Memory/PaddedChunks.definitions.md#def-5437562fd5b33739)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `instHMul`

<a id="def-cf73107deb5a3f9e"></a>
## `CodedSorting.CommonRecordPrefix.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L325)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  Fin q.inventory.readers →
    {n m source buffer work limit : ℕ} →
      {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} →
        (h : n ≤ m) →
          CodedSorting.CommonRecordProgram.Program q m buffer work limit F →
            source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer →
              buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ work →
                work ≤ limit →
                  limit ≤ q.N ^ q.exponent →
                    CodedSorting.CommonRecordProgram.Program q n source buffer limit
                      (CodedSorting.CommonRecordPrefix.restrictOutput h F)
```

**定义**

```lean
fun {q} reader {n m source buffer work limit} {F} h p hs hw hwl hl =>
  { instructions := CodedSorting.CommonRecordPrefix.code reader p,
    charge :=
      12 * CodedSorting.CommonRecordProgram.recordBlocks q n + 3 * CodedSorting.CommonRecordProgram.recordBlocks q m +
        p.charge,
    correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRecordPrefix.program._proof_24](RecordOperations.definitions.md#def-0bceb946e742b211)
- [CodedSorting.CommonRecordPrefix.program._proof_21](RecordOperations.definitions.md#def-84bf8db5c776751f)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordProgram.Program.mk](RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.CommonRecordPrefix.code](RecordOperations.definitions.md#def-ee3cf67e053976c4)
- [CodedSorting.CommonRecordPrefix.program._proof_22](RecordOperations.definitions.md#def-c4f5444a985fc0ba)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordPrefix.program._proof_23](RecordOperations.definitions.md#def-8b17b51e56178e3c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordPrefix.restrictOutput](RecordOperations.definitions.md#def-1ff13236813def56)
- [CodedSorting.CommonRecordPrefix.program._proof_20](RecordOperations.definitions.md#def-9058051824452821)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-502e25cd25b52e28"></a>
## `CodedSorting.CommonRecordReindex.castRecords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L402)

**类型**

```lean
{α : Type u_1} → {n n' : ℕ} → n = n' → (Fin n → α) → Fin n' → α
```

**定义**

```lean
fun {α} {n n'} h f i => f ((finCongr h).symm i)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Equiv.instFunLike`, `finCongr`, `Equiv`, `Nat`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-5d0de92d31fd312b"></a>
## `CodedSorting.CommonRecordReindex.castFunction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L423)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {n n' : ℕ} →
    n = n' →
      (CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n) →
        CodedSorting.CommonRecordProgram.Records q n' → CodedSorting.CommonRecordProgram.Records q n'
```

**定义**

```lean
fun q {n n'} h F f =>
  CodedSorting.CommonRecordReindex.castRecords h (F (CodedSorting.CommonRecordReindex.castRecords ⋯ f))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Nat`, `Eq.symm`, `Eq`

<a id="def-2ef3a997d0144ffd"></a>
## `CodedSorting.CommonRecordReindex.castProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L427)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n n' source buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      CodedSorting.CommonRecordProgram.Program q n source buffer limit F →
        (h : n = n') →
          CodedSorting.CommonRecordProgram.Program q n' source buffer limit
            (CodedSorting.CommonRecordReindex.castFunction q h F)
```

**定义**

```lean
fun {q} {n n' source buffer limit} {F} p h =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRecordReindex.castProgram._proof_25](RecordOperations.definitions.md#def-8301ae536ca54466)
- [CodedSorting.CommonRecordProgram.Program.mk](RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.CommonRecordProgram.Program.cost_le](RecordOperations.definitions.md#def-755ba98c8833d7fa)
- [CodedSorting.CommonRecordProgram.Program.length_le](RecordOperations.definitions.md#def-7d40c8596cace851)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordReindex.castProgram._proof_26](RecordOperations.definitions.md#def-4f2f3c7c8e0473e0)
- [CodedSorting.CommonRecordProgram.Program.safe](RecordOperations.definitions.md#def-93f4dfd4226a6f19)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordReindex.castFunction](RecordOperations.definitions.md#def-5d0de92d31fd312b)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Nat`, `Eq`

<a id="def-0f2418ea3a290277"></a>
## `CodedSorting.CommonRecordInterval.EncodedAt`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecordOperations.lean#L469)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {n : ℕ} → CodedSorting.CommonLeafProgram.Disk q → ℕ → ℕ → CodedSorting.CommonRecordProgram.Records q n → Prop
```

**定义**

```lean
fun q {n} disk base O f =>
  ∀ (i : Fin n) (j : Fin 3),
    CodedSorting.CommonMarginTransform.wordAt q disk base (3 * O + ↑i * 3 + ↑j) =
      CodedSorting.KeyRecordWords.encode q.w ⋯ (f i) j
```

**继续展开**

- [CodedSorting.CommonRecordProgram.bits._proof_4](RecordOperations.definitions.md#def-46221c734e9f680d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafProgram.Disk](../Memory/Leaf/Program.definitions.md#def-e343337119cf665f)
- [CodedSorting.CommonMarginTransform.wordAt](../Memory/MarginTransform.definitions.md#def-cbb100c2961a0843)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.KeyRecordWords.encode](KeyRecordWords.definitions.md#def-db8b85b6def9e34c)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-2721e3818979b9a7"></a>
## `CodedSorting.CommonRecordInterval.Program`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](RecordOperations.lean#L499)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) →
    ℕ → ℕ → ℕ → ℕ → (CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n) → Type
```

**继续展开**

- [CodedSorting.CommonRecordInterval.Program.mk](RecordOperations.definitions.md#def-314c682c284969a9)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Nat`

<a id="def-314c682c284969a9"></a>
## `CodedSorting.CommonRecordInterval.Program.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](RecordOperations.lean#L499)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n base O buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      (instructions : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
        (charge : ℕ) →
          (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
              CodedSorting.CommonRecordInterval.EncodedAt q s.disk base O f →
                CodedSorting.CommonRecordInterval.EncodedAt q
                  (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk base O (F f)) →
            (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (j : ℕ),
                base + j / q.block < q.N ^ q.exponent →
                  j < 3 * O ∨ 3 * O + 3 * n ≤ j →
                    base + j / q.block < buffer ∨ limit ≤ base + j / q.block →
                      CodedSorting.CommonMarginTransform.wordAt q
                          (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk base j =
                        CodedSorting.CommonMarginTransform.wordAt q s.disk base j) →
              (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
                  ↑a < base + 3 * O / q.block ∨
                      base + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * n) ≤ ↑a →
                    ↑a < buffer ∨ limit ≤ ↑a →
                      (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk a = s.disk a) →
                (∀ i ∈ instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
                  CodedSorting.CommonStaticSchedule.cost q instructions ≤ charge →
                    instructions.length ≤ charge → CodedSorting.CommonRecordInterval.Program q n base O buffer limit F
```

**继续展开**

- [CodedSorting.CommonRecordInterval.Program](RecordOperations.definitions.md#def-2721e3818979b9a7)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonMarginTransform.wordAt](../Memory/MarginTransform.definitions.md#def-cbb100c2961a0843)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.PhysicalStreamCursor.blockCount](../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordInterval.EncodedAt](RecordOperations.definitions.md#def-0f2418ea3a290277)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `List.length`, `instHMul`

<a id="def-16d82df30e410adf"></a>
## `CodedSorting.CommonRecordInterval.Program.instructions`

读取 `CodedSorting.CommonRecordInterval.Program` 的 `instructions` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](RecordOperations.lean#L501)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n base O buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      CodedSorting.CommonRecordInterval.Program q n base O buffer limit F →
        List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q n base O buffer limit F self => self.1
```

**继续展开**

- [CodedSorting.CommonRecordInterval.Program](RecordOperations.definitions.md#def-2721e3818979b9a7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`List`, `Nat`

<a id="def-63452802ff71011d"></a>
## `CodedSorting.CommonRecordInterval.Program.charge`

读取 `CodedSorting.CommonRecordInterval.Program` 的 `charge` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](RecordOperations.lean#L502)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n base O buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      CodedSorting.CommonRecordInterval.Program q n base O buffer limit F → ℕ
```

**定义**

```lean
fun q n base O buffer limit F self => self.2
```

**继续展开**

- [CodedSorting.CommonRecordInterval.Program](RecordOperations.definitions.md#def-2721e3818979b9a7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Nat`

<a id="def-9058051824452821"></a>
## `CodedSorting.CommonRecordPrefix.program._proof_20`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m} (h : n ≤ m)
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F),
  source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer →
    buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ work →
      work ≤ limit →
        limit ≤ q.N ^ q.exponent →
          ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
            CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
              CodedSorting.CommonRecordProgram.Encoded q
                (CodedSorting.CommonStaticSchedule.executeRaw q (CodedSorting.CommonRecordPrefix.code reader p)
                      s).1.disk
                source (CodedSorting.CommonRecordPrefix.restrictOutput h F f)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonRecordPrefix.code](RecordOperations.definitions.md#def-ee3cf67e053976c4)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordPrefix.restrictOutput](RecordOperations.definitions.md#def-1ff13236813def56)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Fin`

<a id="def-84bf8db5c776751f"></a>
## `CodedSorting.CommonRecordPrefix.program._proof_21`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m},
  n ≤ m →
    ∀ (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F),
      source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer →
        buffer + CodedSorting.CommonRecordProgram.recordBlocks q m ≤ work →
          work ≤ limit →
            limit ≤ q.N ^ q.exponent →
              ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
                ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
                  ↑a < buffer ∨ limit ≤ ↑a →
                    (CodedSorting.CommonStaticSchedule.executeRaw q (CodedSorting.CommonRecordPrefix.code reader p)
                              s).1.disk
                        a =
                      s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonRecordPrefix.code](RecordOperations.definitions.md#def-ee3cf67e053976c4)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-c4f5444a985fc0ba"></a>
## `CodedSorting.CommonRecordPrefix.program._proof_22`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m}
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F),
  ∀ i ∈ CodedSorting.CommonRecordPrefix.code reader p, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordPrefix.code](RecordOperations.definitions.md#def-ee3cf67e053976c4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`, `Fin`

<a id="def-8b17b51e56178e3c"></a>
## `CodedSorting.CommonRecordPrefix.program._proof_23`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m}
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F),
  CodedSorting.CommonStaticSchedule.cost q (CodedSorting.CommonRecordPrefix.code reader p) ≤
    12 * CodedSorting.CommonRecordProgram.recordBlocks q n + 3 * CodedSorting.CommonRecordProgram.recordBlocks q m +
      p.charge
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordPrefix.code](RecordOperations.definitions.md#def-ee3cf67e053976c4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-0bceb946e742b211"></a>
## `CodedSorting.CommonRecordPrefix.program._proof_24`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} (reader : Fin q.inventory.readers)
  {n m source buffer work limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q m}
  (p : CodedSorting.CommonRecordProgram.Program q m buffer work limit F),
  (CodedSorting.CommonRecordPrefix.code reader p).length ≤
    12 * CodedSorting.CommonRecordProgram.recordBlocks q n + 3 * CodedSorting.CommonRecordProgram.recordBlocks q m +
      p.charge
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordPrefix.code](RecordOperations.definitions.md#def-ee3cf67e053976c4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`

<a id="def-46221c734e9f680d"></a>
## `CodedSorting.CommonRecordProgram.bits._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), 2 ≤ q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-8301ae536ca54466"></a>
## `CodedSorting.CommonRecordReindex.castProgram._proof_25`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n n' source buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n source buffer limit F) (h : n = n')
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n'),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    CodedSorting.CommonRecordProgram.Encoded q (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk
      source (CodedSorting.CommonRecordReindex.castFunction q h F f)
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordReindex.castFunction](RecordOperations.definitions.md#def-5d0de92d31fd312b)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Prod.fst`, `HPow.hPow`, `Nat`, `instHPow`, `Eq`

<a id="def-4f2f3c7c8e0473e0"></a>
## `CodedSorting.CommonRecordReindex.castProgram._proof_26`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n n' source buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n source buffer limit F),
  n = n' →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
      ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n' ≤ ↑a →
        ↑a < buffer ∨ limit ≤ ↑a → (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-ff3b875631471c93"></a>
## `CodedSorting.KeyRecordBits.recordBot._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ (w : ℕ) (a : CodedSorting.KeyRecordWords.Record w), CodedSorting.KeyRecordWords.Record.bottom ≤ a
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)

**基础库名称**

`PartialOrder.toPreorder`, `Preorder.toLE`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `LE.le`, `Nat`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-86536345184338d1"></a>
## `CodedSorting.KeyRecordBits.recordTop._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RecordOperations.lean)

**类型**

```lean
∀ (w : ℕ) (a : CodedSorting.KeyRecordWords.Record w), a ≤ CodedSorting.KeyRecordWords.Record.top
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.top](KeyRecordWords.definitions.md#def-dfff22d085934d4b)
- [CodedSorting.ResidentLeafSort.recordOrder](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)

**基础库名称**

`PartialOrder.toPreorder`, `Preorder.toLE`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `LE.le`, `Nat`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`
