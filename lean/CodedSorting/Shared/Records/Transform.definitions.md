# Transform 的定义

[源码](Transform.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2835e8bed6afef06"></a>
## `CodedSorting.CommonRecordTransform.Stage`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Transform.lean#L14)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n m : ℕ) →
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            ℕ → ℕ → (CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m) → Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordTransform.Stage.mk](Transform.definitions.md#def-36774215a354885f)

**基础库名称**

`Nat`

<a id="def-36774215a354885f"></a>
## `CodedSorting.CommonRecordTransform.Stage.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Transform.lean#L14)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m source target origin original buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m} →
      (instructions : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
        (charge : ℕ) →
          (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
              CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
                CodedSorting.CommonRecordProgram.Encoded q
                  (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk target (F f)) →
            (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
                ↑a < origin ∨ origin + CodedSorting.CommonRecordProgram.recordBlocks q original ≤ ↑a →
                  ↑a < buffer ∨ limit ≤ ↑a →
                    (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk a = s.disk a) →
              (∀ i ∈ instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
                CodedSorting.CommonStaticSchedule.cost q instructions ≤ charge →
                  instructions.length ≤ charge →
                    CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
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
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `List.length`

<a id="def-5d637e030078e0b3"></a>
## `CodedSorting.CommonRecordTransform.Stage.instructions`

读取 `CodedSorting.CommonRecordTransform.Stage` 的 `instructions` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Transform.lean#L16)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m source target origin original buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m} →
      CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F →
        List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q n m source target origin original buffer limit F self => self.1
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`List`, `Nat`

<a id="def-30123232aa6eccd6"></a>
## `CodedSorting.CommonRecordTransform.Stage.charge`

读取 `CodedSorting.CommonRecordTransform.Stage` 的 `charge` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Transform.lean#L17)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m source target origin original buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m} →
      CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F → ℕ
```

**定义**

```lean
fun q n m source target origin original buffer limit F self => self.2
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Nat`

<a id="def-de12ae41a5e4352e"></a>
## `CodedSorting.CommonRecordTransform.Stage.correct`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean#L18)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n m source target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  (self : CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F)
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    CodedSorting.CommonRecordProgram.Encoded q
      (CodedSorting.CommonStaticSchedule.executeRaw q self.instructions s).1.disk target (F f)
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Prod.fst`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-67388f8d3c4d6698"></a>
## `CodedSorting.CommonRecordTransform.Stage.frame`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean#L20)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n m source target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  (self : CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F)
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < origin ∨ origin + CodedSorting.CommonRecordProgram.recordBlocks q original ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a → (CodedSorting.CommonStaticSchedule.executeRaw q self.instructions s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-af488cc4d0ab71ee"></a>
## `CodedSorting.CommonRecordTransform.Stage.safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean#L23)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n m source target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  (self : CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F),
  ∀ i ∈ self.instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`

<a id="def-250cffad06942118"></a>
## `CodedSorting.CommonRecordTransform.Stage.cost_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean#L24)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n m source target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  (self : CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F),
  CodedSorting.CommonStaticSchedule.cost q self.instructions ≤ self.charge
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordTransform.Stage.charge](Transform.definitions.md#def-30123232aa6eccd6)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-73bc93b8cc017efe"></a>
## `CodedSorting.CommonRecordTransform.Stage.length_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean#L25)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n m source target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  (self : CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F),
  self.instructions.length ≤ self.charge
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordTransform.Stage.charge](Transform.definitions.md#def-30123232aa6eccd6)

**基础库名称**

`LE.le`, `instLENat`, `Nat`, `List.length`

<a id="def-9ad94e264d94adcf"></a>
## `CodedSorting.CommonRecordTransform.Stage.append`

读取 `CodedSorting.CommonRecordTransform.Stage` 的 `append` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Transform.lean#L31)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m k source middle target origin original buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m} →
      {G : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q k} →
        CodedSorting.CommonRecordTransform.Stage q n m source middle origin original buffer limit F →
          CodedSorting.CommonRecordTransform.Stage q m k middle target origin original buffer limit G →
            CodedSorting.CommonRecordTransform.Stage q n k source target origin original buffer limit (G ∘ F)
```

**定义**

```lean
fun {q} {n m k source middle target origin original buffer limit} {F} {G} p r =>
  { instructions := p.instructions ++ r.instructions, charge := p.charge + r.charge, correct := ⋯, frame := ⋯,
    safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.append._proof_3](Transform.definitions.md#def-f50ca99146e34ac5)
- [CodedSorting.CommonRecordTransform.Stage.append._proof_5](Transform.definitions.md#def-a1bf60d5f39571d7)
- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordTransform.Stage.append._proof_2](Transform.definitions.md#def-6e1729c7954a2221)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordTransform.Stage.mk](Transform.definitions.md#def-36774215a354885f)
- [CodedSorting.CommonRecordTransform.Stage.charge](Transform.definitions.md#def-30123232aa6eccd6)
- [CodedSorting.CommonRecordTransform.Stage.append._proof_4](Transform.definitions.md#def-03ddca65e8943ee6)
- [CodedSorting.CommonRecordTransform.Stage.append._proof_1](Transform.definitions.md#def-8515a552e82279c1)

**基础库名称**

`Function.comp`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `HAppend.hAppend`

<a id="def-a7b739ca983554fe"></a>
## `CodedSorting.CommonRecordTransform.Stage.castOutput`

读取 `CodedSorting.CommonRecordTransform.Stage` 的 `castOutput` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Transform.lean#L51)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m source target origin original buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m} →
      {m' : ℕ} →
        CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F →
          (h : m = m') →
            CodedSorting.CommonRecordTransform.Stage q n m' source target origin original buffer limit
              (CodedSorting.CommonRecordReindex.castRecords h ∘ F)
```

**定义**

```lean
fun {q} {n m source target origin original buffer limit} {F} {m'} p h =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.length_le](Transform.definitions.md#def-73bc93b8cc017efe)
- [CodedSorting.CommonRecordTransform.Stage.safe](Transform.definitions.md#def-af488cc4d0ab71ee)
- [CodedSorting.CommonRecordTransform.Stage.castOutput._proof_6](Transform.definitions.md#def-675141e7ba72e152)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonRecordTransform.Stage.cost_le](Transform.definitions.md#def-250cffad06942118)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTransform.Stage.frame](Transform.definitions.md#def-67388f8d3c4d6698)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordTransform.Stage.mk](Transform.definitions.md#def-36774215a354885f)
- [CodedSorting.CommonRecordTransform.Stage.charge](Transform.definitions.md#def-30123232aa6eccd6)

**基础库名称**

`Function.comp`, `Nat`, `Fin`, `Eq`

<a id="def-9e60f1f0ebcc04a3"></a>
## `CodedSorting.CommonRecordTransform.Stage.changeFunction`

读取 `CodedSorting.CommonRecordTransform.Stage` 的 `changeFunction` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Transform.lean#L66)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n m source target origin original buffer limit : ℕ} →
    {F G : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m} →
      CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F →
        F = G → CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit G
```

**定义**

```lean
fun {q} {n m source target origin original buffer limit} {F G} p h => h ▸ p
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`Eq.rec`, `Nat`, `Eq`

<a id="def-405f8315e35261de"></a>
## `CodedSorting.CommonRecordTransform.Stage.toProgram`

读取 `CodedSorting.CommonRecordTransform.Stage` 的 `toProgram` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Transform.lean#L77)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {n source buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      CodedSorting.CommonRecordTransform.Stage q n n source source source n buffer limit F →
        CodedSorting.CommonRecordProgram.Program q n source buffer limit F
```

**定义**

```lean
fun {q} {n source buffer limit} {F} p =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.length_le](Transform.definitions.md#def-73bc93b8cc017efe)
- [CodedSorting.CommonRecordTransform.Stage.safe](Transform.definitions.md#def-af488cc4d0ab71ee)
- [CodedSorting.CommonRecordTransform.Stage.correct](Transform.definitions.md#def-de12ae41a5e4352e)
- [CodedSorting.CommonRecordProgram.Program.mk](RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonRecordTransform.Stage.cost_le](Transform.definitions.md#def-250cffad06942118)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTransform.Stage.frame](Transform.definitions.md#def-67388f8d3c4d6698)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordTransform.Stage.charge](Transform.definitions.md#def-30123232aa6eccd6)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Nat`

<a id="def-21e561adcb69c1e3"></a>
## `CodedSorting.CommonRecordTransform.workspaceProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Transform.lean#L92)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {n source work origin original buffer limit : ℕ} →
    {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n} →
      CodedSorting.CommonRecordProgram.Program q n source work limit F →
        buffer ≤ source →
          source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ limit →
            buffer ≤ work → CodedSorting.CommonRecordTransform.Stage q n n source source origin original buffer limit F
```

**定义**

```lean
fun q {n source work origin original buffer limit} {F} p hs he hw =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRecordTransform.workspaceProgram._proof_10](Transform.definitions.md#def-484a9c01b346d517)
- [CodedSorting.CommonRecordProgram.Program.cost_le](RecordOperations.definitions.md#def-755ba98c8833d7fa)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonRecordProgram.Program.length_le](RecordOperations.definitions.md#def-7d40c8596cace851)
- [CodedSorting.CommonRecordProgram.Program.correct](RecordOperations.definitions.md#def-35824ef4d996ed98)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Program.safe](RecordOperations.definitions.md#def-93f4dfd4226a6f19)
- [CodedSorting.CommonRecordProgram.Program.instructions](RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordTransform.Stage.mk](Transform.definitions.md#def-36774215a354885f)
- [CodedSorting.CommonRecordProgram.Program.charge](RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-ded405593deceff5"></a>
## `CodedSorting.CommonRecordTransform.margins`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Transform.lean#L118)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    {K : ℕ} →
      (L N R O source target origin original buffer limit : ℕ) →
        (hKN : O + N ≤ K) →
          CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O) →
            source + CodedSorting.CommonRecordProgram.recordBlocks q K ≤ q.N ^ q.exponent →
              source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * N)) ≤ q.N ^ q.exponent →
                target + CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R) ≤ q.N ^ q.exponent →
                  source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * N)) ≤ target ∨
                      target + CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R) ≤ source →
                    (∀ (a : Fin (q.N ^ q.exponent)),
                        ↑a < origin ∨ origin + CodedSorting.CommonRecordProgram.recordBlocks q original ≤ ↑a →
                          ↑a < buffer ∨ limit ≤ ↑a →
                            ↑a < target ∨ target + CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R) ≤ ↑a) →
                      CodedSorting.CommonRecordTransform.Stage q K (L + N + R) source target origin original buffer
                        limit (CodedSorting.CommonStaticMarginsRecords.margin L N R O hKN)
```

**定义**

```lean
fun q reader {K} L N R O source target origin original buffer limit hKN hshape hsource hs ht hsep hframe =>
  { instructions := CodedSorting.CommonStaticMargins.code q reader (3 * L) (3 * N) (3 * R) (3 * O) source target,
    charge := 3 * CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R), correct := ⋯, frame := ⋯, safe := ⋯,
    cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRecordTransform.margins._proof_13](Transform.definitions.md#def-70739c4a8f89b90d)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonStaticMargins.code](../Programs/Static/MarginsRecords.definitions.md#def-299c5b27906f0156)
- [CodedSorting.CommonRecordTransform.margins._proof_14](Transform.definitions.md#def-788f0671b8b5c2f0)
- [CodedSorting.PhysicalStreamCursor.blockCount](../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordTransform.margins._proof_12](Transform.definitions.md#def-6d524adeff1af3b0)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonRecordTransform.Stage.mk](Transform.definitions.md#def-36774215a354885f)
- [CodedSorting.CommonRecordTransform.margins._proof_15](Transform.definitions.md#def-fcfa3d81ddc373fc)
- [CodedSorting.CommonRecordTransform.margins._proof_11](Transform.definitions.md#def-3dfb858886856187)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-8515a552e82279c1"></a>
## `CodedSorting.CommonRecordTransform.Stage.append._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  {n m k source middle target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  {G : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q k}
  (p : CodedSorting.CommonRecordTransform.Stage q n m source middle origin original buffer limit F)
  (r : CodedSorting.CommonRecordTransform.Stage q m k middle target origin original buffer limit G)
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    CodedSorting.CommonRecordProgram.Encoded q
      (CodedSorting.CommonStaticSchedule.executeRaw q (p.instructions ++ r.instructions) s).1.disk target ((G ∘ F) f)
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Function.comp`, `Monoid.toNatPow`, `Prod.fst`, `instHAppendOfAppend`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `List.instAppend`, `HAppend.hAppend`

<a id="def-6e1729c7954a2221"></a>
## `CodedSorting.CommonRecordTransform.Stage.append._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  {n m k source middle target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  {G : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q k}
  (p : CodedSorting.CommonRecordTransform.Stage q n m source middle origin original buffer limit F)
  (r : CodedSorting.CommonRecordTransform.Stage q m k middle target origin original buffer limit G)
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < origin ∨ origin + CodedSorting.CommonRecordProgram.recordBlocks q original ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q (p.instructions ++ r.instructions) s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAppendOfAppend`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `List.instAppend`, `Fin`, `Eq`, `HAppend.hAppend`

<a id="def-f50ca99146e34ac5"></a>
## `CodedSorting.CommonRecordTransform.Stage.append._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  {n m k source middle target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  {G : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q k}
  (p : CodedSorting.CommonRecordTransform.Stage q n m source middle origin original buffer limit F)
  (r : CodedSorting.CommonRecordTransform.Stage q m k middle target origin original buffer limit G),
  ∀ i ∈ p.instructions ++ r.instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `instHAppendOfAppend`, `List`, `List.instMembership`, `Nat`, `List.instAppend`, `HAppend.hAppend`

<a id="def-03ddca65e8943ee6"></a>
## `CodedSorting.CommonRecordTransform.Stage.append._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  {n m k source middle target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  {G : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q k}
  (p : CodedSorting.CommonRecordTransform.Stage q n m source middle origin original buffer limit F)
  (r : CodedSorting.CommonRecordTransform.Stage q m k middle target origin original buffer limit G),
  CodedSorting.CommonStaticSchedule.cost q (p.instructions ++ r.instructions) ≤ p.charge + r.charge
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonRecordTransform.Stage.charge](Transform.definitions.md#def-30123232aa6eccd6)

**基础库名称**

`LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `HAppend.hAppend`

<a id="def-a1bf60d5f39571d7"></a>
## `CodedSorting.CommonRecordTransform.Stage.append._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  {n m k source middle target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m}
  {G : CodedSorting.CommonRecordProgram.Records q m → CodedSorting.CommonRecordProgram.Records q k}
  (p : CodedSorting.CommonRecordTransform.Stage q n m source middle origin original buffer limit F)
  (r : CodedSorting.CommonRecordTransform.Stage q m k middle target origin original buffer limit G),
  (p.instructions ++ r.instructions).length ≤ p.charge + r.charge
```

**继续展开**

- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonRecordTransform.Stage.charge](Transform.definitions.md#def-30123232aa6eccd6)

**基础库名称**

`LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `List.length`, `HAppend.hAppend`

<a id="def-675141e7ba72e152"></a>
## `CodedSorting.CommonRecordTransform.Stage.castOutput._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {n m source target origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q m} {m' : ℕ}
  (p : CodedSorting.CommonRecordTransform.Stage q n m source target origin original buffer limit F) (h : m = m')
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    CodedSorting.CommonRecordProgram.Encoded q (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk
      target (CodedSorting.CommonRecordReindex.castRecords h (F f))
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordTransform.Stage.instructions](Transform.definitions.md#def-5d637e030078e0b3)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonRecordTransform.Stage](Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordReindex.castRecords](RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Prod.fst`, `HPow.hPow`, `Nat`, `instHPow`, `Eq`

<a id="def-3dfb858886856187"></a>
## `CodedSorting.CommonRecordTransform.margins._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers) {K : ℕ}
  (L N R O source target : ℕ) (hKN : O + N ≤ K),
  CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O) →
    source + CodedSorting.CommonRecordProgram.recordBlocks q K ≤ q.N ^ q.exponent →
      source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * N)) ≤ q.N ^ q.exponent →
        target + CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R) ≤ q.N ^ q.exponent →
          source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * N)) ≤ target ∨
              target + CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R) ≤ source →
            ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q K),
              CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
                CodedSorting.CommonRecordProgram.Encoded q
                  (CodedSorting.CommonStaticSchedule.executeRaw q
                        (CodedSorting.CommonStaticMargins.code q reader (3 * L) (3 * N) (3 * R) (3 * O) source target)
                        s).1.disk
                  target (CodedSorting.CommonStaticMarginsRecords.margin L N R O hKN f)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonStaticMargins.code](../Programs/Static/MarginsRecords.definitions.md#def-299c5b27906f0156)
- [CodedSorting.PhysicalStreamCursor.blockCount](../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Records](RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticMarginsRecords.margin](../Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `Or`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-6d524adeff1af3b0"></a>
## `CodedSorting.CommonRecordTransform.margins._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (L N R O source target origin original buffer limit : ℕ),
  CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O) →
    source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * N)) ≤ q.N ^ q.exponent →
      target + CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R) ≤ q.N ^ q.exponent →
        source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * O + 3 * N)) ≤ target ∨
            target + CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R) ≤ source →
          (∀ (a : Fin (q.N ^ q.exponent)),
              ↑a < origin ∨ origin + CodedSorting.CommonRecordProgram.recordBlocks q original ≤ ↑a →
                ↑a < buffer ∨ limit ≤ ↑a →
                  ↑a < target ∨ target + CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R) ≤ ↑a) →
            ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
              ↑a < origin ∨ origin + CodedSorting.CommonRecordProgram.recordBlocks q original ≤ ↑a →
                ↑a < buffer ∨ limit ≤ ↑a →
                  (CodedSorting.CommonStaticSchedule.executeRaw q
                            (CodedSorting.CommonStaticMargins.code q reader (3 * L) (3 * N) (3 * R) (3 * O) source
                              target)
                            s).1.disk
                      a =
                    s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonStaticMargins.code](../Programs/Static/MarginsRecords.definitions.md#def-299c5b27906f0156)
- [CodedSorting.PhysicalStreamCursor.blockCount](../Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonLeafProgram.Machine](../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-70739c4a8f89b90d"></a>
## `CodedSorting.CommonRecordTransform.margins._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (L N R O source target : ℕ),
  ∀ i ∈ CodedSorting.CommonStaticMargins.code q reader (3 * L) (3 * N) (3 * R) (3 * O) source target,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonStaticMargins.code](../Programs/Static/MarginsRecords.definitions.md#def-299c5b27906f0156)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`HMul.hMul`, `Membership.mem`, `instMulNat`, `instOfNatNat`, `List`, `List.instMembership`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-788f0671b8b5c2f0"></a>
## `CodedSorting.CommonRecordTransform.margins._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (L N R O source target : ℕ),
  CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O) →
    CodedSorting.CommonStaticSchedule.cost q
        (CodedSorting.CommonStaticMargins.code q reader (3 * L) (3 * N) (3 * R) (3 * O) source target) ≤
      3 * CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonStaticMargins.code](../Programs/Static/MarginsRecords.definitions.md#def-299c5b27906f0156)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.cost](../Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-fcfa3d81ddc373fc"></a>
## `CodedSorting.CommonRecordTransform.margins._proof_15`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (L N R O source target : ℕ),
  CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O) →
    (CodedSorting.CommonStaticMargins.code q reader (3 * L) (3 * N) (3 * R) (3 * O) source target).length ≤
      3 * CodedSorting.CommonRecordProgram.recordBlocks q (L + N + R)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonStaticMargins.ShapeFits](../Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRecordProgram.recordBlocks](RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonStaticMargins.code](../Programs/Static/MarginsRecords.definitions.md#def-299c5b27906f0156)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`

<a id="def-484a9c01b346d517"></a>
## `CodedSorting.CommonRecordTransform.workspaceProgram._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Transform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {n source work origin original buffer limit : ℕ}
  {F : CodedSorting.CommonRecordProgram.Records q n → CodedSorting.CommonRecordProgram.Records q n}
  (p : CodedSorting.CommonRecordProgram.Program q n source work limit F),
  buffer ≤ source →
    source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ limit →
      buffer ≤ work →
        ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
          ↑a < origin ∨ origin + CodedSorting.CommonRecordProgram.recordBlocks q original ≤ ↑a →
            ↑a < buffer ∨ limit ≤ ↑a →
              (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk a = s.disk a
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
