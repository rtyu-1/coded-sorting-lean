# ExchangeShapeProgram 的定义

[源码](ExchangeShapeProgram.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-fd13f4ef35da2a03"></a>
## `CodedSorting.CommonFinitePermutation.Program`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ExchangeShapeProgram.lean#L14)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → (V : ℕ) → ℕ → ℕ → ℕ → Equiv.Perm (Fin V) → Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.mk](ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)

**基础库名称**

`Equiv.Perm`, `Nat`, `Fin`

<a id="def-9d0f3517055893f6"></a>
## `CodedSorting.CommonFinitePermutation.Program.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ExchangeShapeProgram.lean#L14)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {V source buffer limit : ℕ} →
    {π : Equiv.Perm (Fin V)} →
      (instructions : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
        (charge : ℕ) →
          (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin V),
              CodedSorting.CommonPermutationPairs.readBit q
                  (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk source ↑y =
                CodedSorting.CommonPermutationPairs.readBit q s.disk source ↑(π y)) →
            (∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
                ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q V ≤ ↑a →
                  ↑a < buffer ∨ limit ≤ ↑a →
                    (CodedSorting.CommonStaticSchedule.executeRaw q instructions s).1.disk a = s.disk a) →
              (∀ i ∈ instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i) →
                CodedSorting.CommonStaticSchedule.cost q instructions ≤ charge →
                  instructions.length ≤ charge → CodedSorting.CommonFinitePermutation.Program q V source buffer limit π
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `List.length`, `DFunLike.coe`

<a id="def-5733429a20219ee2"></a>
## `CodedSorting.CommonFinitePermutation.Program.instructions`

读取 `CodedSorting.CommonFinitePermutation.Program` 的 `instructions` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeShapeProgram.lean#L16)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {V source buffer limit : ℕ} →
    {π : Equiv.Perm (Fin V)} →
      CodedSorting.CommonFinitePermutation.Program q V source buffer limit π →
        List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q V source buffer limit π self => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)

**基础库名称**

`List`, `Equiv.Perm`, `Nat`, `Fin`

<a id="def-ea781d269aea8c1c"></a>
## `CodedSorting.CommonFinitePermutation.Program.charge`

读取 `CodedSorting.CommonFinitePermutation.Program` 的 `charge` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeShapeProgram.lean#L17)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {V source buffer limit : ℕ} →
    {π : Equiv.Perm (Fin V)} → CodedSorting.CommonFinitePermutation.Program q V source buffer limit π → ℕ
```

**定义**

```lean
fun q V source buffer limit π self => self.2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)

**基础库名称**

`Equiv.Perm`, `Nat`, `Fin`

<a id="def-daa50b29624216d4"></a>
## `CodedSorting.CommonFinitePermutation.Program.frame`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean#L21)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π : Equiv.Perm (Fin V)}
  (self : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π)
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q V ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a → (CodedSorting.CommonStaticSchedule.executeRaw q self.instructions s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-942392eb0d48d54c"></a>
## `CodedSorting.CommonFinitePermutation.Program.safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean#L25)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π : Equiv.Perm (Fin V)}
  (self : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π),
  ∀ i ∈ self.instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Equiv.Perm`, `Nat`, `Fin`

<a id="def-710865af16bddbfe"></a>
## `CodedSorting.CommonFinitePermutation.Program.cost_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean#L26)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π : Equiv.Perm (Fin V)}
  (self : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π),
  CodedSorting.CommonStaticSchedule.cost q self.instructions ≤ self.charge
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`LE.le`, `instLENat`, `Equiv.Perm`, `Nat`, `Fin`

<a id="def-b69e1050814d5489"></a>
## `CodedSorting.CommonFinitePermutation.Program.length_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean#L27)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π : Equiv.Perm (Fin V)}
  (self : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π),
  self.instructions.length ≤ self.charge
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`LE.le`, `instLENat`, `Equiv.Perm`, `Nat`, `Fin`, `List.length`

<a id="def-3c75e77e76e9a63a"></a>
## `CodedSorting.CommonFinitePermutation.Program.identity`

读取 `CodedSorting.CommonFinitePermutation.Program` 的 `identity` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeShapeProgram.lean#L33)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (V source buffer limit : ℕ) →
    CodedSorting.CommonFinitePermutation.Program q V source buffer limit (Equiv.refl (Fin V))
```

**定义**

```lean
fun q V source buffer limit =>
  { instructions := [], charge := 0, correct := ⋯, frame := ⋯, safe := ⋯,
    cost_le := CodedSorting.CommonFinitePermutation.Program.identity._proof_4,
    length_le := CodedSorting.CommonFinitePermutation.Program.identity._proof_4 }
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.identity._proof_3](ExchangeShapeProgram.definitions.md#def-848fd32c60cbb8bc)
- [CodedSorting.CommonFinitePermutation.Program.identity._proof_1](ExchangeShapeProgram.definitions.md#def-fd8bd7030373bd6b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.mk](ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonFinitePermutation.Program.identity._proof_4](ExchangeShapeProgram.definitions.md#def-dc56baee2084b67a)
- [CodedSorting.CommonFinitePermutation.Program.identity._proof_2](ExchangeShapeProgram.definitions.md#def-c63750994ca0e215)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `List.nil`

<a id="def-91ea532bb04faf9e"></a>
## `CodedSorting.CommonFinitePermutation.Program.append`

读取 `CodedSorting.CommonFinitePermutation.Program` 的 `append` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeShapeProgram.lean#L43)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {V source buffer limit : ℕ} →
    {π₁ π₂ : Equiv.Perm (Fin V)} →
      CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₁ →
        CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₂ →
          CodedSorting.CommonFinitePermutation.Program q V source buffer limit (Equiv.trans π₂ π₁)
```

**定义**

```lean
fun {q} {V source buffer limit} {π₁ π₂} p₁ p₂ =>
  { instructions := p₁.instructions ++ p₂.instructions, charge := p₁.charge + p₂.charge, correct := ⋯, frame := ⋯,
    safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.append._proof_5](ExchangeShapeProgram.definitions.md#def-cdb83d33cd0515d0)
- [CodedSorting.CommonFinitePermutation.Program.append._proof_9](ExchangeShapeProgram.definitions.md#def-ea83285082e2fc21)
- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonFinitePermutation.Program.append._proof_7](ExchangeShapeProgram.definitions.md#def-0b8d9858f264567d)
- [CodedSorting.CommonFinitePermutation.Program.append._proof_8](ExchangeShapeProgram.definitions.md#def-11bdf95106cb41ad)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.append._proof_6](ExchangeShapeProgram.definitions.md#def-763d998f6060f8b0)
- [CodedSorting.CommonFinitePermutation.Program.mk](ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)

**基础库名称**

`Equiv.trans`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-abb56e7c683c1f81"></a>
## `CodedSorting.CommonFinitePermutation.Program.changePermutation`

读取 `CodedSorting.CommonFinitePermutation.Program` 的 `changePermutation` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeShapeProgram.lean#L67)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {V source buffer limit : ℕ} →
    {π π' : Equiv.Perm (Fin V)} →
      CodedSorting.CommonFinitePermutation.Program q V source buffer limit π →
        π = π' → CodedSorting.CommonFinitePermutation.Program q V source buffer limit π'
```

**定义**

```lean
fun {q} {V source buffer limit} {π π'} p h => h ▸ p
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)

**基础库名称**

`Eq.rec`, `Equiv.Perm`, `Nat`, `Fin`, `Eq`

<a id="def-011d8c0416a63718"></a>
## `CodedSorting.CommonFinitePermutation.Program.castVolume`

读取 `CodedSorting.CommonFinitePermutation.Program` 的 `castVolume` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeShapeProgram.lean#L70)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {V V' source buffer limit : ℕ} →
    {π : Equiv.Perm (Fin V)} →
      CodedSorting.CommonFinitePermutation.Program q V source buffer limit π →
        (h : V = V') →
          CodedSorting.CommonFinitePermutation.Program q V' source buffer limit
            ((finCongr h).symm.trans (Equiv.trans π (finCongr h)))
```

**定义**

```lean
fun {q} {V V' source buffer limit} {π} p h =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.castVolume._proof_11](ExchangeShapeProgram.definitions.md#def-131c1466679709a1)
- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonFinitePermutation.Program.length_le](ExchangeShapeProgram.definitions.md#def-b69e1050814d5489)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.safe](ExchangeShapeProgram.definitions.md#def-942392eb0d48d54c)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.mk](ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonFinitePermutation.Program.castVolume._proof_10](ExchangeShapeProgram.definitions.md#def-88d74922e663c950)
- [CodedSorting.CommonFinitePermutation.Program.cost_le](ExchangeShapeProgram.definitions.md#def-710865af16bddbfe)

**基础库名称**

`Equiv.trans`, `finCongr`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `Eq`

<a id="def-996aff3a413a714f"></a>
## `CodedSorting.CommonExchangeShapeProgram.reshape`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeShapeProgram.lean#L116)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {P Q G S P' Q' G' S' source buffer limit : ℕ} →
    P = P' →
      Q = Q' →
        G = G' →
          S = S' →
            CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q G S) source buffer
                limit (CodedSorting.CommonChunkLayout.swap P Q G S) →
              CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P' Q' G' S') source
                buffer limit (CodedSorting.CommonChunkLayout.swap P' Q' G' S')
```

**定义**

```lean
fun q {P Q G S P' Q' G' S' source buffer limit} hP hQ hG hS p =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonExchangeShapeProgram.reshape._proof_14](ExchangeShapeProgram.definitions.md#def-33e29eee90a73e70)
- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonExchangeShapeProgram.reshape._proof_13](ExchangeShapeProgram.definitions.md#def-6b4627a8bfa64c6f)
- [CodedSorting.CommonExchangeShapeProgram.reshape._proof_15](ExchangeShapeProgram.definitions.md#def-adacf5e1e2dd2e71)
- [CodedSorting.CommonExchangeShapeProgram.reshape._proof_16](ExchangeShapeProgram.definitions.md#def-9ed590f2114e73a3)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonExchangeShapeProgram.reshape._proof_12](ExchangeShapeProgram.definitions.md#def-d0fdd14805e124d4)
- [CodedSorting.CommonFinitePermutation.Program.mk](ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)

**基础库名称**

`Nat`, `Eq`

<a id="def-d0fdd14805e124d4"></a>
## `CodedSorting.CommonExchangeShapeProgram.reshape._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {P Q G S P' Q' G' S' source buffer limit : ℕ},
  P = P' →
    Q = Q' →
      G = G' →
        S = S' →
          ∀
            (p :
              CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q G S) source
                buffer limit (CodedSorting.CommonChunkLayout.swap P Q G S))
            (s : CodedSorting.CommonLeafProgram.Machine q)
            (i : Fin (CodedSorting.CommonChunkLayout.Volume P' Q' G' S')),
            CodedSorting.CommonPermutationPairs.readBit q
                (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk source ↑i =
              CodedSorting.CommonPermutationPairs.readBit q s.disk source
                ↑((CodedSorting.CommonChunkLayout.swap P' Q' G' S') i)
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPermutationPairs.readBit](Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.val`, `Prod.fst`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-6b4627a8bfa64c6f"></a>
## `CodedSorting.CommonExchangeShapeProgram.reshape._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {P Q G S P' Q' G' S' source buffer limit : ℕ},
  P = P' →
    Q = Q' →
      G = G' →
        S = S' →
          ∀
            (p :
              CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q G S) source
                buffer limit (CodedSorting.CommonChunkLayout.swap P Q G S))
            (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
            ↑a < source ∨
                source +
                    CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume P' Q' G' S') ≤
                  ↑a →
              ↑a < buffer ∨ limit ≤ ↑a →
                (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-33e29eee90a73e70"></a>
## `CodedSorting.CommonExchangeShapeProgram.reshape._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {P Q G S source buffer limit : ℕ}
  (p :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q G S) source buffer limit
      (CodedSorting.CommonChunkLayout.swap P Q G S)),
  ∀ i ∈ p.instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`

<a id="def-adacf5e1e2dd2e71"></a>
## `CodedSorting.CommonExchangeShapeProgram.reshape._proof_15`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {P Q G S source buffer limit : ℕ}
  (p :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q G S) source buffer limit
      (CodedSorting.CommonChunkLayout.swap P Q G S)),
  CodedSorting.CommonStaticSchedule.cost q p.instructions ≤ p.charge
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-9ed590f2114e73a3"></a>
## `CodedSorting.CommonExchangeShapeProgram.reshape._proof_16`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {P Q G S source buffer limit : ℕ}
  (p :
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume P Q G S) source buffer limit
      (CodedSorting.CommonChunkLayout.swap P Q G S)),
  p.instructions.length ≤ p.charge
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`LE.le`, `instLENat`, `Nat`, `List.length`

<a id="def-cdb83d33cd0515d0"></a>
## `CodedSorting.CommonFinitePermutation.Program.append._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π₁ π₂ : Equiv.Perm (Fin V)}
  (p₁ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₁)
  (p₂ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₂)
  (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin V),
  CodedSorting.CommonPermutationPairs.readBit q
      (CodedSorting.CommonStaticSchedule.executeRaw q (p₁.instructions ++ p₂.instructions) s).1.disk source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q s.disk source ↑((Equiv.trans π₂ π₁) y)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.val`, `Prod.fst`, `instHAppendOfAppend`, `List`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `List.instAppend`, `Fin`, `Eq`, `DFunLike.coe`, `HAppend.hAppend`

<a id="def-763d998f6060f8b0"></a>
## `CodedSorting.CommonFinitePermutation.Program.append._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π₁ π₂ : Equiv.Perm (Fin V)}
  (p₁ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₁)
  (p₂ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₂)
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q V ≤ ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q (p₁.instructions ++ p₂.instructions) s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAppendOfAppend`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `List.instAppend`, `Fin`, `Eq`, `HAppend.hAppend`

<a id="def-0b8d9858f264567d"></a>
## `CodedSorting.CommonFinitePermutation.Program.append._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π₁ π₂ : Equiv.Perm (Fin V)}
  (p₁ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₁)
  (p₂ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₂),
  ∀ i ∈ p₁.instructions ++ p₂.instructions, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`Membership.mem`, `instHAppendOfAppend`, `List`, `List.instMembership`, `Equiv.Perm`, `Nat`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-11bdf95106cb41ad"></a>
## `CodedSorting.CommonFinitePermutation.Program.append._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π₁ π₂ : Equiv.Perm (Fin V)}
  (p₁ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₁)
  (p₂ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₂),
  CodedSorting.CommonStaticSchedule.cost q (p₁.instructions ++ p₂.instructions) ≤ p₁.charge + p₂.charge
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-ea83285082e2fc21"></a>
## `CodedSorting.CommonFinitePermutation.Program.append._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ} {π₁ π₂ : Equiv.Perm (Fin V)}
  (p₁ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₁)
  (p₂ : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π₂),
  (p₁.instructions ++ p₂.instructions).length ≤ p₁.charge + p₂.charge
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.charge](ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)

**基础库名称**

`LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `instHAdd`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `List.instAppend`, `Fin`, `List.length`, `HAppend.hAppend`

<a id="def-88d74922e663c950"></a>
## `CodedSorting.CommonFinitePermutation.Program.castVolume._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V V' source buffer limit : ℕ} {π : Equiv.Perm (Fin V)}
  (p : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π) (h : V = V')
  (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin V'),
  CodedSorting.CommonPermutationPairs.readBit q (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk
      source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q s.disk source
      ↑(((finCongr h).symm.trans (Equiv.trans π (finCongr h))) y)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Equiv.trans`, `Nat.instMonoid`, `finCongr`, `Monoid.toNatPow`, `Fin.val`, `Prod.fst`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-131c1466679709a1"></a>
## `CodedSorting.CommonFinitePermutation.Program.castVolume._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V V' source buffer limit : ℕ} {π : Equiv.Perm (Fin V)}
  (p : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π),
  V = V' →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
      ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q V' ≤ ↑a →
        ↑a < buffer ∨ limit ≤ ↑a → (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-fd8bd7030373bd6b"></a>
## `CodedSorting.CommonFinitePermutation.Program.identity._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (V source : ℕ)
  (x : CodedSorting.CommonLeafProgram.Machine q) (x_1 : Fin V),
  CodedSorting.CommonPermutationPairs.readBit q (CodedSorting.CommonStaticSchedule.executeRaw q [] x).1.disk source
      ↑x_1 =
    CodedSorting.CommonPermutationPairs.readBit q (CodedSorting.CommonStaticSchedule.executeRaw q [] x).1.disk source
      ↑x_1
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.val`, `Prod.fst`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`, `List.nil`

<a id="def-c63750994ca0e215"></a>
## `CodedSorting.CommonFinitePermutation.Program.identity._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (V source buffer limit : ℕ)
  (x : CodedSorting.CommonLeafProgram.Machine q) (x_1 : Fin (q.N ^ q.exponent)),
  ↑x_1 < source ∨ source + CodedSorting.CommonPermutationPairs.count q V ≤ ↑x_1 →
    ↑x_1 < buffer ∨ limit ≤ ↑x_1 →
      (CodedSorting.CommonStaticSchedule.executeRaw q [] x).1.disk x_1 =
        (CodedSorting.CommonStaticSchedule.executeRaw q [] x).1.disk x_1
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonPermutationPairs.count](Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `List.nil`

<a id="def-848fd32c60cbb8bc"></a>
## `CodedSorting.CommonFinitePermutation.Program.identity._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ∀ a ∈ [], CodedSorting.CommonStaticSchedule.RespectsPC q a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `List.nil`

<a id="def-dc56baee2084b67a"></a>
## `CodedSorting.CommonFinitePermutation.Program.identity._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeShapeProgram.lean)

**类型**

```lean
0 ≤ 0
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`
