# ExchangeInterface 的定义

[源码](ExchangeInterface.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-c6473a9159649804"></a>
## `CodedSorting.Construction.ExchangeInterface.Call`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ExchangeInterface.lean#L35)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call.mk](ExchangeInterface.definitions.md#def-88d363c434138873)

<a id="def-88d363c434138873"></a>
## `CodedSorting.Construction.ExchangeInterface.Call.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ExchangeInterface.lean#L36)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → CodedSorting.Construction.ExchangeInterface.Call
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`Nat`

<a id="def-f09839abbd91973c"></a>
## `CodedSorting.Construction.ExchangeInterface.Call.fieldWidth`

读取 `CodedSorting.Construction.ExchangeInterface.Call` 的 `fieldWidth` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeInterface.lean#L37)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun self => self.1
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`Nat`

<a id="def-c6970b08eef740c9"></a>
## `CodedSorting.Construction.ExchangeInterface.Call.prefixCount`

读取 `CodedSorting.Construction.ExchangeInterface.Call` 的 `prefixCount` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeInterface.lean#L38)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun self => self.2
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`Nat`

<a id="def-2a660b38466586e9"></a>
## `CodedSorting.Construction.ExchangeInterface.Call.gap`

读取 `CodedSorting.Construction.ExchangeInterface.Call` 的 `gap` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeInterface.lean#L39)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun self => self.3
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`Nat`

<a id="def-f885a54e84cd2206"></a>
## `CodedSorting.Construction.ExchangeInterface.Call.suffix`

读取 `CodedSorting.Construction.ExchangeInterface.Call` 的 `suffix` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeInterface.lean#L40)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun self => self.4
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`Nat`

<a id="def-be4ab17220402aee"></a>
## `CodedSorting.Construction.ExchangeInterface.Call.source`

读取 `CodedSorting.Construction.ExchangeInterface.Call` 的 `source` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeInterface.lean#L41)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun self => self.5
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`Nat`

<a id="def-a29f8f671ec8e5d7"></a>
## `CodedSorting.Construction.ExchangeInterface.Call.buffer`

读取 `CodedSorting.Construction.ExchangeInterface.Call` 的 `buffer` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeInterface.lean#L42)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun self => self.6
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`Nat`

<a id="def-d41482827313e1e3"></a>
## `CodedSorting.Construction.ExchangeInterface.Call.limit`

读取 `CodedSorting.Construction.ExchangeInterface.Call` 的 `limit` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ExchangeInterface.lean#L43)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun self => self.7
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)

**基础库名称**

`Nat`

<a id="def-2265644281f87336"></a>
## `CodedSorting.Construction.ExchangeInterface.volume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeInterface.lean#L45)

**类型**

```lean
ℕ → CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun radix c => CodedSorting.CommonChunkLayout.Volume c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonChunkLayout.Volume](../Framework/Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.Construction.ExchangeInterface.Call.prefixCount](ExchangeInterface.definitions.md#def-c6970b08eef740c9)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.Construction.ExchangeInterface.Call.suffix](ExchangeInterface.definitions.md#def-f885a54e84cd2206)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](ExchangeInterface.definitions.md#def-2a660b38466586e9)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-236d2da6a3da9b5c"></a>
## `CodedSorting.Construction.ExchangeInterface.permutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeInterface.lean#L48)

**类型**

```lean
(radix : ℕ) →
  (c : CodedSorting.Construction.ExchangeInterface.Call) →
    Equiv.Perm (Fin (CodedSorting.Construction.ExchangeInterface.volume radix c))
```

**定义**

```lean
fun radix c => CodedSorting.CommonChunkLayout.swap c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Framework/Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.prefixCount](ExchangeInterface.definitions.md#def-c6970b08eef740c9)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.Construction.ExchangeInterface.volume](ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.suffix](ExchangeInterface.definitions.md#def-f885a54e84cd2206)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](ExchangeInterface.definitions.md#def-2a660b38466586e9)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Fin`

<a id="def-5c2c8be0965caaed"></a>
## `CodedSorting.Construction.ExchangeInterface.Program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeInterface.lean#L51)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → CodedSorting.Construction.ExchangeInterface.Call → Type
```

**定义**

```lean
fun q radix c =>
  CodedSorting.CommonFinitePermutation.Program q (CodedSorting.Construction.ExchangeInterface.volume radix c) c.source
    c.buffer c.limit (CodedSorting.Construction.ExchangeInterface.permutation radix c)
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.ExchangeInterface.permutation](ExchangeInterface.definitions.md#def-236d2da6a3da9b5c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ExchangeInterface.volume](ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`Nat`

<a id="def-d25bf8911134460c"></a>
## `CodedSorting.Construction.ExchangeInterface.Allocation`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ExchangeInterface.lean#L56)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → CodedSorting.Construction.ExchangeInterface.Call → Prop
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Allocation.mk](ExchangeInterface.definitions.md#def-5bd2e92dc581c0a3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-5bd2e92dc581c0a3"></a>
## `CodedSorting.Construction.ExchangeInterface.Allocation.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ExchangeInterface.lean#L59)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {radix : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  c.source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.ExchangeInterface.volume radix c) ≤
      c.buffer →
    c.buffer +
          CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.ExchangeInterface.volume radix c) ≤
        c.limit →
      c.limit ≤ q.N ^ q.exponent → CodedSorting.Construction.ExchangeInterface.Allocation q radix c
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`

<a id="def-a9d74d6c18a3bf8f"></a>
## `CodedSorting.Construction.ExchangeInterface.Allocation.limit_fits`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExchangeInterface.lean#L62)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {radix : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.ExchangeInterface.Allocation q radix c → c.limit ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-caaeb667315f77f7"></a>
## `CodedSorting.Construction.ExchangeInterface.costBound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeInterface.lean#L181)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun coefficient b cutoff x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → ℕ) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → ℕ → Nat.below (motive := fun x => ℕ → ℕ) x → ℕ) x, x_2 with
        | 0, V => fun x => 20 * (V / b + 1)
        | k.succ, V => fun x =>
          if V ≤ cutoff then 20 * (V / b + 1)
          else
            coefficient * (V / b + 1) +
              CodedSorting.Construction.rankBudget * x.1 (V / CodedSorting.Construction.streamCount))
        f)
    x_1
```

**继续展开**

- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.rankBudget](../../Circuit/Parameters/Counts.definitions.md#def-64416b74593cf091)
- [CodedSorting.Construction.ExchangeInterface.costBound.match_1](ExchangeInterface.definitions.md#def-93fb3995b7a9e4c9)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.brecOn`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`, `Nat.succ`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-968c9a7921183848"></a>
## `CodedSorting.Construction.ExchangeInterface.LeafFits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExchangeInterface.lean#L194)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ℕ → ℕ → ℕ → CodedSorting.Construction.ExchangeInterface.Call → Prop
```

**定义**

```lean
fun q radix cutoff k c =>
  if CodedSorting.Construction.ExchangeInterface.volume radix c ≤ cutoff then
    CodedSorting.Construction.ExchangeInterface.volume radix c ≤ CodedSorting.CommonExchangeLeaf.bankBits q
  else
    k = 0 ∧
      (radix ^ c.fieldWidth) ^ 2 * q.block ≤ CodedSorting.CommonExchangeLeaf.bankWords q ∧
        (radix ^ c.fieldWidth) ^ 2 * CodedSorting.CommonPermutationPairs.width q ≤
          cutoff + CodedSorting.CommonPermutationPairs.width q
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonExchangeLeaf.bankWords](../Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.volume](ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonExchangeLeaf.bankBits](../Framework/Memory/ExchangeLeaf.definitions.md#def-88582f6aa0de40db)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Eq`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-93fb3995b7a9e4c9"></a>
## `CodedSorting.Construction.ExchangeInterface.costBound.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ExchangeInterface.lean)

**类型**

```lean
(motive : ℕ → ℕ → Sort u_1) → (x x_1 : ℕ) → ((V : ℕ) → motive 0 V) → ((k V : ℕ) → motive k.succ V) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`
