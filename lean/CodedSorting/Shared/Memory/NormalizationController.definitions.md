# NormalizationController 的定义

[源码](NormalizationController.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2d188bbafc1ff917"></a>
## `CodedSorting.CommonNormalizationController.instDecidableEqOptionNone_codedSorting`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L14)

**类型**

```lean
{α : Type u_1} → (o : Option α) → Decidable (o = none)
```

**定义**

```lean
fun {α} o => Option.decidable_eq_none
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Decidable`, `Option.none`, `Option.decidable_eq_none`, `Eq`, `Option`

<a id="def-1cfe9467af4437b1"></a>
## `CodedSorting.CommonNormalizationController.Address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L16)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun R => Fin R ⊕ Fin R ⊕ Fin R
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Sum`, `Nat`, `Fin`

<a id="def-ad6b8f91b6dfa7db"></a>
## `CodedSorting.CommonNormalizationController.Disk`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L17)

**类型**

```lean
ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun R B w => CodedSorting.CommonNormalizationController.Address R → CodedSorting.WordControl.Words B w
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Address](NormalizationController.definitions.md#def-1cfe9467af4437b1)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-8e30ae3ef69cec39"></a>
## `CodedSorting.CommonNormalizationController.Program`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](NormalizationController.lean#L19)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program.mk](NormalizationController.definitions.md#def-c8f48bd4c9348d9c)

**基础库名称**

`Nat`

<a id="def-c8f48bd4c9348d9c"></a>
## `CodedSorting.CommonNormalizationController.Program.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](NormalizationController.lean#L19)

**类型**

```lean
{L R B b d w : ℕ} →
  0 < R →
    0 < B →
      b ≤ B →
        R < (2 ^ w) ^ d →
          8 ≤ 2 ^ w →
            CodedSorting.WordControl.Word w →
              CodedSorting.ControlledNormalization.Policy L b R (CodedSorting.WordControl.Word w) →
                CodedSorting.CommonNormalizationController.Program L R B b d w
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.ControlledNormalization.Policy](../Programs/ControlledNormalization.definitions.md#def-311feb3c44e69784)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-451a59c50b940657"></a>
## `CodedSorting.CommonNormalizationController.Program.positive_region`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean#L20)

**类型**

```lean
∀ {L R B b d w : ℕ}, CodedSorting.CommonNormalizationController.Program L R B b d w → 0 < R
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-43a11d3e49f95394"></a>
## `CodedSorting.CommonNormalizationController.Program.positive_block`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean#L21)

**类型**

```lean
∀ {L R B b d w : ℕ}, CodedSorting.CommonNormalizationController.Program L R B b d w → 0 < B
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-c2157a5ea0255b0a"></a>
## `CodedSorting.CommonNormalizationController.Program.block_ratio`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean#L22)

**类型**

```lean
∀ {L R B b d w : ℕ}, CodedSorting.CommonNormalizationController.Program L R B b d w → b ≤ B
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-82466763d92a8411"></a>
## `CodedSorting.CommonNormalizationController.Program.phase_capacity`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean#L24)

**类型**

```lean
∀ {L R B b d w : ℕ}, CodedSorting.CommonNormalizationController.Program L R B b d w → 8 ≤ 2 ^ w
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-d1fbc1c5889ded60"></a>
## `CodedSorting.CommonNormalizationController.Program.padding`

读取 `CodedSorting.CommonNormalizationController.Program` 的 `padding` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L25)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.Program L R B b d w → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun L R B b d w self => self.6
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)

**基础库名称**

`Nat`

<a id="def-c4b941ce1f1eb711"></a>
## `CodedSorting.CommonNormalizationController.Program.policy`

读取 `CodedSorting.CommonNormalizationController.Program` 的 `policy` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L26)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w →
    CodedSorting.ControlledNormalization.Policy L b R (CodedSorting.WordControl.Word w)
```

**定义**

```lean
fun L R B b d w self => self.7
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.ControlledNormalization.Policy](../Programs/ControlledNormalization.definitions.md#def-311feb3c44e69784)

**基础库名称**

`Nat`

<a id="def-f2e4d72f6ceee1dd"></a>
## `CodedSorting.CommonNormalizationController.State`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](NormalizationController.lean#L28)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State.mk](NormalizationController.definitions.md#def-fb93c0454ab3d11a)

**基础库名称**

`Nat`

<a id="def-fb93c0454ab3d11a"></a>
## `CodedSorting.CommonNormalizationController.State.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](NormalizationController.lean#L28)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.WordControl.Words L w →
    CodedSorting.WordControl.Words B w →
      CodedSorting.WordControl.Words b w →
        CodedSorting.WordControl.Words d w →
          CodedSorting.WordControl.Words d w →
            CodedSorting.WordControl.Words d w →
              CodedSorting.WordControl.Word w →
                CodedSorting.WordControl.Word w →
                  CodedSorting.CommonNormalizationController.Disk R B w →
                    CodedSorting.CommonNormalizationController.State L R B b d w
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.Disk](NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-4a284b749f933d01"></a>
## `CodedSorting.CommonNormalizationController.State.ram`

读取 `CodedSorting.CommonNormalizationController.State` 的 `ram` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L29)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.WordControl.Words L w
```

**定义**

```lean
fun L R B b d w self => self.1
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-2d5a479d9bec19b6"></a>
## `CodedSorting.CommonNormalizationController.State.buffer`

读取 `CodedSorting.CommonNormalizationController.State` 的 `buffer` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L30)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.WordControl.Words B w
```

**定义**

```lean
fun L R B b d w self => self.2
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-7b21a939bc5c2512"></a>
## `CodedSorting.CommonNormalizationController.State.scratch`

读取 `CodedSorting.CommonNormalizationController.State` 的 `scratch` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L31)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.WordControl.Words b w
```

**定义**

```lean
fun L R B b d w self => self.3
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-bd0066273c7e97df"></a>
## `CodedSorting.CommonNormalizationController.State.counter`

读取 `CodedSorting.CommonNormalizationController.State` 的 `counter` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L32)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun L R B b d w self => self.4
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-589dac48ea92a522"></a>
## `CodedSorting.CommonNormalizationController.State.inputCount`

读取 `CodedSorting.CommonNormalizationController.State` 的 `inputCount` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L33)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun L R B b d w self => self.5
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-6759209159746a5f"></a>
## `CodedSorting.CommonNormalizationController.State.outputCount`

读取 `CodedSorting.CommonNormalizationController.State` 的 `outputCount` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L34)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun L R B b d w self => self.6
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-b6732970c4299503"></a>
## `CodedSorting.CommonNormalizationController.State.phase`

读取 `CodedSorting.CommonNormalizationController.State` 的 `phase` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L35)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun L R B b d w self => self.7
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)

**基础库名称**

`Nat`

<a id="def-d2e501b11ede2ee3"></a>
## `CodedSorting.CommonNormalizationController.State.stage`

读取 `CodedSorting.CommonNormalizationController.State` 的 `stage` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L36)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun L R B b d w self => self.8
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)

**基础库名称**

`Nat`

<a id="def-57b507872aac004b"></a>
## `CodedSorting.CommonNormalizationController.State.disk`

读取 `CodedSorting.CommonNormalizationController.State` 的 `disk` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationController.lean#L37)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.CommonNormalizationController.Disk R B w
```

**定义**

```lean
fun L R B b d w self => self.9
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.Disk](NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)

**基础库名称**

`Nat`

<a id="def-c011e67b6b9fd156"></a>
## `CodedSorting.CommonNormalizationController.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L39)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w → Fin 8 → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun {L R B b d w} p k => ⟨↑k, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonNormalizationController.code._proof_1](NormalizationController.definitions.md#def-f1513b45dd51d6d1)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `instOfNatNat`, `Fin.val`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-2ade1b011ffce6d0"></a>
## `CodedSorting.CommonNormalizationController.inputSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L42)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → ℕ
```

**定义**

```lean
fun {L R B b d w} s => min (CodedSorting.WordControl.decodeWords s.inputCount) R
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.decodeWords](../Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonNormalizationController.State.inputCount](NormalizationController.definitions.md#def-589dac48ea92a522)

**基础库名称**

`Nat`, `Nat.instMin_mathlib`, `Min.min`

<a id="def-e508a5339484c801"></a>
## `CodedSorting.CommonNormalizationController.outputSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L43)

**类型**

```lean
{L R B b d w : ℕ} → CodedSorting.CommonNormalizationController.State L R B b d w → ℕ
```

**定义**

```lean
fun {L R B b d w} s => min (CodedSorting.WordControl.decodeWords s.outputCount) (R - 1)
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.decodeWords](../Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonNormalizationController.State.outputCount](NormalizationController.definitions.md#def-6759209159746a5f)

**基础库名称**

`HSub.hSub`, `instSubNat`, `instOfNatNat`, `instHSub`, `Nat`, `Nat.instMin_mathlib`, `OfNat.ofNat`, `Min.min`

<a id="def-32b29de65f7b27e9"></a>
## `CodedSorting.CommonNormalizationController.converter`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L45)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w →
    (n : ℕ) → n ≤ R → CodedSorting.PhysicalNormalizationLayout.Program R B b d w
```

**定义**

```lean
fun {L R B b d w} p n hn =>
  { blocks := n, block_bound := hn, counter_bound := ⋯, positive_region := ⋯, positive_block := ⋯, block_ratio := ⋯,
    phase_capacity := ⋯, padding := p.padding }
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program.phase_capacity](NormalizationController.definitions.md#def-82466763d92a8411)
- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.PhysicalNormalizationLayout.Program](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationLayout.Program.mk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-ee384cfcf662b4d7)
- [CodedSorting.CommonNormalizationController.Program.block_ratio](NormalizationController.definitions.md#def-c2157a5ea0255b0a)
- [CodedSorting.CommonNormalizationController.converter._proof_2](NormalizationController.definitions.md#def-4d7d169c67ab4ee8)
- [CodedSorting.CommonNormalizationController.Program.padding](NormalizationController.definitions.md#def-d1fbc1c5889ded60)
- [CodedSorting.CommonNormalizationController.Program.positive_block](NormalizationController.definitions.md#def-43a11d3e49f95394)
- [CodedSorting.CommonNormalizationController.Program.positive_region](NormalizationController.definitions.md#def-451a59c50b940657)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-653ce09287d6a834"></a>
## `CodedSorting.CommonNormalizationController.inputProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L50)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w →
    CodedSorting.CommonNormalizationController.State L R B b d w →
      CodedSorting.PhysicalNormalizationLayout.Program R B b d w
```

**定义**

```lean
fun {L R B b d w} p s =>
  CodedSorting.CommonNormalizationController.converter p (CodedSorting.CommonNormalizationController.inputSize s) ⋯
```

**继续展开**

- [CodedSorting.CommonNormalizationController.inputProgram._proof_3](NormalizationController.definitions.md#def-6522fd210bdae81e)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.PhysicalNormalizationLayout.Program](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.CommonNormalizationController.converter](NormalizationController.definitions.md#def-32b29de65f7b27e9)
- [CodedSorting.CommonNormalizationController.inputSize](NormalizationController.definitions.md#def-2ade1b011ffce6d0)

**基础库名称**

`Nat`

<a id="def-30ac3096fc21aa58"></a>
## `CodedSorting.CommonNormalizationController.outputProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L52)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w →
    CodedSorting.CommonNormalizationController.State L R B b d w →
      CodedSorting.PhysicalNormalizationLayout.Program R B b d w
```

**定义**

```lean
fun {L R B b d w} p s =>
  CodedSorting.CommonNormalizationController.converter p (CodedSorting.CommonNormalizationController.outputSize s) ⋯
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.PhysicalNormalizationLayout.Program](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.CommonNormalizationController.converter](NormalizationController.definitions.md#def-32b29de65f7b27e9)
- [CodedSorting.CommonNormalizationController.outputProgram._proof_4](NormalizationController.definitions.md#def-b35a2e14a0fc86f9)
- [CodedSorting.CommonNormalizationController.outputSize](NormalizationController.definitions.md#def-e508a5339484c801)

**基础库名称**

`Nat`

<a id="def-39da011dbebf3767"></a>
## `CodedSorting.CommonNormalizationController.expandView`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L55)

**类型**

```lean
{R B w : ℕ} →
  CodedSorting.CommonNormalizationController.Disk R B w → CodedSorting.PhysicalNormalizationLayout.Disk R B w
```

**定义**

```lean
fun {R B w} disk x =>
  match x with
  | Sum.inl a => disk (Sum.inl a)
  | Sum.inr a => disk (Sum.inr (Sum.inl a))
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Address](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-07aca1946acd437c)
- [CodedSorting.CommonNormalizationController.Disk](NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.PhysicalNormalizationLayout.Disk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-9e955a98938d0ed5)
- [CodedSorting.CommonNormalizationController.expandView.match_1](NormalizationController.definitions.md#def-4aaa778d88fe4973)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Sum`, `Sum.inl`, `Sum.inr`, `Nat`, `Fin`

<a id="def-8b4a7b91efa6bfbb"></a>
## `CodedSorting.CommonNormalizationController.compactView`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L58)

**类型**

```lean
{R B w : ℕ} →
  CodedSorting.CommonNormalizationController.Disk R B w → CodedSorting.PhysicalNormalizationLayout.Disk R B w
```

**定义**

```lean
fun {R B w} disk x =>
  match x with
  | Sum.inl a => disk (Sum.inr (Sum.inl a))
  | Sum.inr a => disk (Sum.inr (Sum.inr a))
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Address](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-07aca1946acd437c)
- [CodedSorting.CommonNormalizationController.Disk](NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.PhysicalNormalizationLayout.Disk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-9e955a98938d0ed5)
- [CodedSorting.CommonNormalizationController.expandView.match_1](NormalizationController.definitions.md#def-4aaa778d88fe4973)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Sum`, `Sum.inl`, `Sum.inr`, `Nat`, `Fin`

<a id="def-b9a3c32c6f039548"></a>
## `CodedSorting.CommonNormalizationController.installExpand`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L61)

**类型**

```lean
{R B w : ℕ} →
  CodedSorting.CommonNormalizationController.Disk R B w →
    CodedSorting.PhysicalNormalizationLayout.Disk R B w → CodedSorting.CommonNormalizationController.Disk R B w
```

**定义**

```lean
fun {R B w} old new x =>
  match x with
  | Sum.inl a => new (Sum.inl a)
  | Sum.inr (Sum.inl a) => new (Sum.inr a)
  | Sum.inr (Sum.inr a) => old (Sum.inr (Sum.inr a))
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Disk](NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.CommonNormalizationController.Address](NormalizationController.definitions.md#def-1cfe9467af4437b1)
- [CodedSorting.CommonNormalizationController.installExpand.match_1](NormalizationController.definitions.md#def-7d6980ad396c2e40)
- [CodedSorting.PhysicalNormalizationLayout.Disk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-9e955a98938d0ed5)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Sum`, `Sum.inl`, `Sum.inr`, `Nat`, `Fin`

<a id="def-472f1973a18879b4"></a>
## `CodedSorting.CommonNormalizationController.installCompact`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L65)

**类型**

```lean
{R B w : ℕ} →
  CodedSorting.CommonNormalizationController.Disk R B w →
    CodedSorting.PhysicalNormalizationLayout.Disk R B w → CodedSorting.CommonNormalizationController.Disk R B w
```

**定义**

```lean
fun {R B w} old new x =>
  match x with
  | Sum.inl a => old (Sum.inl a)
  | Sum.inr (Sum.inl a) => new (Sum.inl a)
  | Sum.inr (Sum.inr a) => new (Sum.inr a)
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Disk](NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.CommonNormalizationController.Address](NormalizationController.definitions.md#def-1cfe9467af4437b1)
- [CodedSorting.CommonNormalizationController.installExpand.match_1](NormalizationController.definitions.md#def-7d6980ad396c2e40)
- [CodedSorting.PhysicalNormalizationLayout.Disk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-9e955a98938d0ed5)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Sum`, `Sum.inl`, `Sum.inr`, `Nat`, `Fin`

<a id="def-89cfc129c5b315ec"></a>
## `CodedSorting.CommonNormalizationController.installCore`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L69)

**类型**

```lean
{R B w : ℕ} →
  CodedSorting.CommonNormalizationController.Disk R B w →
    CodedSorting.Normalization.Disk R B (CodedSorting.WordControl.Word w) →
      CodedSorting.CommonNormalizationController.Disk R B w
```

**定义**

```lean
fun {R B w} old new x =>
  match x with
  | Sum.inl a => old (Sum.inl a)
  | Sum.inr (Sum.inl a) => new a
  | Sum.inr (Sum.inr a) => old (Sum.inr (Sum.inr a))
```

**继续展开**

- [CodedSorting.Normalization.Disk](../Programs/Normalization.definitions.md#def-18f3e234560b5b4a)
- [CodedSorting.CommonNormalizationController.Disk](NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.CommonNormalizationController.Address](NormalizationController.definitions.md#def-1cfe9467af4437b1)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonNormalizationController.installExpand.match_1](NormalizationController.definitions.md#def-7d6980ad396c2e40)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Sum`, `Sum.inl`, `Sum.inr`, `Nat`, `Fin`

<a id="def-6251b7c625fd81bf"></a>
## `CodedSorting.CommonNormalizationController.expandState`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L74)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.State L R B b d w →
    CodedSorting.PhysicalNormalizationLayout.State R B b d w
```

**定义**

```lean
fun {L R B b d w} s =>
  { buffer := s.buffer, scratch := s.scratch, counter := s.counter, phase := s.phase,
    disk := CodedSorting.CommonNormalizationController.expandView s.disk }
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State.counter](NormalizationController.definitions.md#def-bd0066273c7e97df)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.State.scratch](NormalizationController.definitions.md#def-7b21a939bc5c2512)
- [CodedSorting.CommonNormalizationController.State.disk](NormalizationController.definitions.md#def-57b507872aac004b)
- [CodedSorting.CommonNormalizationController.State.phase](NormalizationController.definitions.md#def-b6732970c4299503)
- [CodedSorting.PhysicalNormalizationLayout.State.mk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-f8bfca1e966aa73b)
- [CodedSorting.PhysicalNormalizationLayout.State](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.CommonNormalizationController.expandView](NormalizationController.definitions.md#def-39da011dbebf3767)
- [CodedSorting.CommonNormalizationController.State.buffer](NormalizationController.definitions.md#def-2d5a479d9bec19b6)

**基础库名称**

`Nat`

<a id="def-e19df4ea88e08772"></a>
## `CodedSorting.CommonNormalizationController.compactState`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L76)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.State L R B b d w →
    CodedSorting.PhysicalNormalizationLayout.State R B b d w
```

**定义**

```lean
fun {L R B b d w} s =>
  { buffer := s.buffer, scratch := s.scratch, counter := s.counter, phase := s.phase,
    disk := CodedSorting.CommonNormalizationController.compactView s.disk }
```

**继续展开**

- [CodedSorting.CommonNormalizationController.compactView](NormalizationController.definitions.md#def-8b4a7b91efa6bfbb)
- [CodedSorting.CommonNormalizationController.State.counter](NormalizationController.definitions.md#def-bd0066273c7e97df)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.State.scratch](NormalizationController.definitions.md#def-7b21a939bc5c2512)
- [CodedSorting.CommonNormalizationController.State.disk](NormalizationController.definitions.md#def-57b507872aac004b)
- [CodedSorting.CommonNormalizationController.State.phase](NormalizationController.definitions.md#def-b6732970c4299503)
- [CodedSorting.PhysicalNormalizationLayout.State.mk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-f8bfca1e966aa73b)
- [CodedSorting.PhysicalNormalizationLayout.State](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.CommonNormalizationController.State.buffer](NormalizationController.definitions.md#def-2d5a479d9bec19b6)

**基础库名称**

`Nat`

<a id="def-2a57c1994d70128c"></a>
## `CodedSorting.CommonNormalizationController.coreState`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L78)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.State L R B b d w → CodedSorting.FixedPolicyNormalization.State L B R w
```

**定义**

```lean
fun {L R B b d w} s =>
  { data := { ram := s.ram, buffer := s.buffer, disk := fun a => s.disk (Sum.inr (Sum.inl a)) }, phase := s.phase }
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.State.disk](NormalizationController.definitions.md#def-57b507872aac004b)
- [CodedSorting.Normalization.PhysicalState.mk](../Programs/Normalization.definitions.md#def-2b2feddbbfb01c5b)
- [CodedSorting.FixedPolicyNormalization.State](../Programs/FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.CommonNormalizationController.State.phase](NormalizationController.definitions.md#def-b6732970c4299503)
- [CodedSorting.FixedPolicyNormalization.Word](../Programs/FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.CommonNormalizationController.State.ram](NormalizationController.definitions.md#def-4a284b749f933d01)
- [CodedSorting.FixedPolicyNormalization.State.mk](../Programs/FixedPolicyNormalization.definitions.md#def-ab55087183329d74)
- [CodedSorting.CommonNormalizationController.State.buffer](NormalizationController.definitions.md#def-2d5a479d9bec19b6)

**基础库名称**

`Sum`, `Sum.inl`, `Sum.inr`, `Nat`, `Fin`

<a id="def-f4fbce162ab95e25"></a>
## `CodedSorting.CommonNormalizationController.putExpand`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L81)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.State L R B b d w →
    CodedSorting.PhysicalNormalizationLayout.State R B b d w →
      CodedSorting.CommonNormalizationController.State L R B b d w
```

**定义**

```lean
fun {L R B b d w} s t =>
  { ram := s.ram, buffer := t.buffer, scratch := t.scratch, counter := t.counter, inputCount := s.inputCount,
    outputCount := s.outputCount, phase := t.phase, stage := s.stage,
    disk := CodedSorting.CommonNormalizationController.installExpand s.disk t.disk }
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State.buffer](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-c70ce37a8b88fc3e)
- [CodedSorting.CommonNormalizationController.State.mk](NormalizationController.definitions.md#def-fb93c0454ab3d11a)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.PhysicalNormalizationLayout.State.counter](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-0f6743e028e821e8)
- [CodedSorting.CommonNormalizationController.installExpand](NormalizationController.definitions.md#def-b9a3c32c6f039548)
- [CodedSorting.CommonNormalizationController.State.disk](NormalizationController.definitions.md#def-57b507872aac004b)
- [CodedSorting.CommonNormalizationController.State.inputCount](NormalizationController.definitions.md#def-589dac48ea92a522)
- [CodedSorting.CommonNormalizationController.State.ram](NormalizationController.definitions.md#def-4a284b749f933d01)
- [CodedSorting.CommonNormalizationController.State.outputCount](NormalizationController.definitions.md#def-6759209159746a5f)
- [CodedSorting.PhysicalNormalizationLayout.State](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.CommonNormalizationController.State.stage](NormalizationController.definitions.md#def-d2e501b11ede2ee3)
- [CodedSorting.PhysicalNormalizationLayout.State.disk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-48fddd883aa3f5eb)
- [CodedSorting.PhysicalNormalizationLayout.State.scratch](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-7a685606d02225f1)
- [CodedSorting.PhysicalNormalizationLayout.State.phase](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-d8014df3dd931356)

**基础库名称**

`Nat`

<a id="def-17c57cea8d019990"></a>
## `CodedSorting.CommonNormalizationController.putCompact`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L83)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.State L R B b d w →
    CodedSorting.PhysicalNormalizationLayout.State R B b d w →
      CodedSorting.CommonNormalizationController.State L R B b d w
```

**定义**

```lean
fun {L R B b d w} s t =>
  { ram := s.ram, buffer := t.buffer, scratch := t.scratch, counter := t.counter, inputCount := s.inputCount,
    outputCount := s.outputCount, phase := t.phase, stage := s.stage,
    disk := CodedSorting.CommonNormalizationController.installCompact s.disk t.disk }
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State.buffer](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-c70ce37a8b88fc3e)
- [CodedSorting.CommonNormalizationController.State.mk](NormalizationController.definitions.md#def-fb93c0454ab3d11a)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.PhysicalNormalizationLayout.State.counter](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-0f6743e028e821e8)
- [CodedSorting.CommonNormalizationController.State.disk](NormalizationController.definitions.md#def-57b507872aac004b)
- [CodedSorting.CommonNormalizationController.State.inputCount](NormalizationController.definitions.md#def-589dac48ea92a522)
- [CodedSorting.CommonNormalizationController.State.ram](NormalizationController.definitions.md#def-4a284b749f933d01)
- [CodedSorting.CommonNormalizationController.installCompact](NormalizationController.definitions.md#def-472f1973a18879b4)
- [CodedSorting.CommonNormalizationController.State.outputCount](NormalizationController.definitions.md#def-6759209159746a5f)
- [CodedSorting.PhysicalNormalizationLayout.State](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.CommonNormalizationController.State.stage](NormalizationController.definitions.md#def-d2e501b11ede2ee3)
- [CodedSorting.PhysicalNormalizationLayout.State.disk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-48fddd883aa3f5eb)
- [CodedSorting.PhysicalNormalizationLayout.State.scratch](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-7a685606d02225f1)
- [CodedSorting.PhysicalNormalizationLayout.State.phase](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-d8014df3dd931356)

**基础库名称**

`Nat`

<a id="def-3d065edf1f1b9219"></a>
## `CodedSorting.CommonNormalizationController.putCore`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L85)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.State L R B b d w →
    CodedSorting.FixedPolicyNormalization.State L B R w → CodedSorting.CommonNormalizationController.State L R B b d w
```

**定义**

```lean
fun {L R B b d w} s t =>
  { ram := t.data.ram, buffer := t.data.buffer, scratch := s.scratch, counter := s.counter, inputCount := s.inputCount,
    outputCount := s.outputCount, phase := t.phase, stage := s.stage,
    disk := CodedSorting.CommonNormalizationController.installCore s.disk t.data.disk }
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State.mk](NormalizationController.definitions.md#def-fb93c0454ab3d11a)
- [CodedSorting.CommonNormalizationController.State.counter](NormalizationController.definitions.md#def-bd0066273c7e97df)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.State.scratch](NormalizationController.definitions.md#def-7b21a939bc5c2512)
- [CodedSorting.CommonNormalizationController.installCore](NormalizationController.definitions.md#def-89cfc129c5b315ec)
- [CodedSorting.CommonNormalizationController.State.disk](NormalizationController.definitions.md#def-57b507872aac004b)
- [CodedSorting.FixedPolicyNormalization.State](../Programs/FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.Normalization.PhysicalState.disk](../Programs/Normalization.definitions.md#def-df054804f555e188)
- [CodedSorting.CommonNormalizationController.State.inputCount](NormalizationController.definitions.md#def-589dac48ea92a522)
- [CodedSorting.FixedPolicyNormalization.Word](../Programs/FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.CommonNormalizationController.State.outputCount](NormalizationController.definitions.md#def-6759209159746a5f)
- [CodedSorting.FixedPolicyNormalization.State.phase](../Programs/FixedPolicyNormalization.definitions.md#def-8811097908191dac)
- [CodedSorting.FixedPolicyNormalization.State.data](../Programs/FixedPolicyNormalization.definitions.md#def-b353367b3b3b5fbc)
- [CodedSorting.Normalization.PhysicalState.buffer](../Programs/Normalization.definitions.md#def-74cb96dbfc7116c1)
- [CodedSorting.Normalization.PhysicalState.ram](../Programs/Normalization.definitions.md#def-401047fe136aec1d)
- [CodedSorting.CommonNormalizationController.State.stage](NormalizationController.definitions.md#def-d2e501b11ede2ee3)

**基础库名称**

`Nat`

<a id="def-35b0e81743543f27"></a>
## `CodedSorting.CommonNormalizationController.step`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L137)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w →
    CodedSorting.CommonNormalizationController.State L R B b d w →
      CodedSorting.CommonNormalizationController.State L R B b d w × ℕ
```

**定义**

```lean
fun {L R B b d w} p s =>
  match ↑s.stage with
  | 0 =>
    if CodedSorting.WordControl.decodeWords s.counter < CodedSorting.CommonNormalizationController.inputSize s then
      let e :=
        CodedSorting.PhysicalNormalizationLayout.run (CodedSorting.CommonNormalizationController.inputProgram p s) 7
          (CodedSorting.CommonNormalizationController.expandState s);
      (CodedSorting.CommonNormalizationController.putExpand s e.1, e.2)
    else
      ({ ram := s.ram, buffer := s.buffer, scratch := s.scratch, counter := s.counter, inputCount := s.inputCount,
          outputCount := s.outputCount, phase := CodedSorting.CommonNormalizationController.code p 0,
          stage := CodedSorting.CommonNormalizationController.code p 1, disk := s.disk },
        0)
  | 1 =>
    if p.policy s.ram = none then
      ({ ram := s.ram, buffer := fun x => p.padding, scratch := fun x => p.padding,
          counter := CodedSorting.PhysicalNormalizationLayout.counterCode d w 0, inputCount := s.inputCount,
          outputCount := s.outputCount, phase := CodedSorting.CommonNormalizationController.code p 0,
          stage := CodedSorting.CommonNormalizationController.code p 2, disk := s.disk },
        0)
    else
      let e :=
        CodedSorting.FixedPolicyNormalization.run ⋯ ⋯ p.padding { policy := p.policy } 2
          (CodedSorting.CommonNormalizationController.coreState s);
      (CodedSorting.CommonNormalizationController.putCore s e.1, e.2)
  | 2 =>
    if CodedSorting.WordControl.decodeWords s.counter < CodedSorting.CommonNormalizationController.outputSize s then
      let e :=
        CodedSorting.PhysicalNormalizationCompact.run (CodedSorting.CommonNormalizationController.outputProgram p s) 8
          (CodedSorting.CommonNormalizationController.compactState s);
      (CodedSorting.CommonNormalizationController.putCompact s e.1, e.2)
    else
      ({ ram := s.ram, buffer := s.buffer, scratch := s.scratch, counter := s.counter, inputCount := s.inputCount,
          outputCount := s.outputCount, phase := s.phase, stage := CodedSorting.CommonNormalizationController.code p 3,
          disk := s.disk },
        0)
  | x => (s, 0)
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.Program.mk](../Programs/FixedPolicyNormalization.definitions.md#def-8dc84ed3cbacb15d)
- [CodedSorting.CommonNormalizationController.coreMicro._proof_6](NormalizationController.definitions.md#def-b6aba43c48fad852)
- [CodedSorting.CommonNormalizationController.putCompact](NormalizationController.definitions.md#def-17c57cea8d019990)
- [CodedSorting.CommonNormalizationController.putCore](NormalizationController.definitions.md#def-3d065edf1f1b9219)
- [CodedSorting.CommonNormalizationController.outputProgram](NormalizationController.definitions.md#def-30ac3096fc21aa58)
- [CodedSorting.PhysicalNormalizationLayout.counterCode](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-92718a548009d747)
- [CodedSorting.CommonNormalizationController.State.mk](NormalizationController.definitions.md#def-fb93c0454ab3d11a)
- [CodedSorting.CommonNormalizationController.State.counter](NormalizationController.definitions.md#def-bd0066273c7e97df)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.State.scratch](NormalizationController.definitions.md#def-7b21a939bc5c2512)
- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonNormalizationController.State.disk](NormalizationController.definitions.md#def-57b507872aac004b)
- [CodedSorting.WordControl.decodeWords](../Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.FixedPolicyNormalization.run](../Programs/FixedPolicyNormalization.definitions.md#def-5b674c82b533c4d0)
- [CodedSorting.FixedPolicyNormalization.State](../Programs/FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.CommonNormalizationController.State.phase](NormalizationController.definitions.md#def-b6732970c4299503)
- [CodedSorting.CommonNormalizationController.instDecidableEqOptionNone_codedSorting](NormalizationController.definitions.md#def-2d188bbafc1ff917)
- [CodedSorting.CommonNormalizationController.coreState](NormalizationController.definitions.md#def-2a57c1994d70128c)
- [CodedSorting.CommonNormalizationController.State.inputCount](NormalizationController.definitions.md#def-589dac48ea92a522)
- [CodedSorting.CommonNormalizationController.expandState](NormalizationController.definitions.md#def-6251b7c625fd81bf)
- [CodedSorting.PhysicalNormalizationLayout.run](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-0d08100b73d62612)
- [CodedSorting.CommonNormalizationController.step._proof_7](NormalizationController.definitions.md#def-074d1aa92a867972)
- [CodedSorting.CommonNormalizationController.Program.block_ratio](NormalizationController.definitions.md#def-c2157a5ea0255b0a)
- [CodedSorting.CommonNormalizationController.State.ram](NormalizationController.definitions.md#def-4a284b749f933d01)
- [CodedSorting.CommonNormalizationController.step.match_1](NormalizationController.definitions.md#def-0d17696600d8128c)
- [CodedSorting.PhysicalNormalizationCompact.run](PhysicalNormalizationCompact.definitions.md#def-37963a3a6483170d)
- [CodedSorting.CommonNormalizationController.State.outputCount](NormalizationController.definitions.md#def-6759209159746a5f)
- [CodedSorting.CommonNormalizationController.inputSize](NormalizationController.definitions.md#def-2ade1b011ffce6d0)
- [CodedSorting.CommonNormalizationController.compactState](NormalizationController.definitions.md#def-e19df4ea88e08772)
- [CodedSorting.CommonNormalizationController.Program.policy](NormalizationController.definitions.md#def-c4b941ce1f1eb711)
- [CodedSorting.CommonNormalizationController.code](NormalizationController.definitions.md#def-c011e67b6b9fd156)
- [CodedSorting.PhysicalNormalizationLayout.State](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.CommonNormalizationController.Program.padding](NormalizationController.definitions.md#def-d1fbc1c5889ded60)
- [CodedSorting.CommonNormalizationController.State.stage](NormalizationController.definitions.md#def-d2e501b11ede2ee3)
- [CodedSorting.CommonNormalizationController.inputProgram](NormalizationController.definitions.md#def-653ce09287d6a834)
- [CodedSorting.ControlledNormalization.Instruction](../Programs/ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)
- [CodedSorting.CommonNormalizationController.outputSize](NormalizationController.definitions.md#def-e508a5339484c801)
- [CodedSorting.CommonNormalizationController.putExpand](NormalizationController.definitions.md#def-f4fbce162ab95e25)
- [CodedSorting.CommonNormalizationController.State.buffer](NormalizationController.definitions.md#def-2d5a479d9bec19b6)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.instOfNat`, `Prod.mk`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `Option.none`, `Unit`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.decLt`, `instHPow`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `Option`, `ite`

<a id="def-264bc12b56c5844a"></a>
## `CodedSorting.CommonNormalizationController.run`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L161)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w →
    ℕ →
      CodedSorting.CommonNormalizationController.State L R B b d w →
        CodedSorting.CommonNormalizationController.State L R B b d w × ℕ
```

**定义**

```lean
fun {L R B b d w} p x x_1 =>
  Nat.brecOn (motive := fun x =>
    CodedSorting.CommonNormalizationController.State L R B b d w →
      CodedSorting.CommonNormalizationController.State L R B b d w × ℕ)
    x
    (fun x f x_2 =>
      (match (motive :=
          (x : ℕ) →
            CodedSorting.CommonNormalizationController.State L R B b d w →
              Nat.below (motive := fun x =>
                  CodedSorting.CommonNormalizationController.State L R B b d w →
                    CodedSorting.CommonNormalizationController.State L R B b d w × ℕ)
                  x →
                CodedSorting.CommonNormalizationController.State L R B b d w × ℕ)
          x, x_2 with
        | 0, s => fun x => (s, 0)
        | n.succ, s => fun x =>
          let first := CodedSorting.CommonNormalizationController.step p s;
          let rest := x.1 first.1;
          (rest.1, first.2 + rest.2))
        f)
    x_1
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.CommonNormalizationController.microRun.match_1](NormalizationController.definitions.md#def-5fe7351155ee3738)
- [CodedSorting.CommonNormalizationController.step](NormalizationController.definitions.md#def-35b0e81743543f27)

**基础库名称**

`Nat.brecOn`, `Prod.mk`, `instOfNatNat`, `Prod.fst`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Nat.succ`, `Prod.snd`

<a id="def-26af14d29c13c568"></a>
## `CodedSorting.CommonNormalizationController.initial`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L178)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w →
    CodedSorting.WordControl.Words L w →
      CodedSorting.WordControl.Words d w →
        CodedSorting.WordControl.Words d w →
          CodedSorting.CommonNormalizationController.Disk R B w →
            CodedSorting.CommonNormalizationController.State L R B b d w
```

**定义**

```lean
fun {L R B b d w} p ram inputCount outputCount disk =>
  { ram := ram, buffer := fun x => p.padding, scratch := fun x => p.padding,
    counter := CodedSorting.PhysicalNormalizationLayout.counterCode d w 0, inputCount := inputCount,
    outputCount := outputCount, phase := CodedSorting.CommonNormalizationController.code p 0,
    stage := CodedSorting.CommonNormalizationController.code p 0, disk := disk }
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.counterCode](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-92718a548009d747)
- [CodedSorting.CommonNormalizationController.State.mk](NormalizationController.definitions.md#def-fb93c0454ab3d11a)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.CommonNormalizationController.Disk](NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.CommonNormalizationController.step._proof_7](NormalizationController.definitions.md#def-074d1aa92a867972)
- [CodedSorting.CommonNormalizationController.code](NormalizationController.definitions.md#def-c011e67b6b9fd156)
- [CodedSorting.CommonNormalizationController.Program.padding](NormalizationController.definitions.md#def-d1fbc1c5889ded60)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-2e4323c264f6c9d9"></a>
## `CodedSorting.CommonNormalizationController.outputWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationController.lean#L452)

**类型**

```lean
{L R B b d w : ℕ} →
  CodedSorting.CommonNormalizationController.Program L R B b d w →
    CodedSorting.CommonNormalizationController.State L R B b d w →
      CodedSorting.BlockReflection.Disk (CodedSorting.WordControl.Word w)
```

**定义**

```lean
fun {L R B b d w} p s =>
  CodedSorting.PhysicalNormalizationCompact.targetWord (CodedSorting.CommonNormalizationController.outputProgram p s)
    (CodedSorting.CommonNormalizationController.compactView s.disk)
```

**继续展开**

- [CodedSorting.CommonNormalizationController.outputProgram](NormalizationController.definitions.md#def-30ac3096fc21aa58)
- [CodedSorting.BlockReflection.Disk](../../Interchange/Framework/Memory/LayoutMachine.definitions.md#def-1f6cc5cd0ca85726)
- [CodedSorting.CommonNormalizationController.compactView](NormalizationController.definitions.md#def-8b4a7b91efa6bfbb)
- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonNormalizationController.State.disk](NormalizationController.definitions.md#def-57b507872aac004b)
- [CodedSorting.PhysicalNormalizationCompact.targetWord](PhysicalNormalizationCompact.definitions.md#def-2c2009d41f4dd5b2)

**基础库名称**

`Nat`

<a id="def-f1513b45dd51d6d1"></a>
## `CodedSorting.CommonNormalizationController.code._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean)

**类型**

```lean
∀ {L R B b d w : ℕ}, CodedSorting.CommonNormalizationController.Program L R B b d w → ∀ (k : Fin 8), ↑k < 2 ^ w
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)

**基础库名称**

`Preorder.toLT`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `Fin.val`, `HPow.hPow`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-4d7d169c67ab4ee8"></a>
## `CodedSorting.CommonNormalizationController.converter._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean)

**类型**

```lean
∀ {L R B b d w : ℕ}, CodedSorting.CommonNormalizationController.Program L R B b d w → ∀ n ≤ R, n < (2 ^ w) ^ d
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)

**基础库名称**

`Preorder.toLT`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instHPow`, `OfNat.ofNat`

<a id="def-b6aba43c48fad852"></a>
## `CodedSorting.CommonNormalizationController.coreMicro._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean)

**类型**

```lean
∀ {L R B b d w : ℕ}, CodedSorting.CommonNormalizationController.Program L R B b d w → 4 ≤ 2 ^ w
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Program](NormalizationController.definitions.md#def-8e30ae3ef69cec39)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-4aaa778d88fe4973"></a>
## `CodedSorting.CommonNormalizationController.expandView.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](NormalizationController.lean)

**类型**

```lean
{R : ℕ} →
  (motive : CodedSorting.PhysicalNormalizationLayout.Address R → Sort u_1) →
    (x : CodedSorting.PhysicalNormalizationLayout.Address R) →
      ((a : Fin R) → motive (Sum.inl a)) → ((a : Fin R) → motive (Sum.inr a)) → motive x
```

**定义**

```lean
fun {R} motive x h_1 h_2 => Sum.casesOn x (fun val => h_1 val) fun val => h_2 val
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Address](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-07aca1946acd437c)

**基础库名称**

`Sum.casesOn`, `Sum.inl`, `Sum.inr`, `Nat`, `Fin`

<a id="def-6522fd210bdae81e"></a>
## `CodedSorting.CommonNormalizationController.inputProgram._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean)

**类型**

```lean
∀ {L R B b d w : ℕ} (s : CodedSorting.CommonNormalizationController.State L R B b d w),
  min (CodedSorting.WordControl.decodeWords s.inputCount) R ≤ R
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.decodeWords](../Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonNormalizationController.State.inputCount](NormalizationController.definitions.md#def-589dac48ea92a522)

**基础库名称**

`LE.le`, `instLENat`, `Nat`, `Min.min`, `instMinNat`

<a id="def-7d6980ad396c2e40"></a>
## `CodedSorting.CommonNormalizationController.installExpand.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](NormalizationController.lean)

**类型**

```lean
{R : ℕ} →
  (motive : CodedSorting.CommonNormalizationController.Address R → Sort u_1) →
    (x : CodedSorting.CommonNormalizationController.Address R) →
      ((a : Fin R) → motive (Sum.inl a)) →
        ((a : Fin R) → motive (Sum.inr (Sum.inl a))) → ((a : Fin R) → motive (Sum.inr (Sum.inr a))) → motive x
```

**定义**

```lean
fun {R} motive x h_1 h_2 h_3 =>
  Sum.casesOn x (fun val => h_1 val) fun val => Sum.casesOn val (fun val => h_2 val) fun val => h_3 val
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Address](NormalizationController.definitions.md#def-1cfe9467af4437b1)

**基础库名称**

`Sum.casesOn`, `Sum`, `Sum.inl`, `Sum.inr`, `Nat`, `Fin`

<a id="def-5fe7351155ee3738"></a>
## `CodedSorting.CommonNormalizationController.microRun.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](NormalizationController.lean)

**类型**

```lean
{L R B b d w : ℕ} →
  (motive : ℕ → CodedSorting.CommonNormalizationController.State L R B b d w → Sort u_1) →
    (x : ℕ) →
      (x_1 : CodedSorting.CommonNormalizationController.State L R B b d w) →
        ((s : CodedSorting.CommonNormalizationController.State L R B b d w) → motive 0 s) →
          ((n : ℕ) → (s : CodedSorting.CommonNormalizationController.State L R B b d w) → motive n.succ s) →
            motive x x_1
```

**定义**

```lean
fun {L R B b d w} motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-b35a2e14a0fc86f9"></a>
## `CodedSorting.CommonNormalizationController.outputProgram._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean)

**类型**

```lean
∀ {L R B b d w : ℕ} (s : CodedSorting.CommonNormalizationController.State L R B b d w),
  min (CodedSorting.WordControl.decodeWords s.outputCount) (R - 1) ≤ R
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.WordControl.decodeWords](../Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonNormalizationController.State.outputCount](NormalizationController.definitions.md#def-6759209159746a5f)

**基础库名称**

`HSub.hSub`, `Preorder.toLE`, `instSubNat`, `instOfNatNat`, `LE.le`, `instHSub`, `Nat.instPreorder`, `Nat`, `OfNat.ofNat`, `Min.min`, `instMinNat`

<a id="def-074d1aa92a867972"></a>
## `CodedSorting.CommonNormalizationController.step._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationController.lean)

**类型**

```lean
NeZero (7 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-0d17696600d8128c"></a>
## `CodedSorting.CommonNormalizationController.step.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](NormalizationController.lean)

**类型**

```lean
(motive : ℕ → Sort u_1) →
  (x : ℕ) → (Unit → motive 0) → (Unit → motive 1) → (Unit → motive 2) → ((x : ℕ) → motive x) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 h_4 =>
  if h_1_1 : x = 0 then ⋯ ▸ ⋯ ▸ h_1 ()
  else
    if h_2_1 : x = 1 then Eq.ndrec (motive := fun x => ¬x = 0 → motive x) (fun h_1 => ⋯ ▸ h_2 ()) ⋯ h_1_1
    else
      if h_3_1 : x = 2 then
        Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → motive x) (fun h_1 h_2 => ⋯ ▸ h_3 ()) ⋯ h_1_1 h_2_1
      else h_4 x
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `instOfNatNat`, `dite`, `Unit`, `Nat`, `Eq.ndrec`, `instDecidableEqNat`, `OfNat.ofNat`, `Eq.symm`, `Eq`, `Not`
