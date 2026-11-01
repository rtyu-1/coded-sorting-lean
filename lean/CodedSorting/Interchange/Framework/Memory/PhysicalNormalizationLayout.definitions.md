# PhysicalNormalizationLayout 的定义

[源码](PhysicalNormalizationLayout.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-07aca1946acd437c"></a>
## `CodedSorting.PhysicalNormalizationLayout.Address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L15)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun R => Fin R ⊕ Fin R
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Sum`, `Nat`, `Fin`

<a id="def-9e955a98938d0ed5"></a>
## `CodedSorting.PhysicalNormalizationLayout.Disk`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L18)

**类型**

```lean
ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun R B w => CodedSorting.PhysicalNormalizationLayout.Address R → CodedSorting.WordControl.Words B w
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Address](PhysicalNormalizationLayout.definitions.md#def-07aca1946acd437c)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-678a62c95e8cebaa"></a>
## `CodedSorting.PhysicalNormalizationLayout.State`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](PhysicalNormalizationLayout.lean#L20)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State.mk](PhysicalNormalizationLayout.definitions.md#def-f8bfca1e966aa73b)

**基础库名称**

`Nat`

<a id="def-f8bfca1e966aa73b"></a>
## `CodedSorting.PhysicalNormalizationLayout.State.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalNormalizationLayout.lean#L20)

**类型**

```lean
{R B b d w : ℕ} →
  CodedSorting.WordControl.Words B w →
    CodedSorting.WordControl.Words b w →
      CodedSorting.WordControl.Words d w →
        CodedSorting.WordControl.Word w →
          CodedSorting.PhysicalNormalizationLayout.Disk R B w → CodedSorting.PhysicalNormalizationLayout.State R B b d w
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalNormalizationLayout.Disk](PhysicalNormalizationLayout.definitions.md#def-9e955a98938d0ed5)
- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-c70ce37a8b88fc3e"></a>
## `CodedSorting.PhysicalNormalizationLayout.State.buffer`

读取 `CodedSorting.PhysicalNormalizationLayout.State` 的 `buffer` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalNormalizationLayout.lean#L21)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.State R B b d w → CodedSorting.WordControl.Words B w
```

**定义**

```lean
fun R B b d w self => self.1
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-7a685606d02225f1"></a>
## `CodedSorting.PhysicalNormalizationLayout.State.scratch`

读取 `CodedSorting.PhysicalNormalizationLayout.State` 的 `scratch` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalNormalizationLayout.lean#L22)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.State R B b d w → CodedSorting.WordControl.Words b w
```

**定义**

```lean
fun R B b d w self => self.2
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-0f6743e028e821e8"></a>
## `CodedSorting.PhysicalNormalizationLayout.State.counter`

读取 `CodedSorting.PhysicalNormalizationLayout.State` 的 `counter` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalNormalizationLayout.lean#L23)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.State R B b d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun R B b d w self => self.3
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-d8014df3dd931356"></a>
## `CodedSorting.PhysicalNormalizationLayout.State.phase`

读取 `CodedSorting.PhysicalNormalizationLayout.State` 的 `phase` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalNormalizationLayout.lean#L24)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.State R B b d w → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun R B b d w self => self.4
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)

**基础库名称**

`Nat`

<a id="def-48fddd883aa3f5eb"></a>
## `CodedSorting.PhysicalNormalizationLayout.State.disk`

读取 `CodedSorting.PhysicalNormalizationLayout.State` 的 `disk` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalNormalizationLayout.lean#L25)

**类型**

```lean
{R B b d w : ℕ} →
  CodedSorting.PhysicalNormalizationLayout.State R B b d w → CodedSorting.PhysicalNormalizationLayout.Disk R B w
```

**定义**

```lean
fun R B b d w self => self.5
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Disk](PhysicalNormalizationLayout.definitions.md#def-9e955a98938d0ed5)
- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)

**基础库名称**

`Nat`

<a id="def-ee21ebfead1ec0f6"></a>
## `CodedSorting.PhysicalNormalizationLayout.Program`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](PhysicalNormalizationLayout.lean#L27)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program.mk](PhysicalNormalizationLayout.definitions.md#def-ee384cfcf662b4d7)

**基础库名称**

`Nat`

<a id="def-ee384cfcf662b4d7"></a>
## `CodedSorting.PhysicalNormalizationLayout.Program.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalNormalizationLayout.lean#L27)

**类型**

```lean
{R B b d w : ℕ} →
  (blocks : ℕ) →
    blocks ≤ R →
      blocks < (2 ^ w) ^ d →
        0 < R →
          0 < B →
            b ≤ B →
              8 ≤ 2 ^ w → CodedSorting.WordControl.Word w → CodedSorting.PhysicalNormalizationLayout.Program R B b d w
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-7de1abc85c13406f"></a>
## `CodedSorting.PhysicalNormalizationLayout.Program.blocks`

读取 `CodedSorting.PhysicalNormalizationLayout.Program` 的 `blocks` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalNormalizationLayout.lean#L28)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.Program R B b d w → ℕ
```

**定义**

```lean
fun R B b d w self => self.1
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)

**基础库名称**

`Nat`

<a id="def-b2b3660041ad9aa6"></a>
## `CodedSorting.PhysicalNormalizationLayout.Program.positive_block`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalNormalizationLayout.lean#L32)

**类型**

```lean
∀ {R B b d w : ℕ}, CodedSorting.PhysicalNormalizationLayout.Program R B b d w → 0 < B
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-5a467ed2df64d58d"></a>
## `CodedSorting.PhysicalNormalizationLayout.Program.block_ratio`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalNormalizationLayout.lean#L33)

**类型**

```lean
∀ {R B b d w : ℕ}, CodedSorting.PhysicalNormalizationLayout.Program R B b d w → b ≤ B
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-19a979e41b815eaf"></a>
## `CodedSorting.PhysicalNormalizationLayout.Program.padding`

读取 `CodedSorting.PhysicalNormalizationLayout.Program` 的 `padding` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalNormalizationLayout.lean#L35)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.Program R B b d w → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun R B b d w self => self.8
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)

**基础库名称**

`Nat`

<a id="def-2fdfeb567bc0368f"></a>
## `CodedSorting.PhysicalNormalizationLayout.phaseCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L37)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.Program R B b d w → Fin 8 → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun {R B b d w} p k => ⟨↑k, ⋯⟩
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationLayout.phaseCode._proof_1](PhysicalNormalizationLayout.definitions.md#def-0b98a7a48d816c95)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `instOfNatNat`, `Fin.val`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-92718a548009d747"></a>
## `CodedSorting.PhysicalNormalizationLayout.counterCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L40)

**类型**

```lean
(d w : ℕ) → ℕ → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun d w j => finFunctionFinEquiv.symm ⟨j % (2 ^ w) ^ d, ⋯⟩
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.counterCode._proof_2](PhysicalNormalizationLayout.definitions.md#def-15dd29ac0ee79579)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `finFunctionFinEquiv`, `Monoid.toNatPow`, `Fin.mk`, `Equiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `HMod.hMod`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-acd374e79f7fc86a"></a>
## `CodedSorting.PhysicalNormalizationLayout.index`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L47)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.Program R B b d w → ℕ → Fin R
```

**定义**

```lean
fun {R B b d w} p j => ⟨j % R, ⋯⟩
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationLayout.index._proof_3](PhysicalNormalizationLayout.definitions.md#def-1fbdc629b8772dde)

**基础库名称**

`Fin.mk`, `Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `Fin`

<a id="def-8911b9716478d17d"></a>
## `CodedSorting.PhysicalNormalizationLayout.current`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L52)

**类型**

```lean
{R B b d w : ℕ} → CodedSorting.PhysicalNormalizationLayout.State R B b d w → ℕ
```

**定义**

```lean
fun {R B b d w} s => CodedSorting.WordControl.decodeWords s.counter
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State.counter](PhysicalNormalizationLayout.definitions.md#def-0f6743e028e821e8)
- [CodedSorting.WordControl.decodeWords](../../../Shared/Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)

**基础库名称**

`Nat`

<a id="def-f08ca752e1e41067"></a>
## `CodedSorting.PhysicalNormalizationLayout.nextPhase`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L54)

**类型**

```lean
{R B b d w : ℕ} →
  CodedSorting.PhysicalNormalizationLayout.Program R B b d w →
    Fin 8 →
      CodedSorting.PhysicalNormalizationLayout.State R B b d w →
        CodedSorting.PhysicalNormalizationLayout.State R B b d w
```

**定义**

```lean
fun {R B b d w} p k s =>
  { buffer := s.buffer, scratch := s.scratch, counter := s.counter,
    phase := CodedSorting.PhysicalNormalizationLayout.phaseCode p k, disk := s.disk }
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State.buffer](PhysicalNormalizationLayout.definitions.md#def-c70ce37a8b88fc3e)
- [CodedSorting.PhysicalNormalizationLayout.State.counter](PhysicalNormalizationLayout.definitions.md#def-0f6743e028e821e8)
- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationLayout.State.mk](PhysicalNormalizationLayout.definitions.md#def-f8bfca1e966aa73b)
- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.PhysicalNormalizationLayout.State.disk](PhysicalNormalizationLayout.definitions.md#def-48fddd883aa3f5eb)
- [CodedSorting.PhysicalNormalizationLayout.phaseCode](PhysicalNormalizationLayout.definitions.md#def-2fdfeb567bc0368f)
- [CodedSorting.PhysicalNormalizationLayout.State.scratch](PhysicalNormalizationLayout.definitions.md#def-7a685606d02225f1)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-7f700362a3bac5e3"></a>
## `CodedSorting.PhysicalNormalizationLayout.step`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L57)

**类型**

```lean
{R B b d w : ℕ} →
  CodedSorting.PhysicalNormalizationLayout.Program R B b d w →
    CodedSorting.PhysicalNormalizationLayout.State R B b d w →
      CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ
```

**定义**

```lean
fun {R B b d w} p s =>
  let j := CodedSorting.PhysicalNormalizationLayout.current s;
  if j < p.blocks then
    match ↑s.phase with
    | 0 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 1
          { buffer := s.buffer, scratch := fun x => p.padding, counter := s.counter, phase := s.phase, disk := s.disk },
        0)
    | 1 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 2
          { buffer := s.disk (Sum.inl (CodedSorting.PhysicalNormalizationLayout.index p (j * b / B))),
            scratch := s.scratch, counter := s.counter, phase := s.phase, disk := s.disk },
        1)
    | 2 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 3
          { buffer := s.buffer,
            scratch := CodedSorting.LayoutConversion.extract B b (j * b) (j * b / B) ⋯ s.buffer s.scratch,
            counter := s.counter, phase := s.phase, disk := s.disk },
        0)
    | 3 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 4
          { buffer := s.disk (Sum.inl (CodedSorting.PhysicalNormalizationLayout.index p (j * b / B + 1))),
            scratch := s.scratch, counter := s.counter, phase := s.phase, disk := s.disk },
        1)
    | 4 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 5
          { buffer := s.buffer,
            scratch := CodedSorting.LayoutConversion.extract B b (j * b) (j * b / B + 1) ⋯ s.buffer s.scratch,
            counter := s.counter, phase := s.phase, disk := s.disk },
        0)
    | 5 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 6
          { buffer := CodedSorting.Normalization.pack p.padding s.scratch, scratch := s.scratch, counter := s.counter,
            phase := s.phase, disk := s.disk },
        0)
    | 6 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 0
          { buffer := s.buffer, scratch := s.scratch,
            counter := CodedSorting.PhysicalNormalizationLayout.counterCode d w (j + 1), phase := s.phase,
            disk := Function.update s.disk (Sum.inr (CodedSorting.PhysicalNormalizationLayout.index p j)) s.buffer },
        1)
    | x => (s, 0)
  else (s, 0)
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State.buffer](PhysicalNormalizationLayout.definitions.md#def-c70ce37a8b88fc3e)
- [CodedSorting.PhysicalNormalizationLayout.Address](PhysicalNormalizationLayout.definitions.md#def-07aca1946acd437c)
- [CodedSorting.PhysicalNormalizationLayout.counterCode](PhysicalNormalizationLayout.definitions.md#def-92718a548009d747)
- [CodedSorting.PhysicalNormalizationLayout.current](PhysicalNormalizationLayout.definitions.md#def-8911b9716478d17d)
- [CodedSorting.PhysicalNormalizationLayout.State.counter](PhysicalNormalizationLayout.definitions.md#def-0f6743e028e821e8)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationLayout.Program.padding](PhysicalNormalizationLayout.definitions.md#def-19a979e41b815eaf)
- [CodedSorting.PhysicalNormalizationLayout.State.mk](PhysicalNormalizationLayout.definitions.md#def-f8bfca1e966aa73b)
- [CodedSorting.PhysicalNormalizationLayout.nextPhase](PhysicalNormalizationLayout.definitions.md#def-f08ca752e1e41067)
- [CodedSorting.PhysicalNormalizationLayout.step.match_1](PhysicalNormalizationLayout.definitions.md#def-c811eb9d1aa00fa7)
- [CodedSorting.PhysicalNormalizationLayout.Program.blocks](PhysicalNormalizationLayout.definitions.md#def-7de1abc85c13406f)
- [CodedSorting.PhysicalNormalizationLayout.Program.positive_block](PhysicalNormalizationLayout.definitions.md#def-b2b3660041ad9aa6)
- [CodedSorting.PhysicalNormalizationLayout.step._proof_4](PhysicalNormalizationLayout.definitions.md#def-9842cb876b5d6ae9)
- [CodedSorting.PhysicalNormalizationLayout.index](PhysicalNormalizationLayout.definitions.md#def-acd374e79f7fc86a)
- [CodedSorting.LayoutConversion.extract](LayoutMachine.definitions.md#def-f91cdfd77ce1ef79)
- [CodedSorting.Normalization.pack](../../../Shared/Programs/Normalization.definitions.md#def-97797717e5f5913c)
- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.PhysicalNormalizationLayout.State.disk](PhysicalNormalizationLayout.definitions.md#def-48fddd883aa3f5eb)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)
- [CodedSorting.PhysicalNormalizationLayout.State.scratch](PhysicalNormalizationLayout.definitions.md#def-7a685606d02225f1)
- [CodedSorting.PhysicalNormalizationLayout.State.phase](PhysicalNormalizationLayout.definitions.md#def-d8014df3dd931356)

**基础库名称**

`instHDiv`, `Function.update`, `HMul.hMul`, `Nat.instMonoid`, `instDecidableEqFin`, `Monoid.toNatPow`, `Fin.instOfNat`, `HDiv.hDiv`, `Sum.instDecidableEq`, `Prod.mk`, `instMulNat`, `instOfNatNat`, `Sum.inl`, `Fin.val`, `instHAdd`, `Unit`, `HPow.hPow`, `HAdd.hAdd`, `Sum.inr`, `Nat`, `LT.lt`, `Nat.instDiv`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`, `instHMul`, `ite`

<a id="def-0d08100b73d62612"></a>
## `CodedSorting.PhysicalNormalizationLayout.run`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationLayout.lean#L74)

**类型**

```lean
{R B b d w : ℕ} →
  CodedSorting.PhysicalNormalizationLayout.Program R B b d w →
    ℕ →
      CodedSorting.PhysicalNormalizationLayout.State R B b d w →
        CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ
```

**定义**

```lean
fun {R B b d w} p x x_1 =>
  Nat.brecOn (motive := fun x =>
    CodedSorting.PhysicalNormalizationLayout.State R B b d w →
      CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ)
    x
    (fun x f x_2 =>
      (match (motive :=
          (x : ℕ) →
            CodedSorting.PhysicalNormalizationLayout.State R B b d w →
              Nat.below (motive := fun x =>
                  CodedSorting.PhysicalNormalizationLayout.State R B b d w →
                    CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ)
                  x →
                CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ)
          x, x_2 with
        | 0, s => fun x => (s, 0)
        | fuel.succ, s => fun x =>
          let first := CodedSorting.PhysicalNormalizationLayout.step p s;
          let rest := x.1 first.1;
          (rest.1, first.2 + rest.2))
        f)
    x_1
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationLayout.run.match_1](PhysicalNormalizationLayout.definitions.md#def-26796d097533088a)
- [CodedSorting.PhysicalNormalizationLayout.step](PhysicalNormalizationLayout.definitions.md#def-7f700362a3bac5e3)
- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)

**基础库名称**

`Nat.brecOn`, `Prod.mk`, `instOfNatNat`, `Prod.fst`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Nat.succ`, `Prod.snd`

<a id="def-15dd29ac0ee79579"></a>
## `CodedSorting.PhysicalNormalizationLayout.counterCode._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalNormalizationLayout.lean)

**类型**

```lean
∀ (d w j : ℕ), j % (2 ^ w) ^ d < (2 ^ w) ^ d
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `HMod.hMod`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-1fbdc629b8772dde"></a>
## `CodedSorting.PhysicalNormalizationLayout.index._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalNormalizationLayout.lean)

**类型**

```lean
∀ {R B b d w : ℕ}, CodedSorting.PhysicalNormalizationLayout.Program R B b d w → ∀ (j : ℕ), j % R < R
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`

<a id="def-0b98a7a48d816c95"></a>
## `CodedSorting.PhysicalNormalizationLayout.phaseCode._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalNormalizationLayout.lean)

**类型**

```lean
∀ {R B b d w : ℕ}, CodedSorting.PhysicalNormalizationLayout.Program R B b d w → ∀ (k : Fin 8), ↑k < 2 ^ w
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)

**基础库名称**

`Preorder.toLT`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `Fin.val`, `HPow.hPow`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-26796d097533088a"></a>
## `CodedSorting.PhysicalNormalizationLayout.run.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PhysicalNormalizationLayout.lean)

**类型**

```lean
{R B b d w : ℕ} →
  (motive : ℕ → CodedSorting.PhysicalNormalizationLayout.State R B b d w → Sort u_1) →
    (x : ℕ) →
      (x_1 : CodedSorting.PhysicalNormalizationLayout.State R B b d w) →
        ((s : CodedSorting.PhysicalNormalizationLayout.State R B b d w) → motive 0 s) →
          ((fuel : ℕ) → (s : CodedSorting.PhysicalNormalizationLayout.State R B b d w) → motive fuel.succ s) →
            motive x x_1
```

**定义**

```lean
fun {R B b d w} motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State](PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-9842cb876b5d6ae9"></a>
## `CodedSorting.PhysicalNormalizationLayout.step._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalNormalizationLayout.lean)

**类型**

```lean
NeZero (7 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-c811eb9d1aa00fa7"></a>
## `CodedSorting.PhysicalNormalizationLayout.step.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PhysicalNormalizationLayout.lean)

**类型**

```lean
(motive : ℕ → Sort u_1) →
  (x : ℕ) →
    (Unit → motive 0) →
      (Unit → motive 1) →
        (Unit → motive 2) →
          (Unit → motive 3) →
            (Unit → motive 4) → (Unit → motive 5) → (Unit → motive 6) → ((x : ℕ) → motive x) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 =>
  if h_1_1 : x = 0 then ⋯ ▸ ⋯ ▸ h_1 ()
  else
    if h_2_1 : x = 1 then Eq.ndrec (motive := fun x => ¬x = 0 → motive x) (fun h_1 => ⋯ ▸ h_2 ()) ⋯ h_1_1
    else
      if h_3_1 : x = 2 then
        Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → motive x) (fun h_1 h_2 => ⋯ ▸ h_3 ()) ⋯ h_1_1 h_2_1
      else
        if h_4_1 : x = 3 then
          Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → motive x) (fun h_1 h_2 h_3 => ⋯ ▸ h_4 ()) ⋯ h_1_1
            h_2_1 h_3_1
        else
          if h_5_1 : x = 4 then
            Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → motive x)
              (fun h_1 h_2 h_3 h_4 => ⋯ ▸ h_5 ()) ⋯ h_1_1 h_2_1 h_3_1 h_4_1
          else
            if h_6_1 : x = 5 then
              Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → motive x)
                (fun h_1 h_2 h_3 h_4 h_5 => ⋯ ▸ h_6 ()) ⋯ h_1_1 h_2_1 h_3_1 h_4_1 h_5_1
            else
              if h_7_1 : x = 6 then
                Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → motive x)
                  (fun h_1 h_2 h_3 h_4 h_5 h_6 => ⋯ ▸ h_7 ()) ⋯ h_1_1 h_2_1 h_3_1 h_4_1 h_5_1 h_6_1
              else h_8 x
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `instOfNatNat`, `dite`, `Unit`, `Nat`, `Eq.ndrec`, `instDecidableEqNat`, `OfNat.ofNat`, `Eq.symm`, `Eq`, `Not`
