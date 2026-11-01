# KeyRecordWords 的定义

[源码](KeyRecordWords.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-da9a81f7a1b37843"></a>
## `CodedSorting.KeyRecords.Record`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](KeyRecordWords.lean#L12)

**类型**

```lean
Type
```

**定义**

```lean
WithBot (WithTop (Lex (ℕ × ℕ)))
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`WithBot`, `Lex`, `Nat`, `Prod`, `WithTop`

<a id="def-54535a8f09e69570"></a>
## `CodedSorting.KeyRecordWords.Record`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](KeyRecordWords.lean#L75)

**类型**

```lean
ℕ → Type
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record.data](KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.KeyRecordWords.Record.bottom](KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.KeyRecordWords.Record.top](KeyRecordWords.definitions.md#def-dfff22d085934d4b)

**基础库名称**

`Nat`

<a id="def-ad7ef446def9fade"></a>
## `CodedSorting.KeyRecordWords.Record.casesOn`

读取 `CodedSorting.KeyRecordWords.Record` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](KeyRecordWords.lean#L75)

**类型**

```lean
{w : ℕ} →
  {motive : CodedSorting.KeyRecordWords.Record w → Sort u} →
    (t : CodedSorting.KeyRecordWords.Record w) →
      motive CodedSorting.KeyRecordWords.Record.bottom →
        ((key payload : CodedSorting.WordControl.Word w) →
            motive (CodedSorting.KeyRecordWords.Record.data key payload)) →
          motive CodedSorting.KeyRecordWords.Record.top → motive t
```

**定义**

```lean
fun {w} {motive} t bottom data top =>
  CodedSorting.KeyRecordWords.Record.rec bottom (fun key payload => data key payload) top t
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record.data](KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.KeyRecordWords.Record.top](KeyRecordWords.definitions.md#def-dfff22d085934d4b)
- [CodedSorting.KeyRecordWords.Record.rec](KeyRecordWords.definitions.md#def-c59a68bea0d03f0b)

**基础库名称**

`Nat`

<a id="def-c59a68bea0d03f0b"></a>
## `CodedSorting.KeyRecordWords.Record.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](KeyRecordWords.lean#L75)

**类型**

```lean
{w : ℕ} →
  {motive : CodedSorting.KeyRecordWords.Record w → Sort u} →
    motive CodedSorting.KeyRecordWords.Record.bottom →
      ((key payload : CodedSorting.WordControl.Word w) → motive (CodedSorting.KeyRecordWords.Record.data key payload)) →
        motive CodedSorting.KeyRecordWords.Record.top → (t : CodedSorting.KeyRecordWords.Record w) → motive t
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record.data](KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.KeyRecordWords.Record.top](KeyRecordWords.definitions.md#def-dfff22d085934d4b)

**基础库名称**

`Nat`

<a id="def-8224b0db2863a7d3"></a>
## `CodedSorting.KeyRecordWords.Record.bottom`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](KeyRecordWords.lean#L76)

**类型**

```lean
{w : ℕ} → CodedSorting.KeyRecordWords.Record w
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)

**基础库名称**

`Nat`

<a id="def-4ed08201e01cac90"></a>
## `CodedSorting.KeyRecordWords.Record.data`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](KeyRecordWords.lean#L77)

**类型**

```lean
{w : ℕ} → CodedSorting.WordControl.Word w → CodedSorting.WordControl.Word w → CodedSorting.KeyRecordWords.Record w
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)

**基础库名称**

`Nat`

<a id="def-dfff22d085934d4b"></a>
## `CodedSorting.KeyRecordWords.Record.top`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](KeyRecordWords.lean#L78)

**类型**

```lean
{w : ℕ} → CodedSorting.KeyRecordWords.Record w
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)

**基础库名称**

`Nat`

<a id="def-6f337235d082695a"></a>
## `CodedSorting.KeyRecordWords.abstract`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](KeyRecordWords.lean#L81)

**类型**

```lean
{w : ℕ} → CodedSorting.KeyRecordWords.Record w → CodedSorting.KeyRecords.Record
```

**定义**

```lean
fun {w} x =>
  match x with
  | CodedSorting.KeyRecordWords.Record.bottom => ⊥
  | CodedSorting.KeyRecordWords.Record.data key payload => ↑↑(toLex (↑key, ↑payload))
  | CodedSorting.KeyRecordWords.Record.top => ↑⊤
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.abstract.match_1](KeyRecordWords.definitions.md#def-48647a6fe9f5dbd8)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecords.Record](KeyRecordWords.definitions.md#def-da9a81f7a1b37843)

**基础库名称**

`WithBot.some`, `Equiv.instFunLike`, `Lex`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `Prod.mk`, `instOfNatNat`, `Bot.bot`, `Fin.val`, `WithTop.some`, `Unit`, `WithTop.top`, `HPow.hPow`, `Nat`, `instHPow`, `Prod`, `Top.top`, `OfNat.ofNat`, `DFunLike.coe`, `WithBot.bot`, `WithTop`, `toLex`

<a id="def-efc63314861ebe3a"></a>
## `_private.CodedSorting.Shared.Records.KeyRecordWords.0.CodedSorting.KeyRecordWords.tag_bound`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](KeyRecordWords.lean#L87)

**类型**

```lean
∀ (w : ℕ), 2 ≤ w → 2 < 2 ^ w
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-db8b85b6def9e34c"></a>
## `CodedSorting.KeyRecordWords.encode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](KeyRecordWords.lean#L92)

**类型**

```lean
(w : ℕ) → 2 ≤ w → CodedSorting.KeyRecordWords.Record w → CodedSorting.WordControl.Words 3 w
```

**定义**

```lean
fun w hw x =>
  match x with
  | CodedSorting.KeyRecordWords.Record.bottom => ![0, 0, 0]
  | CodedSorting.KeyRecordWords.Record.data key payload => ![⟨1, ⋯⟩, key, payload]
  | CodedSorting.KeyRecordWords.Record.top => ![⟨2, ⋯⟩, 0, 0]
```

**继续展开**

- [_private.CodedSorting.Shared.Records.KeyRecordWords.0.CodedSorting.KeyRecordWords.tag_bound](KeyRecordWords.definitions.md#def-efc63314861ebe3a)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.abstract.match_1](KeyRecordWords.definitions.md#def-48647a6fe9f5dbd8)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.encode._proof_15](KeyRecordWords.definitions.md#def-c9e5323d2b8d49da)
- [CodedSorting.KeyRecordWords.encode._proof_14](KeyRecordWords.definitions.md#def-d4395a52bba50136)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `Fin.instOfNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Unit`, `HPow.hPow`, `Nat`, `Matrix.vecEmpty`, `instHPow`, `OfNat.ofNat`, `Matrix.vecCons`

<a id="def-3f469f7bb48913b3"></a>
## `CodedSorting.KeyRecordWords.decode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](KeyRecordWords.lean#L99)

**类型**

```lean
{w : ℕ} → CodedSorting.WordControl.Words 3 w → CodedSorting.KeyRecordWords.Record w
```

**定义**

```lean
fun {w} words =>
  if ↑(words 0) = 1 then CodedSorting.KeyRecordWords.Record.data (words 1) (words 2)
  else if ↑(words 0) = 2 then CodedSorting.KeyRecordWords.Record.top else CodedSorting.KeyRecordWords.Record.bottom
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record.data](KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.KeyRecordWords.Record.top](KeyRecordWords.definitions.md#def-dfff22d085934d4b)
- [CodedSorting.KeyRecordWords.decode._proof_16](KeyRecordWords.definitions.md#def-ec69abc577cebb95)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.instOfNat`, `instOfNatNat`, `Fin.val`, `HPow.hPow`, `Nat`, `instDecidableEqNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `ite`

<a id="def-28947ec3b2347acc"></a>
## `CodedSorting.KeyRecordWords.abstract_injective`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](KeyRecordWords.lean#L112)

**类型**

```lean
∀ (w : ℕ), Function.Injective CodedSorting.KeyRecordWords.abstract
```

**继续展开**

- [CodedSorting.KeyRecordWords.abstract](KeyRecordWords.definitions.md#def-6f337235d082695a)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecords.Record](KeyRecordWords.definitions.md#def-da9a81f7a1b37843)

**基础库名称**

`Nat`, `Function.Injective`

<a id="def-48647a6fe9f5dbd8"></a>
## `CodedSorting.KeyRecordWords.abstract.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](KeyRecordWords.lean)

**类型**

```lean
{w : ℕ} →
  (motive : CodedSorting.KeyRecordWords.Record w → Sort u_1) →
    (x : CodedSorting.KeyRecordWords.Record w) →
      (Unit → motive CodedSorting.KeyRecordWords.Record.bottom) →
        ((key payload : CodedSorting.WordControl.Word w) →
            motive (CodedSorting.KeyRecordWords.Record.data key payload)) →
          (Unit → motive CodedSorting.KeyRecordWords.Record.top) → motive x
```

**定义**

```lean
fun {w} motive x h_1 h_2 h_3 =>
  CodedSorting.KeyRecordWords.Record.casesOn x (h_1 ()) (fun key payload => h_2 key payload) (h_3 ())
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record.casesOn](KeyRecordWords.definitions.md#def-ad7ef446def9fade)
- [CodedSorting.KeyRecordWords.Record.data](KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.KeyRecordWords.Record](KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.KeyRecordWords.Record.top](KeyRecordWords.definitions.md#def-dfff22d085934d4b)

**基础库名称**

`Unit.unit`, `Unit`, `Nat`

<a id="def-ec69abc577cebb95"></a>
## `CodedSorting.KeyRecordWords.decode._proof_16`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](KeyRecordWords.lean)

**类型**

```lean
NeZero (2 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-d4395a52bba50136"></a>
## `CodedSorting.KeyRecordWords.encode._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](KeyRecordWords.lean)

**类型**

```lean
∀ (w : ℕ), NeZero (2 ^ w)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `OfNat.ofNat`, `MulZeroClass.toZero`

<a id="def-c9e5323d2b8d49da"></a>
## `CodedSorting.KeyRecordWords.encode._proof_15`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](KeyRecordWords.lean)

**类型**

```lean
∀ (w : ℕ), 2 ≤ w → 1 < 2 ^ w
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`
