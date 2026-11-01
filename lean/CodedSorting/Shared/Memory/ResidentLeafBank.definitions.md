# ResidentLeafBank 的定义

[源码](ResidentLeafBank.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-d1d4a603610970b9"></a>
## `CodedSorting.ResidentLeafBank.raw`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafBank.lean#L12)

**类型**

```lean
{cap d w : ℕ} → CodedSorting.ResidentLeafSort.RAM cap d w → Fin (cap * 3) → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun {cap d w} ram i => ram (Fin.natAdd d i)
```

**继续展开**

- [CodedSorting.ResidentLeafSort.RAM](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-351ba66701581e98)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)

**基础库名称**

`Fin.natAdd`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-43482f33d26d74a0"></a>
## `CodedSorting.ResidentLeafBank.getWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafBank.lean#L15)

**类型**

```lean
{cap d w : ℕ} → CodedSorting.ResidentLeafSort.RAM cap d w → ℕ → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun {cap d w} ram j => if h : j < cap * 3 then CodedSorting.ResidentLeafBank.raw ram ⟨j, h⟩ else 0
```

**继续展开**

- [CodedSorting.ResidentLeafBank.raw](ResidentLeafBank.definitions.md#def-d1d4a603610970b9)
- [CodedSorting.ResidentLeafSort.RAM](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-351ba66701581e98)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.ResidentLeafBank.getWord._proof_1](ResidentLeafBank.definitions.md#def-cdfd3185064e2e89)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `Fin.instOfNat`, `instMulNat`, `instOfNatNat`, `dite`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.decLt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Not`, `instHMul`

<a id="def-32878637bd21e594"></a>
## `CodedSorting.ResidentLeafBank.putBlock`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafBank.lean#L42)

**类型**

```lean
{cap d w b : ℕ} →
  ℕ →
    ℕ →
      CodedSorting.WordControl.Words b w →
        CodedSorting.ResidentLeafSort.RAM cap d w → CodedSorting.ResidentLeafSort.RAM cap d w
```

**定义**

```lean
fun {cap d w b} offset valid block ram =>
  Fin.append (CodedSorting.ResidentLeafSort.header ram) fun i =>
    if h : offset ≤ ↑i ∧ ↑i < offset + min valid b then block ⟨↑i - offset, ⋯⟩
    else CodedSorting.ResidentLeafBank.raw ram i
```

**继续展开**

- [CodedSorting.ResidentLeafBank.raw](ResidentLeafBank.definitions.md#def-d1d4a603610970b9)
- [CodedSorting.ResidentLeafSort.RAM](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-351ba66701581e98)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.ResidentLeafSort.header](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-8e5c767d09c080c6)
- [CodedSorting.ResidentLeafBank.putBlock._proof_3](ResidentLeafBank.definitions.md#def-b087e781be3cae88)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `Fin.mk`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `dite`, `instHAdd`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instMin_mathlib`, `Nat.decLt`, `instAddNat`, `instLTNat`, `instDecidableAnd`, `OfNat.ofNat`, `Fin`, `Not`, `Nat.decLe`, `Fin.append`, `Min.min`, `instHMul`

<a id="def-b47675a5946adf37"></a>
## `CodedSorting.ResidentLeafBank.getBlock`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafBank.lean#L106)

**类型**

```lean
{cap d w b : ℕ} → ℕ → ℕ → CodedSorting.ResidentLeafSort.RAM cap d w → CodedSorting.WordControl.Words b w
```

**定义**

```lean
fun {cap d w b} offset valid ram i =>
  if h : ↑i < valid ∧ offset + ↑i < cap * 3 then CodedSorting.ResidentLeafBank.raw ram ⟨offset + ↑i, ⋯⟩ else 0
```

**继续展开**

- [CodedSorting.ResidentLeafBank.raw](ResidentLeafBank.definitions.md#def-d1d4a603610970b9)
- [CodedSorting.ResidentLeafSort.RAM](../../Sorting/Local/Framework/ResidentLeafSort.definitions.md#def-351ba66701581e98)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.ResidentLeafBank.getWord._proof_1](ResidentLeafBank.definitions.md#def-cdfd3185064e2e89)
- [CodedSorting.ResidentLeafBank.getBlock._proof_5](ResidentLeafBank.definitions.md#def-2521151ef7aa5057)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `Fin.instOfNat`, `instMulNat`, `instOfNatNat`, `Fin.val`, `dite`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `instDecidableAnd`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-2521151ef7aa5057"></a>
## `CodedSorting.ResidentLeafBank.getBlock._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ResidentLeafBank.lean)

**类型**

```lean
∀ {cap b : ℕ} (offset valid : ℕ) (i : Fin b), ↑i < valid ∧ offset + ↑i < cap * 3 → offset + ↑i < cap * 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `And`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-cdfd3185064e2e89"></a>
## `CodedSorting.ResidentLeafBank.getWord._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ResidentLeafBank.lean)

**类型**

```lean
∀ {w : ℕ}, NeZero (2 ^ w)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `OfNat.ofNat`, `MulZeroClass.toZero`

<a id="def-b087e781be3cae88"></a>
## `CodedSorting.ResidentLeafBank.putBlock._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ResidentLeafBank.lean)

**类型**

```lean
∀ {cap b : ℕ} (offset valid : ℕ) (i : Fin (cap * 3)), offset ≤ ↑i ∧ ↑i < offset + min valid b → ↑i - offset < b
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instMin_mathlib`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Min.min`, `instHMul`
