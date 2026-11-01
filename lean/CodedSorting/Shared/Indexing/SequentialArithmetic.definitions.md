# SequentialArithmetic 的定义

[源码](SequentialArithmetic.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2f2ddfa2bc96f097"></a>
## `CodedSorting.SequentialArithmetic.multiply`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SequentialArithmetic.lean#L19)

**类型**

```lean
{Q : ℕ} → ℕ → 0 < Q → Fin Q → Fin Q
```

**定义**

```lean
fun {Q} a hQ x => ⟨a * ↑x % Q, ⋯⟩
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiply._proof_1](SequentialArithmetic.definitions.md#def-36b1f588ffdfface)

**基础库名称**

`HMul.hMul`, `Fin.mk`, `Nat.instMod`, `instHMod`, `instMulNat`, `instOfNatNat`, `Fin.val`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-90e6aa00b76f15a7"></a>
## `CodedSorting.SequentialArithmetic.multiplicationRun`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SequentialArithmetic.lean#L22)

**类型**

```lean
{Q a : ℕ} → 0 < a → 0 < Q → Fin Q → Fin a
```

**定义**

```lean
fun {Q a} ha hQ x => ⟨a * ↑x / Q, ⋯⟩
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiplicationRun._proof_2](SequentialArithmetic.definitions.md#def-ba04f34f9084f7de)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Fin.mk`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Nat`, `LT.lt`, `Nat.instDiv`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-c03a22fa254d24ac"></a>
## `CodedSorting.SequentialArithmetic.multiplication_increasing_in_run`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SequentialArithmetic.lean#L25)

**类型**

```lean
∀ {Q a : ℕ} (ha : 0 < a) (hQ : 0 < Q) (x y : Fin Q),
  x < y →
    CodedSorting.SequentialArithmetic.multiplicationRun ha hQ x =
        CodedSorting.SequentialArithmetic.multiplicationRun ha hQ y →
      CodedSorting.SequentialArithmetic.multiply a hQ x < CodedSorting.SequentialArithmetic.multiply a hQ y
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiplicationRun](SequentialArithmetic.definitions.md#def-90e6aa00b76f15a7)
- [CodedSorting.SequentialArithmetic.multiply](SequentialArithmetic.definitions.md#def-2f2ddfa2bc96f097)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-01c1425c48ff0323"></a>
## `CodedSorting.SequentialArithmetic.multiply_bijective`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SequentialArithmetic.lean#L66)

**类型**

```lean
∀ {Q a : ℕ} (hQ : 0 < Q), a.Coprime Q → Function.Bijective (CodedSorting.SequentialArithmetic.multiply a hQ)
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiply](SequentialArithmetic.definitions.md#def-2f2ddfa2bc96f097)

**基础库名称**

`Nat.Coprime`, `instOfNatNat`, `Nat`, `LT.lt`, `Function.Bijective`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-347eea4112933180"></a>
## `CodedSorting.SequentialArithmetic.multiplicationEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SequentialArithmetic.lean#L70)

**类型**

```lean
{Q a : ℕ} → 0 < Q → a.Coprime Q → Equiv.Perm (Fin Q)
```

**定义**

```lean
fun {Q a} hQ hcoprime => Equiv.ofBijective (CodedSorting.SequentialArithmetic.multiply a hQ) ⋯
```

**继续展开**

- [CodedSorting.SequentialArithmetic.multiply](SequentialArithmetic.definitions.md#def-2f2ddfa2bc96f097)
- [CodedSorting.SequentialArithmetic.multiply_bijective](SequentialArithmetic.definitions.md#def-01c1425c48ff0323)

**基础库名称**

`Nat.Coprime`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `Equiv.ofBijective`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-4958ad02f45d9028"></a>
## `CodedSorting.SequentialArithmetic.additionRun`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SequentialArithmetic.lean#L89)

**类型**

```lean
{Q : ℕ} → Fin Q → Fin Q → Fin 2
```

**定义**

```lean
fun {Q} c x => ⟨(↑x + ↑c) / Q, ⋯⟩
```

**继续展开**

- [CodedSorting.SequentialArithmetic.additionRun._proof_4](SequentialArithmetic.definitions.md#def-f72a43ec29c2c162)

**基础库名称**

`instHDiv`, `Fin.mk`, `HDiv.hDiv`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-1af292012b811a2b"></a>
## `CodedSorting.SequentialArithmetic.addOffset`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](SequentialArithmetic.lean#L94)

**类型**

```lean
{Q : ℕ} → Fin Q → Fin Q → Fin Q
```

**定义**

```lean
fun {Q} c x => ⟨(↑x + ↑c) % Q, ⋯⟩
```

**继续展开**

- [CodedSorting.SequentialArithmetic.addOffset._proof_5](SequentialArithmetic.definitions.md#def-77416f8a442ce138)

**基础库名称**

`Fin.mk`, `Nat.instMod`, `instHMod`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-77416f8a442ce138"></a>
## `CodedSorting.SequentialArithmetic.addOffset._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SequentialArithmetic.lean)

**类型**

```lean
∀ {Q : ℕ} (c x : Fin Q), (↑x + ↑c) % Q < Q
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMod`, `instHMod`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`

<a id="def-f72a43ec29c2c162"></a>
## `CodedSorting.SequentialArithmetic.additionRun._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SequentialArithmetic.lean)

**类型**

```lean
∀ {Q : ℕ} (c x : Fin Q), (↑x + ↑c) / Q < 2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-ba04f34f9084f7de"></a>
## `CodedSorting.SequentialArithmetic.multiplicationRun._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SequentialArithmetic.lean)

**类型**

```lean
∀ {Q a : ℕ}, 0 < a → 0 < Q → ∀ (x : Fin Q), a * ↑x / Q < a
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Nat`, `LT.lt`, `Nat.instDiv`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-36b1f588ffdfface"></a>
## `CodedSorting.SequentialArithmetic.multiply._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](SequentialArithmetic.lean)

**类型**

```lean
∀ {Q : ℕ} (a : ℕ), 0 < Q → ∀ (x : Fin Q), a * ↑x % Q < Q
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `Nat.instMod`, `instHMod`, `instMulNat`, `instOfNatNat`, `Fin.val`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`
