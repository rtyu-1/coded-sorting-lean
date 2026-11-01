# LayoutMachine 的定义

[源码](LayoutMachine.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2e5e41a722aa61eb"></a>
## `CodedSorting.BlockReflection.reverseAddress`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LayoutMachine.lean#L20)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun L x => L * (x / L) + (L - 1 - x % L)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HMul.hMul`, `HSub.hSub`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instSubNat`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HMod.hMod`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-5d59a52eabcd3361"></a>
## `CodedSorting.BlockReflection.segmentReverseEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LayoutMachine.lean#L22)

**类型**

```lean
(T L : ℕ) → Equiv.Perm (Fin (T * L))
```

**定义**

```lean
fun T L => finProdFinEquiv.symm.trans (((Equiv.refl (Fin T)).prodCongr Fin.revPerm).trans finProdFinEquiv)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `instMulNat`, `Equiv.Perm`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Equiv.prodCongr`, `Fin`, `Equiv.refl`, `Fin.revPerm`, `instHMul`

<a id="def-01ab4e365e60e7b2"></a>
## `CodedSorting.BlockReflection.center`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LayoutMachine.lean#L80)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun L x j => (2 * j + 1) * L - 1 - x
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `instOfNatNat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-f1b696dcb523faea"></a>
## `CodedSorting.BlockReflection.sourceBlock`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LayoutMachine.lean#L82)

**类型**

```lean
ℕ → ℕ → ℕ → Fin 4 → ℕ
```

**定义**

```lean
fun B L b slot =>
  if L ≤ B then if ↑slot = 0 then b - 1 else if ↑slot = 1 then b else b + 1
  else
    let c := CodedSorting.BlockReflection.center L (b * B) (b * B / L + ↑slot / 2);
    if ↑slot % 2 = 0 then c / B else c / B - 1
```

**继续展开**

- [CodedSorting.BlockReflection.center](LayoutMachine.definitions.md#def-01ab4e365e60e7b2)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HSub.hSub`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instDecidableEqNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-98c9023027af1808"></a>
## `CodedSorting.BlockReflection.sourceSlot`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LayoutMachine.lean#L154)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → Fin 4
```

**定义**

```lean
fun B L b y =>
  if CodedSorting.BlockReflection.sourceBlock B L b 0 = CodedSorting.BlockReflection.reverseAddress L y / B then 0
  else
    if CodedSorting.BlockReflection.sourceBlock B L b 1 = CodedSorting.BlockReflection.reverseAddress L y / B then 1
    else
      if CodedSorting.BlockReflection.sourceBlock B L b 2 = CodedSorting.BlockReflection.reverseAddress L y / B then 2
      else 3
```

**继续展开**

- [CodedSorting.BlockReflection.reverseAddress](LayoutMachine.definitions.md#def-2e5e41a722aa61eb)
- [CodedSorting.BlockReflection.sourceSlot._proof_1](LayoutMachine.definitions.md#def-a9c891acec223537)
- [CodedSorting.BlockReflection.sourceBlock](LayoutMachine.definitions.md#def-f1b696dcb523faea)

**基础库名称**

`instHDiv`, `Fin.instOfNat`, `HDiv.hDiv`, `instOfNatNat`, `Nat`, `Nat.instDiv`, `instDecidableEqNat`, `OfNat.ofNat`, `Fin`, `Eq`, `ite`

<a id="def-1f6cc5cd0ca85726"></a>
## `CodedSorting.BlockReflection.Disk`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LayoutMachine.lean#L172)

**类型**

```lean
Type u_2 → Type u_2
```

**定义**

```lean
fun Value => ℕ → Value
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`

<a id="def-f91cdfd77ce1ef79"></a>
## `CodedSorting.LayoutConversion.extract`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LayoutMachine.lean#L323)

**类型**

```lean
{Value : Type u_1} → (B b : ℕ) → ℕ → ℕ → 0 < B → (Fin B → Value) → (Fin b → Value) → Fin b → Value
```

**定义**

```lean
fun {Value} B b start block hB buffer scratch i =>
  if (start + ↑i) / B = block then buffer ⟨(start + ↑i) % B, ⋯⟩ else scratch i
```

**继续展开**

- [CodedSorting.LayoutConversion.extract._proof_9](LayoutMachine.definitions.md#def-bdb5e7aeb7ec7b53)

**基础库名称**

`instHDiv`, `Fin.mk`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `ite`

<a id="def-caaf5ace3c9f2f31"></a>
## `CodedSorting.LayoutConversion.patchBuffer`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LayoutMachine.lean#L454)

**类型**

```lean
{Value : Type u_1} → (B b : ℕ) → ℕ → ℕ → (Fin b → Value) → (Fin B → Value) → Fin B → Value
```

**定义**

```lean
fun {Value} B b start block scratch old i =>
  if h : start ≤ block * B + ↑i ∧ block * B + ↑i < start + b then scratch ⟨block * B + ↑i - start, ⋯⟩ else old i
```

**继续展开**

- [CodedSorting.LayoutConversion.patchBuffer._proof_13](LayoutMachine.definitions.md#def-c127dcdf7f3cd2ae)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `Fin.mk`, `instSubNat`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `dite`, `instHAdd`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instLTNat`, `instDecidableAnd`, `Fin`, `Not`, `Nat.decLe`, `instHMul`

<a id="def-a9c891acec223537"></a>
## `CodedSorting.BlockReflection.sourceSlot._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LayoutMachine.lean)

**类型**

```lean
NeZero (3 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-bdb5e7aeb7ec7b53"></a>
## `CodedSorting.LayoutConversion.extract._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LayoutMachine.lean)

**类型**

```lean
∀ (B b start : ℕ), 0 < B → ∀ (i : Fin b), (start + ↑i) % B < B
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMod`, `instHMod`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-c127dcdf7f3cd2ae"></a>
## `CodedSorting.LayoutConversion.patchBuffer._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LayoutMachine.lean)

**类型**

```lean
∀ (B b start block : ℕ) (i : Fin B), start ≤ block * B + ↑i ∧ block * B + ↑i < start + b → block * B + ↑i - start < b
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `And`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`, `instHMul`
