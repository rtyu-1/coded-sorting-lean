# MonotoneExtension 的定义

[源码](MonotoneExtension.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e6d33f0e555b9ffb"></a>
## `CodedSorting.CommonMonotoneExtension.unused`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneExtension.lean#L13)

**类型**

```lean
{V M : ℕ} → (Fin V → Fin M) → Finset (Fin M)
```

**定义**

```lean
fun {V M} e => (Finset.image e Finset.univ)ᶜ
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Finset.univ`, `Finset`, `instDecidableEqFin`, `Fin.fintype`, `Nat`, `Finset.booleanAlgebra`, `BooleanAlgebra.toHasCompl`, `Fin`, `Finset.image`, `HasCompl.compl`

<a id="def-525b1f4a0d678b89"></a>
## `CodedSorting.CommonMonotoneExtension.unused_card`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MonotoneExtension.lean#L15)

**类型**

```lean
∀ {V M : ℕ} (e : Fin V → Fin M), StrictMono e → (CodedSorting.CommonMonotoneExtension.unused e).card = M - V
```

**继续展开**

- [CodedSorting.CommonMonotoneExtension.unused](MonotoneExtension.definitions.md#def-e6d33f0e555b9ffb)

**基础库名称**

`StrictMono`, `PartialOrder.toPreorder`, `HSub.hSub`, `instSubNat`, `instHSub`, `Fin.instPartialOrder`, `Nat`, `Finset.card`, `Fin`, `Eq`

<a id="def-3ef396f88bab1358"></a>
## `CodedSorting.CommonMonotoneExtension.tailEmbedding`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneExtension.lean#L20)

**类型**

```lean
{V M : ℕ} → (e : Fin V → Fin M) → StrictMono e → Fin (M - V) ↪o Fin M
```

**定义**

```lean
fun {V M} e he => (CodedSorting.CommonMonotoneExtension.unused e).orderEmbOfFin ⋯
```

**继续展开**

- [CodedSorting.CommonMonotoneExtension.unused](MonotoneExtension.definitions.md#def-e6d33f0e555b9ffb)
- [CodedSorting.CommonMonotoneExtension.unused_card](MonotoneExtension.definitions.md#def-525b1f4a0d678b89)

**基础库名称**

`Finset.orderEmbOfFin`, `StrictMono`, `PartialOrder.toPreorder`, `HSub.hSub`, `instSubNat`, `instLEFin`, `Fin.instLinearOrder`, `instHSub`, `Fin.instPartialOrder`, `Nat`, `OrderEmbedding`, `Fin`

<a id="def-b6174db0565c954a"></a>
## `CodedSorting.CommonMonotoneExtension.extend`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneExtension.lean#L28)

**类型**

```lean
{V M : ℕ} → V ≤ M → (e : Fin V → Fin M) → StrictMono e → Fin M → Fin M
```

**定义**

```lean
fun {V M} h e he x =>
  if hx : ↑x < V then e ⟨↑x, hx⟩ else (CodedSorting.CommonMonotoneExtension.tailEmbedding e he) ⟨↑x - V, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonMonotoneExtension.extend._proof_2](MonotoneExtension.definitions.md#def-dbda1c007fe3a810)
- [CodedSorting.CommonMonotoneExtension.tailEmbedding](MonotoneExtension.definitions.md#def-3ef396f88bab1358)

**基础库名称**

`StrictMono`, `PartialOrder.toPreorder`, `HSub.hSub`, `Fin.mk`, `instSubNat`, `LE.le`, `instLENat`, `Fin.val`, `dite`, `instLEFin`, `instHSub`, `Fin.instPartialOrder`, `Nat`, `LT.lt`, `Nat.decLt`, `OrderEmbedding`, `instLTNat`, `Fin`, `DFunLike.coe`, `Not`, `RelEmbedding.instFunLike`

<a id="def-dc652367a7659577"></a>
## `CodedSorting.CommonMonotoneExtension.permutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneExtension.lean#L54)

**类型**

```lean
{V M : ℕ} → V ≤ M → (e : Fin V → Fin M) → StrictMono e → Equiv.Perm (Fin M)
```

**定义**

```lean
fun {V M} h e he => Equiv.ofBijective (CodedSorting.CommonMonotoneExtension.extend h e he) ⋯
```

**继续展开**

- [CodedSorting.CommonMonotoneExtension.extend](MonotoneExtension.definitions.md#def-b6174db0565c954a)
- [CodedSorting.CommonMonotoneExtension.permutation._proof_3](MonotoneExtension.definitions.md#def-d18b5370dbece3fa)

**基础库名称**

`StrictMono`, `PartialOrder.toPreorder`, `LE.le`, `instLENat`, `Fin.instPartialOrder`, `Equiv.Perm`, `Nat`, `Equiv.ofBijective`, `Fin`

<a id="def-ef8ff90a35dea536"></a>
## `CodedSorting.CommonMonotoneExtension.colour`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneExtension.lean#L64)

**类型**

```lean
{M : ℕ} → ℕ → Fin M → Fin 2
```

**定义**

```lean
fun {M} V x => if ↑x < V then 0 else 1
```

**继续展开**

- [CodedSorting.CommonMonotoneExtension.colour._proof_4](MonotoneExtension.definitions.md#def-693f4a9800831690)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `Fin.val`, `Nat`, `LT.lt`, `Nat.decLt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `ite`

<a id="def-98ba883de6bb98d6"></a>
## `CodedSorting.CommonMonotoneExtension.inverseColour`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneExtension.lean#L81)

**类型**

```lean
{V M : ℕ} → V ≤ M → (e : Fin V → Fin M) → StrictMono e → Fin M → Fin 2
```

**定义**

```lean
fun {V M} h e he x =>
  CodedSorting.CommonMonotoneExtension.colour V
    ((Equiv.symm (CodedSorting.CommonMonotoneExtension.permutation h e he)) x)
```

**继续展开**

- [CodedSorting.CommonMonotoneExtension.colour](MonotoneExtension.definitions.md#def-ef8ff90a35dea536)
- [CodedSorting.CommonMonotoneExtension.permutation](MonotoneExtension.definitions.md#def-dc652367a7659577)

**基础库名称**

`Equiv.instFunLike`, `StrictMono`, `PartialOrder.toPreorder`, `Equiv`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.instPartialOrder`, `Nat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-693f4a9800831690"></a>
## `CodedSorting.CommonMonotoneExtension.colour._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MonotoneExtension.lean)

**类型**

```lean
NeZero (1 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-dbda1c007fe3a810"></a>
## `CodedSorting.CommonMonotoneExtension.extend._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MonotoneExtension.lean)

**类型**

```lean
∀ {V M : ℕ}, V ≤ M → ∀ (x : Fin M), ¬↑x < V → ↑x - V < M - V
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HSub.hSub`, `instSubNat`, `LE.le`, `instLENat`, `Fin.val`, `instHSub`, `Nat`, `LT.lt`, `instLTNat`, `Fin`, `Not`

<a id="def-d18b5370dbece3fa"></a>
## `CodedSorting.CommonMonotoneExtension.permutation._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MonotoneExtension.lean)

**类型**

```lean
∀ {V M : ℕ} (h : V ≤ M) (e : Fin V → Fin M) (he : StrictMono e),
  Function.Bijective (CodedSorting.CommonMonotoneExtension.extend h e he)
```

**继续展开**

- [CodedSorting.CommonMonotoneExtension.extend](MonotoneExtension.definitions.md#def-b6174db0565c954a)

**基础库名称**

`StrictMono`, `PartialOrder.toPreorder`, `LE.le`, `instLENat`, `Fin.instPartialOrder`, `Nat`, `Function.Bijective`, `Fin`
