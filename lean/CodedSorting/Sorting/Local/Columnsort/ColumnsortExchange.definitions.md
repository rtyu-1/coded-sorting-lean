# ColumnsortExchange 的定义

[源码](ColumnsortExchange.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-631f7a9c097d4331"></a>
## `CodedSorting.ColumnsortExchange.Fields`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortExchange.lean#L11)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun s => Fin s × Fin s × Fin s × Fin s
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`, `Prod`, `Fin`

<a id="def-a4b5dfeae3779c74"></a>
## `CodedSorting.ColumnsortExchange.encode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortExchange.lean#L13)

**类型**

```lean
(s : ℕ) → CodedSorting.ColumnsortExchange.Fields s ≃ Fin (s ^ 4)
```

**定义**

```lean
fun s =>
  (((Equiv.refl (Fin s)).prodCongr (((Equiv.refl (Fin s)).prodCongr finProdFinEquiv).trans finProdFinEquiv)).trans
        finProdFinEquiv).trans
    (finCongr ⋯)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.ColumnsortExchange.encode._proof_1](ColumnsortExchange.definitions.md#def-eb85c2248b07fc06)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `finCongr`, `Monoid.toNatPow`, `Equiv`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `finProdFinEquiv`, `instHPow`, `Prod`, `Equiv.prodCongr`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `instHMul`

<a id="def-bf2e3e56da5a996e"></a>
## `CodedSorting.ColumnsortExchange.swap34`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortExchange.lean#L24)

**类型**

```lean
(s : ℕ) → CodedSorting.ColumnsortExchange.Fields s ≃ CodedSorting.ColumnsortExchange.Fields s
```

**定义**

```lean
fun s =>
  { toFun := fun x => (x.1, x.2.1, x.2.2.2, x.2.2.1), invFun := fun x => (x.1, x.2.1, x.2.2.2, x.2.2.1), left_inv := ⋯,
    right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.ColumnsortExchange.swap34._proof_2](ColumnsortExchange.definitions.md#def-65a064d844da1b62)

**基础库名称**

`Equiv.mk`, `Equiv`, `Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Prod.snd`

<a id="def-223ecff613971a53"></a>
## `CodedSorting.ColumnsortExchange.swap23`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortExchange.lean#L30)

**类型**

```lean
(s : ℕ) → CodedSorting.ColumnsortExchange.Fields s ≃ CodedSorting.ColumnsortExchange.Fields s
```

**定义**

```lean
fun s =>
  { toFun := fun x => (x.1, x.2.2.1, x.2.1, x.2.2.2), invFun := fun x => (x.1, x.2.2.1, x.2.1, x.2.2.2), left_inv := ⋯,
    right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.ColumnsortExchange.swap23._proof_3](ColumnsortExchange.definitions.md#def-f18245c29435f983)

**基础库名称**

`Equiv.mk`, `Equiv`, `Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Prod.snd`

<a id="def-57782437d8e566ea"></a>
## `CodedSorting.ColumnsortExchange.swap12`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortExchange.lean#L36)

**类型**

```lean
(s : ℕ) → CodedSorting.ColumnsortExchange.Fields s ≃ CodedSorting.ColumnsortExchange.Fields s
```

**定义**

```lean
fun s =>
  { toFun := fun x => (x.2.1, x.1, x.2.2.1, x.2.2.2), invFun := fun x => (x.2.1, x.1, x.2.2.1, x.2.2.2), left_inv := ⋯,
    right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.ColumnsortExchange.swap12._proof_4](ColumnsortExchange.definitions.md#def-bc0e0a0dd8e3306a)

**基础库名称**

`Equiv.mk`, `Equiv`, `Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Prod.snd`

<a id="def-a2193fa6142ef825"></a>
## `CodedSorting.ColumnsortExchange.forward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortExchange.lean#L42)

**类型**

```lean
(s : ℕ) → CodedSorting.ColumnsortExchange.Fields s ≃ CodedSorting.ColumnsortExchange.Fields s
```

**定义**

```lean
fun s =>
  ((CodedSorting.ColumnsortExchange.swap34 s).trans (CodedSorting.ColumnsortExchange.swap23 s)).trans
    (CodedSorting.ColumnsortExchange.swap12 s)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.swap34](ColumnsortExchange.definitions.md#def-bf2e3e56da5a996e)
- [CodedSorting.ColumnsortExchange.swap23](ColumnsortExchange.definitions.md#def-223ecff613971a53)
- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.ColumnsortExchange.swap12](ColumnsortExchange.definitions.md#def-57782437d8e566ea)

**基础库名称**

`Equiv.trans`, `Equiv`, `Nat`

<a id="def-f00041a50c5b2acc"></a>
## `CodedSorting.ColumnsortExchange.transpose`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortExchange.lean#L76)

**类型**

```lean
(s : ℕ) → Fin (s ^ 4) ≃ Fin (s ^ 4)
```

**定义**

```lean
fun s =>
  ((CodedSorting.ColumnsortExchange.encode s).symm.trans (CodedSorting.ColumnsortExchange.forward s)).trans
    (CodedSorting.ColumnsortExchange.encode s)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.encode](ColumnsortExchange.definitions.md#def-a4b5dfeae3779c74)
- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.ColumnsortExchange.forward](ColumnsortExchange.definitions.md#def-a2193fa6142ef825)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`

<a id="def-37af7200b313ff9a"></a>
## `CodedSorting.ColumnsortExchange.forwardRecord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ColumnsortExchange.lean#L85)

**类型**

```lean
(s : ℕ) →
  (Suffix : Type u_1) →
    CodedSorting.ColumnsortExchange.Fields s × Suffix ≃ CodedSorting.ColumnsortExchange.Fields s × Suffix
```

**定义**

```lean
fun s Suffix => (CodedSorting.ColumnsortExchange.forward s).prodCongr (Equiv.refl Suffix)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.ColumnsortExchange.forward](ColumnsortExchange.definitions.md#def-a2193fa6142ef825)

**基础库名称**

`Equiv`, `Nat`, `Prod`, `Equiv.prodCongr`, `Equiv.refl`

<a id="def-eb85c2248b07fc06"></a>
## `CodedSorting.ColumnsortExchange.encode._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ColumnsortExchange.lean)

**类型**

```lean
∀ (s : ℕ), s * (s * (s * s)) = s ^ 4
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-bc0e0a0dd8e3306a"></a>
## `CodedSorting.ColumnsortExchange.swap12._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ColumnsortExchange.lean)

**类型**

```lean
∀ (s : ℕ) (x : CodedSorting.ColumnsortExchange.Fields s),
  ((x.2.1, x.1, x.2.2.1, x.2.2.2).2.1, (x.2.1, x.1, x.2.2.1, x.2.2.2).1, (x.2.1, x.1, x.2.2.1, x.2.2.2).2.2.1,
      (x.2.1, x.1, x.2.2.1, x.2.2.2).2.2.2) =
    ((x.2.1, x.1, x.2.2.1, x.2.2.2).2.1, (x.2.1, x.1, x.2.2.1, x.2.2.2).1, (x.2.1, x.1, x.2.2.1, x.2.2.2).2.2.1,
      (x.2.1, x.1, x.2.2.1, x.2.2.2).2.2.2)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Eq`, `Prod.snd`

<a id="def-f18245c29435f983"></a>
## `CodedSorting.ColumnsortExchange.swap23._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ColumnsortExchange.lean)

**类型**

```lean
∀ (s : ℕ) (x : CodedSorting.ColumnsortExchange.Fields s),
  ((x.1, x.2.2.1, x.2.1, x.2.2.2).1, (x.1, x.2.2.1, x.2.1, x.2.2.2).2.2.1, (x.1, x.2.2.1, x.2.1, x.2.2.2).2.1,
      (x.1, x.2.2.1, x.2.1, x.2.2.2).2.2.2) =
    ((x.1, x.2.2.1, x.2.1, x.2.2.2).1, (x.1, x.2.2.1, x.2.1, x.2.2.2).2.2.1, (x.1, x.2.2.1, x.2.1, x.2.2.2).2.1,
      (x.1, x.2.2.1, x.2.1, x.2.2.2).2.2.2)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Eq`, `Prod.snd`

<a id="def-65a064d844da1b62"></a>
## `CodedSorting.ColumnsortExchange.swap34._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ColumnsortExchange.lean)

**类型**

```lean
∀ (s : ℕ) (x : CodedSorting.ColumnsortExchange.Fields s),
  ((x.1, x.2.1, x.2.2.2, x.2.2.1).1, (x.1, x.2.1, x.2.2.2, x.2.2.1).2.1, (x.1, x.2.1, x.2.2.2, x.2.2.1).2.2.2,
      (x.1, x.2.1, x.2.2.2, x.2.2.1).2.2.1) =
    ((x.1, x.2.1, x.2.2.2, x.2.2.1).1, (x.1, x.2.1, x.2.2.2, x.2.2.1).2.1, (x.1, x.2.1, x.2.2.2, x.2.2.1).2.2.2,
      (x.1, x.2.1, x.2.2.2, x.2.2.1).2.2.1)
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](ColumnsortExchange.definitions.md#def-631f7a9c097d4331)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Nat`, `Prod`, `Fin`, `Eq`, `Prod.snd`
