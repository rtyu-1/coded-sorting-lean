# ExternalMSD 的定义

[源码](ExternalMSD.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-621d9c0b96834a0d"></a>
## `CodedSorting.MSD.digit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExternalMSD.lean#L14)

**类型**

```lean
(base : ℕ) → 0 < base → ℕ → ℕ → Fin base
```

**定义**

```lean
fun base hb remaining x => ⟨x / base ^ remaining % base, ⋯⟩
```

**继续展开**

- [CodedSorting.MSD.digit._proof_1](ExternalMSD.definitions.md#def-81141e19bfad030d)

**基础库名称**

`instHDiv`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `HMod.hMod`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instDiv`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-b11efcbd6ec6994e"></a>
## `CodedSorting.ExternalMSD.sortedChunks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExternalMSD.lean#L270)

**类型**

```lean
{α : Type u_1} → (chunk : ℕ) → 0 < chunk → (List α → List α) → List α → List (List α)
```

**定义**

```lean
fun {α} chunk hc localSort xs => List.map localSort (CodedSorting.BucketMachine.pack chunk hc xs)
```

**继续展开**

- [CodedSorting.BucketMachine.pack](../../../Shared/Programs/BucketMachine.definitions.md#def-36f30f5275354d85)

**基础库名称**

`List.map`, `instOfNatNat`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-a8b344a00e5f0985"></a>
## `CodedSorting.ExternalMSD.child`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ExternalMSD.lean#L480)

**类型**

```lean
{α : Type u_1} → {K : ℕ} → (α → Fin K) → List (List α) → Fin K → List α
```

**定义**

```lean
fun {α} {K} key rows k => List.flatMap (fun row => CodedSorting.BucketMachine.bucket key row k) rows
```

**继续展开**

- [CodedSorting.BucketMachine.bucket](../../../Shared/Programs/BucketMachine.definitions.md#def-11002f2d737e133d)

**基础库名称**

`List`, `Nat`, `Fin`, `List.flatMap`

<a id="def-81141e19bfad030d"></a>
## `CodedSorting.MSD.digit._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ExternalMSD.lean)

**类型**

```lean
∀ (base : ℕ), 0 < base → ∀ (remaining x : ℕ), x / base ^ remaining % base < base
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `Nat.instMonoid`, `Monoid.toNatPow`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `HMod.hMod`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instDiv`, `instHPow`, `instLTNat`, `OfNat.ofNat`
