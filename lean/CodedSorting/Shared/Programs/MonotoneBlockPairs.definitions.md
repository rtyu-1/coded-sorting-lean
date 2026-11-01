# MonotoneBlockPairs 的定义

[源码](MonotoneBlockPairs.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-3fda578a3f5dcbac"></a>
## `CodedSorting.MonotoneBlockPairs.pair`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneBlockPairs.lean#L14)

**类型**

```lean
{Q : ℕ} → Equiv.Perm (Fin Q) → ℕ → Fin Q → ℕ × ℕ
```

**定义**

```lean
fun {Q} e B x => (↑x / B, ↑(e x) / B)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Equiv.instFunLike`, `instHDiv`, `HDiv.hDiv`, `Prod.mk`, `Fin.val`, `Equiv.Perm`, `Nat`, `Nat.instDiv`, `Prod`, `Fin`, `DFunLike.coe`

<a id="def-897bcf41565f72f3"></a>
## `CodedSorting.MonotoneBlockPairs.pairs`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneBlockPairs.lean#L17)

**类型**

```lean
{Q K : ℕ} → Equiv.Perm (Fin Q) → (Fin Q → Fin K) → ℕ → Fin K → List (ℕ × ℕ)
```

**定义**

```lean
fun {Q K} e key B k =>
  (List.map (CodedSorting.MonotoneBlockPairs.pair e B)
      (List.filter (fun x => decide (key x = k)) (List.finRange Q))).dedup
```

**继续展开**

- [CodedSorting.MonotoneBlockPairs.pair](MonotoneBlockPairs.definitions.md#def-3fda578a3f5dcbac)

**基础库名称**

`instDecidableEqProd`, `List.map`, `instDecidableEqFin`, `List.dedup`, `List`, `Equiv.Perm`, `Nat`, `List.filter`, `instDecidableEqNat`, `Prod`, `Fin`, `Decidable.decide`, `List.finRange`, `Eq`

<a id="def-92fbad4edf5c50a1"></a>
## `CodedSorting.MonotoneBlockPairs.schedule`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MonotoneBlockPairs.lean#L79)

**类型**

```lean
{Q K : ℕ} → Equiv.Perm (Fin Q) → (Fin Q → Fin K) → ℕ → List (Fin K × ℕ × ℕ)
```

**定义**

```lean
fun {Q K} e key B =>
  List.flatMap (fun k => List.map (fun a => (k, a)) (CodedSorting.MonotoneBlockPairs.pairs e key B k)) (List.finRange K)
```

**继续展开**

- [CodedSorting.MonotoneBlockPairs.pairs](MonotoneBlockPairs.definitions.md#def-897bcf41565f72f3)

**基础库名称**

`List.map`, `Prod.mk`, `List`, `Equiv.Perm`, `Nat`, `Prod`, `Fin`, `List.finRange`, `List.flatMap`
