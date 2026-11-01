# BucketMachine 的定义

[源码](BucketMachine.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-11002f2d737e133d"></a>
## `CodedSorting.BucketMachine.bucket`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BucketMachine.lean#L21)

**类型**

```lean
{α : Type u_1} → {K : ℕ} → (α → Fin K) → List α → Fin K → List α
```

**定义**

```lean
fun {α} {K} key xs k => List.filter (fun a => key a == k) xs
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instDecidableEqFin`, `instBEqOfDecidableEq`, `List`, `BEq.beq`, `Nat`, `List.filter`, `Fin`

<a id="def-36f30f5275354d85"></a>
## `CodedSorting.BucketMachine.pack`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BucketMachine.lean#L70)

**类型**

```lean
{α : Type u_1} → (B : ℕ) → 0 < B → List α → List (List α)
```

**定义**

```lean
fun {α} B hB =>
  ⋯.fix fun xs a =>
    (match (motive :=
        (xs : List α) →
          ((y : List α) → (invImage (fun x => x.length) instWellFoundedRelationOfSizeOf).1 y xs → List (List α)) →
            List (List α))
        xs with
      | [] => fun x => []
      | a :: rest => fun x => List.take B (a :: rest) :: x (List.drop B (a :: rest)) ⋯)
      a
```

**继续展开**

- [CodedSorting.BucketMachine.pack.match_1](BucketMachine.definitions.md#def-3edb15bfaa532c1c)
- [CodedSorting.BucketMachine.pack._proof_2](BucketMachine.definitions.md#def-c3ba41b83fb6374a)
- [CodedSorting.BucketMachine.pack._proof_1](BucketMachine.definitions.md#def-b1baea5e536615e7)

**基础库名称**

`invImage`, `WellFoundedRelation`, `instOfNatNat`, `List.cons`, `List`, `Unit`, `List.drop`, `Nat`, `LT.lt`, `instWellFoundedRelationOfSizeOf`, `instSizeOfNat`, `instLTNat`, `OfNat.ofNat`, `List.take`, `List.length`, `WellFounded.fix`, `List.nil`

<a id="def-b1baea5e536615e7"></a>
## `CodedSorting.BucketMachine.pack._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BucketMachine.lean)

**类型**

```lean
∀ {α : Type u_1}, WellFounded (invImage (fun x => x.length) instWellFoundedRelationOfSizeOf).1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`invImage`, `WellFoundedRelation`, `List`, `Nat`, `instWellFoundedRelationOfSizeOf`, `instSizeOfNat`, `WellFounded`, `List.length`

<a id="def-c3ba41b83fb6374a"></a>
## `CodedSorting.BucketMachine.pack._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BucketMachine.lean)

**类型**

```lean
∀ {α : Type u_1} (B : ℕ),
  0 < B →
    ∀ (a : α) (rest : List α),
      (invImage (fun x => x.length) instWellFoundedRelationOfSizeOf).1 (List.drop B (a :: rest)) (a :: rest)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`invImage`, `WellFoundedRelation`, `instOfNatNat`, `List.cons`, `List`, `List.drop`, `Nat`, `LT.lt`, `instWellFoundedRelationOfSizeOf`, `instSizeOfNat`, `instLTNat`, `OfNat.ofNat`, `List.length`

<a id="def-3edb15bfaa532c1c"></a>
## `CodedSorting.BucketMachine.pack.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](BucketMachine.lean)

**类型**

```lean
{α : Type u_1} →
  (motive : List α → Sort u_2) →
    (xs : List α) → (Unit → motive []) → ((a : α) → (rest : List α) → motive (a :: rest)) → motive xs
```

**定义**

```lean
fun {α} motive xs h_1 h_2 => List.casesOn xs (h_1 ()) fun head tail => h_2 head tail
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `List.casesOn`, `List.nil`
