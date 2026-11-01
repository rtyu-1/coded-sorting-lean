# CostBound 的定义

[源码](CostBound.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-5a4da9ae621ec1bb"></a>
## `CodedSorting.CommonLocalAdmissible.Admissible`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CostBound.lean#L13)

**类型**

```lean
ℕ → ℕ → ℕ → Prop
```

**定义**

```lean
fun H x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → Prop) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → ℕ → Nat.below (motive := fun x => ℕ → Prop) x → Prop) x, x_2 with
        | 0, n => fun x => n ≤ 512 * H
        | fuel.succ, n => fun x => if n ≤ 512 * H then True else x.1 (CodedSorting.LocalShape.columnLength n))
        f)
    x_1
```

**继续展开**

- [CodedSorting.CommonLocalAdmissible.Admissible.match_1](CostBound.definitions.md#def-de134206ede2ae1d)
- [CodedSorting.LocalShape.columnLength](../../../Shared/Programs/LocalTrace.definitions.md#def-0ba59d4f9543a5be)

**基础库名称**

`HMul.hMul`, `Nat.brecOn`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `PProd`, `Nat`, `True`, `OfNat.ofNat`, `Nat.succ`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-fd9bae2d2f813ccf"></a>
## `CodedSorting.CommonLocalBudget.batchBound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CostBound.lean#L56)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q child c r =>
  if r ≤ 512 * q.height then 256 * (CodedSorting.CommonRecordProgram.recordBlocks q (c * r) + 1)
  else c * (child + 12 * CodedSorting.CommonRecordProgram.recordBlocks q r)
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-de134206ede2ae1d"></a>
## `CodedSorting.CommonLocalAdmissible.Admissible.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](CostBound.lean)

**类型**

```lean
(motive : ℕ → ℕ → Sort u_1) → (x x_1 : ℕ) → ((n : ℕ) → motive 0 n) → ((fuel n : ℕ) → motive fuel.succ n) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`
