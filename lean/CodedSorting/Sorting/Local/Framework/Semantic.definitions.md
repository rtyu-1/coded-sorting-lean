# Semantic 的定义

[源码](Semantic.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-b78823851e91ab63"></a>
## `CodedSorting.CommonLocalSemantic.Operation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L18)

**类型**

```lean
Type u_2 → Type u_2
```

**定义**

```lean
fun α => (n : ℕ) → (Fin n → α) → Fin n → α
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`, `Fin`

<a id="def-95a6d284c26943ee"></a>
## `CodedSorting.CommonLocalSemantic.columns`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L20)

**类型**

```lean
{α : Type u_1} → (c r : ℕ) → (Fin (c * r) → α) → Fin c → Fin r → α
```

**定义**

```lean
fun {α} c r f j i => f (finProdFinEquiv (j, i))
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Nat`, `finProdFinEquiv`, `Prod`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-2f94e0dc8bd6f005"></a>
## `CodedSorting.CommonLocalSemantic.batch`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L34)

**类型**

```lean
{α : Type u_1} → CodedSorting.CommonLocalSemantic.Operation α → (c r : ℕ) → (Fin (c * r) → α) → Fin (c * r) → α
```

**定义**

```lean
fun {α} op c r f =>
  CodedSorting.PhysicalLocalSortPadding.flattenColumns c r fun j =>
    op r (CodedSorting.CommonLocalSemantic.columns c r f j)
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalSemantic.columns](Semantic.definitions.md#def-95a6d284c26943ee)
- [CodedSorting.PhysicalLocalSortPadding.flattenColumns](PhysicalLocalSortNode.definitions.md#def-2fddd3888cb48ed2)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Fin`, `instHMul`

<a id="def-73fbf5cf9a4e2cae"></a>
## `CodedSorting.CommonLocalSemantic.forward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L43)

**类型**

```lean
{α : Type u_1} → (s : ℕ) → (Fin (s * CodedSorting.PhysicalLocalSortNode.rows s) → α) → Fin (s * (s * (s ^ 2 * 1))) → α
```

**定义**

```lean
fun {α} s f =>
  CodedSorting.PhysicalLocalSortPadding.flattenColumns s (s * (s ^ 2 * 1))
    (CodedSorting.RecursiveColumnsort.secondInput (s ^ 2) s
      (CodedSorting.CommonLocalSemantic.columns s (CodedSorting.PhysicalLocalSortNode.rows s) f))
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.columns](Semantic.definitions.md#def-95a6d284c26943ee)
- [CodedSorting.PhysicalLocalSortPadding.flattenColumns](PhysicalLocalSortNode.definitions.md#def-2fddd3888cb48ed2)
- [CodedSorting.RecursiveColumnsort.secondInput](../Columnsort/FiniteColumnsort.definitions.md#def-be1706634a4e8f78)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-7cfe465cda0e4774"></a>
## `CodedSorting.CommonLocalSemantic.backward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L46)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] →
      [inst : OrderTop α] →
        (s : ℕ) → (Fin (s * (s * (s ^ 2 * 1))) → α) → Fin (s * CodedSorting.PhysicalLocalSortNode.rows s) → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] s f =>
  CodedSorting.PhysicalLocalSortPadding.flattenColumns s (CodedSorting.PhysicalLocalSortNode.rows s)
    (CodedSorting.PhysicalLocalSortNode.thirdColumns s (CodedSorting.CommonLocalSemantic.columns s (s * (s ^ 2 * 1)) f))
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.columns](Semantic.definitions.md#def-95a6d284c26943ee)
- [CodedSorting.PhysicalLocalSortNode.thirdColumns](PhysicalLocalSortNode.definitions.md#def-706a0fe104c01557)
- [CodedSorting.PhysicalLocalSortPadding.flattenColumns](PhysicalLocalSortNode.definitions.md#def-2fddd3888cb48ed2)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `instMulNat`, `instOfNatNat`, `OrderTop`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-4428e9a1cf4ad9ae"></a>
## `CodedSorting.CommonLocalSemantic.shift`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L114)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] → [inst : OrderTop α] → (s r : ℕ) → ℕ → (Fin (s * r) → α) → Fin ((s + 1) * r) → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] s r h f =>
  CodedSorting.PhysicalLocalSortPadding.flattenColumns (s + 1) r
    (CodedSorting.PhysicalLocalSortPadding.fourthInput s r h (CodedSorting.CommonLocalSemantic.columns s r f))
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.columns](Semantic.definitions.md#def-95a6d284c26943ee)
- [CodedSorting.PhysicalLocalSortPadding.fourthInput](PhysicalLocalSortNode.definitions.md#def-a6a16a5bf73a34cf)
- [CodedSorting.PhysicalLocalSortPadding.flattenColumns](PhysicalLocalSortNode.definitions.md#def-2fddd3888cb48ed2)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `instMulNat`, `instOfNatNat`, `OrderTop`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-601d84687321e5a1"></a>
## `CodedSorting.CommonLocalSemantic.unshift`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L118)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] → [inst : OrderTop α] → (s r : ℕ) → ℕ → (Fin ((s + 1) * r) → α) → Fin (s * r) → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] s r h f =>
  CodedSorting.PhysicalLocalSortPadding.unshiftedRecords s r h (CodedSorting.CommonLocalSemantic.columns (s + 1) r f)
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.columns](Semantic.definitions.md#def-95a6d284c26943ee)
- [CodedSorting.PhysicalLocalSortPadding.unshiftedRecords](PhysicalLocalSortNode.definitions.md#def-419396c640f974a3)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `instMulNat`, `instOfNatNat`, `OrderTop`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-5593436e1b4f55c7"></a>
## `CodedSorting.CommonLocalSemantic.padded_size`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Semantic.lean#L163)

**类型**

```lean
∀ (n : ℕ),
  n ≤
    CodedSorting.LocalShape.sizeChoice n *
      CodedSorting.PhysicalLocalSortNode.rows (CodedSorting.LocalShape.sizeChoice n)
```

**继续展开**

- [CodedSorting.LocalShape.sizeChoice](../../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `Nat`, `instHMul`

<a id="def-7b92eabdfc5498d4"></a>
## `CodedSorting.CommonLocalSemantic.pipeline`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L167)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] →
      [inst : OrderTop α] → CodedSorting.CommonLocalSemantic.Operation α → (n : ℕ) → (Fin n → α) → Fin n → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] op n f =>
  let s := CodedSorting.LocalShape.sizeChoice n;
  let r := CodedSorting.PhysicalLocalSortNode.rows s;
  let h := CodedSorting.LocalShape.columnLength n / 2;
  let padded := CodedSorting.RecursiveColumnsort.pad f;
  let first := CodedSorting.CommonLocalSemantic.batch op s r padded;
  let second :=
    CodedSorting.CommonLocalSemantic.batch op s (s * (s ^ 2 * 1)) (CodedSorting.CommonLocalSemantic.forward s first);
  let third := CodedSorting.CommonLocalSemantic.batch op s r (CodedSorting.CommonLocalSemantic.backward s second);
  let fourth :=
    CodedSorting.CommonLocalSemantic.batch op (s + 1) r (CodedSorting.CommonLocalSemantic.shift s r h third);
  CodedSorting.RecursiveColumnsort.trim ⋯ (CodedSorting.CommonLocalSemantic.unshift s r h fourth)
```

**继续展开**

- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalSemantic.forward](Semantic.definitions.md#def-73fbf5cf9a4e2cae)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalSemantic.backward](Semantic.definitions.md#def-7cfe465cda0e4774)
- [CodedSorting.LocalShape.sizeChoice](../../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.CommonLocalSemantic.padded_size](Semantic.definitions.md#def-5593436e1b4f55c7)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.LocalShape.columnLength](../../../Shared/Programs/LocalTrace.definitions.md#def-0ba59d4f9543a5be)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `OrderTop`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-b2b056f6ee3001d4"></a>
## `CodedSorting.CommonLocalSemantic.returned`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Semantic.lean#L180)

**类型**

```lean
{α : Type u_1} → CodedSorting.RecursiveColumnsort.Sorter α → CodedSorting.CommonLocalSemantic.Operation α
```

**定义**

```lean
fun {α} sorter n f => (sorter n f).output
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.Sorter](../../Bounds/RecursiveSortBase.definitions.md#def-e90528ad227dadd9)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.RecursiveColumnsort.Run.output](../../Bounds/RecursiveSortBase.definitions.md#def-f8d4919f40a96246)

**基础库名称**

`Nat`, `Fin`
