# PhysicalLocalSortNode 的定义

[源码](PhysicalLocalSortNode.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2fddd3888cb48ed2"></a>
## `CodedSorting.PhysicalLocalSortPadding.flattenColumns`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalLocalSortNode.lean#L325)

**类型**

```lean
{α : Type u_1} → (s r : ℕ) → (Fin s → Fin r → α) → Fin (s * r) → α
```

**定义**

```lean
fun {α} s r f i => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-a6a16a5bf73a34cf"></a>
## `CodedSorting.PhysicalLocalSortPadding.fourthInput`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalLocalSortNode.lean#L328)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] → [inst : OrderTop α] → (s r : ℕ) → ℕ → (Fin s → Fin r → α) → Fin (s + 1) → Fin r → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] s r h three c =>
  CodedSorting.RecursiveColumnsort.gridInput r (-↑h) (CodedSorting.RecursiveColumnsort.gridTape s r 0 three) ↑↑c
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.gridInput](../../../Shared/Indexing/FiniteGrid.definitions.md#def-cc50d54fa931e83e)
- [CodedSorting.RecursiveColumnsort.gridTape](../../../Shared/Indexing/FiniteGrid.definitions.md#def-785afc3e3d4da11d)

**基础库名称**

`LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Int.instNegInt`, `instOfNatNat`, `Int`, `Fin.val`, `OrderTop`, `Nat.cast`, `instHAdd`, `instOfNat`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instNatCastInt`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Neg.neg`, `Lattice.toSemilatticeInf`

<a id="def-419396c640f974a3"></a>
## `CodedSorting.PhysicalLocalSortPadding.unshiftedRecords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalLocalSortNode.lean#L403)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] → [inst : OrderTop α] → (s r : ℕ) → ℕ → (Fin (s + 1) → Fin r → α) → Fin (s * r) → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] s r h four i =>
  CodedSorting.RecursiveColumnsort.gridTape (s + 1) r (-↑h) four ↑↑i
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.gridTape](../../../Shared/Indexing/FiniteGrid.definitions.md#def-785afc3e3d4da11d)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Int.instNegInt`, `instMulNat`, `instOfNatNat`, `Int`, `Fin.val`, `OrderTop`, `Nat.cast`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instNatCastInt`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Neg.neg`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-b825fe6d9317cd2c"></a>
## `CodedSorting.PhysicalLocalSortNode.rows`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalLocalSortNode.lean#L721)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun s => s ^ 2 * s * 1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-706a0fe104c01557"></a>
## `CodedSorting.PhysicalLocalSortNode.thirdColumns`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalLocalSortNode.lean#L750)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] →
      [inst : OrderTop α] →
        (s : ℕ) → (Fin s → Fin (s * (s ^ 2 * 1)) → α) → Fin s → Fin (CodedSorting.PhysicalLocalSortNode.rows s) → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] s two c =>
  CodedSorting.RecursiveColumnsort.gridInput (CodedSorting.PhysicalLocalSortNode.rows s) 0
    (CodedSorting.RecursiveColumnsort.afterTwoTape (s ^ 2) s two) ↑↑c
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.afterTwoTape](../Columnsort/FiniteColumnsort.definitions.md#def-e47c7a722fa5f7a3)
- [CodedSorting.RecursiveColumnsort.gridInput](../../../Shared/Indexing/FiniteGrid.definitions.md#def-cc50d54fa931e83e)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `instMulNat`, `instOfNatNat`, `Int`, `Fin.val`, `OrderTop`, `Nat.cast`, `HPow.hPow`, `instOfNat`, `Nat`, `instNatCastInt`, `instHPow`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`
