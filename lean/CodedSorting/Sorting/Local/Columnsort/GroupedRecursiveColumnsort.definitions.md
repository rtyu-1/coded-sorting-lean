# GroupedRecursiveColumnsort 的定义

[源码](GroupedRecursiveColumnsort.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-1f3e89389ec68c2c"></a>
## `CodedSorting.RecursiveColumnsort.paddedLength`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedRecursiveColumnsort.lean#L158)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n =>
  CodedSorting.LocalShape.sizeChoice n * CodedSorting.LocalShape.sizeChoice n ^ 2 *
    (CodedSorting.LocalShape.sizeChoice n * 1)
```

**继续展开**

- [CodedSorting.LocalShape.sizeChoice](../../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-750168200b22127b"></a>
## `CodedSorting.RecursiveColumnsort.paddedLength_ge`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GroupedRecursiveColumnsort.lean#L165)

**类型**

```lean
∀ (n : ℕ), n ≤ CodedSorting.RecursiveColumnsort.paddedLength n
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.paddedLength](GroupedRecursiveColumnsort.definitions.md#def-1f3e89389ec68c2c)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-f49c73055b91f3c9"></a>
## `CodedSorting.RecursiveColumnsort.paddedInput`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedRecursiveColumnsort.lean#L169)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst : OrderTop α] →
      {n : ℕ} →
        (Fin n → α) →
          Fin (CodedSorting.LocalShape.sizeChoice n) →
            Fin (CodedSorting.LocalShape.sizeChoice n ^ 2 * CodedSorting.LocalShape.sizeChoice n * 1) → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderTop α] {n} f a j =>
  CodedSorting.RecursiveColumnsort.pad f
    ((CodedSorting.Columnsort.inputEquiv (CodedSorting.LocalShape.sizeChoice n ^ 2)
          (CodedSorting.LocalShape.sizeChoice n) 1).symm
      (a, j))
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.paddedLength](GroupedRecursiveColumnsort.definitions.md#def-1f3e89389ec68c2c)
- [CodedSorting.Columnsort.inputEquiv](ColumnsortParameters.definitions.md#def-c3695925ec3092f4)
- [CodedSorting.LocalShape.sizeChoice](../../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Nat.instMonoid`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `Equiv`, `Prod.mk`, `instMulNat`, `instOfNatNat`, `OrderTop`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-488052f996fd75e4"></a>
## `CodedSorting.RecursiveColumnsort.nodeRun`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedRecursiveColumnsort.lean#L184)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] →
      [inst : OrderTop α] →
        CodedSorting.RecursiveColumnsort.Sorter α → (n : ℕ) → (Fin n → α) → CodedSorting.RecursiveColumnsort.Run α n
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] sorter n f =>
  let s := CodedSorting.LocalShape.sizeChoice n;
  let result :=
    CodedSorting.RecursiveColumnsort.fourRounds sorter (s ^ 2) s (CodedSorting.LocalShape.columnLength n / 2)
      (CodedSorting.RecursiveColumnsort.paddedInput f);
  { output := CodedSorting.RecursiveColumnsort.trim ⋯ result.output,
    trace := CodedSorting.RecursiveColumnsort.CallTree.node n s result.first result.second result.third result.fourth }
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.paddedLength](GroupedRecursiveColumnsort.definitions.md#def-1f3e89389ec68c2c)
- [CodedSorting.RecursiveColumnsort.CallTree.node](../../Bounds/RecursiveSortBase.definitions.md#def-c9b7e3677f9f6480)
- [CodedSorting.RecursiveColumnsort.fourRounds](FiniteColumnsort.definitions.md#def-7c34e5749d8a3cf5)
- [CodedSorting.RecursiveColumnsort.Sorter](../../Bounds/RecursiveSortBase.definitions.md#def-e90528ad227dadd9)
- [CodedSorting.RecursiveColumnsort.FourRun.second](FiniteColumnsort.definitions.md#def-8385e7bf9d968db9)
- [CodedSorting.RecursiveColumnsort.paddedInput](GroupedRecursiveColumnsort.definitions.md#def-f49c73055b91f3c9)
- [CodedSorting.LocalShape.sizeChoice](../../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.RecursiveColumnsort.FourRun.first](FiniteColumnsort.definitions.md#def-afa9e0bfce6f6a3f)
- [CodedSorting.RecursiveColumnsort.FourRun.third](FiniteColumnsort.definitions.md#def-656693f989577c45)
- [CodedSorting.RecursiveColumnsort.FourRun.output](FiniteColumnsort.definitions.md#def-80ee29ec9c5a9f0b)
- [CodedSorting.RecursiveColumnsort.FourRun](FiniteColumnsort.definitions.md#def-265136dbd6469771)
- [CodedSorting.RecursiveColumnsort.Run](../../Bounds/RecursiveSortBase.definitions.md#def-b896814d19d1eb69)
- [CodedSorting.RecursiveColumnsort.FourRun.fourth](FiniteColumnsort.definitions.md#def-ec82949c12ed32e2)
- [CodedSorting.RecursiveColumnsort.Run.mk](../../Bounds/RecursiveSortBase.definitions.md#def-b4442984defa943d)
- [CodedSorting.RecursiveColumnsort.paddedLength_ge](GroupedRecursiveColumnsort.definitions.md#def-750168200b22127b)
- [CodedSorting.LocalShape.columnLength](../../../Shared/Programs/LocalTrace.definitions.md#def-0ba59d4f9543a5be)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `DistribLattice.toLattice`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `OrderTop`, `HPow.hPow`, `Nat`, `Nat.instDiv`, `instHPow`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-e4250e49e60d6398"></a>
## `CodedSorting.RecursiveColumnsort.localRun`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GroupedRecursiveColumnsort.lean#L192)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] →
      [inst : OrderTop α] → (H : ℕ) → 0 < H → ℕ → (n : ℕ) → (Fin n → α) → CodedSorting.RecursiveColumnsort.Run α n
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] H _hH x x_1 x_2 =>
  Nat.brecOn (motive := fun x => (x : ℕ) → (Fin x → α) → CodedSorting.RecursiveColumnsort.Run α x) x
    (fun x f x_3 x_4 =>
      (match (motive :=
          (x x_5 : ℕ) →
            (Fin x_5 → α) →
              Nat.below (motive := fun x => (x : ℕ) → (Fin x → α) → CodedSorting.RecursiveColumnsort.Run α x) x →
                CodedSorting.RecursiveColumnsort.Run α x_5)
          x, x_3, x_4 with
        | 0, n, f => fun x =>
          { output := CodedSorting.Columnsort.sortColumn f, trace := CodedSorting.RecursiveColumnsort.CallTree.leaf n }
        | fuel.succ, n, f => fun x =>
          if n ≤ 512 * H then
            { output := CodedSorting.Columnsort.sortColumn f,
              trace := CodedSorting.RecursiveColumnsort.CallTree.leaf n }
          else CodedSorting.RecursiveColumnsort.nodeRun x.1 n f)
        f)
    x_1 x_2
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.localRun.match_1](GroupedRecursiveColumnsort.definitions.md#def-53e0ca27e387ba57)
- [CodedSorting.RecursiveColumnsort.CallTree.leaf](../../Bounds/RecursiveSortBase.definitions.md#def-f7c82018bada47e5)
- [CodedSorting.Columnsort.sortColumn](Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.RecursiveColumnsort.nodeRun](GroupedRecursiveColumnsort.definitions.md#def-488052f996fd75e4)
- [CodedSorting.RecursiveColumnsort.Run](../../Bounds/RecursiveSortBase.definitions.md#def-b896814d19d1eb69)
- [CodedSorting.RecursiveColumnsort.Run.mk](../../Bounds/RecursiveSortBase.definitions.md#def-b4442984defa943d)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Nat.brecOn`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `OrderTop`, `Nat.below`, `PProd`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `Nat.decLe`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`, `ite`

<a id="def-53e0ca27e387ba57"></a>
## `CodedSorting.RecursiveColumnsort.localRun.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](GroupedRecursiveColumnsort.lean)

**类型**

```lean
{α : Type u_2} →
  (motive : ℕ → (x : ℕ) → (Fin x → α) → Sort u_1) →
    (x x_1 : ℕ) →
      (x_2 : Fin x_1 → α) →
        ((n : ℕ) → (f : Fin n → α) → motive 0 n f) →
          ((fuel n : ℕ) → (f : Fin n → α) → motive fuel.succ n f) → motive x x_1 x_2
```

**定义**

```lean
fun {α} motive x x_1 x_2 h_1 h_2 => Nat.casesOn x (h_1 x_1 x_2) fun n => h_2 n x_1 x_2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `Nat.casesOn`
