# FiniteColumnsort 的定义

[源码](FiniteColumnsort.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-be1706634a4e8f78"></a>
## `CodedSorting.RecursiveColumnsort.secondInput`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteColumnsort.lean#L12)

**类型**

```lean
{α : Type u_1} → (q s : ℕ) → (Fin s → Fin (q * s * 1) → α) → Fin s → Fin (s * (q * 1)) → α
```

**定义**

```lean
fun {α} q s one c i =>
  let p := finProdFinEquiv.symm i;
  one p.1 ⟨CodedSorting.Columnsort.stripeIndex s 1 ↑c ↑p.2, ⋯⟩
```

**继续展开**

- [CodedSorting.Columnsort.stripeIndex](Columnsort.definitions.md#def-02d0c9816dc97387)
- [CodedSorting.RecursiveColumnsort.secondInput._proof_1](FiniteColumnsort.definitions.md#def-e954f66b234afab1)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Fin.mk`, `Equiv`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-e47c7a722fa5f7a3"></a>
## `CodedSorting.RecursiveColumnsort.afterTwoTape`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteColumnsort.lean#L20)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] → [inst : OrderTop α] → (q s : ℕ) → (Fin s → Fin (s * (q * 1)) → α) → ℤ → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] q s two i =>
  if hi : 0 ≤ i ∧ i < ↑(s * q * (s * 1)) then
    let j := ⟨i.toNat, ⋯⟩;
    let p := finProdFinEquiv.symm j;
    let cv := finProdFinEquiv.symm p.2;
    two cv.1 ⟨↑p.1 * 1 + ↑cv.2, ⋯⟩
  else if i < 0 then ⊥ else ⊤
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.afterTwoTape._proof_3](FiniteColumnsort.definitions.md#def-69d69eb654a37e88)
- [CodedSorting.RecursiveColumnsort.afterTwoTape._proof_4](FiniteColumnsort.definitions.md#def-9011225ef08e8e18)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `LinearOrder`, `OrderBot.toBot`, `PartialOrder.toPreorder`, `Int.decLe`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.mk`, `Equiv`, `instMulNat`, `instOfNatNat`, `Bot.bot`, `Int`, `LE.le`, `Fin.val`, `OrderTop`, `Nat.cast`, `Prod.fst`, `dite`, `Int.instLTInt`, `instHAdd`, `And`, `OrderTop.toTop`, `instOfNat`, `HAdd.hAdd`, `Nat`, `LT.lt`, `finProdFinEquiv`, `instAddNat`, `Int.toNat`, `Int.decLt`, `instNatCastInt`, `instDecidableAnd`, `Equiv.symm`, `Prod`, `Top.top`, `OfNat.ofNat`, `Fin`, `Prod.snd`, `DFunLike.coe`, `Not`, `instDistribLatticeOfLinearOrder`, `Int.instLEInt`, `Lattice.toSemilatticeInf`, `instHMul`, `ite`

<a id="def-265136dbd6469771"></a>
## `CodedSorting.RecursiveColumnsort.FourRun`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](FiniteColumnsort.lean#L30)

**类型**

```lean
Type u_2 → ℕ → Type u_2
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.FourRun.mk](FiniteColumnsort.definitions.md#def-0ad2c3316fbef6b9)

**基础库名称**

`Nat`

<a id="def-0ad2c3316fbef6b9"></a>
## `CodedSorting.RecursiveColumnsort.FourRun.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](FiniteColumnsort.lean#L31)

**类型**

```lean
{α : Type u_2} →
  {n : ℕ} →
    (Fin n → α) →
      List CodedSorting.RecursiveColumnsort.CallTree →
        List CodedSorting.RecursiveColumnsort.CallTree →
          List CodedSorting.RecursiveColumnsort.CallTree →
            List CodedSorting.RecursiveColumnsort.CallTree → CodedSorting.RecursiveColumnsort.FourRun α n
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](../../Bounds/RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)
- [CodedSorting.RecursiveColumnsort.FourRun](FiniteColumnsort.definitions.md#def-265136dbd6469771)

**基础库名称**

`List`, `Nat`, `Fin`

<a id="def-80ee29ec9c5a9f0b"></a>
## `CodedSorting.RecursiveColumnsort.FourRun.output`

读取 `CodedSorting.RecursiveColumnsort.FourRun` 的 `output` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteColumnsort.lean#L32)

**类型**

```lean
{α : Type u_2} → {n : ℕ} → CodedSorting.RecursiveColumnsort.FourRun α n → Fin n → α
```

**定义**

```lean
fun α n self => self.1
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.FourRun](FiniteColumnsort.definitions.md#def-265136dbd6469771)

**基础库名称**

`Nat`, `Fin`

<a id="def-afa9e0bfce6f6a3f"></a>
## `CodedSorting.RecursiveColumnsort.FourRun.first`

读取 `CodedSorting.RecursiveColumnsort.FourRun` 的 `first` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteColumnsort.lean#L33)

**类型**

```lean
{α : Type u_2} → {n : ℕ} → CodedSorting.RecursiveColumnsort.FourRun α n → List CodedSorting.RecursiveColumnsort.CallTree
```

**定义**

```lean
fun α n self => self.2
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](../../Bounds/RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)
- [CodedSorting.RecursiveColumnsort.FourRun](FiniteColumnsort.definitions.md#def-265136dbd6469771)

**基础库名称**

`List`, `Nat`

<a id="def-8385e7bf9d968db9"></a>
## `CodedSorting.RecursiveColumnsort.FourRun.second`

读取 `CodedSorting.RecursiveColumnsort.FourRun` 的 `second` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteColumnsort.lean#L34)

**类型**

```lean
{α : Type u_2} → {n : ℕ} → CodedSorting.RecursiveColumnsort.FourRun α n → List CodedSorting.RecursiveColumnsort.CallTree
```

**定义**

```lean
fun α n self => self.3
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](../../Bounds/RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)
- [CodedSorting.RecursiveColumnsort.FourRun](FiniteColumnsort.definitions.md#def-265136dbd6469771)

**基础库名称**

`List`, `Nat`

<a id="def-656693f989577c45"></a>
## `CodedSorting.RecursiveColumnsort.FourRun.third`

读取 `CodedSorting.RecursiveColumnsort.FourRun` 的 `third` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteColumnsort.lean#L35)

**类型**

```lean
{α : Type u_2} → {n : ℕ} → CodedSorting.RecursiveColumnsort.FourRun α n → List CodedSorting.RecursiveColumnsort.CallTree
```

**定义**

```lean
fun α n self => self.4
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](../../Bounds/RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)
- [CodedSorting.RecursiveColumnsort.FourRun](FiniteColumnsort.definitions.md#def-265136dbd6469771)

**基础库名称**

`List`, `Nat`

<a id="def-ec82949c12ed32e2"></a>
## `CodedSorting.RecursiveColumnsort.FourRun.fourth`

读取 `CodedSorting.RecursiveColumnsort.FourRun` 的 `fourth` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FiniteColumnsort.lean#L36)

**类型**

```lean
{α : Type u_2} → {n : ℕ} → CodedSorting.RecursiveColumnsort.FourRun α n → List CodedSorting.RecursiveColumnsort.CallTree
```

**定义**

```lean
fun α n self => self.5
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](../../Bounds/RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)
- [CodedSorting.RecursiveColumnsort.FourRun](FiniteColumnsort.definitions.md#def-265136dbd6469771)

**基础库名称**

`List`, `Nat`

<a id="def-7c34e5749d8a3cf5"></a>
## `CodedSorting.RecursiveColumnsort.fourRounds`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteColumnsort.lean#L38)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] →
    [inst_1 : OrderBot α] →
      [inst : OrderTop α] →
        CodedSorting.RecursiveColumnsort.Sorter α →
          (q s : ℕ) → ℕ → (Fin s → Fin (q * s * 1) → α) → CodedSorting.RecursiveColumnsort.FourRun α (s * q * (s * 1))
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] sorter q s H f =>
  let first := fun c => sorter (q * s * 1) (f c);
  let second := fun c =>
    sorter (s * (q * 1)) (CodedSorting.RecursiveColumnsort.secondInput q s (fun c => (first c).output) c);
  let A := CodedSorting.RecursiveColumnsort.afterTwoTape q s fun c => (second c).output;
  let third := fun c => sorter (q * s * 1) (CodedSorting.RecursiveColumnsort.gridInput (q * s * 1) 0 A ↑↑c);
  let G := CodedSorting.RecursiveColumnsort.gridTape s (q * s * 1) 0 fun c => (third c).output;
  let fourth := fun c => sorter (q * s * 1) (CodedSorting.RecursiveColumnsort.gridInput (q * s * 1) (-↑H) G ↑↑c);
  {
    output := fun i =>
      CodedSorting.RecursiveColumnsort.gridTape (s + 1) (q * s * 1) (-↑H) (fun c => (fourth c).output) ↑↑i,
    first := List.ofFn fun c => (first c).trace, second := List.ofFn fun c => (second c).trace,
    third := List.ofFn fun c => (third c).trace, fourth := List.ofFn fun c => (fourth c).trace }
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.FourRun.mk](FiniteColumnsort.definitions.md#def-0ad2c3316fbef6b9)
- [CodedSorting.RecursiveColumnsort.afterTwoTape](FiniteColumnsort.definitions.md#def-e47c7a722fa5f7a3)
- [CodedSorting.RecursiveColumnsort.CallTree](../../Bounds/RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)
- [CodedSorting.RecursiveColumnsort.Sorter](../../Bounds/RecursiveSortBase.definitions.md#def-e90528ad227dadd9)
- [CodedSorting.RecursiveColumnsort.gridInput](../../../Shared/Indexing/FiniteGrid.definitions.md#def-cc50d54fa931e83e)
- [CodedSorting.RecursiveColumnsort.secondInput](FiniteColumnsort.definitions.md#def-be1706634a4e8f78)
- [CodedSorting.RecursiveColumnsort.Run.trace](../../Bounds/RecursiveSortBase.definitions.md#def-481ca50755f2ed2e)
- [CodedSorting.RecursiveColumnsort.Run.output](../../Bounds/RecursiveSortBase.definitions.md#def-f8d4919f40a96246)
- [CodedSorting.RecursiveColumnsort.gridTape](../../../Shared/Indexing/FiniteGrid.definitions.md#def-785afc3e3d4da11d)
- [CodedSorting.RecursiveColumnsort.FourRun](FiniteColumnsort.definitions.md#def-265136dbd6469771)
- [CodedSorting.RecursiveColumnsort.Run](../../Bounds/RecursiveSortBase.definitions.md#def-b896814d19d1eb69)

**基础库名称**

`HMul.hMul`, `LinearOrder`, `PartialOrder.toPreorder`, `List.ofFn`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Int.instNegInt`, `instMulNat`, `instOfNatNat`, `Int`, `Fin.val`, `OrderTop`, `Nat.cast`, `instHAdd`, `instOfNat`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instNatCastInt`, `OfNat.ofNat`, `Fin`, `instDistribLatticeOfLinearOrder`, `Neg.neg`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-69d69eb654a37e88"></a>
## `CodedSorting.RecursiveColumnsort.afterTwoTape._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](FiniteColumnsort.lean)

**类型**

```lean
∀ (q s : ℕ) (i : ℤ), 0 ≤ i ∧ i < ↑(s * q * (s * 1)) → i.toNat < s * q * (s * 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Int`, `LE.le`, `Nat.cast`, `Int.instLTInt`, `And`, `instOfNat`, `Nat`, `LT.lt`, `Int.toNat`, `instNatCastInt`, `instLTNat`, `OfNat.ofNat`, `Int.instLEInt`, `instHMul`

<a id="def-9011225ef08e8e18"></a>
## `CodedSorting.RecursiveColumnsort.afterTwoTape._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](FiniteColumnsort.lean)

**类型**

```lean
∀ (q s : ℕ) (i : ℤ) (hi : 0 ≤ i ∧ i < ↑(s * q * (s * 1))),
  ↑(finProdFinEquiv.symm ⟨i.toNat, ⋯⟩).1 * 1 + ↑(finProdFinEquiv.symm (finProdFinEquiv.symm ⟨i.toNat, ⋯⟩).2).2 <
    s * (q * 1)
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.afterTwoTape._proof_3](FiniteColumnsort.definitions.md#def-69d69eb654a37e88)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Fin.mk`, `Equiv`, `instMulNat`, `instOfNatNat`, `Int`, `LE.le`, `Fin.val`, `Nat.cast`, `Prod.fst`, `Int.instLTInt`, `instHAdd`, `And`, `instOfNat`, `HAdd.hAdd`, `Nat`, `LT.lt`, `finProdFinEquiv`, `instAddNat`, `Int.toNat`, `instNatCastInt`, `instLTNat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`, `DFunLike.coe`, `Int.instLEInt`, `instHMul`

<a id="def-e954f66b234afab1"></a>
## `CodedSorting.RecursiveColumnsort.secondInput._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](FiniteColumnsort.lean)

**类型**

```lean
∀ (q s : ℕ) (c : Fin s) (i : Fin (s * (q * 1))),
  CodedSorting.Columnsort.stripeIndex s 1 ↑c ↑(finProdFinEquiv.symm i).2 < q * s * 1
```

**继续展开**

- [CodedSorting.Columnsort.stripeIndex](Columnsort.definitions.md#def-02d0c9816dc97387)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Nat`, `LT.lt`, `finProdFinEquiv`, `instLTNat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`
