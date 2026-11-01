# FiniteGrid 的定义

[源码](FiniteGrid.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-785afc3e3d4da11d"></a>
## `CodedSorting.RecursiveColumnsort.gridTape`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteGrid.lean#L13)

**类型**

```lean
{α : Type u_1} →
  [inst : LinearOrder α] → [inst_1 : OrderBot α] → [inst : OrderTop α] → (n B : ℕ) → ℤ → (Fin n → Fin B → α) → ℤ → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderBot α] [OrderTop α] n B offset f i =>
  if hl : i < offset then ⊥
  else
    if hu : i < offset + ↑(n * B) then
      let j := ⟨(i - offset).toNat, ⋯⟩;
      let p := finProdFinEquiv.symm j;
      f p.1 p.2
    else ⊤
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.gridTape._proof_3](FiniteGrid.definitions.md#def-fb240e92916b89cc)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `LinearOrder`, `OrderBot.toBot`, `PartialOrder.toPreorder`, `HSub.hSub`, `Preorder.toLE`, `OrderBot`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.mk`, `Equiv`, `instMulNat`, `Bot.bot`, `Int`, `OrderTop`, `Nat.cast`, `Prod.fst`, `dite`, `Int.instLTInt`, `instHAdd`, `instHSub`, `OrderTop.toTop`, `HAdd.hAdd`, `Nat`, `LT.lt`, `finProdFinEquiv`, `Int.instAdd`, `Int.instSub`, `Int.toNat`, `Int.decLt`, `instNatCastInt`, `Equiv.symm`, `Prod`, `Top.top`, `Fin`, `Prod.snd`, `DFunLike.coe`, `Not`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`, `instHMul`

<a id="def-cc50d54fa931e83e"></a>
## `CodedSorting.RecursiveColumnsort.gridInput`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FiniteGrid.lean#L22)

**类型**

```lean
{α : Type u_1} → (B : ℕ) → ℤ → (ℤ → α) → ℤ → Fin B → α
```

**定义**

```lean
fun {α} B offset f c j => f (offset + c * ↑B + ↑↑j)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `Int`, `Fin.val`, `Nat.cast`, `Int.instMul`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Int.instAdd`, `instNatCastInt`, `Fin`, `instHMul`

<a id="def-fb240e92916b89cc"></a>
## `CodedSorting.RecursiveColumnsort.gridTape._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](FiniteGrid.lean)

**类型**

```lean
∀ (n B : ℕ) (offset i : ℤ), ¬i < offset → i < offset + ↑(n * B) → (i - offset).toNat < n * B
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instMulNat`, `Int`, `Nat.cast`, `Int.instLTInt`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Int.instAdd`, `Int.instSub`, `Int.toNat`, `instNatCastInt`, `instLTNat`, `Not`, `instHMul`
