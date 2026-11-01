# NetworkAdapter 的定义

[源码](NetworkAdapter.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2e2fa962a2b01453"></a>
## `CodedSorting.Construction.NetworkAdapter.overwriteCopy`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NetworkAdapter.lean#L33)

**类型**

```lean
{Reg : Type u_1} → [inst : DecidableEq Reg] → Reg → Reg → CodedSorting.CircuitProgram.XorGate Reg
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] destination source =>
  { ports := {destination, source}, targets := {destination}, controls := fun x => {destination, source},
    targets_subset := ⋯, controls_subset := ⋯ }
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.mk](../Framework/CircuitProgram.definitions.md#def-a958dc84c6bc445e)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.NetworkAdapter.overwriteCopy._proof_2](NetworkAdapter.definitions.md#def-8a532a1dcd772c1e)

**基础库名称**

`Finset`, `Membership.mem`, `Insert.insert`, `Finset.instMembership`, `Finset.instInsert`, `Finset.instSingleton`, `Singleton.singleton`, `DecidableEq`

<a id="def-8a532a1dcd772c1e"></a>
## `CodedSorting.Construction.NetworkAdapter.overwriteCopy._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NetworkAdapter.lean)

**类型**

```lean
∀ {Reg : Type u_1} [inst : DecidableEq Reg] (destination source : Reg) ⦃r : Reg⦄,
  r ∈ {destination} → r ∈ {destination, source}
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Finset`, `Membership.mem`, `Insert.insert`, `Finset.instMembership`, `Finset.instInsert`, `Finset.instSingleton`, `Singleton.singleton`, `DecidableEq`
