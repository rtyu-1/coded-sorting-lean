# Sort 的定义

[源码](Sort.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-33013a25250433a6"></a>
## `CodedSorting.TwoWordRadixFootprint.BoundedCommand`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Sort.lean#L551)

**类型**

```lean
{W : Type u_1} → ℕ → CodedSorting.TwoWordPhysicalAddresses.Command W → Prop
```

**定义**

```lean
fun {W} L x =>
  match x with
  | CodedSorting.TwoWordPhysicalAddresses.Command.readLeft a => a < L
  | CodedSorting.TwoWordPhysicalAddresses.Command.readRight a => a < L
  | CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt a => ∀ (r : CodedSorting.TwoWordSpill.Resident W), a r < L
  | CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft a => a < L
  | CodedSorting.TwoWordPhysicalAddresses.Command.writeRight a => ∀ (r : CodedSorting.TwoWordSpill.Resident W), a r < L
  | CodedSorting.TwoWordPhysicalAddresses.Command.localOp f => True
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordSpill.Resident](../PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)
- [CodedSorting.TwoWordRadixFootprint.BoundedCommand.match_1](Sort.definitions.md#def-6fe77a6a26925dcc)

**基础库名称**

`Nat`, `LT.lt`, `True`, `instLTNat`

<a id="def-cbabc3ac9275b80c"></a>
## `CodedSorting.TwoWordRadixFootprint.BoundedStage`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Sort.lean#L559)

**类型**

```lean
{W : Type u_1} → ℕ → CodedSorting.TwoWordRadixPreparedBuild.Stage W → Prop
```

**定义**

```lean
fun {W} L x =>
  match x with
  | CodedSorting.TwoWordRadixPreparedBuild.Stage.straight cmds =>
    ∀ c ∈ cmds, CodedSorting.TwoWordRadixFootprint.BoundedCommand L c
  | CodedSorting.TwoWordRadixPreparedBuild.Stage.loop p =>
    p.pcAddress < L ∧ ∀ c ∈ p.body, CodedSorting.TwoWordRadixFootprint.BoundedCommand L c
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](../Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordRadixFootprint.BoundedStage.match_1](Sort.definitions.md#def-4d0eff11d62f4ae2)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordUniformLoop.Physical.Program.body](../Uniform/Loop.definitions.md#def-2ecb4f4fd3b78862)
- [CodedSorting.TwoWordRadixFootprint.BoundedCommand](Sort.definitions.md#def-33013a25250433a6)
- [CodedSorting.TwoWordUniformLoop.Physical.Program.pcAddress](../Uniform/Loop.definitions.md#def-39fb5e508f68d9fd)

**基础库名称**

`Membership.mem`, `List`, `And`, `List.instMembership`, `Nat`, `LT.lt`, `instLTNat`

<a id="def-d6a278ca2e43429a"></a>
## `CodedSorting.TwoWordRadixFootprint.BoundedCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Sort.lean#L563)

**类型**

```lean
{W : Type u_1} → ℕ → List (CodedSorting.TwoWordRadixPreparedBuild.Stage W) → Prop
```

**定义**

```lean
fun {W} L code => ∀ s ∈ code, CodedSorting.TwoWordRadixFootprint.BoundedStage L s
```

**继续展开**

- [CodedSorting.TwoWordRadixFootprint.BoundedStage](Sort.definitions.md#def-cbabc3ac9275b80c)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Initialize.definitions.md#def-472036ed275c48db)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`

<a id="def-6fe77a6a26925dcc"></a>
## `CodedSorting.TwoWordRadixFootprint.BoundedCommand.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Sort.lean)

**类型**

```lean
{W : Type u_1} →
  (motive : CodedSorting.TwoWordPhysicalAddresses.Command W → Sort u_2) →
    (x : CodedSorting.TwoWordPhysicalAddresses.Command W) →
      ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.readLeft a)) →
        ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.readRight a)) →
          ((a : CodedSorting.TwoWordSpill.Resident W → ℕ) →
              motive (CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt a)) →
            ((a : ℕ) → motive (CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft a)) →
              ((a : CodedSorting.TwoWordSpill.Resident W → ℕ) →
                  motive (CodedSorting.TwoWordPhysicalAddresses.Command.writeRight a)) →
                ((f : CodedSorting.TwoWordSpill.Resident W → CodedSorting.TwoWordSpill.Resident W) →
                    motive (CodedSorting.TwoWordPhysicalAddresses.Command.localOp f)) →
                  motive x
```

**定义**

```lean
fun {W} motive x h_1 h_2 h_3 h_4 h_5 h_6 =>
  CodedSorting.TwoWordPhysicalAddresses.Command.casesOn x (fun a => h_1 a) (fun a => h_2 a) (fun a => h_3 a)
    (fun a => h_4 a) (fun a => h_5 a) fun f => h_6 f
```

**继续展开**

- [CodedSorting.TwoWordPhysicalAddresses.Command.readRight](../PhysicalAddresses.definitions.md#def-80ee4e0629315e7a)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeRight](../PhysicalAddresses.definitions.md#def-ba338466a2ed8462)
- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordPhysicalAddresses.Command.localOp](../PhysicalAddresses.definitions.md#def-c713e8bf83b71ce0)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readLeft](../PhysicalAddresses.definitions.md#def-10977754ba9e1532)
- [CodedSorting.TwoWordPhysicalAddresses.Command.casesOn](../PhysicalAddresses.definitions.md#def-a499b9b9d54d5380)
- [CodedSorting.TwoWordSpill.Resident](../PhysicalAddresses.definitions.md#def-06c53f2492a6c79b)
- [CodedSorting.TwoWordPhysicalAddresses.Command.writeLeft](../PhysicalAddresses.definitions.md#def-38889ca9c555a290)
- [CodedSorting.TwoWordPhysicalAddresses.Command.readRightAt](../PhysicalAddresses.definitions.md#def-463ccc65763d544d)

**基础库名称**

`Nat`

<a id="def-4d0eff11d62f4ae2"></a>
## `CodedSorting.TwoWordRadixFootprint.BoundedStage.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Sort.lean)

**类型**

```lean
{W : Type u_1} →
  (motive : CodedSorting.TwoWordRadixPreparedBuild.Stage W → Sort u_2) →
    (x : CodedSorting.TwoWordRadixPreparedBuild.Stage W) →
      ((cmds : List (CodedSorting.TwoWordPhysicalAddresses.Command W)) →
          motive (CodedSorting.TwoWordRadixPreparedBuild.Stage.straight cmds)) →
        ((p : CodedSorting.TwoWordUniformLoop.Physical.Program W) →
            motive (CodedSorting.TwoWordRadixPreparedBuild.Stage.loop p)) →
          motive x
```

**定义**

```lean
fun {W} motive x h_1 h_2 =>
  CodedSorting.TwoWordRadixPreparedBuild.Stage.casesOn x (fun code => h_1 code) fun program => h_2 program
```

**继续展开**

- [CodedSorting.TwoWordUniformLoop.Physical.Program](../Uniform/Loop.definitions.md#def-5efe9fa745fd2b70)
- [CodedSorting.TwoWordPhysicalAddresses.Command](../PhysicalAddresses.definitions.md#def-e0c87ff3db4dbd69)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.casesOn](Initialize.definitions.md#def-b6f64e5ac7614dd7)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage](Initialize.definitions.md#def-472036ed275c48db)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.straight](Initialize.definitions.md#def-a8dd39815ba3f078)
- [CodedSorting.TwoWordRadixPreparedBuild.Stage.loop](Initialize.definitions.md#def-37406744c0a136a6)

**基础库名称**

`List`
