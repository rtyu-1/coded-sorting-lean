# StageLabels 的定义

[源码](StageLabels.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-4c226b64a556f910"></a>
## `CodedSorting.StageLabels.wireTrace`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StageLabels.lean#L55)

**类型**

```lean
{d : ℕ} →
  {Reg : Type u_1} →
    {G : Type u_2} →
      [inst : DecidableEq Reg] →
        List G →
          (G → CodedSorting.CircuitProgram.XorGate Reg) →
            (G → CodedSorting.TensorLabels.Label d) →
              (Reg → CodedSorting.TensorLabels.Label d) → Reg → List (CodedSorting.TensorLabels.Label d)
```

**定义**

```lean
fun {d} {Reg} {G} [DecidableEq Reg] gs gate label src r =>
  CodedSorting.TensorLabels.stageLabels (fun u => decide (r ∈ (gate u).ports)) label (src r) gs
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.TensorLabels.stageLabels](TensorLabels.definitions.md#def-3d1791b695e4d854)
- [CodedSorting.TensorLabels.Label](TensorLabels.definitions.md#def-43a4598c9218b5b2)

**基础库名称**

`Finset`, `Membership.mem`, `Finset.instMembership`, `List`, `Nat`, `Finset.decidableMem`, `Decidable.decide`, `DecidableEq`

<a id="def-fce87c300b941dbd"></a>
## `CodedSorting.StageLabels.vertexLabel`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StageLabels.lean#L62)

**类型**

```lean
{d : ℕ} →
  {Reg : Type u_1} →
    {G : Type u_2} →
      [inst : DecidableEq Reg] →
        (gs : List G) →
          (gate : G → CodedSorting.CircuitProgram.XorGate Reg) →
            (G → CodedSorting.TensorLabels.Label d) →
              (Reg → CodedSorting.TensorLabels.Label d) →
                (Reg → CodedSorting.TensorLabels.Label d) →
                  CodedSorting.ProgramNetwork.Vertex Reg (List.map gate gs).length → CodedSorting.TensorLabels.Label d
```

**定义**

```lean
fun {d} {Reg} {G} [DecidableEq Reg] gs gate label src dst x =>
  match x with
  | CodedSorting.ProgramNetwork.Vertex.source r => src r
  | CodedSorting.ProgramNetwork.Vertex.gate t => label (gs.get ⟨↑t, ⋯⟩)
  | CodedSorting.ProgramNetwork.Vertex.pass t r => (CodedSorting.StageLabels.wireTrace gs gate label src r).get ⟨↑t, ⋯⟩
  | CodedSorting.ProgramNetwork.Vertex.sink r => dst r
```

**继续展开**

- [CodedSorting.StageLabels.vertexLabel._proof_2](StageLabels.definitions.md#def-a580bbe661152496)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.StageLabels.vertexLabel._proof_1](StageLabels.definitions.md#def-ce46a56ed5a774b8)
- [CodedSorting.TensorLabels.Label](TensorLabels.definitions.md#def-43a4598c9218b5b2)
- [CodedSorting.StageLabels.wireTrace](StageLabels.definitions.md#def-4c226b64a556f910)
- [CodedSorting.StageLabels.vertexLabel.match_1](StageLabels.definitions.md#def-b1c8d390af81039f)
- [CodedSorting.ProgramNetwork.Vertex](../../NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`List.get`, `List.map`, `Fin.mk`, `Fin.val`, `List`, `Nat`, `Fin`, `List.length`, `DecidableEq`

<a id="def-3069156944b597d9"></a>
## `CodedSorting.StageLabels.transportLabel`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](StageLabels.lean#L192)

**类型**

```lean
{d : ℕ} →
  {Reg : Type u_1} →
    [inst : DecidableEq Reg] →
      {p q : List (CodedSorting.CircuitProgram.XorGate Reg)} →
        p = q →
          (CodedSorting.ProgramNetwork.Vertex Reg p.length → CodedSorting.TensorLabels.Label d) →
            CodedSorting.ProgramNetwork.Vertex Reg q.length → CodedSorting.TensorLabels.Label d
```

**定义**

```lean
fun {d} {Reg} [DecidableEq Reg] {p q} h f =>
  Eq.rec (motive := fun x h => CodedSorting.ProgramNetwork.Vertex Reg x.length → CodedSorting.TensorLabels.Label d) f h
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.TensorLabels.Label](TensorLabels.definitions.md#def-43a4598c9218b5b2)
- [CodedSorting.ProgramNetwork.Vertex](../../NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Eq.rec`, `List`, `Nat`, `Eq`, `List.length`, `DecidableEq`

<a id="def-ce46a56ed5a774b8"></a>
## `CodedSorting.StageLabels.vertexLabel._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StageLabels.lean)

**类型**

```lean
∀ {Reg : Type u_1} {G : Type u_2} [inst : DecidableEq Reg] (gs : List G)
  (gate : G → CodedSorting.CircuitProgram.XorGate Reg) (t : Fin (List.map gate gs).length), ↑t < gs.length
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`List.map`, `Fin.val`, `List`, `Nat`, `LT.lt`, `instLTNat`, `Fin`, `List.length`, `DecidableEq`

<a id="def-a580bbe661152496"></a>
## `CodedSorting.StageLabels.vertexLabel._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](StageLabels.lean)

**类型**

```lean
∀ {d : ℕ} {Reg : Type u_1} {G : Type u_2} [inst : DecidableEq Reg] (gs : List G)
  (gate : G → CodedSorting.CircuitProgram.XorGate Reg) (label : G → CodedSorting.TensorLabels.Label d)
  (src : Reg → CodedSorting.TensorLabels.Label d) (t : Fin (List.map gate gs).length) (r : Reg),
  ↑t < (CodedSorting.StageLabels.wireTrace gs gate label src r).length
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.TensorLabels.Label](TensorLabels.definitions.md#def-43a4598c9218b5b2)
- [CodedSorting.StageLabels.wireTrace](StageLabels.definitions.md#def-4c226b64a556f910)

**基础库名称**

`List.map`, `Fin.val`, `List`, `Nat`, `LT.lt`, `instLTNat`, `Fin`, `List.length`, `DecidableEq`

<a id="def-b1c8d390af81039f"></a>
## `CodedSorting.StageLabels.vertexLabel.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](StageLabels.lean)

**类型**

```lean
{Reg : Type u_1} →
  {G : Type u_2} →
    [inst : DecidableEq Reg] →
      (gs : List G) →
        (gate : G → CodedSorting.CircuitProgram.XorGate Reg) →
          (motive : CodedSorting.ProgramNetwork.Vertex Reg (List.map gate gs).length → Sort u_3) →
            (x : CodedSorting.ProgramNetwork.Vertex Reg (List.map gate gs).length) →
              ((r : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.source r)) →
                ((t : Fin (List.map gate gs).length) → motive (CodedSorting.ProgramNetwork.Vertex.gate t)) →
                  ((t : Fin (List.map gate gs).length) →
                      (r : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.pass t r)) →
                    ((r : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.sink r)) → motive x
```

**定义**

```lean
fun {Reg} {G} [DecidableEq Reg] gs gate motive x h_1 h_2 h_3 h_4 =>
  CodedSorting.ProgramNetwork.Vertex.casesOn x (fun a => h_1 a) (fun a => h_2 a) (fun a a_1 => h_3 a a_1) fun a => h_4 a
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex.casesOn](../../NetworkModel/Framework/ProgramNetwork.definitions.md#def-dce4a35b07c857f6)
- [CodedSorting.ProgramNetwork.Vertex.source](../../NetworkModel/Framework/ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.Vertex.gate](../../NetworkModel/Framework/ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](../../NetworkModel/Framework/ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Vertex.sink](../../NetworkModel/Framework/ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.ProgramNetwork.Vertex](../../NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`List.map`, `List`, `Fin`, `List.length`, `DecidableEq`
