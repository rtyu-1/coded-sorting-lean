# NetworkInputs 的定义

[源码](NetworkInputs.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-c936cacd738e9416"></a>
## `CodedSorting.CommonNetworkInputs.gatePort`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NetworkInputs.lean#L18)

**类型**

```lean
{R : Type u_1} →
  [inst : DecidableEq R] →
    (p : List (CodedSorting.CircuitProgram.XorGate R)) →
      (t : Fin p.length) →
        (r : R) →
          r ∈ (p.get t).ports → CodedSorting.ProgramNetwork.InputPort p (CodedSorting.ProgramNetwork.Vertex.gate t)
```

**定义**

```lean
fun {R} [DecidableEq R] p t r hr => Sum.inr ⟨CodedSorting.ProgramNetwork.incomingWire p t r, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonNetworkInputs.gatePort._proof_1](NetworkInputs.definitions.md#def-480e291e8ce3ea1a)
- [CodedSorting.ProgramNetwork.InputPort](ProgramNetwork.definitions.md#def-c0edc85888c37e6c)
- [CodedSorting.ProgramNetwork.wireHead](ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.incomingWire](ProgramNetwork.definitions.md#def-43af48346923f0c2)
- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Finset`, `List.get`, `Membership.mem`, `Subtype`, `Finset.instMembership`, `Subtype.mk`, `List`, `Sum.inr`, `Fin`, `Eq`, `List.length`, `DecidableEq`

<a id="def-56252d33f90ea900"></a>
## `CodedSorting.CommonNetworkInputs.gateInputs`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NetworkInputs.lean#L29)

**类型**

```lean
{R : Type u_1} →
  [inst : DecidableEq R] →
    (p : List (CodedSorting.CircuitProgram.XorGate R)) →
      (t : Fin p.length) →
        (r : R) →
          r ∈ (p.get t).ports →
            List (CodedSorting.ProgramNetwork.InputPort p (CodedSorting.ProgramNetwork.Vertex.gate t))
```

**定义**

```lean
fun {R} [DecidableEq R] p t r hr =>
  CodedSorting.CommonNetworkInputs.gatePort p t r hr ::
    if ht : r ∈ (p.get t).targets then
      List.map (fun c => CodedSorting.CommonNetworkInputs.gatePort p t ↑c ⋯) ((p.get t).controls r).attach.toList
    else []
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.targets](../../Framework/CircuitProgram.definitions.md#def-257d99bf8097b011)
- [CodedSorting.ProgramNetwork.InputPort](ProgramNetwork.definitions.md#def-c0edc85888c37e6c)
- [CodedSorting.CommonNetworkInputs.gateInputs._proof_2](NetworkInputs.definitions.md#def-9ddba62c34ebbcdd)
- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.CommonNetworkInputs.gatePort](NetworkInputs.definitions.md#def-c936cacd738e9416)
- [CodedSorting.CircuitProgram.XorGate.controls](../../Framework/CircuitProgram.definitions.md#def-623fb3e8f456b5a4)

**基础库名称**

`Finset`, `List.get`, `List.map`, `Membership.mem`, `Subtype`, `Finset.toList`, `Finset.instMembership`, `dite`, `List.cons`, `List`, `Finset.attach`, `Finset.decidableMem`, `Fin`, `Subtype.val`, `List.length`, `Not`, `List.nil`, `DecidableEq`

<a id="def-8e56605cfa6734ed"></a>
## `CodedSorting.CommonNetworkInputs.inputList`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NetworkInputs.lean#L53)

**类型**

```lean
{R : Type u_1} →
  [inst : DecidableEq R] →
    (p : List (CodedSorting.CircuitProgram.XorGate R)) →
      (v : CodedSorting.ProgramNetwork.Vertex R p.length) →
        CodedSorting.ProgramNetwork.OutputPort p v → List (CodedSorting.ProgramNetwork.InputPort p v)
```

**定义**

```lean
fun {R} [DecidableEq R] p x x_1 =>
  match x, x_1 with
  | CodedSorting.ProgramNetwork.Vertex.source r, x => [Sum.inl ⟨r, ⋯⟩]
  | CodedSorting.ProgramNetwork.Vertex.gate t, out => CodedSorting.CommonNetworkInputs.gateInputs p t (↑out).2 ⋯
  | CodedSorting.ProgramNetwork.Vertex.pass t r, x =>
    if hr : r ∈ (p.get t).ports then [] else [Sum.inr ⟨CodedSorting.ProgramNetwork.incomingWire p t r, ⋯⟩]
  | CodedSorting.ProgramNetwork.Vertex.sink a, x => []
```

**继续展开**

- [CodedSorting.CommonNetworkInputs.inputList.match_1](NetworkInputs.definitions.md#def-654a1cdfeb0eba16)
- [CodedSorting.CommonNetworkInputs.inputList._proof_5](NetworkInputs.definitions.md#def-ee19b3c9da9d0c5f)
- [CodedSorting.ProgramNetwork.InputPort](ProgramNetwork.definitions.md#def-c0edc85888c37e6c)
- [CodedSorting.ProgramNetwork.OutputPort](ProgramNetwork.definitions.md#def-d59180e636f2c683)
- [CodedSorting.ProgramNetwork.wireHead](ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.wireTail](ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.CommonNetworkInputs.inputList._proof_3](NetworkInputs.definitions.md#def-2de7039bcee03982)
- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.incomingWire](ProgramNetwork.definitions.md#def-43af48346923f0c2)
- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.CommonNetworkInputs.gateInputs](NetworkInputs.definitions.md#def-56252d33f90ea900)
- [CodedSorting.ProgramNetwork.Vertex.sink](ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.CommonNetworkInputs.inputList._proof_4](NetworkInputs.definitions.md#def-b844622c1e885f6d)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Finset`, `List.get`, `Membership.mem`, `Subtype`, `instOfNatNat`, `Sum.inl`, `Finset.instMembership`, `dite`, `List.cons`, `Subtype.mk`, `List`, `instHAdd`, `HAdd.hAdd`, `Sum.inr`, `Nat`, `instAddNat`, `Finset.decidableMem`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `Prod.snd`, `List.length`, `Not`, `List.nil`, `DecidableEq`

<a id="def-9ddba62c34ebbcdd"></a>
## `CodedSorting.CommonNetworkInputs.gateInputs._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NetworkInputs.lean)

**类型**

```lean
∀ {R : Type u_1} [inst : DecidableEq R] (p : List (CodedSorting.CircuitProgram.XorGate R)) (t : Fin p.length),
  ∀ r ∈ (p.get t).targets, ∀ (c : { x // x ∈ (p.get t).controls r }), ↑c ∈ (p.get t).ports
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.targets](../../Framework/CircuitProgram.definitions.md#def-257d99bf8097b011)
- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.CircuitProgram.XorGate.controls](../../Framework/CircuitProgram.definitions.md#def-623fb3e8f456b5a4)

**基础库名称**

`Finset`, `List.get`, `Membership.mem`, `Subtype`, `Finset.instMembership`, `List`, `Fin`, `Subtype.val`, `List.length`, `DecidableEq`

<a id="def-480e291e8ce3ea1a"></a>
## `CodedSorting.CommonNetworkInputs.gatePort._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NetworkInputs.lean)

**类型**

```lean
∀ {R : Type u_1} [inst : DecidableEq R] (p : List (CodedSorting.CircuitProgram.XorGate R)) (t : Fin p.length),
  ∀ r ∈ (p.get t).ports,
    CodedSorting.ProgramNetwork.wireHead p (CodedSorting.ProgramNetwork.incomingWire p t r) =
      CodedSorting.ProgramNetwork.Vertex.gate t
```

**继续展开**

- [CodedSorting.ProgramNetwork.wireHead](ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.incomingWire](ProgramNetwork.definitions.md#def-43af48346923f0c2)
- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Finset`, `List.get`, `Membership.mem`, `Finset.instMembership`, `List`, `Fin`, `Eq`, `List.length`, `DecidableEq`

<a id="def-2de7039bcee03982"></a>
## `CodedSorting.CommonNetworkInputs.inputList._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NetworkInputs.lean)

**类型**

```lean
∀ {R : Type u_1} [inst : DecidableEq R] (p : List (CodedSorting.CircuitProgram.XorGate R)) (r : R),
  CodedSorting.ProgramNetwork.Vertex.source r = CodedSorting.ProgramNetwork.Vertex.source r
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`List`, `Eq`, `List.length`, `DecidableEq`

<a id="def-b844622c1e885f6d"></a>
## `CodedSorting.CommonNetworkInputs.inputList._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NetworkInputs.lean)

**类型**

```lean
∀ {R : Type u_1} [inst : DecidableEq R] (p : List (CodedSorting.CircuitProgram.XorGate R)) (t : Fin p.length)
  (out : CodedSorting.ProgramNetwork.OutputPort p (CodedSorting.ProgramNetwork.Vertex.gate t)),
  (↑out).2 ∈ (p.get t).ports
```

**继续展开**

- [CodedSorting.ProgramNetwork.OutputPort](ProgramNetwork.definitions.md#def-d59180e636f2c683)
- [CodedSorting.ProgramNetwork.wireTail](ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Finset`, `List.get`, `Membership.mem`, `instOfNatNat`, `Finset.instMembership`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `Prod.snd`, `List.length`, `DecidableEq`

<a id="def-ee19b3c9da9d0c5f"></a>
## `CodedSorting.CommonNetworkInputs.inputList._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NetworkInputs.lean)

**类型**

```lean
∀ {R : Type u_1} [inst : DecidableEq R] (p : List (CodedSorting.CircuitProgram.XorGate R)) (t : Fin p.length),
  ∀ r ∉ (p.get t).ports,
    CodedSorting.ProgramNetwork.wireHead p (CodedSorting.ProgramNetwork.incomingWire p t r) =
      CodedSorting.ProgramNetwork.Vertex.pass t r
```

**继续展开**

- [CodedSorting.ProgramNetwork.wireHead](ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.incomingWire](ProgramNetwork.definitions.md#def-43af48346923f0c2)
- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Finset`, `List.get`, `Membership.mem`, `Finset.instMembership`, `List`, `Fin`, `Eq`, `List.length`, `Not`, `DecidableEq`

<a id="def-654a1cdfeb0eba16"></a>
## `CodedSorting.CommonNetworkInputs.inputList.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](NetworkInputs.lean)

**类型**

```lean
{R : Type u_1} →
  [inst : DecidableEq R] →
    (p : List (CodedSorting.CircuitProgram.XorGate R)) →
      (motive :
          (x : CodedSorting.ProgramNetwork.Vertex R p.length) → CodedSorting.ProgramNetwork.OutputPort p x → Sort u_2) →
        (x : CodedSorting.ProgramNetwork.Vertex R p.length) →
          (x_1 : CodedSorting.ProgramNetwork.OutputPort p x) →
            ((r : R) →
                (x : CodedSorting.ProgramNetwork.OutputPort p (CodedSorting.ProgramNetwork.Vertex.source r)) →
                  motive (CodedSorting.ProgramNetwork.Vertex.source r) x) →
              ((t : Fin p.length) →
                  (out : CodedSorting.ProgramNetwork.OutputPort p (CodedSorting.ProgramNetwork.Vertex.gate t)) →
                    motive (CodedSorting.ProgramNetwork.Vertex.gate t) out) →
                ((t : Fin p.length) →
                    (r : R) →
                      (x : CodedSorting.ProgramNetwork.OutputPort p (CodedSorting.ProgramNetwork.Vertex.pass t r)) →
                        motive (CodedSorting.ProgramNetwork.Vertex.pass t r) x) →
                  ((a : R) →
                      (x : CodedSorting.ProgramNetwork.OutputPort p (CodedSorting.ProgramNetwork.Vertex.sink a)) →
                        motive (CodedSorting.ProgramNetwork.Vertex.sink a) x) →
                    motive x x_1
```

**定义**

```lean
fun {R} [DecidableEq R] p motive x x_1 h_1 h_2 h_3 h_4 =>
  CodedSorting.ProgramNetwork.Vertex.casesOn (motive := fun x =>
    (x_2 : CodedSorting.ProgramNetwork.OutputPort p x) → motive x x_2) x (fun a x => h_1 a x) (fun a x => h_2 a x)
    (fun a a_1 x => h_3 a a_1 x) (fun a x => h_4 a x) x_1
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex.casesOn](ProgramNetwork.definitions.md#def-dce4a35b07c857f6)
- [CodedSorting.ProgramNetwork.OutputPort](ProgramNetwork.definitions.md#def-d59180e636f2c683)
- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Vertex.sink](ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`List`, `Fin`, `List.length`, `DecidableEq`
