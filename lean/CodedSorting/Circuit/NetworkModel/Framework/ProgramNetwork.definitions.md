# ProgramNetwork 的定义

[源码](ProgramNetwork.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-5a51334008fa08b7"></a>
## `CodedSorting.ProgramNetwork.Vertex`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ProgramNetwork.lean#L22)

**类型**

```lean
Type u_1 → ℕ → Type u_1
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.ProgramNetwork.Vertex.sink](ProgramNetwork.definitions.md#def-7c6267025a776389)

**基础库名称**

`Nat`

<a id="def-dce4a35b07c857f6"></a>
## `CodedSorting.ProgramNetwork.Vertex.casesOn`

读取 `CodedSorting.ProgramNetwork.Vertex` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ProgramNetwork.lean#L22)

**类型**

```lean
{Reg : Type u_1} →
  {length : ℕ} →
    {motive : CodedSorting.ProgramNetwork.Vertex Reg length → Sort u} →
      (t : CodedSorting.ProgramNetwork.Vertex Reg length) →
        ((a : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.source a)) →
          ((a : Fin length) → motive (CodedSorting.ProgramNetwork.Vertex.gate a)) →
            ((a : Fin length) → (a_1 : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.pass a a_1)) →
              ((a : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.sink a)) → motive t
```

**定义**

```lean
fun {Reg} {length} {motive} t source gate pass sink =>
  CodedSorting.ProgramNetwork.Vertex.rec (fun a => source a) (fun a => gate a) (fun a a_1 => pass a a_1)
    (fun a => sink a) t
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.ProgramNetwork.Vertex.rec](ProgramNetwork.definitions.md#def-a733b626a5a6afc8)
- [CodedSorting.ProgramNetwork.Vertex.sink](ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Nat`, `Fin`

<a id="def-a733b626a5a6afc8"></a>
## `CodedSorting.ProgramNetwork.Vertex.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](ProgramNetwork.lean#L22)

**类型**

```lean
{Reg : Type u_1} →
  {length : ℕ} →
    {motive : CodedSorting.ProgramNetwork.Vertex Reg length → Sort u} →
      ((a : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.source a)) →
        ((a : Fin length) → motive (CodedSorting.ProgramNetwork.Vertex.gate a)) →
          ((a : Fin length) → (a_1 : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.pass a a_1)) →
            ((a : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.sink a)) →
              (t : CodedSorting.ProgramNetwork.Vertex Reg length) → motive t
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.ProgramNetwork.Vertex.sink](ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Nat`, `Fin`

<a id="def-e888b38289e13ef4"></a>
## `CodedSorting.ProgramNetwork.Vertex.source`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ProgramNetwork.lean#L23)

**类型**

```lean
{Reg : Type u_1} → {length : ℕ} → Reg → CodedSorting.ProgramNetwork.Vertex Reg length
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Nat`

<a id="def-db451a9b9ef0c151"></a>
## `CodedSorting.ProgramNetwork.Vertex.gate`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ProgramNetwork.lean#L24)

**类型**

```lean
{Reg : Type u_1} → {length : ℕ} → Fin length → CodedSorting.ProgramNetwork.Vertex Reg length
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Nat`, `Fin`

<a id="def-afc8f3ea66d065cc"></a>
## `CodedSorting.ProgramNetwork.Vertex.pass`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ProgramNetwork.lean#L25)

**类型**

```lean
{Reg : Type u_1} → {length : ℕ} → Fin length → Reg → CodedSorting.ProgramNetwork.Vertex Reg length
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Nat`, `Fin`

<a id="def-7c6267025a776389"></a>
## `CodedSorting.ProgramNetwork.Vertex.sink`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ProgramNetwork.lean#L26)

**类型**

```lean
{Reg : Type u_1} → {length : ℕ} → Reg → CodedSorting.ProgramNetwork.Vertex Reg length
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Nat`

<a id="def-c8f35892a045d1f9"></a>
## `CodedSorting.ProgramNetwork.instFintypeVertex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L27)

**类型**

```lean
{Reg : Type u_1} → {length : ℕ} → [inst : Fintype Reg] → Fintype (CodedSorting.ProgramNetwork.Vertex Reg length)
```

**定义**

```lean
fun {Reg} {length} [Fintype Reg] =>
  Fintype.ofEquiv (Reg ⊕ Fin length ⊕ (_ : Fin length) × Reg ⊕ Reg)
    (CodedSorting.ProgramNetwork.Vertex.proxyTypeEquiv Reg length)
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex.proxyTypeEquiv](ProgramNetwork.definitions.md#def-353098924b68fb9f)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`instFintypeSum`, `Sum`, `Fintype.ofEquiv`, `Fin.fintype`, `Fintype`, `Nat`, `Sigma.instFintype`, `Fin`, `Sigma`

<a id="def-d72ef8ed1f1d7af4"></a>
## `CodedSorting.ProgramNetwork.Wire`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L29)

**类型**

```lean
Type u_1 → ℕ → Type (max 0 u_1)
```

**定义**

```lean
fun Reg length => Fin (length + 1) × Reg
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-4139b0786aeb042d"></a>
## `CodedSorting.ProgramNetwork.stageVertex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L34)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (program : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      Fin program.length → Reg → CodedSorting.ProgramNetwork.Vertex Reg program.length
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] program t r =>
  if r ∈ (program.get t).ports then CodedSorting.ProgramNetwork.Vertex.gate t
  else CodedSorting.ProgramNetwork.Vertex.pass t r
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.ports](../../Framework/CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Finset`, `List.get`, `Membership.mem`, `Finset.instMembership`, `List`, `Finset.decidableMem`, `Fin`, `List.length`, `DecidableEq`, `ite`

<a id="def-d6643374d872cf41"></a>
## `CodedSorting.ProgramNetwork.wireTail`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L43)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (program : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      CodedSorting.ProgramNetwork.Wire Reg program.length → CodedSorting.ProgramNetwork.Vertex Reg program.length
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] program edge =>
  if h : ↑edge.1 = 0 then CodedSorting.ProgramNetwork.Vertex.source edge.2
  else CodedSorting.ProgramNetwork.stageVertex program ⟨↑edge.1 - 1, ⋯⟩ edge.2
```

**继续展开**

- [CodedSorting.ProgramNetwork.stageVertex](ProgramNetwork.definitions.md#def-4139b0786aeb042d)
- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.wireTail._proof_23](ProgramNetwork.definitions.md#def-e6351cc1dba17a1f)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`HSub.hSub`, `Fin.mk`, `instSubNat`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `dite`, `List`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instDecidableEqNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `List.length`, `Not`, `DecidableEq`

<a id="def-0c7209c651d6dc49"></a>
## `CodedSorting.ProgramNetwork.wireHead`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L47)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (program : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      CodedSorting.ProgramNetwork.Wire Reg program.length → CodedSorting.ProgramNetwork.Vertex Reg program.length
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] program edge =>
  if h : ↑edge.1 = program.length then CodedSorting.ProgramNetwork.Vertex.sink edge.2
  else CodedSorting.ProgramNetwork.stageVertex program ⟨↑edge.1, ⋯⟩ edge.2
```

**继续展开**

- [CodedSorting.ProgramNetwork.stageVertex](ProgramNetwork.definitions.md#def-4139b0786aeb042d)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Vertex.sink](ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.ProgramNetwork.wireHead._proof_25](ProgramNetwork.definitions.md#def-6dad93c887c97847)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Fin.mk`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `dite`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instDecidableEqNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `List.length`, `Not`, `DecidableEq`

<a id="def-43af48346923f0c2"></a>
## `CodedSorting.ProgramNetwork.incomingWire`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L80)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (program : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      Fin program.length → Reg → CodedSorting.ProgramNetwork.Wire Reg program.length
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] program t r => (⟨↑t, ⋯⟩, r)
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.incomingWire._proof_28](ProgramNetwork.definitions.md#def-e976b8de1f48b518)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Fin.mk`, `Prod.mk`, `instOfNatNat`, `Fin.val`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `List.length`, `DecidableEq`

<a id="def-8484131e8c07cf94"></a>
## `CodedSorting.ProgramNetwork.sinkWire`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L88)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (program : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      Reg → CodedSorting.ProgramNetwork.Wire Reg program.length
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] program r => (⟨program.length, ⋯⟩, r)
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.sinkWire._proof_31](ProgramNetwork.definitions.md#def-0fc5a8733de4c5fc)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Fin.mk`, `Prod.mk`, `instOfNatNat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `List.length`, `DecidableEq`

<a id="def-c0edc85888c37e6c"></a>
## `CodedSorting.ProgramNetwork.InputPort`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L216)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (program : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      CodedSorting.ProgramNetwork.Vertex Reg program.length → Type u_1
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] program v =>
  { r // CodedSorting.ProgramNetwork.Vertex.source r = v } ⊕
    { edge // CodedSorting.ProgramNetwork.wireHead program edge = v }
```

**继续展开**

- [CodedSorting.ProgramNetwork.wireHead](ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Sum`, `Subtype`, `List`, `Eq`, `List.length`, `DecidableEq`

<a id="def-d59180e636f2c683"></a>
## `CodedSorting.ProgramNetwork.OutputPort`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ProgramNetwork.lean#L220)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (program : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      CodedSorting.ProgramNetwork.Vertex Reg program.length → Type (max 0 u_1)
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] program v => { edge // CodedSorting.ProgramNetwork.wireTail program edge = v }
```

**继续展开**

- [CodedSorting.ProgramNetwork.wireTail](ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Subtype`, `List`, `Eq`, `List.length`, `DecidableEq`

<a id="def-353098924b68fb9f"></a>
## `CodedSorting.ProgramNetwork.Vertex.proxyTypeEquiv`

读取 `CodedSorting.ProgramNetwork.Vertex` 的 `proxyTypeEquiv` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ProgramNetwork.lean)

**类型**

```lean
(Reg : Type u_1) →
  (length : ℕ) → Reg ⊕ Fin length ⊕ (_ : Fin length) × Reg ⊕ Reg ≃ CodedSorting.ProgramNetwork.Vertex Reg length
```

**定义**

```lean
fun Reg length =>
  {
    toFun := fun x =>
      match x with
      | Sum.inl a => CodedSorting.ProgramNetwork.Vertex.source a
      | Sum.inr (Sum.inl a) => CodedSorting.ProgramNetwork.Vertex.gate a
      | Sum.inr (Sum.inr (Sum.inl ⟨a, a_1⟩)) => CodedSorting.ProgramNetwork.Vertex.pass a a_1
      | Sum.inr (Sum.inr (Sum.inr a)) => CodedSorting.ProgramNetwork.Vertex.sink a,
    invFun := fun x =>
      match x with
      | CodedSorting.ProgramNetwork.Vertex.source a => Sum.inl a
      | CodedSorting.ProgramNetwork.Vertex.gate a => Sum.inr (Sum.inl a)
      | CodedSorting.ProgramNetwork.Vertex.pass a a_1 => Sum.inr (Sum.inr (Sum.inl ⟨a, a_1⟩))
      | CodedSorting.ProgramNetwork.Vertex.sink a => Sum.inr (Sum.inr (Sum.inr a)),
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.ProgramNetwork.instFintypeVertex.match_2](ProgramNetwork.definitions.md#def-0f9723e235b6e64e)
- [CodedSorting.ProgramNetwork.Vertex.casesOn](ProgramNetwork.definitions.md#def-dce4a35b07c857f6)
- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.ProgramNetwork.instFintypeVertex.match_1](ProgramNetwork.definitions.md#def-05733f7a52b232b0)
- [CodedSorting.ProgramNetwork.Vertex.sink](ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Equiv.mk`, `Sum.casesOn`, `Sum`, `Equiv`, `Sum.inl`, `Sum.inr`, `Nat`, `Eq.ndrec`, `Eq.refl`, `Sigma.mk`, `Eq.symm`, `Fin`, `Eq`, `Sigma`

<a id="def-e976b8de1f48b518"></a>
## `CodedSorting.ProgramNetwork.incomingWire._proof_28`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ProgramNetwork.lean)

**类型**

```lean
∀ {Reg : Type u_1} [inst : DecidableEq Reg] (program : List (CodedSorting.CircuitProgram.XorGate Reg))
  (t : Fin program.length), ↑t < program.length.succ
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`Fin.val`, `List`, `Nat`, `LT.lt`, `instLTNat`, `Fin`, `Nat.succ`, `List.length`, `DecidableEq`

<a id="def-05733f7a52b232b0"></a>
## `CodedSorting.ProgramNetwork.instFintypeVertex.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ProgramNetwork.lean)

**类型**

```lean
(Reg : Type u_1) →
  (length : ℕ) →
    (motive : Reg ⊕ Fin length ⊕ (_ : Fin length) × Reg ⊕ Reg → Sort u_2) →
      (x : Reg ⊕ Fin length ⊕ (_ : Fin length) × Reg ⊕ Reg) →
        ((a : Reg) → motive (Sum.inl a)) →
          ((a : Fin length) → motive (Sum.inr (Sum.inl a))) →
            ((a : Fin length) → (a_1 : Reg) → motive (Sum.inr (Sum.inr (Sum.inl ⟨a, a_1⟩)))) →
              ((a : Reg) → motive (Sum.inr (Sum.inr (Sum.inr a)))) → motive x
```

**定义**

```lean
fun Reg length motive x h_1 h_2 h_3 h_4 =>
  Sum.casesOn x (fun val => h_1 val) fun val =>
    Sum.casesOn val (fun val => h_2 val) fun val =>
      Sum.casesOn val (fun val => Sigma.casesOn val fun fst snd => h_3 fst snd) fun val => h_4 val
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Sum.casesOn`, `Sum`, `Sum.inl`, `Sum.inr`, `Nat`, `Sigma.mk`, `Sigma.casesOn`, `Fin`, `Sigma`

<a id="def-0f9723e235b6e64e"></a>
## `CodedSorting.ProgramNetwork.instFintypeVertex.match_2`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ProgramNetwork.lean)

**类型**

```lean
(Reg : Type u_1) →
  (length : ℕ) →
    (motive : CodedSorting.ProgramNetwork.Vertex Reg length → Sort u_2) →
      (x : CodedSorting.ProgramNetwork.Vertex Reg length) →
        ((a : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.source a)) →
          ((a : Fin length) → motive (CodedSorting.ProgramNetwork.Vertex.gate a)) →
            ((a : Fin length) → (a_1 : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.pass a a_1)) →
              ((a : Reg) → motive (CodedSorting.ProgramNetwork.Vertex.sink a)) → motive x
```

**定义**

```lean
fun Reg length motive x h_1 h_2 h_3 h_4 =>
  CodedSorting.ProgramNetwork.Vertex.casesOn x (fun a => h_1 a) (fun a => h_2 a) (fun a a_1 => h_3 a a_1) fun a => h_4 a
```

**继续展开**

- [CodedSorting.ProgramNetwork.Vertex.casesOn](ProgramNetwork.definitions.md#def-dce4a35b07c857f6)
- [CodedSorting.ProgramNetwork.Vertex.source](ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.ProgramNetwork.Vertex.gate](ProgramNetwork.definitions.md#def-db451a9b9ef0c151)
- [CodedSorting.ProgramNetwork.Vertex.pass](ProgramNetwork.definitions.md#def-afc8f3ea66d065cc)
- [CodedSorting.ProgramNetwork.Vertex.sink](ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.ProgramNetwork.Vertex](ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Nat`, `Fin`

<a id="def-0fc5a8733de4c5fc"></a>
## `CodedSorting.ProgramNetwork.sinkWire._proof_31`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ProgramNetwork.lean)

**类型**

```lean
∀ {Reg : Type u_1} [inst : DecidableEq Reg] (program : List (CodedSorting.CircuitProgram.XorGate Reg)),
  program.length < program.length.succ
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`List`, `Nat`, `LT.lt`, `instLTNat`, `Nat.succ`, `List.length`, `DecidableEq`

<a id="def-6dad93c887c97847"></a>
## `CodedSorting.ProgramNetwork.wireHead._proof_25`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ProgramNetwork.lean)

**类型**

```lean
∀ {Reg : Type u_1} [inst : DecidableEq Reg] (program : List (CodedSorting.CircuitProgram.XorGate Reg))
  (edge : CodedSorting.ProgramNetwork.Wire Reg program.length), ¬↑edge.1 = program.length → ↑edge.1 < program.length
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`instOfNatNat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `List.length`, `Not`, `DecidableEq`

<a id="def-e6351cc1dba17a1f"></a>
## `CodedSorting.ProgramNetwork.wireTail._proof_23`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ProgramNetwork.lean)

**类型**

```lean
∀ {Reg : Type u_1} [inst : DecidableEq Reg] (program : List (CodedSorting.CircuitProgram.XorGate Reg))
  (edge : CodedSorting.ProgramNetwork.Wire Reg program.length), ¬↑edge.1 = 0 → ↑edge.1 - 1 < program.length
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`HSub.hSub`, `instSubNat`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `List.length`, `Not`, `DecidableEq`
