# CircuitProgram 的定义

[源码](CircuitProgram.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-53636b8dd9e7f863"></a>
## `CodedSorting.CircuitProgram.XorGate`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](CircuitProgram.lean#L19)

**类型**

```lean
(R : Type u_1) → [inst : DecidableEq R] → Type u_1
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.mk](CircuitProgram.definitions.md#def-a958dc84c6bc445e)

**基础库名称**

`DecidableEq`

<a id="def-a958dc84c6bc445e"></a>
## `CodedSorting.CircuitProgram.XorGate.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](CircuitProgram.lean#L20)

**类型**

```lean
{R : Type u_1} →
  [inst : DecidableEq R] →
    (ports targets : Finset R) →
      (controls : R → Finset R) →
        targets ⊆ ports → (∀ r ∈ targets, controls r ⊆ ports) → CodedSorting.CircuitProgram.XorGate R
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`Finset`, `Membership.mem`, `HasSubset.Subset`, `Finset.instMembership`, `Finset.instHasSubset`, `DecidableEq`

<a id="def-868b71c12739321b"></a>
## `CodedSorting.CircuitProgram.XorGate.ports`

读取 `CodedSorting.CircuitProgram.XorGate` 的 `ports` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](CircuitProgram.lean#L21)

**类型**

```lean
{R : Type u_1} → [inst : DecidableEq R] → CodedSorting.CircuitProgram.XorGate R → Finset R
```

**定义**

```lean
fun R [DecidableEq R] self => self.1
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`Finset`, `DecidableEq`

<a id="def-257d99bf8097b011"></a>
## `CodedSorting.CircuitProgram.XorGate.targets`

读取 `CodedSorting.CircuitProgram.XorGate` 的 `targets` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](CircuitProgram.lean#L22)

**类型**

```lean
{R : Type u_1} → [inst : DecidableEq R] → CodedSorting.CircuitProgram.XorGate R → Finset R
```

**定义**

```lean
fun R [DecidableEq R] self => self.2
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`Finset`, `DecidableEq`

<a id="def-623fb3e8f456b5a4"></a>
## `CodedSorting.CircuitProgram.XorGate.controls`

读取 `CodedSorting.CircuitProgram.XorGate` 的 `controls` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](CircuitProgram.lean#L23)

**类型**

```lean
{R : Type u_1} → [inst : DecidableEq R] → CodedSorting.CircuitProgram.XorGate R → R → Finset R
```

**定义**

```lean
fun R [DecidableEq R] self => self.3
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`Finset`, `DecidableEq`

<a id="def-5733a70d64457842"></a>
## `CodedSorting.CircuitProgram.XorGate.liftControls`

读取 `CodedSorting.CircuitProgram.XorGate` 的 `liftControls` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](CircuitProgram.lean#L153)

**类型**

```lean
{R : Type u_1} →
  {S : Type u_2} →
    [inst : Fintype R] →
      [inst : DecidableEq R] → [inst_1 : DecidableEq S] → (R ↪ S) → CodedSorting.CircuitProgram.XorGate R → S → Finset S
```

**定义**

```lean
fun {R} {S} [Fintype R] [DecidableEq R] [DecidableEq S] e g q => Finset.map e {c | ∃ r, e r = q ∧ c ∈ g.controls r}
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.CircuitProgram.XorGate.controls](CircuitProgram.definitions.md#def-623fb3e8f456b5a4)

**基础库名称**

`Finset.univ`, `Finset`, `Finset.map`, `Membership.mem`, `Exists`, `Finset.instMembership`, `Function.Embedding`, `Fintype.decidableExistsFintype`, `And`, `Fintype`, `instDecidableAnd`, `Function.instFunLikeEmbedding`, `Finset.decidableMem`, `Finset.filter`, `Eq`, `DFunLike.coe`, `DecidableEq`

<a id="def-797ff3f834dbecd3"></a>
## `CodedSorting.CircuitProgram.XorGate.lift`

读取 `CodedSorting.CircuitProgram.XorGate` 的 `lift` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](CircuitProgram.lean#L171)

**类型**

```lean
{R : Type u_1} →
  {S : Type u_2} →
    [inst : Fintype R] →
      [inst : DecidableEq R] →
        [inst_1 : DecidableEq S] →
          (R ↪ S) → CodedSorting.CircuitProgram.XorGate R → CodedSorting.CircuitProgram.XorGate S
```

**定义**

```lean
fun {R} {S} [Fintype R] [DecidableEq R] [DecidableEq S] e g =>
  { ports := Finset.map e g.ports, targets := Finset.map e g.targets,
    controls := CodedSorting.CircuitProgram.XorGate.liftControls e g, targets_subset := ⋯, controls_subset := ⋯ }
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.lift._proof_2](CircuitProgram.definitions.md#def-e4f52462547a43d2)
- [CodedSorting.CircuitProgram.XorGate.targets](CircuitProgram.definitions.md#def-257d99bf8097b011)
- [CodedSorting.CircuitProgram.XorGate.mk](CircuitProgram.definitions.md#def-a958dc84c6bc445e)
- [CodedSorting.CircuitProgram.XorGate.lift._proof_1](CircuitProgram.definitions.md#def-6922731eba5bf561)
- [CodedSorting.CircuitProgram.XorGate.ports](CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.CircuitProgram.XorGate.liftControls](CircuitProgram.definitions.md#def-5733a70d64457842)

**基础库名称**

`Finset.map`, `Function.Embedding`, `Fintype`, `DecidableEq`

<a id="def-7cacfe701ea2402a"></a>
## `CodedSorting.CircuitProgram.partitionProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CircuitProgram.lean#L225)

**类型**

```lean
{K : Type u_1} →
  {R : Type u_2} →
    {S : Type u_3} →
      [inst : Fintype R] →
        [inst : DecidableEq R] →
          [inst_1 : DecidableEq S] →
            (K → R ↪ S) →
              List K → List (CodedSorting.CircuitProgram.XorGate R) → List (CodedSorting.CircuitProgram.XorGate S)
```

**定义**

```lean
fun {K} {R} {S} [Fintype R] [DecidableEq R] [DecidableEq S] e ks p =>
  List.flatMap (fun k => List.map (CodedSorting.CircuitProgram.XorGate.lift (e k)) p) ks
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.lift](CircuitProgram.definitions.md#def-797ff3f834dbecd3)
- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`List.map`, `Function.Embedding`, `List`, `Fintype`, `List.flatMap`, `DecidableEq`

<a id="def-6922731eba5bf561"></a>
## `CodedSorting.CircuitProgram.XorGate.lift._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CircuitProgram.lean)

**类型**

```lean
∀ {R : Type u_2} {S : Type u_1} [inst : DecidableEq R] (e : R ↪ S) (g : CodedSorting.CircuitProgram.XorGate R) ⦃q : S⦄,
  q ∈ Finset.map e g.targets → q ∈ Finset.map e g.ports
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.targets](CircuitProgram.definitions.md#def-257d99bf8097b011)
- [CodedSorting.CircuitProgram.XorGate.ports](CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`Finset`, `Finset.map`, `Membership.mem`, `Finset.instMembership`, `Function.Embedding`, `DecidableEq`

<a id="def-e4f52462547a43d2"></a>
## `CodedSorting.CircuitProgram.XorGate.lift._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CircuitProgram.lean)

**类型**

```lean
∀ {R : Type u_2} {S : Type u_1} [inst : Fintype R] [inst_1 : DecidableEq R] [inst_2 : DecidableEq S] (e : R ↪ S)
  (g : CodedSorting.CircuitProgram.XorGate R),
  ∀ q ∈ Finset.map e g.targets,
    ∀ ⦃c : S⦄, c ∈ CodedSorting.CircuitProgram.XorGate.liftControls e g q → c ∈ Finset.map e g.ports
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate.targets](CircuitProgram.definitions.md#def-257d99bf8097b011)
- [CodedSorting.CircuitProgram.XorGate.ports](CircuitProgram.definitions.md#def-868b71c12739321b)
- [CodedSorting.CircuitProgram.XorGate](CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.CircuitProgram.XorGate.liftControls](CircuitProgram.definitions.md#def-5733a70d64457842)

**基础库名称**

`Finset`, `Finset.map`, `Membership.mem`, `Finset.instMembership`, `Function.Embedding`, `Fintype`, `DecidableEq`
