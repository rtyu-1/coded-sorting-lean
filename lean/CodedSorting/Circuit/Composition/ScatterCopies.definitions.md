# ScatterCopies 的定义

[源码](ScatterCopies.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e9d75cf5c51fb139"></a>
## `CodedSorting.Construction.ExplicitCopies.originalEmbedding`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScatterCopies.lean#L27)

**类型**

```lean
{R : Type u_1} → {T : Type u_2} → R ↪ R ⊕ T
```

**定义**

```lean
fun {R} {T} => { toFun := Sum.inl, inj' := ⋯ }
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Sum.inl_injective`, `Function.Embedding.mk`, `Sum`, `Sum.inl`, `Function.Embedding`

<a id="def-25b5779705424b6b"></a>
## `CodedSorting.Construction.ExplicitCopies.temporaryEmbedding`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScatterCopies.lean#L30)

**类型**

```lean
{R : Type u_1} → {T : Type u_2} → T ↪ R ⊕ T
```

**定义**

```lean
fun {R} {T} => { toFun := Sum.inr, inj' := ⋯ }
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Sum.inr_injective`, `Function.Embedding.mk`, `Sum`, `Function.Embedding`, `Sum.inr`

<a id="def-a03389164991af4f"></a>
## `CodedSorting.Construction.ExplicitCopies.copyGate`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScatterCopies.lean#L35)

**类型**

```lean
{R : Type u_1} →
  {T : Type u_2} →
    [inst : DecidableEq R] → [inst_1 : DecidableEq T] → (T → R) → T → CodedSorting.CircuitProgram.XorGate (R ⊕ T)
```

**定义**

```lean
fun {R} {T} [DecidableEq R] [DecidableEq T] helper t =>
  CodedSorting.Construction.NetworkAdapter.overwriteCopy (Sum.inr t) (Sum.inl (helper t))
```

**继续展开**

- [CodedSorting.Construction.NetworkAdapter.overwriteCopy](../NetworkModel/NetworkAdapter.definitions.md#def-2e2fa962a2b01453)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`Sum`, `Sum.instDecidableEq`, `Sum.inl`, `Sum.inr`, `DecidableEq`

<a id="def-dcb3b0ebd623d764"></a>
## `CodedSorting.Construction.ExplicitCopies.copyProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScatterCopies.lean#L40)

**类型**

```lean
{R : Type u_1} →
  {T : Type u_2} →
    [inst : DecidableEq R] →
      [inst_1 : DecidableEq T] → (T → R) → List T → List (CodedSorting.CircuitProgram.XorGate (R ⊕ T))
```

**定义**

```lean
fun {R} {T} [DecidableEq R] [DecidableEq T] helper temporaries =>
  List.map (CodedSorting.Construction.ExplicitCopies.copyGate helper) temporaries
```

**继续展开**

- [CodedSorting.Construction.ExplicitCopies.copyGate](ScatterCopies.definitions.md#def-a03389164991af4f)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`List.map`, `Sum`, `Sum.instDecidableEq`, `List`, `DecidableEq`

<a id="def-531817fed1066a5c"></a>
## `CodedSorting.Construction.ScatterCopies.ScatterRow`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ScatterCopies.lean#L145)

**类型**

```lean
Type u_3 → Type u_4 → Type (max u_3 u_4)
```

**继续展开**

- [CodedSorting.Construction.ScatterCopies.ScatterRow.mk](ScatterCopies.definitions.md#def-ca957c76c103117c)

<a id="def-ca957c76c103117c"></a>
## `CodedSorting.Construction.ScatterCopies.ScatterRow.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ScatterCopies.lean#L147)

**类型**

```lean
{R : Type u_3} → {T : Type u_4} → R → Finset T → CodedSorting.Construction.ScatterCopies.ScatterRow R T
```

**继续展开**

- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)

**基础库名称**

`Finset`

<a id="def-ad19e1111603264b"></a>
## `CodedSorting.Construction.ScatterCopies.ScatterRow.destination`

读取 `CodedSorting.Construction.ScatterCopies.ScatterRow` 的 `destination` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ScatterCopies.lean#L148)

**类型**

```lean
{R : Type u_3} → {T : Type u_4} → CodedSorting.Construction.ScatterCopies.ScatterRow R T → R
```

**定义**

```lean
fun R T self => self.1
```

**继续展开**

- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)

<a id="def-1d44e9f8149f5749"></a>
## `CodedSorting.Construction.ScatterCopies.ScatterRow.sources`

读取 `CodedSorting.Construction.ScatterCopies.ScatterRow` 的 `sources` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ScatterCopies.lean#L149)

**类型**

```lean
{R : Type u_3} → {T : Type u_4} → CodedSorting.Construction.ScatterCopies.ScatterRow R T → Finset T
```

**定义**

```lean
fun R T self => self.2
```

**继续展开**

- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)

**基础库名称**

`Finset`

<a id="def-8b2995aef7915972"></a>
## `CodedSorting.Construction.ScatterCopies.copiedScatter`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScatterCopies.lean#L158)

**类型**

```lean
{R : Type u_1} →
  {T : Type u_2} →
    [inst : DecidableEq R] →
      [inst_1 : DecidableEq T] →
        CodedSorting.Construction.ScatterCopies.ScatterRow R T → CodedSorting.CircuitProgram.XorGate (R ⊕ T)
```

**定义**

```lean
fun {R} {T} [DecidableEq R] [DecidableEq T] row =>
  {
    ports :=
      {Sum.inl row.destination} ∪ Finset.map CodedSorting.Construction.ExplicitCopies.temporaryEmbedding row.sources,
    targets := {Sum.inl row.destination},
    controls := fun x => Finset.map CodedSorting.Construction.ExplicitCopies.temporaryEmbedding row.sources,
    targets_subset := ⋯, controls_subset := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.ScatterCopies.ScatterRow.destination](ScatterCopies.definitions.md#def-ad19e1111603264b)
- [CodedSorting.Construction.ScatterCopies.copiedScatter._proof_3](ScatterCopies.definitions.md#def-a919de77e17a7d08)
- [CodedSorting.CircuitProgram.XorGate.mk](../Framework/CircuitProgram.definitions.md#def-a958dc84c6bc445e)
- [CodedSorting.Construction.ExplicitCopies.temporaryEmbedding](ScatterCopies.definitions.md#def-25b5779705424b6b)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.ScatterCopies.ScatterRow.sources](ScatterCopies.definitions.md#def-1d44e9f8149f5749)
- [CodedSorting.Construction.ScatterCopies.copiedScatter._proof_4](ScatterCopies.definitions.md#def-eb7ec314894c034d)

**基础库名称**

`Finset.instUnion`, `Finset`, `Finset.map`, `Sum`, `Sum.instDecidableEq`, `Sum.inl`, `Union.union`, `Finset.instSingleton`, `Singleton.singleton`, `DecidableEq`

<a id="def-3d4bd9c0c69b0fce"></a>
## `CodedSorting.Construction.ScatterCopies.physicalScatter`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScatterCopies.lean#L208)

**类型**

```lean
{R : Type u_1} →
  {T : Type u_2} →
    [inst : DecidableEq R] →
      [inst_1 : DecidableEq T] →
        List (CodedSorting.Construction.ScatterCopies.ScatterRow R T) →
          List (CodedSorting.CircuitProgram.XorGate (R ⊕ T))
```

**定义**

```lean
fun {R} {T} [DecidableEq R] [DecidableEq T] rows => List.map CodedSorting.Construction.ScatterCopies.copiedScatter rows
```

**继续展开**

- [CodedSorting.Construction.ScatterCopies.copiedScatter](ScatterCopies.definitions.md#def-8b2995aef7915972)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)

**基础库名称**

`List.map`, `Sum`, `Sum.instDecidableEq`, `List`, `DecidableEq`

<a id="def-6b5504d1a6afa918"></a>
## `CodedSorting.Construction.ScatterCopies.expandedProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScatterCopies.lean#L237)

**类型**

```lean
{R : Type u_1} →
  {T : Type u_2} →
    [inst : DecidableEq R] →
      [inst_1 : DecidableEq T] →
        [inst_2 : Fintype R] →
          (T ↪ R) →
            List T →
              List (CodedSorting.CircuitProgram.XorGate R) →
                List (CodedSorting.CircuitProgram.XorGate R) →
                  List (CodedSorting.Construction.ScatterCopies.ScatterRow R T) →
                    List (CodedSorting.CircuitProgram.XorGate (R ⊕ T))
```

**定义**

```lean
fun {R} {T} [DecidableEq R] [DecidableEq T] [Fintype R] helper temporaries before after rows =>
  List.map (CodedSorting.CircuitProgram.XorGate.lift CodedSorting.Construction.ExplicitCopies.originalEmbedding)
          before ++
        CodedSorting.Construction.ExplicitCopies.copyProgram (⇑helper) temporaries ++
      CodedSorting.Construction.ScatterCopies.physicalScatter rows ++
    List.map (CodedSorting.CircuitProgram.XorGate.lift CodedSorting.Construction.ExplicitCopies.originalEmbedding) after
```

**继续展开**

- [CodedSorting.Construction.ExplicitCopies.originalEmbedding](ScatterCopies.definitions.md#def-e9d75cf5c51fb139)
- [CodedSorting.CircuitProgram.XorGate.lift](../Framework/CircuitProgram.definitions.md#def-797ff3f834dbecd3)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.ExplicitCopies.copyProgram](ScatterCopies.definitions.md#def-dcb3b0ebd623d764)
- [CodedSorting.Construction.ScatterCopies.physicalScatter](ScatterCopies.definitions.md#def-3d4bd9c0c69b0fce)

**基础库名称**

`List.map`, `Sum`, `Sum.instDecidableEq`, `Function.Embedding`, `instHAppendOfAppend`, `List`, `Fintype`, `List.instAppend`, `Function.instFunLikeEmbedding`, `DFunLike.coe`, `HAppend.hAppend`, `DecidableEq`

<a id="def-a919de77e17a7d08"></a>
## `CodedSorting.Construction.ScatterCopies.copiedScatter._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ScatterCopies.lean)

**类型**

```lean
∀ {R : Type u_1} {T : Type u_2} [inst : DecidableEq R] [inst_1 : DecidableEq T]
  (row : CodedSorting.Construction.ScatterCopies.ScatterRow R T),
  {Sum.inl row.destination} ⊆
    {Sum.inl row.destination} ∪ Finset.map CodedSorting.Construction.ExplicitCopies.temporaryEmbedding row.sources
```

**继续展开**

- [CodedSorting.Construction.ScatterCopies.ScatterRow.destination](ScatterCopies.definitions.md#def-ad19e1111603264b)
- [CodedSorting.Construction.ExplicitCopies.temporaryEmbedding](ScatterCopies.definitions.md#def-25b5779705424b6b)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.ScatterCopies.ScatterRow.sources](ScatterCopies.definitions.md#def-1d44e9f8149f5749)

**基础库名称**

`Finset.instUnion`, `Finset`, `Finset.map`, `Sum`, `Sum.instDecidableEq`, `HasSubset.Subset`, `Sum.inl`, `Finset.instHasSubset`, `Union.union`, `Finset.instSingleton`, `Singleton.singleton`, `DecidableEq`

<a id="def-eb7ec314894c034d"></a>
## `CodedSorting.Construction.ScatterCopies.copiedScatter._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ScatterCopies.lean)

**类型**

```lean
∀ {R : Type u_1} {T : Type u_2} [inst : DecidableEq R] [inst_1 : DecidableEq T]
  (row : CodedSorting.Construction.ScatterCopies.ScatterRow R T),
  ∀ r ∈ {Sum.inl row.destination},
    Finset.map CodedSorting.Construction.ExplicitCopies.temporaryEmbedding row.sources ⊆
      {Sum.inl row.destination} ∪ Finset.map CodedSorting.Construction.ExplicitCopies.temporaryEmbedding row.sources
```

**继续展开**

- [CodedSorting.Construction.ScatterCopies.ScatterRow.destination](ScatterCopies.definitions.md#def-ad19e1111603264b)
- [CodedSorting.Construction.ExplicitCopies.temporaryEmbedding](ScatterCopies.definitions.md#def-25b5779705424b6b)
- [CodedSorting.Construction.ScatterCopies.ScatterRow](ScatterCopies.definitions.md#def-531817fed1066a5c)
- [CodedSorting.Construction.ScatterCopies.ScatterRow.sources](ScatterCopies.definitions.md#def-1d44e9f8149f5749)

**基础库名称**

`Finset.instUnion`, `Finset`, `Finset.map`, `Membership.mem`, `Sum`, `Sum.instDecidableEq`, `HasSubset.Subset`, `Sum.inl`, `Finset.instMembership`, `Finset.instHasSubset`, `Union.union`, `Finset.instSingleton`, `Singleton.singleton`, `DecidableEq`
