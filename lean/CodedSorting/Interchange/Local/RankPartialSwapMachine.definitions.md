# RankPartialSwapMachine 的定义

[源码](RankPartialSwapMachine.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e3d2391d9d44e72d"></a>
## `CodedSorting.Construction.PartialSwapMachine.ScanAllocation`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](RankPartialSwapMachine.lean#L28)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → Prop
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation.mk](RankPartialSwapMachine.definitions.md#def-4dff7b5bc286d87a)

**基础库名称**

`Nat`

<a id="def-4dff7b5bc286d87a"></a>
## `CodedSorting.Construction.PartialSwapMachine.ScanAllocation.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](RankPartialSwapMachine.lean#L29)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source buffer limit : ℕ},
  source + CodedSorting.CommonPermutationPairs.count q V ≤ buffer →
    buffer + CodedSorting.CommonPermutationPairs.count q V ≤ limit →
      limit ≤ q.N ^ q.exponent → CodedSorting.Construction.PartialSwapMachine.ScanAllocation q V source buffer limit
```

**继续展开**

- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`

<a id="def-871961d0079ec64f"></a>
## `CodedSorting.Construction.PartialSwapMachine.scans`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L41)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V source buffer limit : ℕ} →
    Fin q.inventory.readers →
      (ps : List (CodedSorting.ScanProgram.Pass V)) →
        CodedSorting.Construction.PartialSwapMachine.ScanAllocation q V source buffer limit →
          CodedSorting.CommonFinitePermutation.Program q V source buffer limit
            (Equiv.symm (CodedSorting.ScanProgram.destination ps))
```

**定义**

```lean
fun q {V source buffer limit} reader ps a =>
  { instructions := CodedSorting.CommonRankEdgeScan.code q reader ps source buffer,
    charge := 3 * (CodedSorting.ScanProgram.totalConstant ps + 8) * CodedSorting.CommonPermutationPairs.count q V,
    correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonRankEdgeScan.cost_le](../../Circuit/NetworkModel/Framework/RankEdgeSum.definitions.md#def-f0839888d16645a0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.CommonRankEdgeScan.safe](../../Circuit/NetworkModel/Framework/RankEdgeSum.definitions.md#def-c7d052f63c520c81)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.PartialSwapMachine.scans._proof_2](RankPartialSwapMachine.definitions.md#def-5ff1d6fb7f761cf2)
- [CodedSorting.Construction.PartialSwapMachine.scans._proof_1](RankPartialSwapMachine.definitions.md#def-6b5bf4fd0d06509a)
- [CodedSorting.ScanProgram.totalConstant](../../Shared/Programs/ScanProgramLift.definitions.md#def-e72f845372e79c59)
- [CodedSorting.CommonRankEdgeScan.code](../../Circuit/NetworkModel/Framework/RankEdgeSum.definitions.md#def-d0422395ca203120)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.destination](../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonRankEdgeScan.length_le](../../Circuit/NetworkModel/Framework/RankEdgeSum.definitions.md#def-6470ee476cc486c1)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-a9dff0a118567cd4"></a>
## `CodedSorting.Construction.PartialSwapMachine.surround`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L67)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V source buffer limit : ℕ} →
    Fin q.inventory.readers →
      (before after : List (CodedSorting.ScanProgram.Pass V)) →
        CodedSorting.Construction.PartialSwapMachine.ScanAllocation q V source buffer limit →
          {π : Equiv.Perm (Fin V)} →
            CodedSorting.CommonFinitePermutation.Program q V source buffer limit π →
              CodedSorting.CommonFinitePermutation.Program q V source buffer limit
                ((Equiv.symm (CodedSorting.ScanProgram.destination after)).trans
                  (Equiv.trans π (Equiv.symm (CodedSorting.ScanProgram.destination before))))
```

**定义**

```lean
fun q {V source buffer limit} reader before after a {π} child =>
  ((CodedSorting.Construction.PartialSwapMachine.scans q reader before a).append child).append
    (CodedSorting.Construction.PartialSwapMachine.scans q reader after a)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.append](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-91ea532bb04faf9e)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.destination](../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)
- [CodedSorting.Construction.PartialSwapMachine.scans](RankPartialSwapMachine.definitions.md#def-871961d0079ec64f)

**基础库名称**

`Equiv.trans`, `List`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`

<a id="def-a9a3b497a5aa5184"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.relabel`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L169)

**类型**

```lean
{V source buffer limit : ℕ} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {π ρ : Equiv.Perm (Fin V)} →
      CodedSorting.CommonFinitePermutation.Program q V source buffer limit π →
        π = ρ → CodedSorting.CommonFinitePermutation.Program q V source buffer limit ρ
```

**定义**

```lean
fun {V source buffer limit} {q} {π ρ} p h =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapMachine.relabel._proof_3](RankPartialSwapMachine.definitions.md#def-977a88968f4d0abc)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonFinitePermutation.Program.length_le](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-b69e1050814d5489)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.frame](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-daa50b29624216d4)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.safe](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-942392eb0d48d54c)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonFinitePermutation.Program.cost_le](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-710865af16bddbfe)

**基础库名称**

`Equiv.Perm`, `Nat`, `Fin`, `Eq`

<a id="def-719d0ad542f4ec21"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.callForward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L181)

**类型**

```lean
{J : Type u_1} →
  {V : ℕ} →
    (J → Equiv.Perm (Fin V)) → CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V → Equiv.Perm (Fin V)
```

**定义**

```lean
fun {J} {V} child b =>
  Equiv.trans (CodedSorting.ScanProgram.destination b.before)
    ((Equiv.symm (child b.childIndex)).trans (CodedSorting.ScanProgram.destination b.after))
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.after](ExchangeFramePermutation.definitions.md#def-d2265b7196bff313)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.childIndex](ExchangeFramePermutation.definitions.md#def-2365622cd8ec6ede)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.before](ExchangeFramePermutation.definitions.md#def-e3e5bf868096e1b2)
- [CodedSorting.ScanProgram.destination](../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)

**基础库名称**

`Equiv.trans`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`

<a id="def-5617bff38032fe9d"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.callProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L186)

**类型**

```lean
{J : Type u_1} →
  {V source buffer limit : ℕ} →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      Fin q.inventory.readers →
        CodedSorting.Construction.PartialSwapMachine.ScanAllocation q V source buffer limit →
          {child : J → Equiv.Perm (Fin V)} →
            ((i : J) → CodedSorting.CommonFinitePermutation.Program q V source buffer limit (child i)) →
              (b : CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V) →
                CodedSorting.CommonFinitePermutation.Program q V source buffer limit
                  (Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.callForward child b))
```

**定义**

```lean
fun {J} {V source buffer limit} {q} reader a {child} children b =>
  CodedSorting.Construction.RankPartialSwapMachine.relabel
    (CodedSorting.Construction.PartialSwapMachine.surround q reader b.before b.after a (children b.childIndex)) ⋯
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.after](ExchangeFramePermutation.definitions.md#def-d2265b7196bff313)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.Construction.RankPartialSwapMachine.callForward](RankPartialSwapMachine.definitions.md#def-719d0ad542f4ec21)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.childIndex](ExchangeFramePermutation.definitions.md#def-2365622cd8ec6ede)
- [CodedSorting.Construction.RankPartialSwapMachine.relabel](RankPartialSwapMachine.definitions.md#def-a9a3b497a5aa5184)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.before](ExchangeFramePermutation.definitions.md#def-e3e5bf868096e1b2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.ScanProgram.destination](../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)
- [CodedSorting.Construction.RankPartialSwapMachine.callProgram._proof_4](RankPartialSwapMachine.definitions.md#def-3c2c881cd51f6ea8)
- [CodedSorting.Construction.PartialSwapMachine.surround](RankPartialSwapMachine.definitions.md#def-a9dff0a118567cd4)

**基础库名称**

`Equiv.trans`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`

<a id="def-36096c30df4cc00a"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.planForward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L197)

**类型**

```lean
{J : Type u_1} →
  {V : ℕ} →
    (J → Equiv.Perm (Fin V)) →
      List (CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V) → Equiv.Perm (Fin V)
```

**定义**

```lean
fun {J} {V} child x =>
  List.brecOn x fun x f =>
    (match (motive :=
        (x : List (CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V)) →
          List.below x → Equiv.Perm (Fin V))
        x with
      | [] => fun x => Equiv.refl (Fin V)
      | b :: bs => fun x => Equiv.trans (CodedSorting.Construction.RankPartialSwapMachine.callForward child b) x.1)
      f
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.Construction.RankPartialSwapMachine.callForward](RankPartialSwapMachine.definitions.md#def-719d0ad542f4ec21)
- [CodedSorting.Construction.RankPartialSwapMachine.planForward.match_1](RankPartialSwapMachine.definitions.md#def-d6c75a6b3979c123)

**基础库名称**

`List.brecOn`, `Equiv.trans`, `List.cons`, `List`, `Unit`, `PProd`, `Equiv.Perm`, `Nat`, `List.below`, `Fin`, `Equiv.refl`, `List.nil`

<a id="def-46158260ab61771d"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.compilePlan`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L201)

**类型**

```lean
{J : Type u_1} →
  {V source buffer limit : ℕ} →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      Fin q.inventory.readers →
        CodedSorting.Construction.PartialSwapMachine.ScanAllocation q V source buffer limit →
          {child : J → Equiv.Perm (Fin V)} →
            ((i : J) → CodedSorting.CommonFinitePermutation.Program q V source buffer limit (child i)) →
              (bs : List (CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V)) →
                CodedSorting.CommonFinitePermutation.Program q V source buffer limit
                  (Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.planForward child bs))
```

**定义**

```lean
fun {J} {V source buffer limit} {q} reader a {child} children x =>
  List.brecOn x fun x f =>
    (match (motive :=
        (x : List (CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V)) →
          List.below x →
            CodedSorting.CommonFinitePermutation.Program q V source buffer limit
              (Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.planForward child x)))
        x with
      | [] => fun x => CodedSorting.CommonFinitePermutation.Program.identity q V source buffer limit
      | b :: bs => fun x =>
        CodedSorting.Construction.RankPartialSwapMachine.relabel
          ((CodedSorting.Construction.RankPartialSwapMachine.callProgram reader a children b).append x.1) ⋯)
      f
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.Construction.RankPartialSwapMachine.callForward](RankPartialSwapMachine.definitions.md#def-719d0ad542f4ec21)
- [CodedSorting.Construction.RankPartialSwapMachine.planForward](RankPartialSwapMachine.definitions.md#def-36096c30df4cc00a)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RankPartialSwapMachine.callProgram](RankPartialSwapMachine.definitions.md#def-5617bff38032fe9d)
- [CodedSorting.Construction.RankPartialSwapMachine.relabel](RankPartialSwapMachine.definitions.md#def-a9a3b497a5aa5184)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.append](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-91ea532bb04faf9e)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RankPartialSwapMachine.planForward.match_1](RankPartialSwapMachine.definitions.md#def-d6c75a6b3979c123)
- [CodedSorting.Construction.RankPartialSwapMachine.compilePlan._proof_5](RankPartialSwapMachine.definitions.md#def-10e7541655179d2c)
- [CodedSorting.CommonFinitePermutation.Program.identity](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-3c75e77e76e9a63a)

**基础库名称**

`List.brecOn`, `Equiv.trans`, `List.cons`, `List`, `Unit`, `PProd`, `Equiv.Perm`, `Nat`, `List.below`, `Equiv.symm`, `Fin`, `List.nil`

<a id="def-e92c5a7c13cbe1b5"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.selected`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L254)

**类型**

```lean
{m Q Pref G S : ℕ} → Fin m → Fin m → Equiv.Perm (Fin (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref Q G S))
```

**定义**

```lean
fun {m Q Pref G S} s t =>
  CodedSorting.CommonAddressLayout.longLayout.symm.trans
    (Equiv.trans (CodedSorting.SingleCoordinate.shortExchange s t) CodedSorting.CommonAddressLayout.longLayout)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Construction.RankPartialSwapMachine.selected._proof_6](RankPartialSwapMachine.definitions.md#def-d958669c61290a79)
- [CodedSorting.SingleCoordinate.shortExchange](../Framework/Fields/BinaryPaddingScan.definitions.md#def-945a2a92a6f3df83)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Equiv.trans`, `Fin.fintype`, `Fin.instLinearOrder`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`

<a id="def-e1105ff8f9f159e3"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.doubledDecEqRank`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L289)

**类型**

```lean
{m : ℕ} → DecidableEq (Lex (Fin m ⊕ Fin m))
```

**定义**

```lean
fun {m} => LinearOrder.toDecidableEq
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`LinearOrder.toDecidableEq`, `Lex`, `LinearOrder`, `inferInstance`, `Sum`, `Fin.instLinearOrder`, `Nat`, `Sum.Lex.linearOrder`, `Fin`, `DecidableEq`

<a id="def-de95d2f06a81e89f"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.childPermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L296)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      (F :
          CodedSorting.MatrixFactorization.SpecializedFamily
            (CodedSorting.Construction.RankPartialSwapExecution.family d)) →
        (f Pref G S : ℕ) →
          Fin P.rank → Equiv.Perm (Fin (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (F.prime ^ f) G S))
```

**定义**

```lean
fun {m} {P} d F f Pref G S i =>
  CodedSorting.Construction.RankPartialSwapMachine.selected
    (CodedSorting.Construction.RankPartialSwapExecution.supports d i).first
    (CodedSorting.Construction.RankPartialSwapExecution.supports d i).last
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.RankPartialSwapMachine.doubledDecEqRank](RankPartialSwapMachine.definitions.md#def-e1105ff8f9f159e3)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.RankPartialSwapMachine.selected](RankPartialSwapMachine.definitions.md#def-e92c5a7c13cbe1b5)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `Fin.fintype`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Fin`, `Rat.commRing`

<a id="def-f89970b98abe15ab"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.forward`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L300)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      (F :
          CodedSorting.MatrixFactorization.SpecializedFamily
            (CodedSorting.Construction.RankPartialSwapExecution.family d)) →
        (f Pref G S : ℕ) →
          0 < G → 0 < S → Equiv.Perm (Fin (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (F.prime ^ f) G S))
```

**定义**

```lean
fun {m} {P} d F f Pref G S hG hS =>
  CodedSorting.Construction.RankPartialSwapMachine.planForward
    (CodedSorting.Construction.RankPartialSwapMachine.childPermutation d F f Pref G S)
    (CodedSorting.Construction.RankPartialSwapExecution.plan d F f Pref G S hG hS)
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.RankPartialSwapMachine.planForward](RankPartialSwapMachine.definitions.md#def-36096c30df4cc00a)
- [CodedSorting.Construction.RankPartialSwapMachine.doubledDecEqRank](RankPartialSwapMachine.definitions.md#def-e1105ff8f9f159e3)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.RankPartialSwapExecution.plan](ExchangeFramePermutation.definitions.md#def-1c2051f11bfc2726)
- [CodedSorting.Construction.RankPartialSwapMachine.childPermutation](RankPartialSwapMachine.definitions.md#def-de95d2f06a81e89f)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.fintype`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Rat.commRing`

<a id="def-7e4835a99fc87d6c"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankPartialSwapMachine.lean#L304)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      (F :
          CodedSorting.MatrixFactorization.SpecializedFamily
            (CodedSorting.Construction.RankPartialSwapExecution.family d)) →
        (f Pref G S : ℕ) →
          (hG : 0 < G) →
            (hS : 0 < S) →
              (q : CodedSorting.CommonSortingNormalization.Configuration) →
                {source buffer limit : ℕ} →
                  Fin q.inventory.readers →
                    CodedSorting.Construction.PartialSwapMachine.ScanAllocation q
                        (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (F.prime ^ f) G S) source buffer limit →
                      ((i : Fin P.rank) →
                          CodedSorting.CommonFinitePermutation.Program q
                            (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (F.prime ^ f) G S) source buffer limit
                            (CodedSorting.Construction.RankPartialSwapMachine.childPermutation d F f Pref G S i)) →
                        CodedSorting.CommonFinitePermutation.Program q
                          (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (F.prime ^ f) G S) source buffer limit
                          (Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.forward d F f Pref G S hG hS))
```

**定义**

```lean
fun {m} {P} d F f Pref G S hG hS q {source buffer limit} reader a children =>
  CodedSorting.Construction.RankPartialSwapMachine.compilePlan reader a children
    (CodedSorting.Construction.RankPartialSwapExecution.plan d F f Pref G S hG hS)
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../../Circuit/Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.RankPartialSwapMachine.doubledDecEqRank](RankPartialSwapMachine.definitions.md#def-e1105ff8f9f159e3)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RankPartialSwapMachine.forward](RankPartialSwapMachine.definitions.md#def-f89970b98abe15ab)
- [CodedSorting.Construction.RankPartialSwapMachine.compilePlan](RankPartialSwapMachine.definitions.md#def-46158260ab61771d)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RankPartialSwapExecution.plan](ExchangeFramePermutation.definitions.md#def-1c2051f11bfc2726)
- [CodedSorting.Construction.RankPartialSwapMachine.childPermutation](RankPartialSwapMachine.definitions.md#def-de95d2f06a81e89f)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../../Circuit/Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Rat.commRing`

<a id="def-6b5bf4fd0d06509a"></a>
## `CodedSorting.Construction.PartialSwapMachine.scans._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankPartialSwapMachine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V source buffer limit : ℕ}
  (reader : Fin q.inventory.readers) (ps : List (CodedSorting.ScanProgram.Pass V)),
  CodedSorting.Construction.PartialSwapMachine.ScanAllocation q V source buffer limit →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin V),
      CodedSorting.CommonPermutationPairs.readBit q
          (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.CommonRankEdgeScan.code q reader ps source buffer) s).1.disk
          source ↑y =
        CodedSorting.CommonPermutationPairs.readBit q s.disk source
          ↑((Equiv.symm (CodedSorting.ScanProgram.destination ps)) y)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.CommonRankEdgeScan.code](../../Circuit/NetworkModel/Framework/RankEdgeSum.definitions.md#def-d0422395ca203120)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ScanProgram.destination](../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `Fin.val`, `Prod.fst`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-5ff1d6fb7f761cf2"></a>
## `CodedSorting.Construction.PartialSwapMachine.scans._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankPartialSwapMachine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V source buffer limit : ℕ}
  (reader : Fin q.inventory.readers) (ps : List (CodedSorting.ScanProgram.Pass V)),
  CodedSorting.Construction.PartialSwapMachine.ScanAllocation q V source buffer limit →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonPermutationPairs.count q V ≤ ↑x →
        ↑x < buffer ∨ limit ≤ ↑x →
          (CodedSorting.CommonStaticSchedule.executeRaw q
                    (CodedSorting.CommonRankEdgeScan.code q reader ps source buffer) s).1.disk
              x =
            s.disk x
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRankEdgeScan.code](../../Circuit/NetworkModel/Framework/RankEdgeSum.definitions.md#def-d0422395ca203120)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ScanProgram.Pass](../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-3c2c881cd51f6ea8"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.callProgram._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankPartialSwapMachine.lean)

**类型**

```lean
∀ {J : Type u_1} {V : ℕ} {child : J → Equiv.Perm (Fin V)}
  (b : CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V),
  (Equiv.symm (CodedSorting.ScanProgram.destination b.after)).trans
      (Equiv.trans (child b.childIndex) (Equiv.symm (CodedSorting.ScanProgram.destination b.before))) =
    Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.callForward child b)
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.after](ExchangeFramePermutation.definitions.md#def-d2265b7196bff313)
- [CodedSorting.Construction.RankPartialSwapMachine.callForward](RankPartialSwapMachine.definitions.md#def-719d0ad542f4ec21)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.childIndex](ExchangeFramePermutation.definitions.md#def-2365622cd8ec6ede)
- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock.before](ExchangeFramePermutation.definitions.md#def-e3e5bf868096e1b2)
- [CodedSorting.ScanProgram.destination](../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)

**基础库名称**

`Equiv.trans`, `Equiv`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `Eq`

<a id="def-10e7541655179d2c"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.compilePlan._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankPartialSwapMachine.lean)

**类型**

```lean
∀ {J : Type u_1} {V : ℕ} {child : J → Equiv.Perm (Fin V)}
  (b : CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V)
  (bs : List (CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V)),
  (Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.planForward child bs)).trans
      (Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.callForward child b)) =
    Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.planForward child (b :: bs))
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)
- [CodedSorting.Construction.RankPartialSwapMachine.callForward](RankPartialSwapMachine.definitions.md#def-719d0ad542f4ec21)
- [CodedSorting.Construction.RankPartialSwapMachine.planForward](RankPartialSwapMachine.definitions.md#def-36096c30df4cc00a)

**基础库名称**

`Equiv.trans`, `Equiv`, `List.cons`, `List`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `Eq`

<a id="def-d6c75a6b3979c123"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.planForward.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](RankPartialSwapMachine.lean)

**类型**

```lean
{J : Type u_1} →
  {V : ℕ} →
    (motive : List (CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V) → Sort u_2) →
      (x : List (CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V)) →
        (Unit → motive []) →
          ((b : CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V) →
              (bs : List (CodedSorting.Construction.RankPartialSwapExecution.CallBlock J V)) → motive (b :: bs)) →
            motive x
```

**定义**

```lean
fun {J} {V} motive x h_1 h_2 => List.casesOn x (h_1 ()) fun head tail => h_2 head tail
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.CallBlock](ExchangeFramePermutation.definitions.md#def-90b3744c8186dcc8)

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `Nat`, `List.casesOn`, `List.nil`

<a id="def-977a88968f4d0abc"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.relabel._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankPartialSwapMachine.lean)

**类型**

```lean
∀ {V source buffer limit : ℕ} {q : CodedSorting.CommonSortingNormalization.Configuration} {π ρ : Equiv.Perm (Fin V)}
  (p : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π),
  π = ρ →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin V),
      CodedSorting.CommonPermutationPairs.readBit q
          (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk source ↑y =
        CodedSorting.CommonPermutationPairs.readBit q s.disk source ↑(ρ y)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.val`, `Prod.fst`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-d958669c61290a79"></a>
## `CodedSorting.Construction.RankPartialSwapMachine.selected._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankPartialSwapMachine.lean)

**类型**

```lean
∀ {m : ℕ}, IsWellFounded (Fin m) fun x1 x2 => x1 < x2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.instLinearOrder`, `Nat`, `LT.lt`, `Fin`, `IsWellFounded`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`
