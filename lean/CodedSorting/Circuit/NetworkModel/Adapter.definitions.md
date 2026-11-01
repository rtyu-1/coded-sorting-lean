# Adapter 的定义

[源码](Adapter.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-ca456abca444cbe3"></a>
## `CodedSorting.Construction.MachineNetworkRankEdge.doubledDecEq`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L20)

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

<a id="def-8ac0bed960918f4a"></a>
## `CodedSorting.Construction.MachineNetworkRankEdge.permutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L27)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      (F :
          CodedSorting.MatrixFactorization.SpecializedFamily
            (CodedSorting.Construction.RankPartialSwapExecution.family d)) →
        (f Pref G S : ℕ) → Equiv.Perm (Fin (CodedSorting.CommonAddressLayout.Volume (Fin m) Pref (F.prime ^ f) G S))
```

**定义**

```lean
fun {m} {P} d F f Pref G S =>
  CodedSorting.Construction.ExchangeFramePermutation.numericPerm
    (CodedSorting.Construction.PartialSwapExecution.fullFinMatrix F f none) ⋯ Pref G S
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.PartialSwapExecution.doubledDecEq](../../Interchange/Local/PartialSwapExecution.definitions.md#def-77d37a75a4e2b6fe)
- [CodedSorting.Construction.RankPartialSwapExecution.finite_target_square](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-bbc9505cf7bd851f)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.PartialSwapExecution.fullFinMatrix](../../Interchange/Local/PartialSwapExecution.definitions.md#def-dc198e292b23529a)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.ExchangeFramePermutation.numericPerm](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-d5b41a60c5233f49)
- [CodedSorting.Construction.RankPartialSwapExecution.instNeZeroNatHPowPrimeFamilyIndexLexSumFin](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-8c442cf28e468aa7)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../../Interchange/Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.MachineNetworkRankEdge.doubledDecEq](Adapter.definitions.md#def-ca456abca444cbe3)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `Fin.fintype`, `Option.none`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `Bool`, `instHPow`, `Prod`, `Fin`, `Rat.commRing`

<a id="def-fd0f275f83c8e5cb"></a>
## `CodedSorting.Construction.MachineNetworkRankEdge.inverse_forward_eq`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean#L38)

**类型**

```lean
∀ {m : ℕ} {P : Matrix (Fin m) (Fin m) ℚ} (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P)
  (F : CodedSorting.MatrixFactorization.SpecializedFamily (CodedSorting.Construction.RankPartialSwapExecution.family d))
  (f Pref G S : ℕ) (hG : 0 < G) (hS : 0 < S),
  Equiv.symm (CodedSorting.Construction.RankPartialSwapMachine.forward d F f Pref G S hG hS) =
    CodedSorting.Construction.MachineNetworkRankEdge.permutation d F f Pref G S
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.RankPartialSwapMachine.doubledDecEqRank](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-e1105ff8f9f159e3)
- [CodedSorting.Construction.RankPartialSwapMachine.forward](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-f89970b98abe15ab)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.MachineNetworkRankEdge.permutation](Adapter.definitions.md#def-8ac0bed960918f4a)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../../Interchange/Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.MachineNetworkRankEdge.doubledDecEq](Adapter.definitions.md#def-ca456abca444cbe3)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Monoid.toNatPow`, `Sum`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-b472b6bb9dc11930"></a>
## `CodedSorting.Construction.MachineNetworkRankEdge.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L49)

**类型**

```lean
{m : ℕ} →
  {P : Matrix (Fin m) (Fin m) ℚ} →
    (d : CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition P) →
      (F :
          CodedSorting.MatrixFactorization.SpecializedFamily
            (CodedSorting.Construction.RankPartialSwapExecution.family d)) →
        (f Pref G S : ℕ) →
          0 < G →
            0 < S →
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
                          (CodedSorting.Construction.MachineNetworkRankEdge.permutation d F f Pref G S)
```

**定义**

```lean
fun {m} {P} d F f Pref G S hG hS q {source buffer limit} reader alloc children =>
  CodedSorting.Construction.RankPartialSwapMachine.relabel
    (CodedSorting.Construction.RankPartialSwapMachine.program d F f Pref G S hG hS q reader alloc children) ⋯
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.family](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-ca2fed603e447af0)
- [CodedSorting.Construction.MachineNetworkRankEdge.inverse_forward_eq](Adapter.definitions.md#def-fd0f275f83c8e5cb)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.Construction.RankPartialSwapMachine.program](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-7e4835a99fc87d6c)
- [CodedSorting.MatrixFactorization.SpecializedFamily](../Framework/MatrixFactorization.definitions.md#def-17e2256f378fb954)
- [CodedSorting.Construction.RankPartialSwapMachine.doubledDecEqRank](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-e1105ff8f9f159e3)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RankPartialSwapMachine.forward](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-f89970b98abe15ab)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition](../Labels/ProjectionRankDecomposition.definitions.md#def-6ea5d5b2ab62988e)
- [CodedSorting.Construction.MachineNetworkRankEdge.permutation](Adapter.definitions.md#def-8ac0bed960918f4a)
- [CodedSorting.Construction.RankPartialSwapMachine.relabel](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-a9a3b497a5aa5184)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RankPartialSwapMachine.childPermutation](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-de95d2f06a81e89f)
- [CodedSorting.Construction.RankPartialSwapExecution.FamilyIndex](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-bf27693c91d0e533)
- [CodedSorting.MatrixFactorization.SpecializedFamily.prime](../Framework/MatrixFactorization.definitions.md#def-5af30279750b8d0f)
- [CodedSorting.CommonAddressLayout.Volume](../../Interchange/Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.MachineNetworkRankEdge.doubledDecEq](Adapter.definitions.md#def-ca456abca444cbe3)

**基础库名称**

`Lex.fintype`, `instFintypeSum`, `Matrix`, `Lex`, `Nat.instMonoid`, `Rat`, `Matrix.rank`, `Monoid.toNatPow`, `Sum`, `instOfNatNat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Rat.commRing`

<a id="def-b4406b1e1be178ef"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.nodes`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L104)

**类型**

```lean
{Reg : Type u_1} → [inst : DecidableEq Reg] → {inputs : ℕ} → List (CodedSorting.CircuitProgram.XorGate Reg) → ℕ
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {inputs} p => (p.length + 1) * inputs
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `List.length`, `instHMul`, `DecidableEq`

<a id="def-eaf4cc872e220049"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L106)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    {inputs : ℕ} →
      (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
        Reg ≃ Fin inputs →
          CodedSorting.ProgramNetwork.Wire Reg p.length ≃ Fin (CodedSorting.Construction.MachineNetworkAdapter.nodes p)
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {inputs} p enumeration =>
  ((Equiv.refl (Fin (p.length + 1))).prodCongr enumeration).trans finProdFinEquiv
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Equiv.trans`, `Equiv`, `instOfNatNat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `finProdFinEquiv`, `instAddNat`, `Prod`, `Equiv.prodCongr`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `List.length`, `DecidableEq`

<a id="def-34d3f11a4129bcb9"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.File`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L118)

**类型**

```lean
{Reg : Type u_1} → [inst : DecidableEq Reg] → List (CodedSorting.CircuitProgram.XorGate Reg) → Type u_1
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] p => Reg ⊕ CodedSorting.ProgramNetwork.Wire Reg p.length
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Sum`, `List`, `List.length`, `DecidableEq`

<a id="def-d6a04ffb1d71a88b"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.fileEnumeration`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L120)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    {inputs : ℕ} →
      (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
        Reg ≃ Fin inputs →
          CodedSorting.Construction.MachineNetworkAdapter.File p ≃
            Fin (inputs + CodedSorting.Construction.MachineNetworkAdapter.nodes p)
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {inputs} p enumeration =>
  (enumeration.sumCongr (CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration p enumeration)).trans
    finSumFinEquiv
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetworkAdapter.File](Adapter.definitions.md#def-34d3f11a4129bcb9)
- [CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration](Adapter.definitions.md#def-eaf4cc872e220049)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Equiv.trans`, `Sum`, `Equiv`, `List`, `instHAdd`, `Equiv.sumCongr`, `HAdd.hAdd`, `Nat`, `finSumFinEquiv`, `instAddNat`, `Fin`, `List.length`, `DecidableEq`

<a id="def-8e256bb8c2f07b94"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.inputIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L123)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    {inputs : ℕ} →
      (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
        Reg ≃ Fin inputs → Reg → Fin (inputs + CodedSorting.Construction.MachineNetworkAdapter.nodes p)
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {inputs} p enumeration r =>
  (CodedSorting.Construction.MachineNetworkAdapter.fileEnumeration p enumeration) (Sum.inl r)
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkAdapter.fileEnumeration](Adapter.definitions.md#def-d6a04ffb1d71a88b)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetworkAdapter.File](Adapter.definitions.md#def-34d3f11a4129bcb9)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Sum.inl`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `List.length`, `DFunLike.coe`, `DecidableEq`

<a id="def-0919e2a552e2d7f8"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.edgeIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L126)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    {inputs : ℕ} →
      (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
        Reg ≃ Fin inputs →
          CodedSorting.ProgramNetwork.Wire Reg p.length →
            Fin (inputs + CodedSorting.Construction.MachineNetworkAdapter.nodes p)
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {inputs} p enumeration e =>
  (CodedSorting.Construction.MachineNetworkAdapter.fileEnumeration p enumeration) (Sum.inr e)
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkAdapter.fileEnumeration](Adapter.definitions.md#def-d6a04ffb1d71a88b)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetworkAdapter.File](Adapter.definitions.md#def-34d3f11a4129bcb9)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `List`, `instHAdd`, `HAdd.hAdd`, `Sum.inr`, `Nat`, `instAddNat`, `Fin`, `List.length`, `DFunLike.coe`, `DecidableEq`

<a id="def-887be63d77fce07e"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.portIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L135)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    {inputs : ℕ} →
      (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
        Reg ≃ Fin inputs →
          {v : CodedSorting.ProgramNetwork.Vertex Reg p.length} →
            CodedSorting.ProgramNetwork.InputPort p v →
              Fin (inputs + CodedSorting.Construction.MachineNetworkAdapter.nodes p)
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {inputs} p enumeration {v} port =>
  match port with
  | Sum.inl r => CodedSorting.Construction.MachineNetworkAdapter.inputIndex p enumeration ↑r
  | Sum.inr e => CodedSorting.Construction.MachineNetworkAdapter.edgeIndex p enumeration ↑e
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkAdapter.portIndex.match_1](Adapter.definitions.md#def-c82e22c585f76222)
- [CodedSorting.ProgramNetwork.InputPort](Framework/ProgramNetwork.definitions.md#def-c0edc85888c37e6c)
- [CodedSorting.ProgramNetwork.wireHead](Framework/ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.Construction.MachineNetworkAdapter.edgeIndex](Adapter.definitions.md#def-0919e2a552e2d7f8)
- [CodedSorting.ProgramNetwork.Vertex.source](Framework/ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkAdapter.inputIndex](Adapter.definitions.md#def-8e256bb8c2f07b94)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Equiv`, `Subtype`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `Subtype.val`, `Eq`, `List.length`, `DecidableEq`

<a id="def-31d64841870f9a04"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.edgePorts`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L141)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      (e : CodedSorting.ProgramNetwork.Wire Reg p.length) →
        List (CodedSorting.ProgramNetwork.InputPort p (CodedSorting.ProgramNetwork.wireTail p e))
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] p e =>
  CodedSorting.CommonNetworkInputs.inputList p (CodedSorting.ProgramNetwork.wireTail p e) ⟨e, ⋯⟩
```

**继续展开**

- [CodedSorting.ProgramNetwork.InputPort](Framework/ProgramNetwork.definitions.md#def-c0edc85888c37e6c)
- [CodedSorting.ProgramNetwork.wireTail](Framework/ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.CommonNetworkInputs.inputList](Framework/NetworkInputs.definitions.md#def-8e56605cfa6734ed)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetworkAdapter.edgePorts._proof_1](Adapter.definitions.md#def-a2d97861d327f30b)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Subtype.mk`, `List`, `Eq`, `List.length`, `DecidableEq`

<a id="def-bb5610488f2fe4b8"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.ports`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L144)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    {inputs : ℕ} →
      (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
        Reg ≃ Fin inputs →
          CodedSorting.ProgramNetwork.Wire Reg p.length →
            List (Fin (inputs + CodedSorting.Construction.MachineNetworkAdapter.nodes p))
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {inputs} p enumeration e =>
  List.map (CodedSorting.Construction.MachineNetworkAdapter.portIndex p enumeration)
    (CodedSorting.Construction.MachineNetworkAdapter.edgePorts p e)
```

**继续展开**

- [CodedSorting.ProgramNetwork.InputPort](Framework/ProgramNetwork.definitions.md#def-c0edc85888c37e6c)
- [CodedSorting.ProgramNetwork.wireTail](Framework/ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetworkAdapter.portIndex](Adapter.definitions.md#def-887be63d77fce07e)
- [CodedSorting.Construction.MachineNetworkAdapter.edgePorts](Adapter.definitions.md#def-31d64841870f9a04)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`List.map`, `Equiv`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `List.length`, `DecidableEq`

<a id="def-b610aff71dd9d6d3"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.edgePermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L169)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    {V : ℕ} →
      (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
        (CodedSorting.ProgramNetwork.Vertex Reg p.length → Equiv.Perm (Fin V)) →
          CodedSorting.ProgramNetwork.Wire Reg p.length → Equiv.Perm (Fin V)
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {V} p frame e =>
  (Equiv.symm (frame (CodedSorting.ProgramNetwork.wireHead p e))).trans
    (frame (CodedSorting.ProgramNetwork.wireTail p e))
```

**继续展开**

- [CodedSorting.ProgramNetwork.wireHead](Framework/ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.wireTail](Framework/ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Equiv.trans`, `List`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `List.length`, `DecidableEq`

<a id="def-144522652fb8afb5"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.FileVolume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L252)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun f Pref G S =>
  CodedSorting.CommonAddressLayout.Volume (Fin 512) Pref (CodedSorting.Construction.ExchangeSpecialization.radix ^ f) G
    S
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonAddressLayout.Volume](../../Interchange/Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-9bc4fe26a115c086"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.childPermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L254)

**类型**

```lean
(f Pref G S : ℕ) →
  (e : CodedSorting.Construction.OneLevelChildren.Edge) →
    Fin (CodedSorting.Construction.OneLevelChildren.edgeRank e) →
      Equiv.Perm (Fin (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S))
```

**定义**

```lean
fun f Pref G S e i =>
  CodedSorting.Construction.RankPartialSwapMachine.childPermutation
    (CodedSorting.Construction.ExchangeSpecialization.decomposition e)
    (CodedSorting.Construction.ExchangeSpecialization.edgeFamily e) f Pref G S
    ((CodedSorting.Construction.ExchangeSpecialization.childIndex e).symm i)
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.childIndex](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-c207797430c73a26)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.edgeFamily](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-2580b898498e1f35)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](../../Interchange/OneLevel/Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.Construction.RankPartialSwapMachine.childPermutation](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-de95d2f06a81e89f)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`Equiv.instFunLike`, `Rat`, `Matrix.rank`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `Rat.commRing`

<a id="def-f45fd6a8fe4a6500"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.Children`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L259)

**类型**

```lean
ℕ →
  ℕ →
    ℕ →
      ℕ →
        CodedSorting.CommonSortingNormalization.Configuration →
          CodedSorting.Construction.OneLevelChildren.Edge → ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun f Pref G S q e source buffer limit =>
  (i : Fin (CodedSorting.Construction.OneLevelChildren.edgeRank e)) →
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S) source buffer limit
      (CodedSorting.Construction.MachineNetworkActualEdges.childPermutation f Pref G S e i)
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](../../Interchange/OneLevel/Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.MachineNetworkActualEdges.childPermutation](Adapter.definitions.md#def-9bc4fe26a115c086)

**基础库名称**

`Nat`, `Fin`

<a id="def-989e10d395af784b"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.rankChildren`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L269)

**类型**

```lean
(f Pref G S : ℕ) →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    (e : CodedSorting.Construction.OneLevelChildren.Edge) →
      {source buffer limit : ℕ} →
        CodedSorting.Construction.MachineNetworkActualEdges.Children f Pref G S q e source buffer limit →
          (i : Fin (Matrix.rank (CodedSorting.Construction.ExchangeSpecialization.edgeProjection e))) →
            CodedSorting.CommonFinitePermutation.Program q
              (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S) source buffer limit
              (CodedSorting.Construction.RankPartialSwapMachine.childPermutation
                (CodedSorting.Construction.ExchangeSpecialization.decomposition e)
                (CodedSorting.Construction.ExchangeSpecialization.edgeFamily e) f Pref G S i)
```

**定义**

```lean
fun f Pref G S q e {source buffer limit} children i =>
  CodedSorting.Construction.RankPartialSwapMachine.relabel
    (children ((CodedSorting.Construction.ExchangeSpecialization.childIndex e) i)) ⋯
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.childIndex](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-c207797430c73a26)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetworkActualEdges.rankChildren._proof_2](Adapter.definitions.md#def-d73e4403ed8bec52)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.MachineNetworkActualEdges.Children](Adapter.definitions.md#def-f45fd6a8fe4a6500)
- [CodedSorting.Construction.ExchangeSpecialization.edgeFamily](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-2580b898498e1f35)
- [CodedSorting.Construction.RankPartialSwapMachine.relabel](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-a9a3b497a5aa5184)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](../../Interchange/OneLevel/Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.RankPartialSwapMachine.childPermutation](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-de95d2f06a81e89f)
- [CodedSorting.Construction.MachineNetworkActualEdges.childPermutation](Adapter.definitions.md#def-9bc4fe26a115c086)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`Equiv.instFunLike`, `Rat`, `Matrix.rank`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `Nat`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `Rat.commRing`

<a id="def-c49d89ca2a9b6042"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L275)

**类型**

```lean
(f Pref G S : ℕ) →
  0 < G →
    0 < S →
      (q : CodedSorting.CommonSortingNormalization.Configuration) →
        (e : CodedSorting.Construction.OneLevelChildren.Edge) →
          {source buffer limit : ℕ} →
            Fin q.inventory.readers →
              CodedSorting.Construction.PartialSwapMachine.ScanAllocation q
                  (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S) source buffer limit →
                CodedSorting.Construction.MachineNetworkActualEdges.Children f Pref G S q e source buffer limit →
                  CodedSorting.CommonFinitePermutation.Program q
                    (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S) source buffer limit
                    (CodedSorting.Construction.ExchangeSpecialization.edgePermutation f Pref G S e)
```

**定义**

```lean
fun f Pref G S hG hS q e {source buffer limit} reader alloc children =>
  CodedSorting.Construction.RankPartialSwapMachine.relabel
    (CodedSorting.Construction.MachineNetworkRankEdge.program
      (CodedSorting.Construction.ExchangeSpecialization.decomposition e)
      (CodedSorting.Construction.ExchangeSpecialization.edgeFamily e) f Pref G S hG hS q reader alloc
      (CodedSorting.Construction.MachineNetworkActualEdges.rankChildren f Pref G S q e children))
    ⋯
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkRankEdge.program](Adapter.definitions.md#def-b472b6bb9dc11930)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.MachineNetworkActualEdges.program._proof_3](Adapter.definitions.md#def-c1051dac618372f1)
- [CodedSorting.Construction.MachineNetworkRankEdge.permutation](Adapter.definitions.md#def-8ac0bed960918f4a)
- [CodedSorting.Construction.MachineNetworkActualEdges.Children](Adapter.definitions.md#def-f45fd6a8fe4a6500)
- [CodedSorting.Construction.ExchangeSpecialization.edgeFamily](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-2580b898498e1f35)
- [CodedSorting.Construction.MachineNetworkActualEdges.rankChildren](Adapter.definitions.md#def-989e10d395af784b)
- [CodedSorting.Construction.RankPartialSwapMachine.relabel](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-a9a3b497a5aa5184)
- [CodedSorting.Construction.ExchangeSpecialization.edgePermutation](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-f505d6f449c2b2be)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-aaee6071befa28bc"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.coefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L281)

**类型**

```lean
CodedSorting.Construction.OneLevelChildren.Edge → ℕ
```

**定义**

```lean
fun e =>
  3 *
    (CodedSorting.Construction.RankPartialSwapExecution.fixedConstant
        (CodedSorting.Construction.ExchangeSpecialization.decomposition e) +
      16 * CodedSorting.Construction.OneLevelChildren.edgeRank e)
```

**继续展开**

- [CodedSorting.Construction.RankPartialSwapExecution.fixedConstant](../../Interchange/Local/ExchangeFramePermutation.definitions.md#def-13d6b020c5190aa2)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](../../Interchange/OneLevel/Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-08e31b40f9286f75"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.originalEnumeration`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L326)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.IndependentStream ≃ Fin CodedSorting.Construction.streamCount
```

**定义**

```lean
(Fintype.equivFin CodedSorting.Construction.ThreeCopySchedule.IndependentStream).trans
  (finCongr CodedSorting.Construction.ThreeCopySchedule.independent_stream_count)
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.independent_stream_count](../Composition/TensorLiftProgram.definitions.md#def-2eaf92ac720f7636)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](../Composition/TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](../Composition/TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.streamCount](../Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](../Composition/TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](../Composition/TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`instFintypeSum`, `Equiv.trans`, `finCongr`, `Fintype.card`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `Fintype.equivFin`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-6f54c03d4c89a4f5"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.temporaryEnumeration`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L331)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.TemporaryStream ≃ Fin 998001
```

**定义**

```lean
(Fintype.equivFin CodedSorting.Construction.TensorLiftProgram.TemporaryStream).trans
  (finCongr CodedSorting.Construction.TensorFrameNetwork.temporary_stream_count)
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](../Composition/TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](../Composition/TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorFrameNetwork.temporary_stream_count](../Composition/TensorFrameNetwork.definitions.md#def-9d1847a336b60ba6)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorLiftProgram.instFintypeRound](../Composition/TensorLiftProgram.definitions.md#def-9d47e1f47feb55c7)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](../Composition/TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Equiv.trans`, `finCongr`, `Fintype.card`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `Fintype.equivFin`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-61b11b4c2aee2759"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.physicalInputs`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L336)

**类型**

```lean
ℕ
```

**定义**

```lean
CodedSorting.Construction.streamCount + 998001
```

**继续展开**

- [CodedSorting.Construction.streamCount](../Parameters/Counts.definitions.md#def-8dbf3b9bec362266)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-0f17f321c22e23fa"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L338)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.GlobalReg ≃
  Fin CodedSorting.Construction.MachineNetworkAdapter.physicalInputs
```

**定义**

```lean
(CodedSorting.Construction.MachineNetworkAdapter.originalEnumeration.sumCongr
      CodedSorting.Construction.MachineNetworkAdapter.temporaryEnumeration).trans
  finSumFinEquiv
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkAdapter.temporaryEnumeration](Adapter.definitions.md#def-6f54c03d4c89a4f5)
- [CodedSorting.Construction.streamCount](../Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.originalEnumeration](Adapter.definitions.md#def-08e31b40f9286f75)

**基础库名称**

`Equiv.trans`, `Sum`, `Equiv`, `instOfNatNat`, `Equiv.sumCongr`, `Nat`, `finSumFinEquiv`, `OfNat.ofNat`, `Fin`

<a id="def-89ed902f7aacf974"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.inputSlot`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L348)

**类型**

```lean
Fin CodedSorting.Construction.streamCount →
  Fin
    (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
      CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)
```

**定义**

```lean
fun c =>
  CodedSorting.Construction.MachineNetworkAdapter.inputIndex CodedSorting.Construction.TensorFrameNetwork.program
    CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration
    (Sum.inl (CodedSorting.Construction.MachineNetworkAdapter.originalEnumeration.symm c))
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.streamCount](../Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkAdapter.inputIndex](Adapter.definitions.md#def-8e256bb8c2f07b94)
- [CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration](Adapter.definitions.md#def-0f17f321c22e23fa)
- [CodedSorting.Construction.MachineNetworkAdapter.originalEnumeration](Adapter.definitions.md#def-08e31b40f9286f75)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Sum.inl`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Equiv.symm`, `Fin`, `DFunLike.coe`

<a id="def-a4493f235434aee1"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.outputSlot`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L353)

**类型**

```lean
Fin CodedSorting.Construction.streamCount →
  Fin
    (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
      CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)
```

**定义**

```lean
fun c =>
  CodedSorting.Construction.MachineNetworkAdapter.edgeIndex CodedSorting.Construction.TensorFrameNetwork.program
    CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration
    (CodedSorting.ProgramNetwork.sinkWire CodedSorting.Construction.TensorFrameNetwork.program
      (Sum.inl
        (CodedSorting.Construction.TensorThreeRound.originalSwap
          (CodedSorting.Construction.MachineNetworkAdapter.originalEnumeration.symm c))))
```

**继续展开**

- [CodedSorting.Construction.TensorThreeRound.originalSwap](../Composition/TensorThreeRound.definitions.md#def-8b3c0826e8b41aa5)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.MachineNetworkAdapter.edgeIndex](Adapter.definitions.md#def-0919e2a552e2d7f8)
- [CodedSorting.Construction.streamCount](../Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.ProgramNetwork.sinkWire](Framework/ProgramNetwork.definitions.md#def-8484131e8c07cf94)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration](Adapter.definitions.md#def-0f17f321c22e23fa)
- [CodedSorting.Construction.MachineNetworkAdapter.originalEnumeration](Adapter.definitions.md#def-08e31b40f9286f75)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Sum.inl`, `instHAdd`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `Equiv.symm`, `Fin`, `DFunLike.coe`

<a id="def-8ad9ceac26312a3c"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.circuit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L409)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    {inputs V : ℕ} →
      (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
        Reg ≃ Fin inputs →
          (CodedSorting.ProgramNetwork.Vertex Reg p.length → Equiv.Perm (Fin V)) →
            CodedSorting.Construction.MachineNetwork.Circuit inputs
              (CodedSorting.Construction.MachineNetworkAdapter.nodes p) V
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] {inputs V} p enumeration frame =>
  {
    ports := fun e =>
      CodedSorting.Construction.MachineNetworkAdapter.ports p enumeration
        ((CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration p enumeration).symm e),
    prior := ⋯,
    permutation := fun e =>
      CodedSorting.Construction.MachineNetworkAdapter.edgePermutation p frame
        ((CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration p enumeration).symm e) }
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkAdapter.edgePermutation](Adapter.definitions.md#def-b610aff71dd9d6d3)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetwork.Circuit.mk](Definitions.definitions.md#def-51e199272a973e37)
- [CodedSorting.Construction.MachineNetworkAdapter.circuit._proof_4](Adapter.definitions.md#def-eaba4ff2894eea49)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.Construction.MachineNetworkAdapter.ports](Adapter.definitions.md#def-bb5610488f2fe4b8)
- [CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration](Adapter.definitions.md#def-eaf4cc872e220049)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `List`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `List.length`, `DFunLike.coe`, `DecidableEq`

<a id="def-3645220e02de1fc0"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.actualCircuit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L501)

**类型**

```lean
{V : ℕ} →
  (CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
        CodedSorting.Construction.TensorFrameNetwork.program.length →
      Equiv.Perm (Fin V)) →
    CodedSorting.Construction.MachineNetwork.Circuit CodedSorting.Construction.MachineNetworkAdapter.physicalInputs
      (CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program) V
```

**定义**

```lean
fun {V} location =>
  CodedSorting.Construction.MachineNetworkAdapter.circuit CodedSorting.Construction.TensorFrameNetwork.program
    CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration location
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.circuit](Adapter.definitions.md#def-8ad9ceac26312a3c)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration](Adapter.definitions.md#def-0f17f321c22e23fa)
- [CodedSorting.ProgramNetwork.Vertex](Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Equiv.Perm`, `Nat`, `Fin`, `List.length`

<a id="def-f0b5bd767df80c65"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.NodeCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L557)

**类型**

```lean
ℕ
```

**定义**

```lean
CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`Nat`

<a id="def-0fcc35f8c0cdcb8a"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L560)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun q f Pref G S =>
  CodedSorting.Construction.MachineNetwork.Layout q CodedSorting.Construction.MachineNetworkAdapter.physicalInputs
    CodedSorting.Construction.MachineNetworkActualEdges.NodeCount
    (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S)
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)

**基础库名称**

`Nat`

<a id="def-28c9d8e4a51dc5b0"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.actualEdge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L564)

**类型**

```lean
Fin CodedSorting.Construction.MachineNetworkActualEdges.NodeCount → CodedSorting.Construction.OneLevelChildren.Edge
```

**定义**

```lean
fun i =>
  (CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration CodedSorting.Construction.TensorFrameNetwork.program
        CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration).symm
    i
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration](Adapter.definitions.md#def-eaf4cc872e220049)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)
- [CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration](Adapter.definitions.md#def-0f17f321c22e23fa)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Equiv.symm`, `Fin`, `List.length`, `DFunLike.coe`

<a id="def-86cc50413ebfb416"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.edgeFile`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L568)

**类型**

```lean
CodedSorting.Construction.OneLevelChildren.Edge →
  Fin
    (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
      CodedSorting.Construction.MachineNetworkActualEdges.NodeCount)
```

**定义**

```lean
fun e =>
  CodedSorting.Construction.MachineNetwork.nodeFile
    ((CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration
        CodedSorting.Construction.TensorFrameNetwork.program
        CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration)
      e)
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration](Adapter.definitions.md#def-eaf4cc872e220049)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)
- [CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration](Adapter.definitions.md#def-0f17f321c22e23fa)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.Construction.MachineNetwork.nodeFile](Definitions.definitions.md#def-959c823048638e7d)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `List.length`, `DFunLike.coe`

<a id="def-fe923d3731d18bb4"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.NetworkChildren`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L573)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (f Pref G S : ℕ) → CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout q f Pref G S → Type
```

**定义**

```lean
fun q f Pref G S layout =>
  (e : CodedSorting.Construction.OneLevelChildren.Edge) →
    CodedSorting.Construction.MachineNetworkActualEdges.Children f Pref G S q e
      (CodedSorting.Construction.MachineNetwork.Layout.base layout
        (CodedSorting.Construction.MachineNetworkActualEdges.edgeFile e))
      layout.buffer layout.limit
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.buffer](Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.Construction.MachineNetworkActualEdges.edgeFile](Adapter.definitions.md#def-86cc50413ebfb416)
- [CodedSorting.Construction.MachineNetworkActualEdges.Children](Adapter.definitions.md#def-f45fd6a8fe4a6500)
- [CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout](Adapter.definitions.md#def-0fcc35f8c0cdcb8a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)

**基础库名称**

`Nat`

<a id="def-149ff657f0ccca02"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.atSource`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L577)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {V source source' buffer limit : ℕ} →
    {π : Equiv.Perm (Fin V)} →
      CodedSorting.CommonFinitePermutation.Program q V source buffer limit π →
        source = source' → CodedSorting.CommonFinitePermutation.Program q V source' buffer limit π
```

**定义**

```lean
fun {q} {V source source' buffer limit} {π} p h =>
  { instructions := p.instructions, charge := p.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.Construction.MachineNetworkActualEdges.atSource._proof_5](Adapter.definitions.md#def-ae496afe9f17bcd4)
- [CodedSorting.CommonFinitePermutation.Program.length_le](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-b69e1050814d5489)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonFinitePermutation.Program.safe](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-942392eb0d48d54c)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.MachineNetworkActualEdges.atSource._proof_6](Adapter.definitions.md#def-4a82edc307de5104)
- [CodedSorting.CommonFinitePermutation.Program.mk](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonFinitePermutation.Program.cost_le](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-710865af16bddbfe)

**基础库名称**

`Equiv.Perm`, `Nat`, `Fin`, `Eq`

<a id="def-3e03bc0f27cff454"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.edgeAllocation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L593)

**类型**

```lean
∀ {f Pref G S : ℕ} {q : CodedSorting.CommonSortingNormalization.Configuration}
  (layout : CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout q f Pref G S),
  layout.buffer +
        CodedSorting.CommonPermutationPairs.count q
          (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S) ≤
      layout.limit →
    ∀ (e : CodedSorting.Construction.OneLevelChildren.Edge),
      CodedSorting.Construction.PartialSwapMachine.ScanAllocation q
        (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S)
        (CodedSorting.Construction.MachineNetwork.Layout.base layout
          (CodedSorting.Construction.MachineNetworkActualEdges.edgeFile e))
        layout.buffer layout.limit
```

**定义**

```lean
fun {f Pref G S} {q} layout hroom e =>
  {
    source_separate :=
      LE.le.trans
        (Nat.add_le_add_left layout.count_le_stride
          (CodedSorting.Construction.MachineNetwork.Layout.base layout
            (CodedSorting.Construction.MachineNetworkActualEdges.edgeFile e)))
        (CodedSorting.Construction.MachineNetwork.Layout.base_end_le layout
          (CodedSorting.Construction.MachineNetworkActualEdges.edgeFile e)),
    buffer_fits := hroom, limit_fits := layout.fit }
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.buffer](Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.MachineNetwork.Layout.base_end_le](Definitions.definitions.md#def-78f002e22b2fbc35)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetwork.Layout.fit](Definitions.definitions.md#def-44823982454c1e08)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-e3d2391d9d44e72d)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.Construction.MachineNetwork.Layout.count_le_stride](Definitions.definitions.md#def-efabe9dbf987dfc9)
- [CodedSorting.Construction.MachineNetworkActualEdges.edgeFile](Adapter.definitions.md#def-86cc50413ebfb416)
- [CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout](Adapter.definitions.md#def-0fcc35f8c0cdcb8a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.PartialSwapMachine.ScanAllocation.mk](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-4dff7b5bc286d87a)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetwork.Layout.stride](Definitions.definitions.md#def-2516d89bed459156)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `LE.le.trans`, `Nat.add_le_add_left`

<a id="def-29921c75fb0340a9"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L604)

**类型**

```lean
(f Pref G S : ℕ) →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin q.inventory.readers →
      0 < G →
        0 < S →
          (layout : CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout q f Pref G S) →
            layout.buffer +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.Construction.MachineNetworkActualEdges.FileVolume f Pref G S) ≤
                layout.limit →
              CodedSorting.Construction.MachineNetworkActualEdges.NetworkChildren q f Pref G S layout →
                CodedSorting.Construction.MachineNetwork.Programs
                  (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit
                    (CodedSorting.Construction.ExchangeSpecialization.location f Pref G S))
                  layout
```

**定义**

```lean
fun f Pref G S q reader hG hS layout hroom children i =>
  let e := CodedSorting.Construction.MachineNetworkActualEdges.actualEdge i;
  let p := CodedSorting.Construction.MachineNetworkActualEdges.program f Pref G S hG hS q e reader ⋯ (children e);
  let_fun hi := ⋯;
  CodedSorting.Construction.RankPartialSwapMachine.relabel
    (CodedSorting.Construction.MachineNetworkActualEdges.atSource p ⋯) ⋯
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.buffer](Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms._proof_8](Adapter.definitions.md#def-b545913322479478)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.MachineNetwork.Programs](Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.MachineNetworkActualEdges.actualEdge](Adapter.definitions.md#def-28c9d8e4a51dc5b0)
- [CodedSorting.Construction.MachineNetworkActualEdges.atSource](Adapter.definitions.md#def-149ff657f0ccca02)
- [CodedSorting.Construction.MachineNetworkActualEdges.edgeFile](Adapter.definitions.md#def-86cc50413ebfb416)
- [CodedSorting.Construction.MachineNetworkActualEdges.edgeAllocation](Adapter.definitions.md#def-3e03bc0f27cff454)
- [CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout](Adapter.definitions.md#def-0fcc35f8c0cdcb8a)
- [CodedSorting.Construction.RankPartialSwapMachine.relabel](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-a9a3b497a5aa5184)
- [CodedSorting.Construction.ExchangeSpecialization.edgePermutation](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-f505d6f449c2b2be)
- [CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms._proof_7](Adapter.definitions.md#def-fc8b6ae36965afa3)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.MachineNetworkActualEdges.program](Adapter.definitions.md#def-c49d89ca2a9b6042)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms._proof_9](Adapter.definitions.md#def-855952756ab0c264)
- [CodedSorting.Construction.MachineNetwork.Circuit.permutation](Definitions.definitions.md#def-a5367bc3961a29e1)
- [CodedSorting.Construction.ExchangeSpecialization.location](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-ccfe084da8739a92)
- [CodedSorting.Construction.MachineNetworkActualEdges.NetworkChildren](Adapter.definitions.md#def-fe923d3731d18bb4)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonAddressLayout.Volume](../../Interchange/Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.MachineNetwork.nodeFile](Definitions.definitions.md#def-959c823048638e7d)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.fintype`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `letFun`

<a id="def-e3dd033ebdbb0de7"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Adapter.lean#L637)

**类型**

```lean
ℕ
```

**定义**

```lean
3 *
    ∑ i,
      ((CodedSorting.Construction.MachineNetworkAdapter.ports CodedSorting.Construction.TensorFrameNetwork.program
            CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration
            (CodedSorting.Construction.MachineNetworkActualEdges.actualEdge i)).length +
        1) +
  ∑ e, CodedSorting.Construction.MachineNetworkActualEdges.coefficient e
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkActualEdges.coefficient](Adapter.definitions.md#def-aaee6071befa28bc)
- [CodedSorting.Construction.TensorLiftProgram.Round](../Composition/TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.ThreeCopySchedule.Block](../Composition/TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](../Composition/TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.MachineNetworkActualEdges.actualEdge](Adapter.definitions.md#def-28c9d8e4a51dc5b0)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](../Composition/TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ThreeCopySchedule.Line](../Composition/TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](../Composition/TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.TensorLiftProgram.instFintypeRound](../Composition/TensorLiftProgram.definitions.md#def-9d47e1f47feb55c7)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](../Composition/TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.MachineNetworkAdapter.ports](Adapter.definitions.md#def-bb5610488f2fe4b8)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)
- [CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration](Adapter.definitions.md#def-0f17f321c22e23fa)

**基础库名称**

`instFintypeSum`, `HMul.hMul`, `Finset.univ`, `instMulNat`, `instOfNatNat`, `Fin.fintype`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Nat.instAddCommMonoid`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`, `List.length`, `Finset.sum`, `instHMul`

<a id="def-ae496afe9f17bcd4"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.atSource._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source source' buffer limit : ℕ}
  {π : Equiv.Perm (Fin V)} (p : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π),
  source = source' →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin V),
      CodedSorting.CommonPermutationPairs.readBit q
          (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk source' ↑y =
        CodedSorting.CommonPermutationPairs.readBit q s.disk source' ↑(π y)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](../../Interchange/Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.val`, `Prod.fst`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-4a82edc307de5104"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.atSource._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {V source source' buffer limit : ℕ}
  {π : Equiv.Perm (Fin V)} (p : CodedSorting.CommonFinitePermutation.Program q V source buffer limit π),
  source = source' →
    ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
      ↑a < source' ∨ source' + CodedSorting.CommonPermutationPairs.count q V ≤ ↑a →
        ↑a < buffer ∨ limit ≤ ↑a → (CodedSorting.CommonStaticSchedule.executeRaw q p.instructions s).1.disk a = s.disk a
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-fc8b6ae36965afa3"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀
  (i :
    Fin (CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)),
  CodedSorting.Construction.MachineNetwork.nodeFile
      ((CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration
          CodedSorting.Construction.TensorFrameNetwork.program
          CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration)
        ((CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration
              CodedSorting.Construction.TensorFrameNetwork.program
              CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration).symm
          i)) =
    CodedSorting.Construction.MachineNetwork.nodeFile i
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration](Adapter.definitions.md#def-eaf4cc872e220049)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)
- [CodedSorting.Construction.MachineNetworkAdapter.registerEnumeration](Adapter.definitions.md#def-0f17f321c22e23fa)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.Construction.MachineNetwork.nodeFile](Definitions.definitions.md#def-959c823048638e7d)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Equiv.symm`, `Fin`, `Eq`, `List.length`, `DFunLike.coe`

<a id="def-b545913322479478"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀ (f Pref G S : ℕ) (q : CodedSorting.CommonSortingNormalization.Configuration)
  (layout : CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout q f Pref G S)
  (i :
    Fin (CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)),
  CodedSorting.Construction.MachineNetworkActualEdges.edgeFile
        (CodedSorting.Construction.MachineNetworkActualEdges.actualEdge i) =
      CodedSorting.Construction.MachineNetwork.nodeFile i →
    CodedSorting.Construction.MachineNetwork.Layout.base layout
        (CodedSorting.Construction.MachineNetworkActualEdges.edgeFile
          (CodedSorting.Construction.MachineNetworkActualEdges.actualEdge i)) =
      CodedSorting.Construction.MachineNetwork.Layout.base layout (CodedSorting.Construction.MachineNetwork.nodeFile i)
```

**继续展开**

- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.MachineNetworkActualEdges.actualEdge](Adapter.definitions.md#def-28c9d8e4a51dc5b0)
- [CodedSorting.Construction.MachineNetworkActualEdges.edgeFile](Adapter.definitions.md#def-86cc50413ebfb416)
- [CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout](Adapter.definitions.md#def-0fcc35f8c0cdcb8a)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](Adapter.definitions.md#def-f0b5bd767df80c65)
- [CodedSorting.Construction.MachineNetwork.nodeFile](Definitions.definitions.md#def-959c823048638e7d)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `Eq`

<a id="def-855952756ab0c264"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀ (f Pref G S : ℕ)
  (i :
    Fin (CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)),
  CodedSorting.Construction.ExchangeSpecialization.edgePermutation f Pref G S
      (CodedSorting.Construction.MachineNetworkActualEdges.actualEdge i) =
    (Equiv.symm
          (CodedSorting.Construction.ExchangeSpecialization.location f Pref G S
            (CodedSorting.ProgramNetwork.wireHead CodedSorting.Construction.TensorFrameNetwork.program
              (CodedSorting.Construction.MachineNetworkActualEdges.actualEdge i)))).trans
      (CodedSorting.Construction.ExchangeSpecialization.location f Pref G S
        (CodedSorting.ProgramNetwork.wireTail CodedSorting.Construction.TensorFrameNetwork.program
          (CodedSorting.Construction.MachineNetworkActualEdges.actualEdge i)))
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.ProgramNetwork.wireHead](Framework/ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.wireTail](Framework/ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.Construction.MachineNetworkActualEdges.actualEdge](Adapter.definitions.md#def-28c9d8e4a51dc5b0)
- [CodedSorting.Construction.ExchangeSpecialization.edgePermutation](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-f505d6f449c2b2be)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.ExchangeSpecialization.location](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-ccfe084da8739a92)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonAddressLayout.Volume](../../Interchange/Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-c1051dac618372f1"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.program._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀ (f Pref G S : ℕ) (e : CodedSorting.Construction.OneLevelChildren.Edge),
  CodedSorting.Construction.MachineNetworkRankEdge.permutation
      (CodedSorting.Construction.ExchangeSpecialization.decomposition e)
      (CodedSorting.Construction.ExchangeSpecialization.edgeFamily e) f Pref G S =
    CodedSorting.Construction.MachineNetworkRankEdge.permutation
      (CodedSorting.Construction.ExchangeSpecialization.decomposition e)
      (CodedSorting.Construction.ExchangeSpecialization.edgeFamily e) f Pref G S
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.MachineNetworkRankEdge.permutation](Adapter.definitions.md#def-8ac0bed960918f4a)
- [CodedSorting.Construction.ExchangeSpecialization.edgeFamily](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-2580b898498e1f35)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`instOfNatNat`, `Equiv.Perm`, `Nat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-d73e4403ed8bec52"></a>
## `CodedSorting.Construction.MachineNetworkActualEdges.rankChildren._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀ (f Pref G S : ℕ) (e : CodedSorting.Construction.OneLevelChildren.Edge)
  (i : Fin (Matrix.rank (CodedSorting.Construction.ExchangeSpecialization.edgeProjection e))),
  CodedSorting.Construction.RankPartialSwapMachine.childPermutation
      (CodedSorting.Construction.ExchangeSpecialization.decomposition e)
      (CodedSorting.Construction.ExchangeSpecialization.edgeFamily e) f Pref G S
      ((CodedSorting.Construction.ExchangeSpecialization.childIndex e).symm
        ((CodedSorting.Construction.ExchangeSpecialization.childIndex e) i)) =
    CodedSorting.Construction.RankPartialSwapMachine.childPermutation
      (CodedSorting.Construction.ExchangeSpecialization.decomposition e)
      (CodedSorting.Construction.ExchangeSpecialization.edgeFamily e) f Pref G S i
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.childIndex](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-c207797430c73a26)
- [CodedSorting.Construction.OneLevelChildren.Edge](../../Interchange/OneLevel/Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.ExchangeSpecialization.edgeFamily](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-2580b898498e1f35)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](../../Interchange/OneLevel/Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.Construction.RankPartialSwapMachine.childPermutation](../../Interchange/Local/RankPartialSwapMachine.definitions.md#def-de95d2f06a81e89f)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](../../Interchange/Bounds/ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`Equiv.instFunLike`, `Rat`, `Matrix.rank`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `Rat.commRing`

<a id="def-eaba4ff2894eea49"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.circuit._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀ {Reg : Type u_1} [inst : DecidableEq Reg] {inputs : ℕ} (p : List (CodedSorting.CircuitProgram.XorGate Reg))
  (enumeration : Reg ≃ Fin inputs) (e : Fin (CodedSorting.Construction.MachineNetworkAdapter.nodes p)),
  ∀
    i ∈
      CodedSorting.Construction.MachineNetworkAdapter.ports p enumeration
        ((CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration p enumeration).symm e),
    ↑i < inputs + ↑e
```

**继续展开**

- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.MachineNetworkAdapter.ports](Adapter.definitions.md#def-bb5610488f2fe4b8)
- [CodedSorting.Construction.MachineNetworkAdapter.edgeEnumeration](Adapter.definitions.md#def-eaf4cc872e220049)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)

**基础库名称**

`Equiv.instFunLike`, `Membership.mem`, `Equiv`, `Fin.val`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Equiv.symm`, `Fin`, `List.length`, `DFunLike.coe`, `DecidableEq`

<a id="def-a2d97861d327f30b"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.edgePorts._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Adapter.lean)

**类型**

```lean
∀ {Reg : Type u_1} [inst : DecidableEq Reg] (p : List (CodedSorting.CircuitProgram.XorGate Reg))
  (e : CodedSorting.ProgramNetwork.Wire Reg p.length),
  CodedSorting.ProgramNetwork.wireTail p e = CodedSorting.ProgramNetwork.wireTail p e
```

**继续展开**

- [CodedSorting.ProgramNetwork.wireTail](Framework/ProgramNetwork.definitions.md#def-d6643374d872cf41)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`List`, `Eq`, `List.length`, `DecidableEq`

<a id="def-c82e22c585f76222"></a>
## `CodedSorting.Construction.MachineNetworkAdapter.portIndex.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Adapter.lean)

**类型**

```lean
{Reg : Type u_1} →
  [inst : DecidableEq Reg] →
    (p : List (CodedSorting.CircuitProgram.XorGate Reg)) →
      {v : CodedSorting.ProgramNetwork.Vertex Reg p.length} →
        (motive : CodedSorting.ProgramNetwork.InputPort p v → Sort u_2) →
          (port : CodedSorting.ProgramNetwork.InputPort p v) →
            ((r : { r // CodedSorting.ProgramNetwork.Vertex.source r = v }) → motive (Sum.inl r)) →
              ((e : { edge // CodedSorting.ProgramNetwork.wireHead p edge = v }) → motive (Sum.inr e)) → motive port
```

**定义**

```lean
fun {Reg} [DecidableEq Reg] p {v} motive port h_1 h_2 => Sum.casesOn port (fun val => h_1 val) fun val => h_2 val
```

**继续展开**

- [CodedSorting.ProgramNetwork.InputPort](Framework/ProgramNetwork.definitions.md#def-c0edc85888c37e6c)
- [CodedSorting.ProgramNetwork.wireHead](Framework/ProgramNetwork.definitions.md#def-0c7209c651d6dc49)
- [CodedSorting.ProgramNetwork.Vertex.source](Framework/ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.ProgramNetwork.Wire](Framework/ProgramNetwork.definitions.md#def-d72ef8ed1f1d7af4)
- [CodedSorting.ProgramNetwork.Vertex](Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Sum.casesOn`, `Subtype`, `Sum.inl`, `List`, `Sum.inr`, `Eq`, `List.length`, `DecidableEq`
