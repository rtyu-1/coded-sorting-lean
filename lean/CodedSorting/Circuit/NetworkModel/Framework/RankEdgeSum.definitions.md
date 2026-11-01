# RankEdgeSum 的定义

[源码](RankEdgeSum.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-b180f12f20b41d6f"></a>
## `CodedSorting.CommonRankEdgeScan.identityPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankEdgeSum.lean#L14)

**类型**

```lean
(V : ℕ) → CodedSorting.ScanProgram.Pass V
```

**定义**

```lean
fun V => CodedSorting.ScanProgram.Pass.streams 1 (Equiv.refl (Fin V)) (fun x => 0) ⋯
```

**继续展开**

- [CodedSorting.CommonRankEdgeScan.identityPass._proof_1](RankEdgeSum.definitions.md#def-36deeeaa3935d174)
- [CodedSorting.ScanProgram.Pass.streams](../../../Shared/Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTFin`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `Eq`

<a id="def-7de3136df7448aa7"></a>
## `CodedSorting.CommonRankEdgeScan.padded`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankEdgeSum.lean#L17)

**类型**

```lean
{V : ℕ} → List (CodedSorting.ScanProgram.Pass V) → List (CodedSorting.ScanProgram.Pass V)
```

**定义**

```lean
fun {V} ps => if ps.length % 2 = 0 then ps else ps ++ [CodedSorting.CommonRankEdgeScan.identityPass V]
```

**继续展开**

- [CodedSorting.CommonRankEdgeScan.identityPass](RankEdgeSum.definitions.md#def-b180f12f20b41d6f)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Nat.instMod`, `instHMod`, `instOfNatNat`, `List.cons`, `instHAppendOfAppend`, `List`, `HMod.hMod`, `Nat`, `instDecidableEqNat`, `List.instAppend`, `OfNat.ofNat`, `Eq`, `List.length`, `HAppend.hAppend`, `List.nil`, `ite`

<a id="def-d0422395ca203120"></a>
## `CodedSorting.CommonRankEdgeScan.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RankEdgeSum.lean#L64)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V : ℕ} →
    Fin q.inventory.readers →
      List (CodedSorting.ScanProgram.Pass V) → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q {V} reader ps source target =>
  CodedSorting.CommonScanProgram.code q reader (CodedSorting.CommonRankEdgeScan.padded ps) source target
```

**继续展开**

- [CodedSorting.CommonScanProgram.code](../../../Shared/Memory/ScanProgram.definitions.md#def-9aed89b5c5f3201c)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRankEdgeScan.padded](RankEdgeSum.definitions.md#def-7de3136df7448aa7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List`, `Nat`, `Fin`

<a id="def-c7d052f63c520c81"></a>
## `CodedSorting.CommonRankEdgeScan.safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankEdgeSum.lean#L68)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
  (ps : List (CodedSorting.ScanProgram.Pass V)) (source target : ℕ),
  ∀ i ∈ CodedSorting.CommonRankEdgeScan.code q reader ps source target, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRankEdgeScan.code](RankEdgeSum.definitions.md#def-d0422395ca203120)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`, `Fin`

<a id="def-6470ee476cc486c1"></a>
## `CodedSorting.CommonRankEdgeScan.length_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankEdgeSum.lean#L73)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
  (ps : List (CodedSorting.ScanProgram.Pass V)) (source target : ℕ),
  (CodedSorting.CommonRankEdgeScan.code q reader ps source target).length ≤
    3 * (CodedSorting.ScanProgram.totalConstant ps + 8) * CodedSorting.CommonPermutationPairs.count q V
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.ScanProgram.totalConstant](../../../Shared/Programs/ScanProgramLift.definitions.md#def-e72f845372e79c59)
- [CodedSorting.CommonRankEdgeScan.code](RankEdgeSum.definitions.md#def-d0422395ca203120)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonPermutationPairs.count](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`

<a id="def-f0839888d16645a0"></a>
## `CodedSorting.CommonRankEdgeScan.cost_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankEdgeSum.lean#L79)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
  (ps : List (CodedSorting.ScanProgram.Pass V)) (source target : ℕ),
  CodedSorting.CommonStaticSchedule.cost q (CodedSorting.CommonRankEdgeScan.code q reader ps source target) ≤
    3 * (CodedSorting.ScanProgram.totalConstant ps + 8) * CodedSorting.CommonPermutationPairs.count q V
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.ScanProgram.totalConstant](../../../Shared/Programs/ScanProgramLift.definitions.md#def-e72f845372e79c59)
- [CodedSorting.CommonRankEdgeScan.code](RankEdgeSum.definitions.md#def-d0422395ca203120)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonPermutationPairs.count](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-36deeeaa3935d174"></a>
## `CodedSorting.CommonRankEdgeScan.identityPass._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](RankEdgeSum.lean)

**类型**

```lean
NeZero (0 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`
