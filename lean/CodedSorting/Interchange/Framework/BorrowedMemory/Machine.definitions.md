# Machine 的定义

[源码](Machine.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-7f3b01c10733f53f"></a>
## `CodedSorting.CommonBorrowMachine.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L23)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V : ℕ} →
    Fin q.inventory.readers →
      List (CodedSorting.ScanProgram.Pass V) → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q {V} reader ps source buffer =>
  CodedSorting.CommonScanProgram.code q reader ps source buffer ++
    if CodedSorting.CommonScanProgram.finalBase ps source buffer = source then []
    else CodedSorting.CommonRecursiveExchange.copyCode q reader V buffer source
```

**继续展开**

- [CodedSorting.CommonScanProgram.code](../../../Shared/Memory/ScanProgram.definitions.md#def-9aed89b5c5f3201c)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonRecursiveExchange.copyCode](../Recursion/OuterCopyFrame.definitions.md#def-654a82544fb518ba)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonScanProgram.finalBase](../../../Shared/Memory/ScanProgram.definitions.md#def-f5f05a8abbd2e902)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`instHAppendOfAppend`, `List`, `Nat`, `instDecidableEqNat`, `List.instAppend`, `Fin`, `Eq`, `HAppend.hAppend`, `List.nil`, `ite`

<a id="def-0cea40eca1143c06"></a>
## `CodedSorting.CommonBorrowMachine.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L29)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → {V : ℕ} → List (CodedSorting.ScanProgram.Pass V) → ℕ
```

**定义**

```lean
fun q {V} ps => (3 * CodedSorting.ScanProgram.totalConstant ps + 6) * CodedSorting.CommonPermutationPairs.count q V
```

**继续展开**

- [CodedSorting.ScanProgram.totalConstant](../../../Shared/Programs/ScanProgramLift.definitions.md#def-e72f845372e79c59)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-a5945b1037ae9b44"></a>
## `CodedSorting.CommonBorrowMachine.raw_correct`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean#L32)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
  (ps : List (CodedSorting.ScanProgram.Pass V)) (source buffer limit : ℕ),
  source + CodedSorting.CommonPermutationPairs.count q V ≤ buffer →
    buffer + CodedSorting.CommonPermutationPairs.count q V ≤ limit →
      limit ≤ q.N ^ q.exponent →
        ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (y : Fin V),
          CodedSorting.CommonPermutationPairs.readBit q
              (CodedSorting.CommonStaticSchedule.executeRaw q
                    (CodedSorting.CommonBorrowMachine.code q reader ps source buffer) s).1.disk
              source ↑y =
            CodedSorting.CommonPermutationPairs.readBit q s.disk source
              ↑((Equiv.symm (CodedSorting.ScanProgram.destination ps)) y)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonPermutationPairs.readBit](../Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonBorrowMachine.code](Machine.definitions.md#def-7f3b01c10733f53f)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ScanProgram.destination](../../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-0391c5498f25d3f4"></a>
## `CodedSorting.CommonBorrowMachine.raw_frame`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean#L52)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
  (ps : List (CodedSorting.ScanProgram.Pass V)) (source buffer limit : ℕ),
  source + CodedSorting.CommonPermutationPairs.count q V ≤ buffer →
    buffer + CodedSorting.CommonPermutationPairs.count q V ≤ limit →
      limit ≤ q.N ^ q.exponent →
        ∀ (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
          ↑a < source ∨ source + CodedSorting.CommonPermutationPairs.count q V ≤ ↑a →
            ↑a < buffer ∨ limit ≤ ↑a →
              (CodedSorting.CommonStaticSchedule.executeRaw q
                        (CodedSorting.CommonBorrowMachine.code q reader ps source buffer) s).1.disk
                  a =
                s.disk a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonBorrowMachine.code](Machine.definitions.md#def-7f3b01c10733f53f)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-ae1b474dfa645919"></a>
## `CodedSorting.CommonBorrowMachine.code_safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean#L72)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
  (ps : List (CodedSorting.ScanProgram.Pass V)) (source buffer : ℕ),
  ∀ i ∈ CodedSorting.CommonBorrowMachine.code q reader ps source buffer,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBorrowMachine.code](Machine.definitions.md#def-7f3b01c10733f53f)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`, `Fin`

<a id="def-fe44a6841c9214af"></a>
## `CodedSorting.CommonBorrowMachine.code_cost`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean#L83)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
  (ps : List (CodedSorting.ScanProgram.Pass V)) (source buffer : ℕ),
  CodedSorting.CommonStaticSchedule.cost q (CodedSorting.CommonBorrowMachine.code q reader ps source buffer) ≤
    CodedSorting.CommonBorrowMachine.charge q ps
```

**继续展开**

- [CodedSorting.CommonBorrowMachine.charge](Machine.definitions.md#def-0cea40eca1143c06)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonBorrowMachine.code](Machine.definitions.md#def-7f3b01c10733f53f)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)

**基础库名称**

`LE.le`, `instLENat`, `List`, `Nat`, `Fin`

<a id="def-21252ea9d611df22"></a>
## `CodedSorting.CommonBorrowMachine.code_length`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean#L92)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
  (ps : List (CodedSorting.ScanProgram.Pass V)) (source buffer : ℕ),
  (CodedSorting.CommonBorrowMachine.code q reader ps source buffer).length ≤
    CodedSorting.CommonBorrowMachine.charge q ps
```

**继续展开**

- [CodedSorting.CommonBorrowMachine.charge](Machine.definitions.md#def-0cea40eca1143c06)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonBorrowMachine.code](Machine.definitions.md#def-7f3b01c10733f53f)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`LE.le`, `instLENat`, `List`, `Nat`, `Fin`, `List.length`

<a id="def-aa10da77fb98c7f3"></a>
## `CodedSorting.CommonBorrowMachine.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L101)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V : ℕ} →
    Fin q.inventory.readers →
      (ps : List (CodedSorting.ScanProgram.Pass V)) →
        (source buffer limit : ℕ) →
          source + CodedSorting.CommonPermutationPairs.count q V ≤ buffer →
            buffer + CodedSorting.CommonPermutationPairs.count q V ≤ limit →
              limit ≤ q.N ^ q.exponent →
                CodedSorting.CommonFinitePermutation.Program q V source buffer limit
                  (Equiv.symm (CodedSorting.ScanProgram.destination ps))
```

**定义**

```lean
fun q {V} reader ps source buffer limit hs hw hl =>
  { instructions := CodedSorting.CommonBorrowMachine.code q reader ps source buffer,
    charge := CodedSorting.CommonBorrowMachine.charge q ps, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonBorrowMachine.raw_correct](Machine.definitions.md#def-a5945b1037ae9b44)
- [CodedSorting.CommonBorrowMachine.charge](Machine.definitions.md#def-0cea40eca1143c06)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonBorrowMachine.code_safe](Machine.definitions.md#def-ae1b474dfa645919)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonBorrowMachine.code_cost](Machine.definitions.md#def-fe44a6841c9214af)
- [CodedSorting.CommonBorrowMachine.code](Machine.definitions.md#def-7f3b01c10733f53f)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ScanProgram.Pass](../../../Shared/Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.CommonBorrowMachine.code_length](Machine.definitions.md#def-21252ea9d611df22)
- [CodedSorting.ScanProgram.destination](../../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonBorrowMachine.raw_frame](Machine.definitions.md#def-0391c5498f25d3f4)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Fin`

<a id="def-137be15beee4df26"></a>
## `CodedSorting.CommonBorrowMachine.borrowProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L131)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (O radix ρ L G S source buffer limit : ℕ) →
      source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤
          buffer →
        buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤
            limit →
          limit ≤ q.N ^ q.exponent →
            CodedSorting.CommonFinitePermutation.Program q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) source
              buffer limit (Equiv.symm (CodedSorting.BorrowScan.borrowPermutation O (radix ^ ρ) L G S))
```

**定义**

```lean
fun q reader O radix ρ L G S source buffer limit hs hw hl =>
  (CodedSorting.CommonBorrowMachine.program q reader (CodedSorting.BorrowScan.borrowProgram O radix ρ L G S) source
        buffer limit hs hw hl).changePermutation
    ⋯
```

**继续展开**

- [CodedSorting.BorrowScan.borrowProgram](../Memory/PhysicalPaddingExchange.definitions.md#def-5b07642e3db0adc2)
- [CodedSorting.CommonFinitePermutation.Program.changePermutation](../Memory/ExchangeShapeProgram.definitions.md#def-abb56e7c683c1f81)
- [CodedSorting.CommonBorrowMachine.program](Machine.definitions.md#def-aa10da77fb98c7f3)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonBorrowMachine.borrowProgram._proof_1](Machine.definitions.md#def-3d6e80872502879c)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.BorrowScan.borrowPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-18059f387df670ea)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ScanProgram.destination](../../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Fin`

<a id="def-70468e490e4d4f35"></a>
## `CodedSorting.CommonBorrowMachine.finishProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L142)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (O radix ρ L G S source buffer limit : ℕ) →
      source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤
          buffer →
        buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤
            limit →
          limit ≤ q.N ^ q.exponent →
            CodedSorting.CommonFinitePermutation.Program q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) source
              buffer limit (Equiv.symm (CodedSorting.BorrowScan.finishPermutation O (radix ^ ρ) L G S))
```

**定义**

```lean
fun q reader O radix ρ L G S source buffer limit hs hw hl =>
  (CodedSorting.CommonBorrowMachine.program q reader (CodedSorting.BorrowScan.finishProgram O radix ρ L G S) source
        buffer limit hs hw hl).changePermutation
    ⋯
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.changePermutation](../Memory/ExchangeShapeProgram.definitions.md#def-abb56e7c683c1f81)
- [CodedSorting.CommonBorrowMachine.program](Machine.definitions.md#def-aa10da77fb98c7f3)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.BorrowScan.finishProgram](../Memory/PhysicalPaddingExchange.definitions.md#def-342db2eba4fb8963)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.BorrowScan.finishPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-b4db3b622c021400)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.ScanProgram.destination](../../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)
- [CodedSorting.CommonBorrowMachine.finishProgram._proof_2](Machine.definitions.md#def-61aad454ad04f286)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Fin`

<a id="def-e38e7f541a617c43"></a>
## `CodedSorting.CommonBorrowLayout.originalSwap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L227)

**类型**

```lean
(O H L G S : ℕ) → Equiv.Perm (Fin (CodedSorting.BorrowScan.volume O H L G S))
```

**定义**

```lean
fun O H L G S => (finCongr ⋯).symm.trans (Equiv.trans (CodedSorting.CommonChunkLayout.swap O (H * L) G S) (finCongr ⋯))
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.PhysicalBorrowLayout.original_volume](../Memory/PhysicalPaddingExchange.definitions.md#def-fd27de74d690c2aa)
- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `finCongr`, `instMulNat`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `instHMul`

<a id="def-77f3cfc4b1073d36"></a>
## `CodedSorting.CommonBorrowLayout.borrowedSwap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L231)

**类型**

```lean
(O H L G S : ℕ) → Equiv.Perm (Fin (CodedSorting.BorrowScan.volume O H L G S))
```

**定义**

```lean
fun O H L G S =>
  (finCongr ⋯).symm.trans (Equiv.trans (CodedSorting.CommonChunkLayout.swap (O * (H * H)) L G S) (finCongr ⋯))
```

**继续展开**

- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.PhysicalBorrowLayout.borrowed_volume](../Memory/PhysicalPaddingExchange.definitions.md#def-c92516d3f96291cc)
- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `finCongr`, `instMulNat`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `instHMul`

<a id="def-c7c72b04608938f6"></a>
## `CodedSorting.CommonBorrowedCore.liftedInner`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L351)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (O H L G S source buffer limit : ℕ) →
    CodedSorting.CommonFinitePermutation.Program q (CodedSorting.CommonChunkLayout.Volume (O * (H * H)) L G S) source
        buffer limit (CodedSorting.CommonChunkLayout.swap (O * (H * H)) L G S) →
      CodedSorting.CommonFinitePermutation.Program q (CodedSorting.BorrowScan.volume O H L G S) source buffer limit
        (CodedSorting.CommonBorrowLayout.borrowedSwap O H L G S)
```

**定义**

```lean
fun q O H L G S source buffer limit p => p.castVolume ⋯
```

**继续展开**

- [CodedSorting.CommonBorrowLayout.borrowedSwap](Machine.definitions.md#def-77f3cfc4b1073d36)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.castVolume](../Memory/ExchangeShapeProgram.definitions.md#def-011d8c0416a63718)
- [CodedSorting.PhysicalBorrowLayout.borrowed_volume](../Memory/PhysicalPaddingExchange.definitions.md#def-c92516d3f96291cc)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-fb425764a557e6db"></a>
## `CodedSorting.CommonBorrowedCore.composed`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L358)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (O radix ρ L G S source buffer limit : ℕ) →
      CodedSorting.CommonFinitePermutation.Program q
          (CodedSorting.CommonChunkLayout.Volume (O * (radix ^ ρ * radix ^ ρ)) L G S) source buffer limit
          (CodedSorting.CommonChunkLayout.swap (O * (radix ^ ρ * radix ^ ρ)) L G S) →
        source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤
            buffer →
          buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤
              limit →
            limit ≤ q.N ^ q.exponent →
              CodedSorting.CommonFinitePermutation.Program q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) source
                buffer limit
                ((Equiv.symm (CodedSorting.BorrowScan.finishPermutation O (radix ^ ρ) L G S)).trans
                  (Equiv.trans (CodedSorting.CommonBorrowLayout.borrowedSwap O (radix ^ ρ) L G S)
                    (Equiv.symm (CodedSorting.BorrowScan.borrowPermutation O (radix ^ ρ) L G S))))
```

**定义**

```lean
fun q reader O radix ρ L G S source buffer limit p hs hw hl =>
  ((CodedSorting.CommonBorrowMachine.borrowProgram q reader O radix ρ L G S source buffer limit hs hw hl).append
        (CodedSorting.CommonBorrowedCore.liftedInner q O (radix ^ ρ) L G S source buffer limit p)).append
    (CodedSorting.CommonBorrowMachine.finishProgram q reader O radix ρ L G S source buffer limit hs hw hl)
```

**继续展开**

- [CodedSorting.CommonBorrowMachine.finishProgram](Machine.definitions.md#def-70468e490e4d4f35)
- [CodedSorting.CommonBorrowedCore.liftedInner](Machine.definitions.md#def-c7c72b04608938f6)
- [CodedSorting.CommonBorrowLayout.borrowedSwap](Machine.definitions.md#def-77f3cfc4b1073d36)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.borrowPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-18059f387df670ea)
- [CodedSorting.BorrowScan.finishPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-b4db3b622c021400)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program.append](../Memory/ExchangeShapeProgram.definitions.md#def-91ea532bb04faf9e)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonBorrowMachine.borrowProgram](Machine.definitions.md#def-137be15beee4df26)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Fin`, `instHMul`

<a id="def-cbec78d7b63d5738"></a>
## `CodedSorting.CommonBorrowedCore.exchanged`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L373)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (O radix ρ L G S source buffer limit : ℕ) →
      CodedSorting.CommonFinitePermutation.Program q
          (CodedSorting.CommonChunkLayout.Volume (O * (radix ^ ρ * radix ^ ρ)) L G S) source buffer limit
          (CodedSorting.CommonChunkLayout.swap (O * (radix ^ ρ * radix ^ ρ)) L G S) →
        source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤
            buffer →
          buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤
              limit →
            limit ≤ q.N ^ q.exponent →
              CodedSorting.CommonFinitePermutation.Program q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) source
                buffer limit (CodedSorting.CommonBorrowLayout.originalSwap O (radix ^ ρ) L G S)
```

**定义**

```lean
fun q reader O radix ρ L G S source buffer limit p hs hw hl =>
  (CodedSorting.CommonBorrowedCore.composed q reader O radix ρ L G S source buffer limit p hs hw hl).changePermutation ⋯
```

**继续展开**

- [CodedSorting.CommonFinitePermutation.Program.changePermutation](../Memory/ExchangeShapeProgram.definitions.md#def-abb56e7c683c1f81)
- [CodedSorting.CommonBorrowLayout.borrowedSwap](Machine.definitions.md#def-77f3cfc4b1073d36)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonBorrowedCore.exchanged._proof_3](Machine.definitions.md#def-f987c7e257d92dec)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.borrowPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-18059f387df670ea)
- [CodedSorting.BorrowScan.finishPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-b4db3b622c021400)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonBorrowLayout.originalSwap](Machine.definitions.md#def-e38e7f541a617c43)
- [CodedSorting.CommonBorrowedCore.composed](Machine.definitions.md#def-fb425764a557e6db)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Equiv.symm`, `Fin`, `instHMul`

<a id="def-354b0e5ca8f5d4da"></a>
## `CodedSorting.CommonBorrowedCore.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Machine.lean#L385)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (O radix ρ L G S source buffer limit : ℕ) →
      CodedSorting.CommonFinitePermutation.Program q
          (CodedSorting.CommonChunkLayout.Volume (O * (radix ^ ρ * radix ^ ρ)) L G S) source buffer limit
          (CodedSorting.CommonChunkLayout.swap (O * (radix ^ ρ * radix ^ ρ)) L G S) →
        source +
              CodedSorting.CommonPermutationPairs.count q
                (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
            buffer →
          buffer +
                CodedSorting.CommonPermutationPairs.count q
                  (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
              limit →
            limit ≤ q.N ^ q.exponent →
              CodedSorting.CommonFinitePermutation.Program q
                (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) source buffer limit
                (CodedSorting.CommonChunkLayout.swap O (radix ^ ρ * L) G S)
```

**定义**

```lean
fun q reader O radix ρ L G S source buffer limit p hs hw hl =>
  let hv := ⋯;
  let t := CodedSorting.CommonBorrowedCore.exchanged q reader O radix ρ L G S source buffer limit p ⋯ ⋯ hl;
  { instructions := t.instructions, charge := t.charge, correct := ⋯, frame := ⋯, safe := ⋯, cost_le := ⋯,
    length_le := ⋯ }
```

**继续展开**

- [CodedSorting.CommonBorrowedCore.program._proof_5](Machine.definitions.md#def-74c23b4453194064)
- [CodedSorting.CommonBorrowedCore.exchanged](Machine.definitions.md#def-cbec78d7b63d5738)
- [CodedSorting.CommonBorrowedCore.program._proof_6](Machine.definitions.md#def-320abdfc4b567bbd)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonBorrowedCore.program._proof_8](Machine.definitions.md#def-3391f2d73d267eb5)
- [CodedSorting.CommonBorrowedCore.program._proof_4](Machine.definitions.md#def-c6816a5c4aa3f465)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonBorrowedCore.program._proof_10](Machine.definitions.md#def-f96213a193d02b92)
- [CodedSorting.CommonBorrowedCore.program._proof_9](Machine.definitions.md#def-72fec7a2454f21be)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonBorrowLayout.originalSwap](Machine.definitions.md#def-e38e7f541a617c43)
- [CodedSorting.CommonBorrowedCore.program._proof_7](Machine.definitions.md#def-9ae6763da93f2c0f)
- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Fin`, `Eq`, `instHMul`

<a id="def-3d6e80872502879c"></a>
## `CodedSorting.CommonBorrowMachine.borrowProgram._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (O radix ρ L G S : ℕ),
  Equiv.symm (CodedSorting.ScanProgram.destination (CodedSorting.BorrowScan.borrowProgram O radix ρ L G S)) =
    Equiv.symm (CodedSorting.BorrowScan.borrowPermutation O (radix ^ ρ) L G S)
```

**继续展开**

- [CodedSorting.BorrowScan.borrowProgram](../Memory/PhysicalPaddingExchange.definitions.md#def-5b07642e3db0adc2)
- [CodedSorting.BorrowScan.borrowPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-18059f387df670ea)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.ScanProgram.destination](../../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`

<a id="def-61aad454ad04f286"></a>
## `CodedSorting.CommonBorrowMachine.finishProgram._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (O radix ρ L G S : ℕ),
  Equiv.symm (CodedSorting.ScanProgram.destination (CodedSorting.BorrowScan.finishProgram O radix ρ L G S)) =
    Equiv.symm (CodedSorting.BorrowScan.finishPermutation O (radix ^ ρ) L G S)
```

**继续展开**

- [CodedSorting.BorrowScan.finishProgram](../Memory/PhysicalPaddingExchange.definitions.md#def-342db2eba4fb8963)
- [CodedSorting.BorrowScan.finishPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-b4db3b622c021400)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.ScanProgram.destination](../../../Shared/Programs/ScanProgramLift.definitions.md#def-155edcb120b335e1)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`

<a id="def-f987c7e257d92dec"></a>
## `CodedSorting.CommonBorrowedCore.exchanged._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (O radix ρ L G S : ℕ),
  (Equiv.symm (CodedSorting.BorrowScan.finishPermutation O (radix ^ ρ) L G S)).trans
      (Equiv.trans (CodedSorting.CommonBorrowLayout.borrowedSwap O (radix ^ ρ) L G S)
        (Equiv.symm (CodedSorting.BorrowScan.borrowPermutation O (radix ^ ρ) L G S))) =
    CodedSorting.CommonBorrowLayout.originalSwap O (radix ^ ρ) L G S
```

**继续展开**

- [CodedSorting.CommonBorrowLayout.borrowedSwap](Machine.definitions.md#def-77f3cfc4b1073d36)
- [CodedSorting.BorrowScan.borrowPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-18059f387df670ea)
- [CodedSorting.BorrowScan.finishPermutation](../Memory/PhysicalPaddingExchange.definitions.md#def-b4db3b622c021400)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonBorrowLayout.originalSwap](Machine.definitions.md#def-e38e7f541a617c43)

**基础库名称**

`Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`

<a id="def-f96213a193d02b92"></a>
## `CodedSorting.CommonBorrowedCore.program._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (O radix ρ L G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonChunkLayout.Volume (O * (radix ^ ρ * radix ^ ρ)) L G S) source buffer limit
      (CodedSorting.CommonChunkLayout.swap (O * (radix ^ ρ * radix ^ ρ)) L G S))
  (hs :
    source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      buffer)
  (hw :
    buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent),
  (CodedSorting.CommonBorrowedCore.exchanged q reader O radix ρ L G S source buffer limit p ⋯ ⋯
          hl).instructions.length ≤
    (CodedSorting.CommonBorrowedCore.exchanged q reader O radix ρ L G S source buffer limit p ⋯ ⋯ hl).charge
```

**继续展开**

- [CodedSorting.CommonBorrowedCore.program._proof_5](Machine.definitions.md#def-74c23b4453194064)
- [CodedSorting.CommonBorrowedCore.exchanged](Machine.definitions.md#def-cbec78d7b63d5738)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonBorrowLayout.originalSwap](Machine.definitions.md#def-e38e7f541a617c43)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Fin`, `List.length`, `instHMul`

<a id="def-c6816a5c4aa3f465"></a>
## `CodedSorting.CommonBorrowedCore.program._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (O radix ρ L G S : ℕ),
  CodedSorting.BinaryPadding.Volume O (radix ^ ρ * L) G S = CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S
```

**继续展开**

- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `HPow.hPow`, `Nat`, `instHPow`, `Eq`, `instHMul`

<a id="def-74c23b4453194064"></a>
## `CodedSorting.CommonBorrowedCore.program._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (O radix ρ L G S source buffer : ℕ),
  source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      buffer →
    source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.BorrowScan.volume O (radix ^ ρ) L G S) ≤ buffer
```

**继续展开**

- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `instHMul`

<a id="def-320abdfc4b567bbd"></a>
## `CodedSorting.CommonBorrowedCore.program._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (O radix ρ L G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonChunkLayout.Volume (O * (radix ^ ρ * radix ^ ρ)) L G S) source buffer limit
      (CodedSorting.CommonChunkLayout.swap (O * (radix ^ ρ * radix ^ ρ)) L G S))
  (hs :
    source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      buffer)
  (hw :
    buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q)
  (y : Fin (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S)),
  CodedSorting.CommonPermutationPairs.readBit q
      (CodedSorting.CommonStaticSchedule.executeRaw q
            (CodedSorting.CommonBorrowedCore.exchanged q reader O radix ρ L G S source buffer limit p ⋯ ⋯
                hl).instructions
            s).1.disk
      source ↑y =
    CodedSorting.CommonPermutationPairs.readBit q s.disk source
      ↑((CodedSorting.CommonChunkLayout.swap O (radix ^ ρ * L) G S) y)
```

**继续展开**

- [CodedSorting.CommonBorrowedCore.program._proof_5](Machine.definitions.md#def-74c23b4453194064)
- [CodedSorting.CommonBorrowedCore.exchanged](Machine.definitions.md#def-cbec78d7b63d5738)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.CommonPermutationPairs.readBit](../Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Circuit.Bit](../../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonBorrowLayout.originalSwap](Machine.definitions.md#def-e38e7f541a617c43)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `instHPow`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-9ae6763da93f2c0f"></a>
## `CodedSorting.CommonBorrowedCore.program._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (O radix ρ L G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonChunkLayout.Volume (O * (radix ^ ρ * radix ^ ρ)) L G S) source buffer limit
      (CodedSorting.CommonChunkLayout.swap (O * (radix ^ ρ * radix ^ ρ)) L G S))
  (hs :
    source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      buffer)
  (hw :
    buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent) (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨
      source +
          CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
        ↑a →
    ↑a < buffer ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.CommonBorrowedCore.exchanged q reader O radix ρ L G S source buffer limit p ⋯ ⋯
                    hl).instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.CommonBorrowedCore.program._proof_5](Machine.definitions.md#def-74c23b4453194064)
- [CodedSorting.CommonBorrowedCore.exchanged](Machine.definitions.md#def-cbec78d7b63d5738)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonBorrowLayout.originalSwap](Machine.definitions.md#def-e38e7f541a617c43)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `instHMul`

<a id="def-3391f2d73d267eb5"></a>
## `CodedSorting.CommonBorrowedCore.program._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (O radix ρ L G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonChunkLayout.Volume (O * (radix ^ ρ * radix ^ ρ)) L G S) source buffer limit
      (CodedSorting.CommonChunkLayout.swap (O * (radix ^ ρ * radix ^ ρ)) L G S))
  (hs :
    source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      buffer)
  (hw :
    buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent),
  ∀ i ∈ (CodedSorting.CommonBorrowedCore.exchanged q reader O radix ρ L G S source buffer limit p ⋯ ⋯ hl).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonBorrowedCore.program._proof_5](Machine.definitions.md#def-74c23b4453194064)
- [CodedSorting.CommonBorrowedCore.exchanged](Machine.definitions.md#def-cbec78d7b63d5738)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonBorrowLayout.originalSwap](Machine.definitions.md#def-e38e7f541a617c43)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `List`, `instHAdd`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Fin`, `instHMul`

<a id="def-72fec7a2454f21be"></a>
## `CodedSorting.CommonBorrowedCore.program._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Machine.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (O radix ρ L G S source buffer limit : ℕ)
  (p :
    CodedSorting.CommonFinitePermutation.Program q
      (CodedSorting.CommonChunkLayout.Volume (O * (radix ^ ρ * radix ^ ρ)) L G S) source buffer limit
      (CodedSorting.CommonChunkLayout.swap (O * (radix ^ ρ * radix ^ ρ)) L G S))
  (hs :
    source + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      buffer)
  (hw :
    buffer + CodedSorting.CommonPermutationPairs.count q (CodedSorting.CommonChunkLayout.Volume O (radix ^ ρ * L) G S) ≤
      limit)
  (hl : limit ≤ q.N ^ q.exponent),
  CodedSorting.CommonStaticSchedule.cost q
      (CodedSorting.CommonBorrowedCore.exchanged q reader O radix ρ L G S source buffer limit p ⋯ ⋯ hl).instructions ≤
    (CodedSorting.CommonBorrowedCore.exchanged q reader O radix ρ L G S source buffer limit p ⋯ ⋯ hl).charge
```

**继续展开**

- [CodedSorting.CommonBorrowedCore.program._proof_5](Machine.definitions.md#def-74c23b4453194064)
- [CodedSorting.CommonBorrowedCore.exchanged](Machine.definitions.md#def-cbec78d7b63d5738)
- [CodedSorting.CommonChunkLayout.swap](../Chunks/Layout.definitions.md#def-6f5402999737c1c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonFinitePermutation.Program.charge](../Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.CommonChunkLayout.Volume](../Chunks/Layout.definitions.md#def-e901e0d94d622ec2)
- [CodedSorting.BorrowScan.volume](../Memory/PhysicalPaddingExchange.definitions.md#def-947bc1534a4ad3ac)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonBorrowLayout.originalSwap](Machine.definitions.md#def-e38e7f541a617c43)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.CommonPermutationPairs.count](../Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Fin`, `instHMul`
