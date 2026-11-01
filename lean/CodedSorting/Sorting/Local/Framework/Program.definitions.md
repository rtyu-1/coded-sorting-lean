# Program 的定义

[源码](Program.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-a49770b9209d9457"></a>
## `CodedSorting.CommonLocalNode.side`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L64)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n => CodedSorting.LocalShape.sizeChoice n
```

**继续展开**

- [CodedSorting.LocalShape.sizeChoice](../../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)

**基础库名称**

`Nat`

<a id="def-201a7ae73aa74a36"></a>
## `CodedSorting.CommonLocalNode.rowCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L65)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n => CodedSorting.PhysicalLocalSortNode.rows (CodedSorting.CommonLocalNode.side n)
```

**继续展开**

- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)

**基础库名称**

`Nat`

<a id="def-2a979370257be30e"></a>
## `CodedSorting.CommonLocalNode.half`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L66)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n => CodedSorting.LocalShape.columnLength n / 2
```

**继续展开**

- [CodedSorting.LocalShape.columnLength](../../../Shared/Programs/LocalTrace.definitions.md#def-0ba59d4f9543a5be)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `instOfNatNat`, `Nat`, `Nat.instDiv`, `OfNat.ofNat`

<a id="def-84131018030affe6"></a>
## `CodedSorting.CommonLocalNode.small`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L67)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n => CodedSorting.CommonLocalNode.side n * CodedSorting.CommonLocalNode.rowCount n
```

**继续展开**

- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-c6fe80e6c46e1fbf"></a>
## `CodedSorting.CommonLocalNode.large`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L68)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun n => (CodedSorting.CommonLocalNode.side n + 1) * CodedSorting.CommonLocalNode.rowCount n
```

**继续展开**

- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-8c86ebfd775e64cc"></a>
## `CodedSorting.CommonLocalNode.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L70)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (n source A B work limit : ℕ) →
      (op : CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w)) →
        CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
            (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
              (CodedSorting.CommonLocalNode.rowCount n)) →
          CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.large n) B work limit
              (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n + 1)
                (CodedSorting.CommonLocalNode.rowCount n)) →
            CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
                (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (CodedSorting.CommonLocalNode.side n)) →
              CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
                  (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (CodedSorting.CommonLocalNode.side n)) →
                source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A →
                  A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤
                      B →
                    B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤
                        work →
                      work ≤ limit →
                        limit ≤ q.N ^ q.exponent →
                          3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits →
                            CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n →
                              CodedSorting.CommonRecordProgram.Program q n source A limit
                                (CodedSorting.CommonLocalSemantic.pipeline op n)
```

**定义**

```lean
fun q reader n source A B work limit op pA pB pf pb hs hAB hBW hwl hl hshape hr =>
  let a := CodedSorting.CommonLocalNode.small n;
  let b := CodedSorting.CommonLocalNode.large n;
  let h := CodedSorting.CommonLocalNode.half n;
  id
    (fun hAB =>
      id
        (fun hBW =>
          let_fun hn := ⋯;
          let_fun hab := ⋯;
          let_fun hh := ⋯;
          let_fun hbh := ⋯;
          let_fun hcount := ⋯;
          let_fun hna := ⋯;
          let_fun habc := ⋯;
          let_fun hhc := ⋯;
          let_fun hSA := ⋯;
          let_fun hAcap := ⋯;
          let_fun hBcap := ⋯;
          let_fun hshape' := ⋯;
          let_fun hwA := ⋯;
          let_fun hAB' := ⋯;
          let_fun hframeA := ⋯;
          let_fun hframeB := ⋯;
          let pad0 :=
            CodedSorting.CommonRecordTransform.margins q reader 0 n (a - n) 0 source A source n A limit ⋯ ⋯ hSA ⋯ ⋯ ⋯ ⋯;
          let padStage := (pad0.castOutput ⋯).changeFunction ⋯;
          let childA := CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA;
          let forwardStage := CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯ hwA;
          let backwardStage := CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA;
          let shift0 :=
            CodedSorting.CommonRecordTransform.margins q reader h a h 0 A B source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯ ⋯;
          let shiftStage := ⋯.changeFunction ⋯;
          let childB := ⋯;
          ⋯)
        hBW)
    hAB
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_67](Program.definitions.md#def-ef3313ca36de27be)
- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalNode.program._proof_80](Program.definitions.md#def-f75a6ac053908c84)
- [CodedSorting.CommonLocalNode.program._proof_90](Program.definitions.md#def-180dee9bf7a5843a)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](../../../Shared/Records/Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](../../../Shared/Records/Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalNode.program._proof_43](Program.definitions.md#def-79b3e68371040493)
- [CodedSorting.CommonLocalNode.program._proof_44](Program.definitions.md#def-deb87b79c7dcdbc1)
- [CodedSorting.CommonLocalNode.program._proof_68](Program.definitions.md#def-4c765b794e21177a)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTransform.workspaceProgram](../../../Shared/Records/Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonRecordProgram.Program.mk](../../../Shared/Records/RecordOperations.definitions.md#def-887b49862da8c4f3)
- [CodedSorting.CommonLocalNode.program._proof_62](Program.definitions.md#def-ef93f65db18d7e32)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](../../../Shared/Records/Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonLocalNode.program._proof_57](Program.definitions.md#def-3e23013b1db55e66)
- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.program._proof_76](Program.definitions.md#def-06adeb1e4d2e683b)
- [CodedSorting.CommonLocalNode.program._proof_87](Program.definitions.md#def-66662a918baf0b36)
- [CodedSorting.CommonLocalNode.program._proof_42](Program.definitions.md#def-4b1c143055360b86)
- [CodedSorting.CommonRecordTransform.margins](../../../Shared/Records/Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonLocalNode.program._proof_81](Program.definitions.md#def-e8628ad34481cde3)
- [CodedSorting.CommonLocalNode.program._proof_84](Program.definitions.md#def-0a92d0f5df03afed)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalNode.program._proof_64](Program.definitions.md#def-2e1ce65559baedfe)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program._proof_61](Program.definitions.md#def-605ab56b0f4e5ed4)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLocalNode.program._proof_54](Program.definitions.md#def-6854585bae4dbf52)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.program._proof_50](Program.definitions.md#def-aef2a7bfc2c8c435)
- [CodedSorting.CommonRecordTransform.Stage](../../../Shared/Records/Transform.definitions.md#def-2835e8bed6afef06)
- [CodedSorting.CommonLocalNode.program._proof_45](Program.definitions.md#def-1a5f6d2bf557879d)
- [CodedSorting.CommonLocalNode.program._proof_75](Program.definitions.md#def-196683c06b23f341)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonLocalSemantic.padded_size](Semantic.definitions.md#def-5593436e1b4f55c7)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.program._proof_86](Program.definitions.md#def-fc5c0e63f9bb67e3)
- [CodedSorting.CommonLocalNode.program._proof_41](Program.definitions.md#def-3c680a6fbb3e8851)
- [CodedSorting.CommonLocalNode.program._proof_55](Program.definitions.md#def-64726af18ac826b9)
- [CodedSorting.CommonLocalNode.program._proof_38](Program.definitions.md#def-e236c9a11c988414)
- [CodedSorting.CommonLocalNode.program._proof_82](Program.definitions.md#def-0a7304d95c3d81a1)
- [CodedSorting.CommonLocalNode.program._proof_66](Program.definitions.md#def-b76263befde85225)
- [CodedSorting.CommonLocalNode.program._proof_53](Program.definitions.md#def-d5a555e58fe1d3eb)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.program._proof_60](Program.definitions.md#def-0b01b0e36c90a84d)
- [CodedSorting.CommonLocalNode.program._proof_85](Program.definitions.md#def-6dd4c902f089038e)
- [CodedSorting.CommonLocalNode.program._proof_39](Program.definitions.md#def-15feb6f989c4af29)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonRecordProgram.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonLocalNode.program._proof_59](Program.definitions.md#def-b5b3d09b1956ff16)
- [CodedSorting.CommonRecordTransform.Stage.append](../../../Shared/Records/Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonLocalNode.program._proof_73](Program.definitions.md#def-02c2547d656d731e)
- [CodedSorting.CommonLocalNode.program._proof_48](Program.definitions.md#def-22e32545a544538c)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalNode.program._proof_46](Program.definitions.md#def-5e86adf0d00942c3)
- [CodedSorting.CommonLocalNode.program._proof_74](Program.definitions.md#def-33b88d1c13a04999)
- [CodedSorting.CommonLocalNode.program._proof_79](Program.definitions.md#def-461c2ae95bcc6338)
- [CodedSorting.CommonLocalNode.program._proof_69](Program.definitions.md#def-a7637ff94026cf84)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalNode.program._proof_49](Program.definitions.md#def-f46c49c52bdc5965)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonLocalNode.program._proof_83](Program.definitions.md#def-2ab0b7ea5c0eaf85)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonLocalNode.program._proof_71](Program.definitions.md#def-62b85bcc4e9489d6)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonLocalNode.program._proof_88](Program.definitions.md#def-cf3438cc7e71806b)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonLocalNode.program._proof_89](Program.definitions.md#def-e1183cd2828f6105)
- [CodedSorting.CommonLocalNode.program._proof_56](Program.definitions.md#def-52f2ff36340d79cd)
- [CodedSorting.CommonLocalNode.program._proof_77](Program.definitions.md#def-5c37dca9e74f828c)
- [CodedSorting.CommonLocalNode.program._proof_70](Program.definitions.md#def-3801261deb2e34d9)
- [CodedSorting.CommonLocalNode.program._proof_65](Program.definitions.md#def-c23f548d23b23e46)
- [CodedSorting.CommonRecordTransform.Stage.charge](../../../Shared/Records/Transform.definitions.md#def-30123232aa6eccd6)
- [CodedSorting.CommonLocalNode.program._proof_47](Program.definitions.md#def-3422ccbb4127dcc4)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonLocalNode.program._proof_63](Program.definitions.md#def-b5d288a28356219c)
- [CodedSorting.CommonLocalNode.program._proof_72](Program.definitions.md#def-60b497b31ca95168)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonLocalNode.program._proof_52](Program.definitions.md#def-0fcdcb2912c6e1de)
- [CodedSorting.CommonLocalNode.program._proof_78](Program.definitions.md#def-10cfff12bcca7add)
- [CodedSorting.CommonLocalNode.program._proof_58](Program.definitions.md#def-72175b577656778c)
- [CodedSorting.CommonLocalNode.program._proof_40](Program.definitions.md#def-c39d97b66bd2e869)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.CommonLocalNode.program._proof_51](Program.definitions.md#def-c615d89c718200ee)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_refl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `id`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `letFun`, `instHMul`

<a id="def-a7cd06ce9a69e356"></a>
## `CodedSorting.CommonLocalRecursion.Descriptors`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L331)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → Prop
```

**定义**

```lean
fun q x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → Prop) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → ℕ → Nat.below (motive := fun x => ℕ → Prop) x → Prop) x, x_2 with
        | 0, x => fun x => True
        | fuel.succ, n => fun x =>
          if n ≤ 512 * q.height then True
          else
            3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits ∧
              x.1 (CodedSorting.CommonLocalNode.rowCount n))
        f)
    x_1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalRecursion.Descriptors.match_1](Program.definitions.md#def-13c87eba66dcfa23)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.brecOn`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `And`, `PProd`, `HPow.hPow`, `Nat`, `LT.lt`, `True`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Nat.succ`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-8f9b5be3d5bc2c96"></a>
## `CodedSorting.CommonLocalRecursion.batchSpace`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L337)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q c r childSpace =>
  if r ≤ 512 * q.height then CodedSorting.CommonGroupedLeafBatch.space q c r
  else c * CodedSorting.CommonRecordProgram.recordBlocks q r + childSpace
```

**继续展开**

- [CodedSorting.CommonGroupedLeafBatch.space](../../../Shared/Memory/GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-3d224d9e59995f0f"></a>
## `CodedSorting.CommonLocalRecursion.height_pos`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean#L349)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), 0 < q.height
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-e87082ef48bf9e49"></a>
## `CodedSorting.CommonLocalRecursion.block_le_height`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean#L353)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), q.block ≤ q.height
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-a17b930897ca503b"></a>
## `CodedSorting.CommonLocalRecursion.operation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L357)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w)
```

**定义**

```lean
fun q fuel => CodedSorting.CommonLocalSemantic.returned (CodedSorting.RecursiveColumnsort.localRun q.height ⋯ fuel)
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.RecursiveColumnsort.localRun](../Columnsort/GroupedRecursiveColumnsort.definitions.md#def-e4250e49e60d6398)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonLocalSemantic.returned](Semantic.definitions.md#def-b2b056f6ee3001d4)
- [CodedSorting.CommonLocalRecursion.height_pos](Program.definitions.md#def-3d224d9e59995f0f)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`Nat`

<a id="def-c59c501b440dfc0d"></a>
## `CodedSorting.CommonLocalRecursion.small_batch`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean#L366)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (fuel c r : ℕ),
  r ≤ 512 * q.height →
    CodedSorting.CommonGroupedLeafBatch.sortColumns c r =
      CodedSorting.CommonLocalSemantic.batch (CodedSorting.CommonLocalRecursion.operation q fuel) c r
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](../../../Shared/Memory/GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-16c1e07c24ee331a"></a>
## `CodedSorting.LocalSorter.Exchange`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Program.lean#L392)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.LocalSorter.Exchange.mk](Program.definitions.md#def-b25cf5f60a180476)

<a id="def-b25cf5f60a180476"></a>
## `CodedSorting.LocalSorter.Exchange.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Program.lean#L395)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  (condition : Prop) →
    (cost : ℕ → ℕ) →
      (space : ℕ → condition → ℕ) →
        (forward :
            Fin q.inventory.readers →
              (t source buffer limit : ℕ) →
                (hnormal : condition) →
                  source +
                        CodedSorting.CommonRecordProgram.recordBlocks q
                          (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
                      buffer →
                    buffer + space t hnormal ≤ limit →
                      limit ≤ q.N ^ q.exponent →
                        CodedSorting.CommonRecordProgram.Program q
                          (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) source buffer limit
                          (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (2 ^ t))) →
          (backward :
              Fin q.inventory.readers →
                (t source buffer limit : ℕ) →
                  (hnormal : condition) →
                    source +
                          CodedSorting.CommonRecordProgram.recordBlocks q
                            (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
                        buffer →
                      buffer + space t hnormal ≤ limit →
                        limit ≤ q.N ^ q.exponent →
                          CodedSorting.CommonRecordProgram.Program q
                            (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) source buffer limit
                            (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (2 ^ t))) →
            (∀ (reader : Fin q.inventory.readers) (t source buffer limit : ℕ) (hnormal : condition)
                (hs :
                  source +
                      CodedSorting.CommonRecordProgram.recordBlocks q
                        (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
                    buffer)
                (hw : buffer + space t hnormal ≤ limit) (hl : limit ≤ q.N ^ q.exponent),
                (forward reader t source buffer limit hnormal hs hw hl).charge ≤ 3 * cost t) →
              (∀ (reader : Fin q.inventory.readers) (t source buffer limit : ℕ) (hnormal : condition)
                  (hs :
                    source +
                        CodedSorting.CommonRecordProgram.recordBlocks q
                          (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
                      buffer)
                  (hw : buffer + space t hnormal ≤ limit) (hl : limit ≤ q.N ^ q.exponent),
                  (backward reader t source buffer limit hnormal hs hw hl).charge ≤ 3 * cost t) →
                CodedSorting.LocalSorter.Exchange q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-d7d8c3e39bc20a0d"></a>
## `CodedSorting.LocalSorter.Exchange.condition`

读取 `CodedSorting.LocalSorter.Exchange` 的 `condition` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Program.lean#L396)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} → CodedSorting.LocalSorter.Exchange q → Prop
```

**定义**

```lean
fun q self => self.1
```

**继续展开**

- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

<a id="def-9253ca30284d92a3"></a>
## `CodedSorting.LocalSorter.Exchange.cost`

读取 `CodedSorting.LocalSorter.Exchange` 的 `cost` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Program.lean#L397)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} → CodedSorting.LocalSorter.Exchange q → ℕ → ℕ
```

**定义**

```lean
fun q self => self.2
```

**继续展开**

- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-1b5706ca953c9fda"></a>
## `CodedSorting.LocalSorter.Exchange.space`

读取 `CodedSorting.LocalSorter.Exchange` 的 `space` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Program.lean#L398)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  (self : CodedSorting.LocalSorter.Exchange q) → ℕ → self.condition → ℕ
```

**定义**

```lean
fun q self => self.3
```

**继续展开**

- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-b16e0f6352fb0bd0"></a>
## `CodedSorting.LocalSorter.Exchange.forward`

读取 `CodedSorting.LocalSorter.Exchange` 的 `forward` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Program.lean#L399)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  (self : CodedSorting.LocalSorter.Exchange q) →
    Fin q.inventory.readers →
      (t source buffer limit : ℕ) →
        (hnormal : self.condition) →
          source +
                CodedSorting.CommonRecordProgram.recordBlocks q
                  (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
              buffer →
            buffer + self.space t hnormal ≤ limit →
              limit ≤ q.N ^ q.exponent →
                CodedSorting.CommonRecordProgram.Program q (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t))
                  source buffer limit (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (2 ^ t))
```

**定义**

```lean
fun q self => self.4
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-f7c1a9048ed96238"></a>
## `CodedSorting.LocalSorter.Exchange.backward`

读取 `CodedSorting.LocalSorter.Exchange` 的 `backward` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Program.lean#L405)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  (self : CodedSorting.LocalSorter.Exchange q) →
    Fin q.inventory.readers →
      (t source buffer limit : ℕ) →
        (hnormal : self.condition) →
          source +
                CodedSorting.CommonRecordProgram.recordBlocks q
                  (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t)) ≤
              buffer →
            buffer + self.space t hnormal ≤ limit →
              limit ≤ q.N ^ q.exponent →
                CodedSorting.CommonRecordProgram.Program q (2 ^ t * CodedSorting.PhysicalLocalSortNode.rows (2 ^ t))
                  source buffer limit (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (2 ^ t))
```

**定义**

```lean
fun q self => self.5
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-e5e926f6441f7a28"></a>
## `CodedSorting.LocalSorter.batchBound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L416)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
CodedSorting.CommonLocalBudget.batchBound
```

**继续展开**

- [CodedSorting.CommonLocalBudget.batchBound](CostBound.definitions.md#def-fd9bae2d2f813ccf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-2a45f731bfb4e38e"></a>
## `CodedSorting.LocalSorter.budget`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L418)

**类型**

```lean
((q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q) →
  CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun swap q x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → ℕ) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → ℕ → Nat.below (motive := fun x => ℕ → ℕ) x → ℕ) x, x_2 with
        | 0, x => fun x_3 => 8 * CodedSorting.CommonRecordProgram.recordBlocks q x + 1
        | fuel.succ, n => fun x =>
          if n ≤ 512 * q.height then 8 * CodedSorting.CommonRecordProgram.recordBlocks q n + 1
          else
            let s := CodedSorting.LocalShape.sizeChoice n;
            let r := CodedSorting.PhysicalLocalSortNode.rows s;
            3 * CodedSorting.LocalSorter.batchBound q (x.1 r) s r +
                  CodedSorting.LocalSorter.batchBound q (x.1 r) (s + 1) r +
                6 * (swap q).cost (CodedSorting.LocalShape.sizeExponent n) +
              3 *
                (2 * CodedSorting.CommonRecordProgram.recordBlocks q (s * r) +
                    CodedSorting.CommonRecordProgram.recordBlocks q ((s + 1) * r) +
                  CodedSorting.CommonRecordProgram.recordBlocks q n))
        f)
    x_1
```

**继续展开**

- [CodedSorting.LocalShape.sizeChoice](../../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.LocalSorter.batchBound](Program.definitions.md#def-e5e926f6441f7a28)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.LocalSorter.Exchange.cost](Program.definitions.md#def-9253ca30284d92a3)
- [CodedSorting.CommonLocalRecursion.Descriptors.match_1](Program.definitions.md#def-13c87eba66dcfa23)

**基础库名称**

`HMul.hMul`, `Nat.brecOn`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.succ`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-f2c3130f446c1b5e"></a>
## `CodedSorting.LocalSorter.space`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L430)

**类型**

```lean
(swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q) →
  (q : CodedSorting.CommonSortingNormalization.Configuration) → (swap q).condition → ℕ → ℕ → ℕ
```

**定义**

```lean
fun swap q hnormal x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → ℕ) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → ℕ → Nat.below (motive := fun x => ℕ → ℕ) x → ℕ) x, x_2 with
        | 0, x => fun x_3 => CodedSorting.CommonRecordProgram.recordBlocks q x
        | fuel.succ, n => fun x =>
          if n ≤ 512 * q.height then CodedSorting.CommonRecordProgram.recordBlocks q n
          else
            max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
              max
                (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
                  (CodedSorting.CommonLocalNode.rowCount n) (x.1 (CodedSorting.CommonLocalNode.rowCount n)))
                (max
                  (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
                    (CodedSorting.CommonLocalNode.rowCount n) (x.1 (CodedSorting.CommonLocalNode.rowCount n)))
                  ((swap q).space (CodedSorting.LocalShape.sizeExponent n) hnormal)))
        f)
    x_1
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalRecursion.Descriptors.match_1](Program.definitions.md#def-13c87eba66dcfa23)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `Nat.brecOn`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.succ`, `Nat.decLe`, `instHMul`, `ite`

<a id="def-f60b3f2c17655ef0"></a>
## `CodedSorting.LocalSorter.batchBuild`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L438)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (fuel c r childSpace childBudget : ℕ) →
      ((source buffer limit : ℕ) →
          source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q r) ≤ buffer →
            buffer + childSpace ≤ limit → limit ≤ q.N ^ q.exponent → { p // p.charge ≤ childBudget }) →
        (source buffer limit : ℕ) →
          source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer →
            buffer + CodedSorting.CommonLocalRecursion.batchSpace q c r childSpace ≤ limit →
              limit ≤ q.N ^ q.exponent → { p // p.charge ≤ CodedSorting.CommonLocalBudget.batchBound q childBudget c r }
```

**定义**

```lean
fun q reader fuel c r childSpace childBudget child source buffer limit hs hw hl =>
  if hr : r ≤ 512 * q.height then
    let p := CodedSorting.CommonGroupedLeafBatch.program q reader c r source buffer limit hr ⋯ hs ⋯ hl;
    ⟨p.changeFunction ⋯, ⋯⟩
  else
    let work := buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r;
    let_fun hwork := ⋯;
    let_fun hwl := ⋯;
    let_fun hpos := ⋯;
    let kids := fun j => ↑(child (CodedSorting.CommonSlabBatch.recordBase q r buffer ↑j) work limit ⋯ hwork hl);
    let p := CodedSorting.CommonSlabBatch.program reader kids hs ⋯ hwl hl;
    ⟨p, ⋯⟩
```

**继续展开**

- [CodedSorting.LocalSorter.batchBuild._proof_102](Program.definitions.md#def-c47b0f45f5950d36)
- [CodedSorting.CommonLocalBudget.batchBound](CostBound.definitions.md#def-fd9bae2d2f813ccf)
- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSlabBatch.Children](../../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-0c2656415697d303)
- [CodedSorting.LocalSorter.batchBuild._proof_98](Program.definitions.md#def-171ea2170531634a)
- [CodedSorting.CommonGroupedLeafBatch.program](../../../Shared/Memory/GroupedLeafBatch.definitions.md#def-b060e8872789c203)
- [CodedSorting.LocalSorter.batchBuild._proof_101](Program.definitions.md#def-09d8744d19d9b009)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.program](../../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-ae51434b8b1ab7f4)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.LocalSorter.batchBuild._proof_100](Program.definitions.md#def-dbbde2bdcb50b812)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](../../../Shared/Memory/GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.LocalSorter.batchBuild._proof_99](Program.definitions.md#def-78e52987c4933689)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalRecursion.small_batch](Program.definitions.md#def-c59c501b440dfc0d)
- [CodedSorting.CommonSlabBatch.recordBase](../../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-e192f85de221fbac)
- [CodedSorting.LocalSorter.batchBuild._proof_96](Program.definitions.md#def-3519369b0b46454c)
- [CodedSorting.CommonLocalRecursion.block_le_height](Program.definitions.md#def-e87082ef48bf9e49)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.LocalSorter.batchBuild._proof_97](Program.definitions.md#def-7f76eac5f86e5e31)
- [CodedSorting.LocalSorter.batchBuild._proof_103](Program.definitions.md#def-ac19e0e38fc3313a)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonSlabBatch.batchOutput](../../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-1e347b15e5d5c6a2)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `dite`, `Subtype.mk`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Not`, `Nat.decLe`, `letFun`, `instHMul`

<a id="def-6731b58c8d479a3d"></a>
## `CodedSorting.LocalSorter.build`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L492)

**类型**

```lean
(swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q) →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin q.inventory.readers →
      (hnormal : (swap q).condition) →
        (fuel n : ℕ) →
          CodedSorting.CommonLocalAdmissible.Admissible q.height fuel n →
            CodedSorting.CommonLocalRecursion.Descriptors q fuel n →
              (source buffer limit : ℕ) →
                source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
                  buffer + CodedSorting.LocalSorter.space swap q hnormal fuel n ≤ limit →
                    limit ≤ q.N ^ q.exponent → { p // p.charge ≤ CodedSorting.LocalSorter.budget swap q fuel n }
```

**定义**

```lean
fun swap q reader hnormal fuel n ha hd source buffer limit hs hw hl =>
  Nat.recAux (motive := fun fuel =>
    (n : ℕ) →
      CodedSorting.CommonLocalAdmissible.Admissible q.height fuel n →
        CodedSorting.CommonLocalRecursion.Descriptors q fuel n →
          (source buffer limit : ℕ) →
            source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
              buffer + CodedSorting.LocalSorter.space swap q hnormal fuel n ≤ limit →
                limit ≤ q.N ^ q.exponent → { p // p.charge ≤ CodedSorting.LocalSorter.budget swap q fuel n })
    (fun n ha hd source buffer limit hs hw hl =>
      let p :=
        CodedSorting.CommonResidentRecordProgram.program q reader n ha CodedSorting.Columnsort.sortColumn source buffer
          limit ⋯ hw hl;
      ⟨p, ⋯⟩)
    (fun fuel ih n ha hd source buffer limit hs hw hl =>
      if hn : n ≤ 512 * q.height then
        let p :=
          CodedSorting.CommonResidentRecordProgram.program q reader n hn CodedSorting.Columnsort.sortColumn source
            buffer limit ⋯ ⋯ hl;
        ⟨p.changeFunction ⋯, ⋯⟩
      else
        let r := CodedSorting.CommonLocalNode.rowCount n;
        let c := CodedSorting.CommonLocalNode.side n;
        let B :=
          buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n));
        let work := B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n));
        let_fun hadm := ⋯;
        let_fun hdesc := ⋯;
        let_fun hrest := ⋯;
        let_fun hwl := ⋯;
        let_fun hwa := ⋯;
        let_fun hwb := ⋯;
        let_fun hwe := ⋯;
        let child := fun src bf lim hs' hw' hl' => ih r hadm ⋯ src bf lim hs' hw' hl';
        let_fun hsepA := ⋯;
        let_fun hsepB := ⋯;
        let pa :=
          CodedSorting.LocalSorter.batchBuild q reader fuel c r (CodedSorting.LocalSorter.space swap q hnormal fuel r)
            (CodedSorting.LocalSorter.budget swap q fuel r) child buffer work limit hsepA hwa hl;
        let pbatch :=
          CodedSorting.LocalSorter.batchBuild q reader fuel (c + 1) r
            (CodedSorting.LocalSorter.space swap q hnormal fuel r) (CodedSorting.LocalSorter.budget swap q fuel r) child
            B work limit hsepB hwb hl;
        let pf :=
          (swap q).forward reader (CodedSorting.LocalShape.sizeExponent n) buffer work limit hnormal hsepA hwe hl;
        let pb :=
          (swap q).backward reader (CodedSorting.LocalShape.sizeExponent n) buffer work limit hnormal hsepA hwe hl;
        let_fun hr := ⋯;
        let p :=
          CodedSorting.CommonLocalNode.program q reader n source buffer B work limit
            (CodedSorting.CommonLocalRecursion.operation q fuel) (↑pa) (↑pbatch) pf pb hs ⋯ ⋯ hwl hl ⋯ hr;
        let_fun he := ⋯;
        ⟨p.changeFunction he, ⋯⟩)
    fuel n ha hd source buffer limit hs hw hl
```

**继续展开**

- [CodedSorting.LocalSorter.build._proof_122](Program.definitions.md#def-8fa1c5403d8de8fe)
- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalBudget.batchBound](CostBound.definitions.md#def-fd9bae2d2f813ccf)
- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.LocalSorter.build._proof_131](Program.definitions.md#def-46ebe66b364398ea)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.LocalSorter.batchBuild](Program.definitions.md#def-f60b3f2c17655ef0)
- [CodedSorting.LocalSorter.build._proof_118](Program.definitions.md#def-d9b00120e9cd829e)
- [CodedSorting.LocalSorter.build._proof_124](Program.definitions.md#def-1d1ed18f40d9dc19)
- [CodedSorting.LocalSorter.build._proof_123](Program.definitions.md#def-2f2d4a85e712b79d)
- [CodedSorting.CommonResidentRecordProgram.program](../../../Interchange/Framework/Resident/RecordProgram.definitions.md#def-b98c803ea5f33c23)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.LocalSorter.build._proof_126](Program.definitions.md#def-6a4866ecee302044)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program](Program.definitions.md#def-8c86ebfd775e64cc)
- [CodedSorting.LocalSorter.build._proof_127](Program.definitions.md#def-5a463d6703adda06)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.build._proof_136](Program.definitions.md#def-5edced85acb006f8)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.LocalSorter.budget](Program.definitions.md#def-2a45f731bfb4e38e)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.PhysicalLocalSortNode.rows](PhysicalLocalSortNode.definitions.md#def-b825fe6d9317cd2c)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.LocalSorter.build._proof_134](Program.definitions.md#def-751efad9ddffdc5d)
- [CodedSorting.LocalSorter.build._proof_128](Program.definitions.md#def-43d418ff513c6b6f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.LocalSorter.build._proof_129](Program.definitions.md#def-e5763fedbc153c93)
- [CodedSorting.LocalSorter.build._proof_125](Program.definitions.md#def-e6c2071a67f74911)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.LocalSorter.Exchange.backward](Program.definitions.md#def-f7c1a9048ed96238)
- [CodedSorting.LocalSorter.build._proof_121](Program.definitions.md#def-5abeeac929d67472)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.LocalSorter.build._proof_130](Program.definitions.md#def-e340274ff2a4dd3a)
- [CodedSorting.Columnsort.sortColumn](../Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonLocalAdmissible.Admissible](CostBound.definitions.md#def-5a4da9ae621ec1bb)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.LocalSorter.build._proof_116](Program.definitions.md#def-9b0b27a19bcc5d0f)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalRecursion.Descriptors](Program.definitions.md#def-a7cd06ce9a69e356)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.LocalSorter.Exchange.forward](Program.definitions.md#def-b16e0f6352fb0bd0)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.LocalSorter.build._proof_135](Program.definitions.md#def-31b93cf28a636b02)
- [CodedSorting.LocalSorter.build._proof_132](Program.definitions.md#def-8ade94c5c7b4fa0a)
- [CodedSorting.LocalSorter.build._proof_120](Program.definitions.md#def-54e0b1b0ba6cd191)
- [CodedSorting.LocalSorter.build._proof_137](Program.definitions.md#def-9f88280375f46300)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.LocalSorter.build._proof_133](Program.definitions.md#def-98031b88a82a094a)
- [CodedSorting.LocalSorter.build._proof_117](Program.definitions.md#def-83671006b7c59ec0)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.LocalSorter.build._proof_119](Program.definitions.md#def-0ba3c7c9b4ead3dc)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`Nat.recAux`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `dite`, `Subtype.mk`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `Not`, `Nat.decLe`, `letFun`, `instHMul`

<a id="def-f846cf9aeab3889a"></a>
## `CodedSorting.LocalSorter.Machine.operation_eq_sortColumn`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean#L663)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (fuel n : ℕ),
  CodedSorting.CommonLocalRecursion.operation q fuel n = CodedSorting.Columnsort.sortColumn
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Columnsort.sortColumn](../Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)

**基础库名称**

`Nat`, `Fin`, `Eq`

<a id="def-558c55682a2f9dca"></a>
## `CodedSorting.LocalSorter.Machine.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L668)

**类型**

```lean
(swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q) →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin q.inventory.readers →
      (hnormal : (swap q).condition) →
        (fuel n : ℕ) →
          CodedSorting.CommonLocalAdmissible.Admissible q.height fuel n →
            CodedSorting.CommonLocalRecursion.Descriptors q fuel n →
              (source buffer limit : ℕ) →
                source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
                  buffer + CodedSorting.LocalSorter.space swap q hnormal fuel n ≤ limit →
                    limit ≤ q.N ^ q.exponent →
                      CodedSorting.CommonRecordProgram.Program q n source buffer limit
                        CodedSorting.Columnsort.sortColumn
```

**定义**

```lean
fun swap q reader hnormal fuel n ha hd source buffer limit hs hw hl =>
  (↑(CodedSorting.LocalSorter.build swap q reader hnormal fuel n ha hd source buffer limit hs hw hl)).changeFunction ⋯
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.LocalSorter.Machine.operation_eq_sortColumn](Program.definitions.md#def-f846cf9aeab3889a)
- [CodedSorting.LocalSorter.build](Program.definitions.md#def-6731b58c8d479a3d)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.LocalSorter.budget](Program.definitions.md#def-2a45f731bfb4e38e)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Columnsort.sortColumn](../Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonLocalAdmissible.Admissible](CostBound.definitions.md#def-5a4da9ae621ec1bb)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalRecursion.Descriptors](Program.definitions.md#def-a7cd06ce9a69e356)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Subtype.val`

<a id="def-03f81def84d153b3"></a>
## `CodedSorting.LocalSorter.Machine.localProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Program.lean#L718)

**类型**

```lean
(swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q) →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    Fin q.inventory.readers →
      (hnormal : (swap q).condition) →
        (n : ℕ) →
          n ≤ q.height ^ 2 →
            2 ≤ q.exponent →
              (source buffer limit : ℕ) →
                source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
                  buffer + CodedSorting.LocalSorter.space swap q hnormal 3 n ≤ limit →
                    limit ≤ q.N ^ q.exponent →
                      CodedSorting.CommonRecordProgram.Program q n source buffer limit
                        CodedSorting.Columnsort.sortColumn
```

**定义**

```lean
fun swap q reader hnormal n hn he source buffer limit hs hw hl =>
  CodedSorting.LocalSorter.Machine.program swap q reader hnormal 3 n ⋯ ⋯ source buffer limit hs hw hl
```

**继续展开**

- [CodedSorting.LocalSorter.Machine.localProgram._proof_138](Program.definitions.md#def-d6e8b9dde296f10f)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.LocalSorter.Machine.localProgram._proof_139](Program.definitions.md#def-3c402777908963e1)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.LocalSorter.Machine.program](Program.definitions.md#def-558c55682a2f9dca)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Columnsort.sortColumn](../Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-e236c9a11c988414"></a>
## `CodedSorting.CommonLocalNode.program._proof_38`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (n : ℕ), CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n
```

**继续展开**

- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-15feb6f989c4af29"></a>
## `CodedSorting.CommonLocalNode.program._proof_39`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (n : ℕ),
  CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n →
    n ≤ CodedSorting.CommonLocalNode.small n →
      CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n
```

**继续展开**

- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-c39d97b66bd2e869"></a>
## `CodedSorting.CommonLocalNode.program._proof_40`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (n : ℕ),
  CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n →
    CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n
```

**继续展开**

- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-3c680a6fbb3e8851"></a>
## `CodedSorting.CommonLocalNode.program._proof_41`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (x y : ℕ),
  x ≤ y →
    CodedSorting.CommonPermutationPairs.count q (x * (3 * q.w)) ≤
      CodedSorting.CommonPermutationPairs.count q (y * (3 * q.w))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonPermutationPairs.count](../../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-4b1c143055360b86"></a>
## `CodedSorting.CommonLocalNode.program._proof_42`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
                    CodedSorting.CommonLocalNode.half n =
                  CodedSorting.CommonLocalNode.large n →
                (∀ (x y : ℕ),
                    x ≤ y →
                      CodedSorting.CommonRecordProgram.recordBlocks q x ≤
                        CodedSorting.CommonRecordProgram.recordBlocks q y) →
                  CodedSorting.CommonRecordProgram.recordBlocks q
                      (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
                    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Eq`

<a id="def-79b3e68371040493"></a>
## `CodedSorting.CommonLocalNode.program._proof_43`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A B work limit : ℕ),
  source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A →
    work ≤ limit →
      limit ≤ q.N ^ q.exponent →
        A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B →
          B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
            CodedSorting.CommonRecordProgram.recordBlocks q n ≤
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) →
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
                  CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
                CodedSorting.CommonRecordProgram.recordBlocks q
                      (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
                    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
                  source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-deb87b79c7dcdbc1"></a>
## `CodedSorting.CommonLocalNode.program._proof_44`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ∀ (A B work limit : ℕ),
      work ≤ limit →
        limit ≤ q.N ^ q.exponent →
          A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B →
            B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
              A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
                q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-1a5f6d2bf557879d"></a>
## `CodedSorting.CommonLocalNode.program._proof_45`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ∀ (B work limit : ℕ),
        work ≤ limit →
          limit ≤ q.N ^ q.exponent →
            B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
              B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤
                q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-5e86adf0d00942c3"></a>
## `CodedSorting.CommonLocalNode.program._proof_46`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits →
              CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
                    CodedSorting.CommonLocalNode.half n =
                  CodedSorting.CommonLocalNode.large n →
                ∀ (L N R O : ℕ),
                  L ≤ CodedSorting.CommonLocalNode.large n →
                    N ≤ CodedSorting.CommonLocalNode.large n →
                      R ≤ CodedSorting.CommonLocalNode.large n →
                        O ≤ CodedSorting.CommonLocalNode.large n →
                          3 * L < (2 ^ q.w) ^ q.digits ∧
                            3 * N < (2 ^ q.w) ^ q.digits ∧ 3 * R < (2 ^ q.w) ^ q.digits ∧ 3 * O < (2 ^ q.w) ^ q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-3422ccbb4127dcc4"></a>
## `CodedSorting.CommonLocalNode.program._proof_47`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ∀ (A B work : ℕ),
      ℕ →
        A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B →
          B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
            CodedSorting.CommonRecordProgram.recordBlocks q n ≤
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) →
              CodedSorting.CommonRecordProgram.recordBlocks q
                    (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
                  CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
                A ≤ work
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-22e32545a544538c"></a>
## `CodedSorting.CommonLocalNode.program._proof_48`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ∀ (A B : ℕ),
      ℕ →
        ℕ →
          A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B → A ≤ B
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-f46c49c52bdc5965"></a>
## `CodedSorting.CommonLocalNode.program._proof_49`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A B work limit : ℕ),
  work ≤ limit →
    B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
          CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
        A ≤ B →
          ∀ (x : Fin (q.N ^ q.exponent)),
            ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
              ↑x < A ∨ limit ≤ ↑x →
                ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-aef2a7bfc2c8c435"></a>
## `CodedSorting.CommonLocalNode.program._proof_50`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A B work limit : ℕ),
  work ≤ limit →
    B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
      A ≤ B →
        ∀ (x : Fin (q.N ^ q.exponent)),
          ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
            ↑x < A ∨ limit ≤ ↑x →
              ↑x < B ∨ B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ ↑x
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-c615d89c718200ee"></a>
## `CodedSorting.CommonLocalNode.program._proof_51`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ∀ (n : ℕ), ℕ → ℕ → ℕ → ℕ → ℕ → 0 + n ≤ n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-0fcdcb2912c6e1de"></a>
## `CodedSorting.CommonLocalNode.program._proof_52`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            n ≤ CodedSorting.CommonLocalNode.small n →
              CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n →
                CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
                      CodedSorting.CommonLocalNode.half n =
                    CodedSorting.CommonLocalNode.large n →
                  (∀ (L N R O : ℕ),
                      L ≤ CodedSorting.CommonLocalNode.large n →
                        N ≤ CodedSorting.CommonLocalNode.large n →
                          R ≤ CodedSorting.CommonLocalNode.large n →
                            O ≤ CodedSorting.CommonLocalNode.large n →
                              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)) →
                    CodedSorting.CommonStaticMargins.ShapeFits q (3 * 0) (3 * n)
                      (3 * (CodedSorting.CommonLocalNode.small n - n)) (3 * 0)
```

**继续展开**

- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-d5a555e58fe1d3eb"></a>
## `CodedSorting.CommonLocalNode.program._proof_53`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A : ℕ),
  ℕ →
    ∀ (work limit : ℕ),
      source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A →
        work ≤ limit →
          limit ≤ q.N ^ q.exponent →
            A ≤ work →
              source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * n)) ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-6854585bae4dbf52"></a>
## `CodedSorting.CommonLocalNode.program._proof_54`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ∀ (A : ℕ),
      ℕ →
        ℕ →
          ℕ →
            n ≤ CodedSorting.CommonLocalNode.small n →
              A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
                  q.N ^ q.exponent →
                A +
                    CodedSorting.CommonRecordProgram.recordBlocks q
                      (0 + n + (CodedSorting.CommonLocalNode.small n - n)) ≤
                  q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-64726af18ac826b9"></a>
## `CodedSorting.CommonLocalNode.program._proof_55`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A : ℕ),
  source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A →
    source + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * n)) ≤ A ∨
      A + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + (CodedSorting.CommonLocalNode.small n - n)) ≤ source
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `Or`, `OfNat.ofNat`, `instHMul`

<a id="def-52f2ff36340d79cd"></a>
## `CodedSorting.CommonLocalNode.program._proof_56`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A limit : ℕ),
  n ≤ CodedSorting.CommonLocalNode.small n →
    (∀ (x : Fin (q.N ^ q.exponent)),
        ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
          ↑x < A ∨ limit ≤ ↑x →
            ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x) →
      ∀ (a : Fin (q.N ^ q.exponent)),
        ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
          ↑a < A ∨ limit ≤ ↑a →
            ↑a < A ∨
              A + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + (CodedSorting.CommonLocalNode.small n - n)) ≤
                ↑a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-3e23013b1db55e66"></a>
## `CodedSorting.CommonLocalNode.program._proof_57`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ∀ (n : ℕ),
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            ℕ →
              n ≤ CodedSorting.CommonLocalNode.small n →
                0 + n + (CodedSorting.CommonLocalNode.small n - n) = CodedSorting.CommonLocalNode.small n
```

**继续展开**

- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HSub.hSub`, `instSubNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`

<a id="def-72175b577656778c"></a>
## `CodedSorting.CommonLocalNode.program._proof_58`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A B work limit : ℕ)
  (hn : n ≤ CodedSorting.CommonLocalNode.small n),
  CodedSorting.CommonRecordReindex.castRecords ⋯ ∘
      CodedSorting.CommonStaticMarginsRecords.margin 0 n (CodedSorting.CommonLocalNode.small n - n) 0 ⋯ =
    CodedSorting.RecursiveColumnsort.pad
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_57](Program.definitions.md#def-3e23013b1db55e66)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.program._proof_51](Program.definitions.md#def-c615d89c718200ee)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`HSub.hSub`, `Function.comp`, `instSubNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-b5b3d09b1956ff16"></a>
## `CodedSorting.CommonLocalNode.program._proof_59`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ∀ (A B work limit : ℕ),
      work ≤ limit →
        B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
          CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
            A ≤ B → A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ limit
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-0b01b0e36c90a84d"></a>
## `CodedSorting.CommonLocalNode.program._proof_60`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ∀ (n : ℕ), ℕ → ℕ → ℕ → ℕ → ℕ → 0 + CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.small n
```

**继续展开**

- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-605ab56b0f4e5ed4"></a>
## `CodedSorting.CommonLocalNode.program._proof_61`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n →
                CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
                      CodedSorting.CommonLocalNode.half n =
                    CodedSorting.CommonLocalNode.large n →
                  (∀ (L N R O : ℕ),
                      L ≤ CodedSorting.CommonLocalNode.large n →
                        N ≤ CodedSorting.CommonLocalNode.large n →
                          R ≤ CodedSorting.CommonLocalNode.large n →
                            O ≤ CodedSorting.CommonLocalNode.large n →
                              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)) →
                    CodedSorting.CommonStaticMargins.ShapeFits q (3 * CodedSorting.CommonLocalNode.half n)
                      (3 * CodedSorting.CommonLocalNode.small n) (3 * CodedSorting.CommonLocalNode.half n) (3 * 0)
```

**继续展开**

- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-ef93f65db18d7e32"></a>
## `CodedSorting.CommonLocalNode.program._proof_62`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ∀ (A B : ℕ),
      ℕ →
        ℕ →
          A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B →
            B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤
                q.N ^ q.exponent →
              A +
                  max 1
                    (CodedSorting.PhysicalStreamCursor.blockCount q.block
                      (3 * 0 + 3 * CodedSorting.CommonLocalNode.small n)) ≤
                q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-b5d288a28356219c"></a>
## `CodedSorting.CommonLocalNode.program._proof_63`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n B : ℕ),
  CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n →
    B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ q.N ^ q.exponent →
      B +
          CodedSorting.CommonRecordProgram.recordBlocks q
            (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
              CodedSorting.CommonLocalNode.half n) ≤
        q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Eq`

<a id="def-2e1ce65559baedfe"></a>
## `CodedSorting.CommonLocalNode.program._proof_64`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n A B : ℕ),
  A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B →
    A +
          max 1
            (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * CodedSorting.CommonLocalNode.small n)) ≤
        B ∨
      B +
          CodedSorting.CommonRecordProgram.recordBlocks q
            (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
              CodedSorting.CommonLocalNode.half n) ≤
        A
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `Or`, `OfNat.ofNat`, `instHMul`

<a id="def-c23f548d23b23e46"></a>
## `CodedSorting.CommonLocalNode.program._proof_65`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A B limit : ℕ),
  CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n →
    (∀ (x : Fin (q.N ^ q.exponent)),
        ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
          ↑x < A ∨ limit ≤ ↑x →
            ↑x < B ∨ B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ ↑x) →
      ∀ (a : Fin (q.N ^ q.exponent)),
        ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
          ↑a < A ∨ limit ≤ ↑a →
            ↑a < B ∨
              B +
                  CodedSorting.CommonRecordProgram.recordBlocks q
                    (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
                      CodedSorting.CommonLocalNode.half n) ≤
                ↑a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`

<a id="def-b76263befde85225"></a>
## `CodedSorting.CommonLocalNode.program._proof_66`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A B work limit : ℕ),
  CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n →
    ∀
      (hbh :
        CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
            CodedSorting.CommonLocalNode.half n =
          CodedSorting.CommonLocalNode.large n),
      CodedSorting.CommonRecordReindex.castRecords hbh ∘
          CodedSorting.CommonStaticMarginsRecords.margin (CodedSorting.CommonLocalNode.half n)
            (CodedSorting.CommonLocalNode.small n) (CodedSorting.CommonLocalNode.half n) 0 ⋯ =
        CodedSorting.CommonLocalSemantic.shift (CodedSorting.CommonLocalNode.side n)
          (CodedSorting.CommonLocalNode.rowCount n) (CodedSorting.CommonLocalNode.half n)
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.program._proof_60](Program.definitions.md#def-0b01b0e36c90a84d)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`HMul.hMul`, `Function.comp`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-ef3313ca36de27be"></a>
## `CodedSorting.CommonLocalNode.program._proof_67`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ∀ (B work limit : ℕ),
        work ≤ limit →
          B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
            B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ limit
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-4c765b794e21177a"></a>
## `CodedSorting.CommonLocalNode.program._proof_68`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ∀ (n : ℕ),
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            ℕ →
              CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n →
                CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
                      CodedSorting.CommonLocalNode.half n =
                    CodedSorting.CommonLocalNode.large n →
                  CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n ≤
                    CodedSorting.CommonLocalNode.large n
```

**继续展开**

- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Eq`

<a id="def-a7637ff94026cf84"></a>
## `CodedSorting.CommonLocalNode.program._proof_69`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n →
                CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
                      CodedSorting.CommonLocalNode.half n =
                    CodedSorting.CommonLocalNode.large n →
                  (∀ (L N R O : ℕ),
                      L ≤ CodedSorting.CommonLocalNode.large n →
                        N ≤ CodedSorting.CommonLocalNode.large n →
                          R ≤ CodedSorting.CommonLocalNode.large n →
                            O ≤ CodedSorting.CommonLocalNode.large n →
                              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)) →
                    CodedSorting.CommonStaticMargins.ShapeFits q (3 * 0) (3 * CodedSorting.CommonLocalNode.small n)
                      (3 * 0) (3 * CodedSorting.CommonLocalNode.half n)
```

**继续展开**

- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-3801261deb2e34d9"></a>
## `CodedSorting.CommonLocalNode.program._proof_70`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ∀ (B work limit : ℕ),
        work ≤ limit →
          limit ≤ q.N ^ q.exponent →
            B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
              CodedSorting.CommonRecordProgram.recordBlocks q
                    (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
                  CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
                B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤
                    q.N ^ q.exponent →
                  B +
                      max 1
                        (CodedSorting.PhysicalStreamCursor.blockCount q.block
                          (3 * CodedSorting.CommonLocalNode.half n + 3 * CodedSorting.CommonLocalNode.small n)) ≤
                    q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-62b85bcc4e9489d6"></a>
## `CodedSorting.CommonLocalNode.program._proof_71`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n A : ℕ),
  A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ q.N ^ q.exponent →
    A + CodedSorting.CommonRecordProgram.recordBlocks q (0 + CodedSorting.CommonLocalNode.small n + 0) ≤
      q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-60b497b31ca95168"></a>
## `CodedSorting.CommonLocalNode.program._proof_72`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ∀ (A B : ℕ),
      ℕ →
        ℕ →
          A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B →
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
              A ≤ B →
                B +
                      max 1
                        (CodedSorting.PhysicalStreamCursor.blockCount q.block
                          (3 * CodedSorting.CommonLocalNode.half n + 3 * CodedSorting.CommonLocalNode.small n)) ≤
                    A ∨
                  A + CodedSorting.CommonRecordProgram.recordBlocks q (0 + CodedSorting.CommonLocalNode.small n + 0) ≤ B
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `Or`, `OfNat.ofNat`, `instHMul`

<a id="def-02c2547d656d731e"></a>
## `CodedSorting.CommonLocalNode.program._proof_73`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A limit : ℕ),
  (∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x) →
    ∀ (a : Fin (q.N ^ q.exponent)),
      ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
        ↑a < A ∨ limit ≤ ↑a →
          ↑a < A ∨
            A + CodedSorting.CommonRecordProgram.recordBlocks q (0 + CodedSorting.CommonLocalNode.small n + 0) ≤ ↑a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-33b88d1c13a04999"></a>
## `CodedSorting.CommonLocalNode.program._proof_74`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ∀ (n : ℕ), ℕ → ℕ → ℕ → ℕ → ℕ → 0 + CodedSorting.CommonLocalNode.small n + 0 = CodedSorting.CommonLocalNode.small n
```

**继续展开**

- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`

<a id="def-196683c06b23f341"></a>
## `CodedSorting.CommonLocalNode.program._proof_75`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A B work limit : ℕ),
  CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n →
    ∀ (hab : CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n)
      (hbh :
        CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
            CodedSorting.CommonLocalNode.half n =
          CodedSorting.CommonLocalNode.large n),
      CodedSorting.CommonRecordReindex.castRecords ⋯ ∘
          CodedSorting.CommonStaticMarginsRecords.margin 0 (CodedSorting.CommonLocalNode.small n) 0
            (CodedSorting.CommonLocalNode.half n) ⋯ =
        CodedSorting.CommonLocalSemantic.unshift (CodedSorting.CommonLocalNode.side n)
          (CodedSorting.CommonLocalNode.rowCount n) (CodedSorting.CommonLocalNode.half n)
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalNode.program._proof_68](Program.definitions.md#def-4c765b794e21177a)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalNode.program._proof_74](Program.definitions.md#def-33b88d1c13a04999)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`HMul.hMul`, `Function.comp`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-06adeb1e4d2e683b"></a>
## `CodedSorting.CommonLocalNode.program._proof_76`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration →
  ∀ (n : ℕ), ℕ → ℕ → ℕ → ℕ → ℕ → n ≤ CodedSorting.CommonLocalNode.small n → 0 + n ≤ CodedSorting.CommonLocalNode.small n
```

**继续展开**

- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-5c37dca9e74f828c"></a>
## `CodedSorting.CommonLocalNode.program._proof_77`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ℕ →
      ℕ →
        ℕ →
          ℕ →
            n ≤ CodedSorting.CommonLocalNode.small n →
              CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n →
                CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n +
                      CodedSorting.CommonLocalNode.half n =
                    CodedSorting.CommonLocalNode.large n →
                  (∀ (L N R O : ℕ),
                      L ≤ CodedSorting.CommonLocalNode.large n →
                        N ≤ CodedSorting.CommonLocalNode.large n →
                          R ≤ CodedSorting.CommonLocalNode.large n →
                            O ≤ CodedSorting.CommonLocalNode.large n →
                              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O)) →
                    CodedSorting.CommonStaticMargins.ShapeFits q (3 * 0) (3 * n) (3 * 0) (3 * 0)
```

**继续展开**

- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-10cfff12bcca7add"></a>
## `CodedSorting.CommonLocalNode.program._proof_78`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ℕ →
    ∀ (A B work limit : ℕ),
      work ≤ limit →
        limit ≤ q.N ^ q.exponent →
          B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work →
            CodedSorting.CommonRecordProgram.recordBlocks q n ≤
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) →
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
                  CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
                A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
                    q.N ^ q.exponent →
                  B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤
                      q.N ^ q.exponent →
                    A ≤ work →
                      A ≤ B →
                        A + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * n)) ≤
                          q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-461c2ae95bcc6338"></a>
## `CodedSorting.CommonLocalNode.program._proof_79`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source : ℕ),
  source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent →
    source + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + 0) ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-f75a6ac053908c84"></a>
## `CodedSorting.CommonLocalNode.program._proof_80`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A : ℕ),
  ℕ →
    ℕ →
      ℕ →
        source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A →
          CodedSorting.CommonRecordProgram.recordBlocks q n ≤
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) →
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
                CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) →
              A + max 1 (CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * 0 + 3 * n)) ≤ source ∨
                source + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + 0) ≤ A
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `Or`, `OfNat.ofNat`, `instHMul`

<a id="def-e8628ad34481cde3"></a>
## `CodedSorting.CommonLocalNode.program._proof_81`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A limit : ℕ) (x : Fin (q.N ^ q.exponent)),
  ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
    ↑x < A ∨ limit ≤ ↑x → ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q (0 + n + 0) ≤ ↑x
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`

<a id="def-0a7304d95c3d81a1"></a>
## `CodedSorting.CommonLocalNode.program._proof_82`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ∀ (n : ℕ), ℕ → ℕ → ℕ → ℕ → ℕ → 0 + n + 0 = n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`

<a id="def-2ab0b7ea5c0eaf85"></a>
## `CodedSorting.CommonLocalNode.program._proof_83`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n source A B work limit : ℕ)
  (hn : n ≤ CodedSorting.CommonLocalNode.small n),
  CodedSorting.CommonRecordReindex.castRecords ⋯ ∘ CodedSorting.CommonStaticMarginsRecords.margin 0 n 0 0 ⋯ =
    CodedSorting.RecursiveColumnsort.trim hn
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_76](Program.definitions.md#def-06adeb1e4d2e683b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.program._proof_82](Program.definitions.md#def-0a7304d95c3d81a1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)

**基础库名称**

`Function.comp`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-0a92d0f5df03afed"></a>
## `CodedSorting.CommonLocalNode.program._proof_84`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (n source A B work limit : ℕ)
  (op : CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w))
  (pA :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pB :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.large n) B work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n + 1)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pf :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (pb :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hr : CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n)
  (hAB : A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B)
  (hBW : B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work)
  (hn : n ≤ CodedSorting.CommonLocalNode.small n)
  (hab : CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n)
  (hh : CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n)
  (hbh :
    CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n)
  (hna :
    CodedSorting.CommonRecordProgram.recordBlocks q n ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n))
  (habc :
    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hhc :
    CodedSorting.CommonRecordProgram.recordBlocks q
        (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hSA : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hAcap :
    A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ q.N ^ q.exponent)
  (hBcap :
    B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ q.N ^ q.exponent)
  (hshape' :
    ∀ (L N R O : ℕ),
      L ≤ CodedSorting.CommonLocalNode.large n →
        N ≤ CodedSorting.CommonLocalNode.large n →
          R ≤ CodedSorting.CommonLocalNode.large n →
            O ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O))
  (hwA : A ≤ work) (hAB' : A ≤ B)
  (hframeA :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x)
  (hframeB :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < B ∨ B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ ↑x),
  ((((((((((((CodedSorting.CommonRecordTransform.margins q reader 0 n (CodedSorting.CommonLocalNode.small n - n) 0
                                                    source A source n A limit ⋯ ⋯ hSA ⋯ ⋯ ⋯ ⋯).castOutput
                                                ⋯).changeFunction
                                            ⋯).append
                                        (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                    (CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯ hwA)).append
                                (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                            (CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA)).append
                        (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                    (((CodedSorting.CommonRecordTransform.margins q reader (CodedSorting.CommonLocalNode.half n)
                              (CodedSorting.CommonLocalNode.small n) (CodedSorting.CommonLocalNode.half n) 0 A B source
                              n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯ ⋯).castOutput
                          hbh).changeFunction
                      ⋯)).append
                (CodedSorting.CommonRecordTransform.workspaceProgram q pB hAB' ⋯ hwA)).append
            (((CodedSorting.CommonRecordTransform.margins q reader 0 (CodedSorting.CommonLocalNode.small n) 0
                      (CodedSorting.CommonLocalNode.half n) B A source n A limit ⋯ ⋯ hBcap ⋯ ⋯ ⋯ ⋯).castOutput
                  ⋯).changeFunction
              ⋯)).append
        (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 A source source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯
                  ⋯).castOutput
              ⋯).changeFunction
          ⋯)).charge =
    3 * pA.charge + pB.charge + pf.charge + pb.charge +
      3 *
        (2 * CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) +
            CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) +
          CodedSorting.CommonRecordProgram.recordBlocks q n)
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_67](Program.definitions.md#def-ef3313ca36de27be)
- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalNode.program._proof_80](Program.definitions.md#def-f75a6ac053908c84)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](../../../Shared/Records/Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](../../../Shared/Records/Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalNode.program._proof_68](Program.definitions.md#def-4c765b794e21177a)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTransform.workspaceProgram](../../../Shared/Records/Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonLocalNode.program._proof_62](Program.definitions.md#def-ef93f65db18d7e32)
- [CodedSorting.CommonLocalNode.program._proof_57](Program.definitions.md#def-3e23013b1db55e66)
- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.program._proof_76](Program.definitions.md#def-06adeb1e4d2e683b)
- [CodedSorting.CommonRecordTransform.margins](../../../Shared/Records/Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonLocalNode.program._proof_81](Program.definitions.md#def-e8628ad34481cde3)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalNode.program._proof_64](Program.definitions.md#def-2e1ce65559baedfe)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program._proof_61](Program.definitions.md#def-605ab56b0f4e5ed4)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLocalNode.program._proof_54](Program.definitions.md#def-6854585bae4dbf52)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.program._proof_75](Program.definitions.md#def-196683c06b23f341)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.program._proof_55](Program.definitions.md#def-64726af18ac826b9)
- [CodedSorting.CommonLocalNode.program._proof_82](Program.definitions.md#def-0a7304d95c3d81a1)
- [CodedSorting.CommonLocalNode.program._proof_66](Program.definitions.md#def-b76263befde85225)
- [CodedSorting.CommonLocalNode.program._proof_53](Program.definitions.md#def-d5a555e58fe1d3eb)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.program._proof_60](Program.definitions.md#def-0b01b0e36c90a84d)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalNode.program._proof_59](Program.definitions.md#def-b5b3d09b1956ff16)
- [CodedSorting.CommonRecordTransform.Stage.append](../../../Shared/Records/Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonLocalNode.program._proof_73](Program.definitions.md#def-02c2547d656d731e)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalNode.program._proof_74](Program.definitions.md#def-33b88d1c13a04999)
- [CodedSorting.CommonLocalNode.program._proof_79](Program.definitions.md#def-461c2ae95bcc6338)
- [CodedSorting.CommonLocalNode.program._proof_69](Program.definitions.md#def-a7637ff94026cf84)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonLocalNode.program._proof_83](Program.definitions.md#def-2ab0b7ea5c0eaf85)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonLocalNode.program._proof_71](Program.definitions.md#def-62b85bcc4e9489d6)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonLocalNode.program._proof_56](Program.definitions.md#def-52f2ff36340d79cd)
- [CodedSorting.CommonLocalNode.program._proof_77](Program.definitions.md#def-5c37dca9e74f828c)
- [CodedSorting.CommonLocalNode.program._proof_70](Program.definitions.md#def-3801261deb2e34d9)
- [CodedSorting.CommonLocalNode.program._proof_65](Program.definitions.md#def-c23f548d23b23e46)
- [CodedSorting.CommonRecordTransform.Stage.charge](../../../Shared/Records/Transform.definitions.md#def-30123232aa6eccd6)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonLocalNode.program._proof_63](Program.definitions.md#def-b5d288a28356219c)
- [CodedSorting.CommonLocalNode.program._proof_72](Program.definitions.md#def-60b497b31ca95168)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalNode.program._proof_52](Program.definitions.md#def-0fcdcb2912c6e1de)
- [CodedSorting.CommonLocalNode.program._proof_78](Program.definitions.md#def-10cfff12bcca7add)
- [CodedSorting.CommonLocalNode.program._proof_58](Program.definitions.md#def-72175b577656778c)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.CommonLocalNode.program._proof_51](Program.definitions.md#def-c615d89c718200ee)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_refl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-6dd4c902f089038e"></a>
## `CodedSorting.CommonLocalNode.program._proof_85`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ)
  (op : CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w))
  (hn : n ≤ CodedSorting.CommonLocalNode.small n),
  CodedSorting.RecursiveColumnsort.trim hn ∘
      CodedSorting.CommonLocalSemantic.unshift (CodedSorting.CommonLocalNode.side n)
          (CodedSorting.CommonLocalNode.rowCount n) (CodedSorting.CommonLocalNode.half n) ∘
        CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n + 1)
            (CodedSorting.CommonLocalNode.rowCount n) ∘
          CodedSorting.CommonLocalSemantic.shift (CodedSorting.CommonLocalNode.side n)
              (CodedSorting.CommonLocalNode.rowCount n) (CodedSorting.CommonLocalNode.half n) ∘
            CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
                (CodedSorting.CommonLocalNode.rowCount n) ∘
              CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (CodedSorting.CommonLocalNode.side n) ∘
                CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
                    (CodedSorting.CommonLocalNode.rowCount n) ∘
                  CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (CodedSorting.CommonLocalNode.side n) ∘
                    CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
                        (CodedSorting.CommonLocalNode.rowCount n) ∘
                      CodedSorting.RecursiveColumnsort.pad =
    CodedSorting.CommonLocalSemantic.pipeline op n
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`Function.comp`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`

<a id="def-fc5c0e63f9bb67e3"></a>
## `CodedSorting.CommonLocalNode.program._proof_86`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (n source A B work limit : ℕ)
  (op : CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w))
  (pA :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pB :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.large n) B work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n + 1)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pf :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (pb :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hr : CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n)
  (hAB : A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B)
  (hBW : B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work)
  (hn : n ≤ CodedSorting.CommonLocalNode.small n)
  (hab : CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n)
  (hh : CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n)
  (hbh :
    CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n)
  (hna :
    CodedSorting.CommonRecordProgram.recordBlocks q n ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n))
  (habc :
    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hhc :
    CodedSorting.CommonRecordProgram.recordBlocks q
        (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hSA : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hAcap :
    A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ q.N ^ q.exponent)
  (hBcap :
    B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ q.N ^ q.exponent)
  (hshape' :
    ∀ (L N R O : ℕ),
      L ≤ CodedSorting.CommonLocalNode.large n →
        N ≤ CodedSorting.CommonLocalNode.large n →
          R ≤ CodedSorting.CommonLocalNode.large n →
            O ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O))
  (hwA : A ≤ work) (hAB' : A ≤ B)
  (hframeA :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x)
  (hframeB :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < B ∨ B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ ↑x)
  (s : CodedSorting.CommonLeafProgram.Machine q) (f : CodedSorting.CommonRecordProgram.Records q n),
  CodedSorting.CommonRecordProgram.Encoded q s.disk source f →
    CodedSorting.CommonRecordProgram.Encoded q
      (CodedSorting.CommonStaticSchedule.executeRaw q
            (((((((((((((CodedSorting.CommonRecordTransform.margins q reader 0 n
                                                                  (CodedSorting.CommonLocalNode.small n - n) 0 source A
                                                                  source n A limit ⋯ ⋯ hSA ⋯ ⋯ ⋯ ⋯).castOutput
                                                              ⋯).changeFunction
                                                          ⋯).append
                                                      (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯
                                                        hwA)).append
                                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯
                                                    hwA)).append
                                              (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                          (CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA)).append
                                      (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                  (((CodedSorting.CommonRecordTransform.margins q reader
                                            (CodedSorting.CommonLocalNode.half n) (CodedSorting.CommonLocalNode.small n)
                                            (CodedSorting.CommonLocalNode.half n) 0 A B source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯
                                            ⋯).castOutput
                                        hbh).changeFunction
                                    ⋯)).append
                              (CodedSorting.CommonRecordTransform.workspaceProgram q pB hAB' ⋯ hwA)).append
                          (((CodedSorting.CommonRecordTransform.margins q reader 0
                                    (CodedSorting.CommonLocalNode.small n) 0 (CodedSorting.CommonLocalNode.half n) B A
                                    source n A limit ⋯ ⋯ hBcap ⋯ ⋯ ⋯ ⋯).castOutput
                                ⋯).changeFunction
                            ⋯)).append
                      (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 A source source n A limit ⋯ ⋯ hAcap
                                ⋯ ⋯ ⋯ ⋯).castOutput
                            ⋯).changeFunction
                        ⋯)).toProgram.changeFunction
                ⋯).instructions
            s).1.disk
      source (CodedSorting.CommonLocalSemantic.pipeline op n f)
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_67](Program.definitions.md#def-ef3313ca36de27be)
- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalNode.program._proof_80](Program.definitions.md#def-f75a6ac053908c84)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](../../../Shared/Records/Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](../../../Shared/Records/Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalNode.program._proof_68](Program.definitions.md#def-4c765b794e21177a)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonRecordTransform.workspaceProgram](../../../Shared/Records/Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonLocalNode.program._proof_62](Program.definitions.md#def-ef93f65db18d7e32)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](../../../Shared/Records/Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonLocalNode.program._proof_57](Program.definitions.md#def-3e23013b1db55e66)
- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.program._proof_76](Program.definitions.md#def-06adeb1e4d2e683b)
- [CodedSorting.CommonRecordTransform.margins](../../../Shared/Records/Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonLocalNode.program._proof_81](Program.definitions.md#def-e8628ad34481cde3)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonRecordProgram.Encoded](../../../Shared/Records/RecordOperations.definitions.md#def-f604a7bec7bf567e)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalNode.program._proof_64](Program.definitions.md#def-2e1ce65559baedfe)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program._proof_61](Program.definitions.md#def-605ab56b0f4e5ed4)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLocalNode.program._proof_54](Program.definitions.md#def-6854585bae4dbf52)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.program._proof_75](Program.definitions.md#def-196683c06b23f341)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.program._proof_55](Program.definitions.md#def-64726af18ac826b9)
- [CodedSorting.CommonLocalNode.program._proof_82](Program.definitions.md#def-0a7304d95c3d81a1)
- [CodedSorting.CommonLocalNode.program._proof_66](Program.definitions.md#def-b76263befde85225)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonLocalNode.program._proof_53](Program.definitions.md#def-d5a555e58fe1d3eb)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.program._proof_60](Program.definitions.md#def-0b01b0e36c90a84d)
- [CodedSorting.CommonLocalNode.program._proof_85](Program.definitions.md#def-6dd4c902f089038e)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonLocalNode.program._proof_59](Program.definitions.md#def-b5b3d09b1956ff16)
- [CodedSorting.CommonRecordTransform.Stage.append](../../../Shared/Records/Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonLocalNode.program._proof_73](Program.definitions.md#def-02c2547d656d731e)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalNode.program._proof_74](Program.definitions.md#def-33b88d1c13a04999)
- [CodedSorting.CommonLocalNode.program._proof_79](Program.definitions.md#def-461c2ae95bcc6338)
- [CodedSorting.CommonLocalNode.program._proof_69](Program.definitions.md#def-a7637ff94026cf84)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonLocalNode.program._proof_83](Program.definitions.md#def-2ab0b7ea5c0eaf85)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLocalNode.program._proof_71](Program.definitions.md#def-62b85bcc4e9489d6)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonLocalNode.program._proof_56](Program.definitions.md#def-52f2ff36340d79cd)
- [CodedSorting.CommonLocalNode.program._proof_77](Program.definitions.md#def-5c37dca9e74f828c)
- [CodedSorting.CommonLocalNode.program._proof_70](Program.definitions.md#def-3801261deb2e34d9)
- [CodedSorting.CommonLocalNode.program._proof_65](Program.definitions.md#def-c23f548d23b23e46)
- [CodedSorting.CommonLocalNode.program._proof_63](Program.definitions.md#def-b5d288a28356219c)
- [CodedSorting.CommonLocalNode.program._proof_72](Program.definitions.md#def-60b497b31ca95168)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonLocalNode.program._proof_52](Program.definitions.md#def-0fcdcb2912c6e1de)
- [CodedSorting.CommonLocalNode.program._proof_78](Program.definitions.md#def-10cfff12bcca7add)
- [CodedSorting.CommonLocalNode.program._proof_58](Program.definitions.md#def-72175b577656778c)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.CommonLocalNode.program._proof_51](Program.definitions.md#def-c615d89c718200ee)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`le_refl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-66662a918baf0b36"></a>
## `CodedSorting.CommonLocalNode.program._proof_87`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (n source A B work limit : ℕ)
  (op : CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w))
  (pA :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pB :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.large n) B work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n + 1)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pf :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (pb :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hr : CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n)
  (hAB : A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B)
  (hBW : B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work)
  (hn : n ≤ CodedSorting.CommonLocalNode.small n)
  (hab : CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n)
  (hh : CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n)
  (hbh :
    CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n)
  (hna :
    CodedSorting.CommonRecordProgram.recordBlocks q n ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n))
  (habc :
    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hhc :
    CodedSorting.CommonRecordProgram.recordBlocks q
        (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hSA : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hAcap :
    A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ q.N ^ q.exponent)
  (hBcap :
    B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ q.N ^ q.exponent)
  (hshape' :
    ∀ (L N R O : ℕ),
      L ≤ CodedSorting.CommonLocalNode.large n →
        N ≤ CodedSorting.CommonLocalNode.large n →
          R ≤ CodedSorting.CommonLocalNode.large n →
            O ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O))
  (hwA : A ≤ work) (hAB' : A ≤ B)
  (hframeA :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x)
  (hframeB :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < B ∨ B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ ↑x)
  (s : CodedSorting.CommonLeafProgram.Machine q) (a : Fin (q.N ^ q.exponent)),
  ↑a < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑a →
    ↑a < A ∨ limit ≤ ↑a →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                ((((((((((((⋯.castOutput ⋯).changeFunction ⋯).append
                                                          (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯
                                                            hwA)).append
                                                      (CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯
                                                        hwA)).append
                                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯
                                                    hwA)).append
                                              (CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA)).append
                                          (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                      (((CodedSorting.CommonRecordTransform.margins q reader
                                                (CodedSorting.CommonLocalNode.half n)
                                                (CodedSorting.CommonLocalNode.small n)
                                                (CodedSorting.CommonLocalNode.half n) 0 A B source n A limit ⋯ ⋯ hAcap ⋯
                                                ⋯ ⋯ ⋯).castOutput
                                            hbh).changeFunction
                                        ⋯)).append
                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pB hAB' ⋯ hwA)).append
                              (((CodedSorting.CommonRecordTransform.margins q reader 0
                                        (CodedSorting.CommonLocalNode.small n) 0 (CodedSorting.CommonLocalNode.half n) B
                                        A source n A limit ⋯ ⋯ hBcap ⋯ ⋯ ⋯ ⋯).castOutput
                                    ⋯).changeFunction
                                ⋯)).append
                          (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 A source source n A limit ⋯ ⋯
                                    hAcap ⋯ ⋯ ⋯ ⋯).castOutput
                                ⋯).changeFunction
                            ⋯)).toProgram.changeFunction
                    ⋯).instructions
                s).1.disk
          a =
        s.disk a
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_67](Program.definitions.md#def-ef3313ca36de27be)
- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalNode.program._proof_80](Program.definitions.md#def-f75a6ac053908c84)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](../../../Shared/Records/Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](../../../Shared/Records/Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalNode.program._proof_68](Program.definitions.md#def-4c765b794e21177a)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonRecordTransform.workspaceProgram](../../../Shared/Records/Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonLocalNode.program._proof_62](Program.definitions.md#def-ef93f65db18d7e32)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](../../../Shared/Records/Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonLocalNode.program._proof_57](Program.definitions.md#def-3e23013b1db55e66)
- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.program._proof_76](Program.definitions.md#def-06adeb1e4d2e683b)
- [CodedSorting.CommonRecordTransform.margins](../../../Shared/Records/Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonLocalNode.program._proof_81](Program.definitions.md#def-e8628ad34481cde3)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalNode.program._proof_64](Program.definitions.md#def-2e1ce65559baedfe)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program._proof_61](Program.definitions.md#def-605ab56b0f4e5ed4)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLocalNode.program._proof_54](Program.definitions.md#def-6854585bae4dbf52)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.program._proof_75](Program.definitions.md#def-196683c06b23f341)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.program._proof_55](Program.definitions.md#def-64726af18ac826b9)
- [CodedSorting.CommonLocalNode.program._proof_82](Program.definitions.md#def-0a7304d95c3d81a1)
- [CodedSorting.CommonLocalNode.program._proof_66](Program.definitions.md#def-b76263befde85225)
- [CodedSorting.CommonLeafProgram.Machine](../../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonLocalNode.program._proof_53](Program.definitions.md#def-d5a555e58fe1d3eb)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonLocalNode.program._proof_60](Program.definitions.md#def-0b01b0e36c90a84d)
- [CodedSorting.CommonLocalNode.program._proof_85](Program.definitions.md#def-6dd4c902f089038e)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.CommonRecordProgram.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonLocalNode.program._proof_59](Program.definitions.md#def-b5b3d09b1956ff16)
- [CodedSorting.CommonRecordTransform.Stage.append](../../../Shared/Records/Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonLocalNode.program._proof_73](Program.definitions.md#def-02c2547d656d731e)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalNode.program._proof_74](Program.definitions.md#def-33b88d1c13a04999)
- [CodedSorting.CommonLocalNode.program._proof_79](Program.definitions.md#def-461c2ae95bcc6338)
- [CodedSorting.CommonLocalNode.program._proof_69](Program.definitions.md#def-a7637ff94026cf84)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonLocalNode.program._proof_83](Program.definitions.md#def-2ab0b7ea5c0eaf85)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLocalNode.program._proof_71](Program.definitions.md#def-62b85bcc4e9489d6)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonLocalNode.program._proof_56](Program.definitions.md#def-52f2ff36340d79cd)
- [CodedSorting.CommonLocalNode.program._proof_77](Program.definitions.md#def-5c37dca9e74f828c)
- [CodedSorting.CommonLocalNode.program._proof_70](Program.definitions.md#def-3801261deb2e34d9)
- [CodedSorting.CommonLocalNode.program._proof_65](Program.definitions.md#def-c23f548d23b23e46)
- [CodedSorting.CommonLocalNode.program._proof_63](Program.definitions.md#def-b5d288a28356219c)
- [CodedSorting.CommonLocalNode.program._proof_72](Program.definitions.md#def-60b497b31ca95168)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonLocalNode.program._proof_52](Program.definitions.md#def-0fcdcb2912c6e1de)
- [CodedSorting.CommonLocalNode.program._proof_78](Program.definitions.md#def-10cfff12bcca7add)
- [CodedSorting.CommonLocalNode.program._proof_58](Program.definitions.md#def-72175b577656778c)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.CommonLocalNode.program._proof_51](Program.definitions.md#def-c615d89c718200ee)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)
- [CodedSorting.Normalization.LogicalState.disk](../../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`le_refl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-cf3438cc7e71806b"></a>
## `CodedSorting.CommonLocalNode.program._proof_88`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (n source A B work limit : ℕ)
  (op : CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w))
  (pA :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pB :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.large n) B work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n + 1)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pf :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (pb :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hr : CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n)
  (hAB : A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B)
  (hBW : B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work)
  (hn : n ≤ CodedSorting.CommonLocalNode.small n)
  (hab : CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n)
  (hh : CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n)
  (hbh :
    CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n)
  (hna :
    CodedSorting.CommonRecordProgram.recordBlocks q n ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n))
  (habc :
    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hhc :
    CodedSorting.CommonRecordProgram.recordBlocks q
        (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hSA : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hAcap :
    A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ q.N ^ q.exponent)
  (hBcap :
    B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ q.N ^ q.exponent)
  (hshape' :
    ∀ (L N R O : ℕ),
      L ≤ CodedSorting.CommonLocalNode.large n →
        N ≤ CodedSorting.CommonLocalNode.large n →
          R ≤ CodedSorting.CommonLocalNode.large n →
            O ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O))
  (hwA : A ≤ work) (hAB' : A ≤ B)
  (hframeA :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x)
  (hframeB :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < B ∨ B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ ↑x),
  ∀
    i ∈
      (((((((((((((CodedSorting.CommonRecordTransform.margins q reader 0 n (CodedSorting.CommonLocalNode.small n - n) 0
                                                            source A source n A limit ⋯ ⋯ hSA ⋯ ⋯ ⋯ ⋯).castOutput
                                                        ⋯).changeFunction
                                                    ⋯).append
                                                (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯
                                                  hwA)).append
                                            (CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯ hwA)).append
                                        (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                    (CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA)).append
                                (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                            (((CodedSorting.CommonRecordTransform.margins q reader (CodedSorting.CommonLocalNode.half n)
                                      (CodedSorting.CommonLocalNode.small n) (CodedSorting.CommonLocalNode.half n) 0 A B
                                      source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯ ⋯).castOutput
                                  hbh).changeFunction
                              ⋯)).append
                        (CodedSorting.CommonRecordTransform.workspaceProgram q pB hAB' ⋯ hwA)).append
                    (((CodedSorting.CommonRecordTransform.margins q reader 0 (CodedSorting.CommonLocalNode.small n) 0
                              (CodedSorting.CommonLocalNode.half n) B A source n A limit ⋯ ⋯ hBcap ⋯ ⋯ ⋯ ⋯).castOutput
                          ⋯).changeFunction
                      ⋯)).append
                (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 A source source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯
                          ⋯).castOutput
                      ⋯).changeFunction
                  ⋯)).toProgram.changeFunction
          ⋯).instructions,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_67](Program.definitions.md#def-ef3313ca36de27be)
- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalNode.program._proof_80](Program.definitions.md#def-f75a6ac053908c84)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](../../../Shared/Records/Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](../../../Shared/Records/Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalNode.program._proof_68](Program.definitions.md#def-4c765b794e21177a)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTransform.workspaceProgram](../../../Shared/Records/Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonLocalNode.program._proof_62](Program.definitions.md#def-ef93f65db18d7e32)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](../../../Shared/Records/Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonLocalNode.program._proof_57](Program.definitions.md#def-3e23013b1db55e66)
- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.program._proof_76](Program.definitions.md#def-06adeb1e4d2e683b)
- [CodedSorting.CommonRecordTransform.margins](../../../Shared/Records/Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonLocalNode.program._proof_81](Program.definitions.md#def-e8628ad34481cde3)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalNode.program._proof_64](Program.definitions.md#def-2e1ce65559baedfe)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program._proof_61](Program.definitions.md#def-605ab56b0f4e5ed4)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLocalNode.program._proof_54](Program.definitions.md#def-6854585bae4dbf52)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.program._proof_75](Program.definitions.md#def-196683c06b23f341)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.program._proof_55](Program.definitions.md#def-64726af18ac826b9)
- [CodedSorting.CommonLocalNode.program._proof_82](Program.definitions.md#def-0a7304d95c3d81a1)
- [CodedSorting.CommonLocalNode.program._proof_66](Program.definitions.md#def-b76263befde85225)
- [CodedSorting.CommonLocalNode.program._proof_53](Program.definitions.md#def-d5a555e58fe1d3eb)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.program._proof_60](Program.definitions.md#def-0b01b0e36c90a84d)
- [CodedSorting.CommonLocalNode.program._proof_85](Program.definitions.md#def-6dd4c902f089038e)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonLocalNode.program._proof_59](Program.definitions.md#def-b5b3d09b1956ff16)
- [CodedSorting.CommonRecordTransform.Stage.append](../../../Shared/Records/Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonLocalNode.program._proof_73](Program.definitions.md#def-02c2547d656d731e)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalNode.program._proof_74](Program.definitions.md#def-33b88d1c13a04999)
- [CodedSorting.CommonLocalNode.program._proof_79](Program.definitions.md#def-461c2ae95bcc6338)
- [CodedSorting.CommonLocalNode.program._proof_69](Program.definitions.md#def-a7637ff94026cf84)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonLocalNode.program._proof_83](Program.definitions.md#def-2ab0b7ea5c0eaf85)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonLocalNode.program._proof_71](Program.definitions.md#def-62b85bcc4e9489d6)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.CommonLocalNode.program._proof_56](Program.definitions.md#def-52f2ff36340d79cd)
- [CodedSorting.CommonLocalNode.program._proof_77](Program.definitions.md#def-5c37dca9e74f828c)
- [CodedSorting.CommonLocalNode.program._proof_70](Program.definitions.md#def-3801261deb2e34d9)
- [CodedSorting.CommonLocalNode.program._proof_65](Program.definitions.md#def-c23f548d23b23e46)
- [CodedSorting.CommonLocalNode.program._proof_63](Program.definitions.md#def-b5d288a28356219c)
- [CodedSorting.CommonLocalNode.program._proof_72](Program.definitions.md#def-60b497b31ca95168)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonLocalNode.program._proof_52](Program.definitions.md#def-0fcdcb2912c6e1de)
- [CodedSorting.CommonLocalNode.program._proof_78](Program.definitions.md#def-10cfff12bcca7add)
- [CodedSorting.CommonLocalNode.program._proof_58](Program.definitions.md#def-72175b577656778c)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.CommonLocalNode.program._proof_51](Program.definitions.md#def-c615d89c718200ee)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_refl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Membership.mem`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `List`, `instHAdd`, `instHSub`, `HPow.hPow`, `List.instMembership`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-e1183cd2828f6105"></a>
## `CodedSorting.CommonLocalNode.program._proof_89`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (n source A B work limit : ℕ)
  (op : CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w))
  (pA :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pB :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.large n) B work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n + 1)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pf :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (pb :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hr : CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n)
  (hAB : A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B)
  (hBW : B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work)
  (hn : n ≤ CodedSorting.CommonLocalNode.small n)
  (hab : CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n)
  (hh : CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n)
  (hbh :
    CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n)
  (hna :
    CodedSorting.CommonRecordProgram.recordBlocks q n ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n))
  (habc :
    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hhc :
    CodedSorting.CommonRecordProgram.recordBlocks q
        (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hSA : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hAcap :
    A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ q.N ^ q.exponent)
  (hBcap :
    B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ q.N ^ q.exponent)
  (hshape' :
    ∀ (L N R O : ℕ),
      L ≤ CodedSorting.CommonLocalNode.large n →
        N ≤ CodedSorting.CommonLocalNode.large n →
          R ≤ CodedSorting.CommonLocalNode.large n →
            O ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O))
  (hwA : A ≤ work) (hAB' : A ≤ B)
  (hframeA :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x)
  (hframeB :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < B ∨ B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ ↑x),
  ((((((((((((CodedSorting.CommonRecordTransform.margins q reader 0 n (CodedSorting.CommonLocalNode.small n - n) 0
                                                      source A source n A limit ⋯ ⋯ hSA ⋯ ⋯ ⋯ ⋯).castOutput
                                                  ⋯).changeFunction
                                              ⋯).append
                                          (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                      (CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯ hwA)).append
                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                              (CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA)).append
                          (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                      (((CodedSorting.CommonRecordTransform.margins q reader (CodedSorting.CommonLocalNode.half n)
                                (CodedSorting.CommonLocalNode.small n) (CodedSorting.CommonLocalNode.half n) 0 A B
                                source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯ ⋯).castOutput
                            hbh).changeFunction
                        ⋯)).append
                  (CodedSorting.CommonRecordTransform.workspaceProgram q pB hAB' ⋯ hwA)).append
              (((CodedSorting.CommonRecordTransform.margins q reader 0 (CodedSorting.CommonLocalNode.small n) 0
                        (CodedSorting.CommonLocalNode.half n) B A source n A limit ⋯ ⋯ hBcap ⋯ ⋯ ⋯ ⋯).castOutput
                    ⋯).changeFunction
                ⋯)).append
          (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 A source source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯
                    ⋯).castOutput
                ⋯).changeFunction
            ⋯)).charge =
      3 * pA.charge + pB.charge + pf.charge + pb.charge +
        3 *
          (2 * CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) +
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) +
            CodedSorting.CommonRecordProgram.recordBlocks q n) →
    CodedSorting.CommonStaticSchedule.cost q
        (((((((((((((CodedSorting.CommonRecordTransform.margins q reader 0 n (CodedSorting.CommonLocalNode.small n - n)
                                                              0 source A source n A limit ⋯ ⋯ hSA ⋯ ⋯ ⋯ ⋯).castOutput
                                                          ⋯).changeFunction
                                                      ⋯).append
                                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯
                                                    hwA)).append
                                              (CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯ hwA)).append
                                          (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                      (CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA)).append
                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                              (((CodedSorting.CommonRecordTransform.margins q reader
                                        (CodedSorting.CommonLocalNode.half n) (CodedSorting.CommonLocalNode.small n)
                                        (CodedSorting.CommonLocalNode.half n) 0 A B source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯
                                        ⋯).castOutput
                                    hbh).changeFunction
                                ⋯)).append
                          (CodedSorting.CommonRecordTransform.workspaceProgram q pB hAB' ⋯ hwA)).append
                      (((CodedSorting.CommonRecordTransform.margins q reader 0 (CodedSorting.CommonLocalNode.small n) 0
                                (CodedSorting.CommonLocalNode.half n) B A source n A limit ⋯ ⋯ hBcap ⋯ ⋯ ⋯ ⋯).castOutput
                            ⋯).changeFunction
                        ⋯)).append
                  (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 A source source n A limit ⋯ ⋯ hAcap ⋯ ⋯
                            ⋯ ⋯).castOutput
                        ⋯).changeFunction
                    ⋯)).toProgram.changeFunction
            ⋯).instructions ≤
      3 * pA.charge + pB.charge + pf.charge + pb.charge +
        3 *
          (2 * CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) +
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) +
            CodedSorting.CommonRecordProgram.recordBlocks q n)
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_67](Program.definitions.md#def-ef3313ca36de27be)
- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalNode.program._proof_80](Program.definitions.md#def-f75a6ac053908c84)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](../../../Shared/Records/Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](../../../Shared/Records/Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalNode.program._proof_68](Program.definitions.md#def-4c765b794e21177a)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTransform.workspaceProgram](../../../Shared/Records/Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonLocalNode.program._proof_62](Program.definitions.md#def-ef93f65db18d7e32)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](../../../Shared/Records/Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonLocalNode.program._proof_57](Program.definitions.md#def-3e23013b1db55e66)
- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.program._proof_76](Program.definitions.md#def-06adeb1e4d2e683b)
- [CodedSorting.CommonRecordTransform.margins](../../../Shared/Records/Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonLocalNode.program._proof_81](Program.definitions.md#def-e8628ad34481cde3)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalNode.program._proof_64](Program.definitions.md#def-2e1ce65559baedfe)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program._proof_61](Program.definitions.md#def-605ab56b0f4e5ed4)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLocalNode.program._proof_54](Program.definitions.md#def-6854585bae4dbf52)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.program._proof_75](Program.definitions.md#def-196683c06b23f341)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.program._proof_55](Program.definitions.md#def-64726af18ac826b9)
- [CodedSorting.CommonLocalNode.program._proof_82](Program.definitions.md#def-0a7304d95c3d81a1)
- [CodedSorting.CommonLocalNode.program._proof_66](Program.definitions.md#def-b76263befde85225)
- [CodedSorting.CommonLocalNode.program._proof_53](Program.definitions.md#def-d5a555e58fe1d3eb)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.program._proof_60](Program.definitions.md#def-0b01b0e36c90a84d)
- [CodedSorting.CommonLocalNode.program._proof_85](Program.definitions.md#def-6dd4c902f089038e)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonRecordProgram.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonLocalNode.program._proof_59](Program.definitions.md#def-b5b3d09b1956ff16)
- [CodedSorting.CommonRecordTransform.Stage.append](../../../Shared/Records/Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonLocalNode.program._proof_73](Program.definitions.md#def-02c2547d656d731e)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalNode.program._proof_74](Program.definitions.md#def-33b88d1c13a04999)
- [CodedSorting.CommonLocalNode.program._proof_79](Program.definitions.md#def-461c2ae95bcc6338)
- [CodedSorting.CommonLocalNode.program._proof_69](Program.definitions.md#def-a7637ff94026cf84)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonLocalNode.program._proof_83](Program.definitions.md#def-2ab0b7ea5c0eaf85)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonLocalNode.program._proof_71](Program.definitions.md#def-62b85bcc4e9489d6)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonStaticSchedule.cost](../../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.CommonLocalNode.program._proof_56](Program.definitions.md#def-52f2ff36340d79cd)
- [CodedSorting.CommonLocalNode.program._proof_77](Program.definitions.md#def-5c37dca9e74f828c)
- [CodedSorting.CommonLocalNode.program._proof_70](Program.definitions.md#def-3801261deb2e34d9)
- [CodedSorting.CommonLocalNode.program._proof_65](Program.definitions.md#def-c23f548d23b23e46)
- [CodedSorting.CommonRecordTransform.Stage.charge](../../../Shared/Records/Transform.definitions.md#def-30123232aa6eccd6)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonLocalNode.program._proof_63](Program.definitions.md#def-b5d288a28356219c)
- [CodedSorting.CommonLocalNode.program._proof_72](Program.definitions.md#def-60b497b31ca95168)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonLocalNode.program._proof_52](Program.definitions.md#def-0fcdcb2912c6e1de)
- [CodedSorting.CommonLocalNode.program._proof_78](Program.definitions.md#def-10cfff12bcca7add)
- [CodedSorting.CommonLocalNode.program._proof_58](Program.definitions.md#def-72175b577656778c)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.CommonLocalNode.program._proof_51](Program.definitions.md#def-c615d89c718200ee)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_refl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-180dee9bf7a5843a"></a>
## `CodedSorting.CommonLocalNode.program._proof_90`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (n source A B work limit : ℕ)
  (op : CodedSorting.CommonLocalSemantic.Operation (CodedSorting.KeyRecordWords.Record q.w))
  (pA :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pB :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.large n) B work limit
      (CodedSorting.CommonLocalSemantic.batch op (CodedSorting.CommonLocalNode.side n + 1)
        (CodedSorting.CommonLocalNode.rowCount n)))
  (pf :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.forwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (pb :
    CodedSorting.CommonRecordProgram.Program q (CodedSorting.CommonLocalNode.small n) A work limit
      (CodedSorting.CommonSortingSemanticSwaps.backwardAtRows q (CodedSorting.CommonLocalNode.side n)))
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ A) (hwl : work ≤ limit)
  (hl : limit ≤ q.N ^ q.exponent)
  (hr : CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n)
  (hAB : A + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤ B)
  (hBW : B + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤ work)
  (hn : n ≤ CodedSorting.CommonLocalNode.small n)
  (hab : CodedSorting.CommonLocalNode.small n ≤ CodedSorting.CommonLocalNode.large n)
  (hh : CodedSorting.CommonLocalNode.half n ≤ CodedSorting.CommonLocalNode.large n)
  (hbh :
    CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n + CodedSorting.CommonLocalNode.half n =
      CodedSorting.CommonLocalNode.large n)
  (hna :
    CodedSorting.CommonRecordProgram.recordBlocks q n ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n))
  (habc :
    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hhc :
    CodedSorting.CommonRecordProgram.recordBlocks q
        (CodedSorting.CommonLocalNode.half n + CodedSorting.CommonLocalNode.small n) ≤
      CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
  (hSA : source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ q.N ^ q.exponent)
  (hAcap :
    A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ q.N ^ q.exponent)
  (hBcap :
    B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ q.N ^ q.exponent)
  (hshape' :
    ∀ (L N R O : ℕ),
      L ≤ CodedSorting.CommonLocalNode.large n →
        N ≤ CodedSorting.CommonLocalNode.large n →
          R ≤ CodedSorting.CommonLocalNode.large n →
            O ≤ CodedSorting.CommonLocalNode.large n →
              CodedSorting.CommonStaticMargins.ShapeFits q (3 * L) (3 * N) (3 * R) (3 * O))
  (hwA : A ≤ work) (hAB' : A ≤ B)
  (hframeA :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < A ∨ A + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) ≤ ↑x)
  (hframeB :
    ∀ (x : Fin (q.N ^ q.exponent)),
      ↑x < source ∨ source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ ↑x →
        ↑x < A ∨ limit ≤ ↑x →
          ↑x < B ∨ B + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) ≤ ↑x),
  ((((((((((((CodedSorting.CommonRecordTransform.margins q reader 0 n (CodedSorting.CommonLocalNode.small n - n) 0
                                                      source A source n A limit ⋯ ⋯ hSA ⋯ ⋯ ⋯ ⋯).castOutput
                                                  ⋯).changeFunction
                                              ⋯).append
                                          (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                      (CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯ hwA)).append
                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                              (CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA)).append
                          (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                      (((CodedSorting.CommonRecordTransform.margins q reader (CodedSorting.CommonLocalNode.half n)
                                (CodedSorting.CommonLocalNode.small n) (CodedSorting.CommonLocalNode.half n) 0 A B
                                source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯ ⋯).castOutput
                            hbh).changeFunction
                        ⋯)).append
                  (CodedSorting.CommonRecordTransform.workspaceProgram q pB hAB' ⋯ hwA)).append
              (((CodedSorting.CommonRecordTransform.margins q reader 0 (CodedSorting.CommonLocalNode.small n) 0
                        (CodedSorting.CommonLocalNode.half n) B A source n A limit ⋯ ⋯ hBcap ⋯ ⋯ ⋯ ⋯).castOutput
                    ⋯).changeFunction
                ⋯)).append
          (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 A source source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯
                    ⋯).castOutput
                ⋯).changeFunction
            ⋯)).charge =
      3 * pA.charge + pB.charge + pf.charge + pb.charge +
        3 *
          (2 * CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) +
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) +
            CodedSorting.CommonRecordProgram.recordBlocks q n) →
    (((((((((((((CodedSorting.CommonRecordTransform.margins q reader 0 n (CodedSorting.CommonLocalNode.small n - n) 0
                                                              source A source n A limit ⋯ ⋯ hSA ⋯ ⋯ ⋯ ⋯).castOutput
                                                          ⋯).changeFunction
                                                      ⋯).append
                                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯
                                                    hwA)).append
                                              (CodedSorting.CommonRecordTransform.workspaceProgram q pf ⋯ ⋯ hwA)).append
                                          (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                                      (CodedSorting.CommonRecordTransform.workspaceProgram q pb ⋯ ⋯ hwA)).append
                                  (CodedSorting.CommonRecordTransform.workspaceProgram q pA ⋯ ⋯ hwA)).append
                              (((CodedSorting.CommonRecordTransform.margins q reader
                                        (CodedSorting.CommonLocalNode.half n) (CodedSorting.CommonLocalNode.small n)
                                        (CodedSorting.CommonLocalNode.half n) 0 A B source n A limit ⋯ ⋯ hAcap ⋯ ⋯ ⋯
                                        ⋯).castOutput
                                    hbh).changeFunction
                                ⋯)).append
                          (CodedSorting.CommonRecordTransform.workspaceProgram q pB hAB' ⋯ hwA)).append
                      (((CodedSorting.CommonRecordTransform.margins q reader 0 (CodedSorting.CommonLocalNode.small n) 0
                                (CodedSorting.CommonLocalNode.half n) B A source n A limit ⋯ ⋯ hBcap ⋯ ⋯ ⋯ ⋯).castOutput
                            ⋯).changeFunction
                        ⋯)).append
                  (((CodedSorting.CommonRecordTransform.margins q reader 0 n 0 0 A source source n A limit ⋯ ⋯ hAcap ⋯ ⋯
                            ⋯ ⋯).castOutput
                        ⋯).changeFunction
                    ⋯)).toProgram.changeFunction
            ⋯).instructions.length ≤
      3 * pA.charge + pB.charge + pf.charge + pb.charge +
        3 *
          (2 * CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n) +
              CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n) +
            CodedSorting.CommonRecordProgram.recordBlocks q n)
```

**继续展开**

- [CodedSorting.CommonLocalNode.program._proof_67](Program.definitions.md#def-ef3313ca36de27be)
- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalNode.program._proof_80](Program.definitions.md#def-f75a6ac053908c84)
- [CodedSorting.CommonRecordTransform.Stage.castOutput](../../../Shared/Records/Transform.definitions.md#def-a7b739ca983554fe)
- [CodedSorting.CommonRecordTransform.Stage.changeFunction](../../../Shared/Records/Transform.definitions.md#def-9e60f1f0ebcc04a3)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalNode.program._proof_68](Program.definitions.md#def-4c765b794e21177a)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonRecordTransform.workspaceProgram](../../../Shared/Records/Transform.definitions.md#def-21e561adcb69c1e3)
- [CodedSorting.CommonLocalNode.program._proof_62](Program.definitions.md#def-ef93f65db18d7e32)
- [CodedSorting.CommonRecordTransform.Stage.toProgram](../../../Shared/Records/Transform.definitions.md#def-405f8315e35261de)
- [CodedSorting.CommonLocalNode.program._proof_57](Program.definitions.md#def-3e23013b1db55e66)
- [CodedSorting.CommonStaticMargins.ShapeFits](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-513df08f5eb2dd0d)
- [CodedSorting.CommonLocalNode.program._proof_76](Program.definitions.md#def-06adeb1e4d2e683b)
- [CodedSorting.CommonRecordTransform.margins](../../../Shared/Records/Transform.definitions.md#def-ded405593deceff5)
- [CodedSorting.CommonLocalNode.program._proof_81](Program.definitions.md#def-e8628ad34481cde3)
- [CodedSorting.CommonLocalSemantic.Operation](Semantic.definitions.md#def-b78823851e91ab63)
- [CodedSorting.CommonLocalNode.program._proof_64](Program.definitions.md#def-2e1ce65559baedfe)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program._proof_61](Program.definitions.md#def-605ab56b0f4e5ed4)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLocalNode.program._proof_54](Program.definitions.md#def-6854585bae4dbf52)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.RecursiveColumnsort.pad](../../Bounds/RecursiveSortBase.definitions.md#def-fd3cc139d7f2794c)
- [CodedSorting.RecursiveColumnsort.trim](../../Bounds/RecursiveSortBase.definitions.md#def-2695ace6fd03771d)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonLocalNode.program._proof_75](Program.definitions.md#def-196683c06b23f341)
- [CodedSorting.CommonSortingSemanticSwaps.backwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-869b338825e3fc26)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonLocalNode.program._proof_55](Program.definitions.md#def-64726af18ac826b9)
- [CodedSorting.CommonLocalNode.program._proof_82](Program.definitions.md#def-0a7304d95c3d81a1)
- [CodedSorting.CommonLocalNode.program._proof_66](Program.definitions.md#def-b76263befde85225)
- [CodedSorting.CommonLocalNode.program._proof_53](Program.definitions.md#def-d5a555e58fe1d3eb)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.program._proof_60](Program.definitions.md#def-0b01b0e36c90a84d)
- [CodedSorting.CommonLocalNode.program._proof_85](Program.definitions.md#def-6dd4c902f089038e)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](../../../Shared/Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.CommonLocalNode.program._proof_59](Program.definitions.md#def-b5b3d09b1956ff16)
- [CodedSorting.CommonRecordTransform.Stage.append](../../../Shared/Records/Transform.definitions.md#def-9ad94e264d94adcf)
- [CodedSorting.CommonLocalNode.program._proof_73](Program.definitions.md#def-02c2547d656d731e)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonRecordReindex.castRecords](../../../Shared/Records/RecordOperations.definitions.md#def-502e25cd25b52e28)
- [CodedSorting.CommonLocalNode.program._proof_74](Program.definitions.md#def-33b88d1c13a04999)
- [CodedSorting.CommonLocalNode.program._proof_79](Program.definitions.md#def-461c2ae95bcc6338)
- [CodedSorting.CommonLocalNode.program._proof_69](Program.definitions.md#def-a7637ff94026cf84)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalSemantic.shift](Semantic.definitions.md#def-4428e9a1cf4ad9ae)
- [CodedSorting.CommonLocalNode.program._proof_83](Program.definitions.md#def-2ab0b7ea5c0eaf85)
- [CodedSorting.CommonRecordProgram.Records](../../../Shared/Records/RecordOperations.definitions.md#def-d97d98eb7adcb603)
- [CodedSorting.CommonLocalNode.program._proof_71](Program.definitions.md#def-62b85bcc4e9489d6)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonLocalNode.program._proof_56](Program.definitions.md#def-52f2ff36340d79cd)
- [CodedSorting.CommonLocalNode.program._proof_77](Program.definitions.md#def-5c37dca9e74f828c)
- [CodedSorting.CommonLocalNode.program._proof_70](Program.definitions.md#def-3801261deb2e34d9)
- [CodedSorting.CommonLocalNode.program._proof_65](Program.definitions.md#def-c23f548d23b23e46)
- [CodedSorting.CommonRecordTransform.Stage.charge](../../../Shared/Records/Transform.definitions.md#def-30123232aa6eccd6)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonLocalNode.program._proof_63](Program.definitions.md#def-b5d288a28356219c)
- [CodedSorting.CommonLocalNode.program._proof_72](Program.definitions.md#def-60b497b31ca95168)
- [CodedSorting.CommonStaticMarginsRecords.margin](../../../Shared/Programs/Static/MarginsRecords.definitions.md#def-5b243d9616c260d3)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonLocalNode.program._proof_52](Program.definitions.md#def-0fcdcb2912c6e1de)
- [CodedSorting.CommonLocalNode.program._proof_78](Program.definitions.md#def-10cfff12bcca7add)
- [CodedSorting.CommonLocalNode.program._proof_58](Program.definitions.md#def-72175b577656778c)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.CommonLocalSemantic.unshift](Semantic.definitions.md#def-601d84687321e5a1)
- [CodedSorting.CommonSortingSemanticSwaps.forwardAtRows](../../Resources/Framework/SemanticSwaps.definitions.md#def-8003b18e12811d84)
- [CodedSorting.CommonLocalNode.program._proof_51](Program.definitions.md#def-c615d89c718200ee)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`le_refl`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Function.comp`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instSubNat`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `List.length`, `instHMul`

<a id="def-13c87eba66dcfa23"></a>
## `CodedSorting.CommonLocalRecursion.Descriptors.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Program.lean)

**类型**

```lean
(motive : ℕ → ℕ → Sort u_1) → (x x_1 : ℕ) → ((x : ℕ) → motive 0 x) → ((fuel n : ℕ) → motive fuel.succ n) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-d6e8b9dde296f10f"></a>
## `CodedSorting.LocalSorter.Machine.localProgram._proof_138`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ∀ n ≤ q.height ^ 2, CodedSorting.CommonLocalAdmissible.Admissible q.height 3 n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalAdmissible.Admissible](CostBound.definitions.md#def-5a4da9ae621ec1bb)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-3c402777908963e1"></a>
## `CodedSorting.LocalSorter.Machine.localProgram._proof_139`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ∀ n ≤ q.height ^ 2, 2 ≤ q.exponent → CodedSorting.CommonLocalRecursion.Descriptors q 3 n
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalRecursion.Descriptors](Program.definitions.md#def-a7cd06ce9a69e356)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-dbbde2bdcb50b812"></a>
## `CodedSorting.LocalSorter.batchBuild._proof_100`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ℕ → ∀ (r : ℕ), ℕ → ℕ → ℕ → ℕ → ¬r ≤ 512 * q.height → 0 < CodedSorting.CommonRecordProgram.recordBlocks q r
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Not`, `instHMul`

<a id="def-09d8744d19d9b009"></a>
## `CodedSorting.LocalSorter.batchBuild._proof_101`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer : ℕ),
  0 < CodedSorting.CommonRecordProgram.recordBlocks q r →
    ∀ (j : Fin c),
      CodedSorting.CommonSlabBatch.recordBase q r buffer ↑j +
          max 1 (CodedSorting.CommonRecordProgram.recordBlocks q r) ≤
        buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](../../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-e192f85de221fbac)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-c47b0f45f5950d36"></a>
## `CodedSorting.LocalSorter.batchBuild._proof_102`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r buffer : ℕ),
  buffer + c * CodedSorting.CommonSlabBatch.stride q (r * 3) ≤
    buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.stride](../../../Interchange/Framework/Memory/SlabBatchAllocation.definitions.md#def-94b29694418488f5)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-ac19e0e38fc3313a"></a>
## `CodedSorting.LocalSorter.batchBuild._proof_103`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (fuel c r childSpace childBudget : ℕ)
  (child :
    (source buffer limit : ℕ) →
      source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q r) ≤ buffer →
        buffer + childSpace ≤ limit → limit ≤ q.N ^ q.exponent → { p // p.charge ≤ childBudget })
  (source buffer limit : ℕ) (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer)
  (hl : limit ≤ q.N ^ q.exponent),
  ¬r ≤ 512 * q.height →
    ∀ (hwork : buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r + childSpace ≤ limit)
      (hwl : buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r ≤ limit)
      (hpos : 0 < CodedSorting.CommonRecordProgram.recordBlocks q r),
      (CodedSorting.CommonSlabBatch.program reader
            (fun j =>
              ↑(child (CodedSorting.CommonSlabBatch.recordBase q r buffer ↑j)
                  (buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r) limit ⋯ hwork hl))
            hs ⋯ hwl hl).charge ≤
        CodedSorting.CommonLocalBudget.batchBound q childBudget c r
```

**继续展开**

- [CodedSorting.LocalSorter.batchBuild._proof_102](Program.definitions.md#def-c47b0f45f5950d36)
- [CodedSorting.CommonLocalBudget.batchBound](CostBound.definitions.md#def-fd9bae2d2f813ccf)
- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.LocalSorter.batchBuild._proof_101](Program.definitions.md#def-09d8744d19d9b009)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSlabBatch.program](../../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-ae51434b8b1ab7f4)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSlabBatch.recordBase](../../../Interchange/Framework/Memory/SlabBatch.definitions.md#def-e192f85de221fbac)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Not`, `instHMul`

<a id="def-3519369b0b46454c"></a>
## `CodedSorting.LocalSorter.batchBuild._proof_96`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r childSpace buffer limit : ℕ),
  buffer + CodedSorting.CommonLocalRecursion.batchSpace q c r childSpace ≤ limit →
    r ≤ 512 * q.height → buffer + CodedSorting.CommonGroupedLeafBatch.space q c r ≤ limit
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonGroupedLeafBatch.space](../../../Shared/Memory/GroupedLeafBatch.definitions.md#def-632f8085f3c024ca)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-7f76eac5f86e5e31"></a>
## `CodedSorting.LocalSorter.batchBuild._proof_97`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (fuel c r childSpace childBudget source buffer limit : ℕ)
  (hs : source + CodedSorting.CommonRecordProgram.recordBlocks q (c * r) ≤ buffer)
  (hw : buffer + CodedSorting.CommonLocalRecursion.batchSpace q c r childSpace ≤ limit) (hl : limit ≤ q.N ^ q.exponent)
  (hr : r ≤ 512 * q.height),
  ((CodedSorting.CommonGroupedLeafBatch.program q reader c r source buffer limit hr ⋯ hs ⋯ hl).changeFunction
        ⋯).charge ≤
    CodedSorting.CommonLocalBudget.batchBound q childBudget c r
```

**继续展开**

- [CodedSorting.CommonLocalBudget.batchBound](CostBound.definitions.md#def-fd9bae2d2f813ccf)
- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonGroupedLeafBatch.program](../../../Shared/Memory/GroupedLeafBatch.definitions.md#def-b060e8872789c203)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonGroupedLeafBatch.sortColumns](../../../Shared/Memory/GroupedLeafBatch.definitions.md#def-a249b8eeae244fe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalRecursion.small_batch](Program.definitions.md#def-c59c501b440dfc0d)
- [CodedSorting.LocalSorter.batchBuild._proof_96](Program.definitions.md#def-3519369b0b46454c)
- [CodedSorting.CommonLocalRecursion.block_le_height](Program.definitions.md#def-e87082ef48bf9e49)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-171ea2170531634a"></a>
## `CodedSorting.LocalSorter.batchBuild._proof_98`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r childSpace buffer limit : ℕ),
  buffer + CodedSorting.CommonLocalRecursion.batchSpace q c r childSpace ≤ limit →
    ¬r ≤ 512 * q.height → buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r + childSpace ≤ limit
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`, `instHMul`

<a id="def-78e52987c4933689"></a>
## `CodedSorting.LocalSorter.batchBuild._proof_99`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (c r childSpace : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r + childSpace ≤ limit →
        buffer + c * CodedSorting.CommonRecordProgram.recordBlocks q r ≤ limit
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-9b0b27a19bcc5d0f"></a>
## `CodedSorting.LocalSorter.build._proof_116`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration),
  (swap q).condition →
    ∀ (n source buffer : ℕ),
      ℕ →
        source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
          source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-83671006b7c59ec0"></a>
## `CodedSorting.LocalSorter.build._proof_117`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  8 * CodedSorting.CommonRecordProgram.recordBlocks q n + 1 ≤ 8 * CodedSorting.CommonRecordProgram.recordBlocks q n + 1
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-d9b00120e9cd829e"></a>
## `CodedSorting.LocalSorter.build._proof_118`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration),
  (swap q).condition →
    ℕ →
      ∀ (n source buffer : ℕ),
        ℕ →
          source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
            source + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ buffer
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-0ba3c7c9b4ead3dc"></a>
## `CodedSorting.LocalSorter.build._proof_119`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration) (hnormal : (swap q).condition) (fuel n buffer limit : ℕ),
  buffer + CodedSorting.LocalSorter.space swap q hnormal (fuel + 1) n ≤ limit →
    n ≤ 512 * q.height → buffer + CodedSorting.CommonRecordProgram.recordBlocks q n ≤ limit
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-54e0b1b0ba6cd191"></a>
## `CodedSorting.LocalSorter.build._proof_120`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (fuel n : ℕ),
  n ≤ 512 * q.height → CodedSorting.Columnsort.sortColumn = CodedSorting.CommonLocalRecursion.operation q (fuel + 1) n
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Columnsort.sortColumn](../Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-5abeeac929d67472"></a>
## `CodedSorting.LocalSorter.build._proof_121`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : (swap q).condition) (fuel n source buffer limit : ℕ)
  (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hw : buffer + CodedSorting.LocalSorter.space swap q hnormal (fuel + 1) n ≤ limit) (hl : limit ≤ q.N ^ q.exponent)
  (hn : n ≤ 512 * q.height),
  ((CodedSorting.CommonResidentRecordProgram.program q reader n hn CodedSorting.Columnsort.sortColumn source buffer
            limit ⋯ ⋯ hl).changeFunction
        ⋯).charge ≤
    CodedSorting.LocalSorter.budget swap q (fuel + 1) n
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.LocalSorter.build._proof_118](Program.definitions.md#def-d9b00120e9cd829e)
- [CodedSorting.CommonResidentRecordProgram.program](../../../Interchange/Framework/Resident/RecordProgram.definitions.md#def-b98c803ea5f33c23)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.LocalSorter.budget](Program.definitions.md#def-2a45f731bfb4e38e)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Columnsort.sortColumn](../Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.LocalSorter.build._proof_120](Program.definitions.md#def-54e0b1b0ba6cd191)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.LocalSorter.build._proof_119](Program.definitions.md#def-0ba3c7c9b4ead3dc)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-8fa1c5403d8de8fe"></a>
## `CodedSorting.LocalSorter.build._proof_122`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration),
  (swap q).condition →
    ∀ (fuel n : ℕ),
      CodedSorting.CommonLocalAdmissible.Admissible q.height (fuel + 1) n →
        ℕ →
          ℕ →
            ℕ →
              ¬n ≤ 512 * q.height →
                CodedSorting.CommonLocalAdmissible.Admissible q.height fuel (CodedSorting.CommonLocalNode.rowCount n)
```

**继续展开**

- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalAdmissible.Admissible](CostBound.definitions.md#def-5a4da9ae621ec1bb)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`, `instHMul`

<a id="def-2f2d4a85e712b79d"></a>
## `CodedSorting.LocalSorter.build._proof_123`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (fuel n : ℕ),
  CodedSorting.CommonLocalRecursion.Descriptors q (fuel + 1) n →
    ¬n ≤ 512 * q.height →
      3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits ∧
        CodedSorting.CommonLocalRecursion.Descriptors q fuel (CodedSorting.CommonLocalNode.rowCount n)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalRecursion.Descriptors](Program.definitions.md#def-a7cd06ce9a69e356)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Not`, `instHMul`

<a id="def-1d1ed18f40d9dc19"></a>
## `CodedSorting.LocalSorter.build._proof_124`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration) (hnormal : (swap q).condition) (fuel n buffer limit : ℕ),
  buffer + CodedSorting.LocalSorter.space swap q hnormal (fuel + 1) n ≤ limit →
    ¬n ≤ 512 * q.height →
      buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
            max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
          max
            (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
              (CodedSorting.CommonLocalNode.rowCount n)
              (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
            (max
              (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
                (CodedSorting.CommonLocalNode.rowCount n)
                (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
              ((swap q).space (CodedSorting.LocalShape.sizeExponent n) hnormal)) ≤
        limit
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Not`, `instHMul`

<a id="def-e6c2071a67f74911"></a>
## `CodedSorting.LocalSorter.build._proof_125`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration) (hnormal : (swap q).condition) (fuel n : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            max
              (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
                (CodedSorting.CommonLocalNode.rowCount n)
                (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
              (max
                (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
                  (CodedSorting.CommonLocalNode.rowCount n)
                  (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
                ((swap q).space (CodedSorting.LocalShape.sizeExponent n) hnormal)) ≤
          limit →
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
            max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤
          limit
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-6a4866ecee302044"></a>
## `CodedSorting.LocalSorter.build._proof_126`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration) (hnormal : (swap q).condition) (fuel n : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            max
              (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
                (CodedSorting.CommonLocalNode.rowCount n)
                (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
              (max
                (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
                  (CodedSorting.CommonLocalNode.rowCount n)
                  (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
                ((swap q).space (CodedSorting.LocalShape.sizeExponent n) hnormal)) ≤
          limit →
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
              (CodedSorting.CommonLocalNode.rowCount n)
              (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)) ≤
          limit
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-5a463d6703adda06"></a>
## `CodedSorting.LocalSorter.build._proof_127`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration) (hnormal : (swap q).condition) (fuel n : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            max
              (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
                (CodedSorting.CommonLocalNode.rowCount n)
                (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
              (max
                (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
                  (CodedSorting.CommonLocalNode.rowCount n)
                  (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
                ((swap q).space (CodedSorting.LocalShape.sizeExponent n) hnormal)) ≤
          limit →
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
              (CodedSorting.CommonLocalNode.rowCount n)
              (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)) ≤
          limit
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-43d418ff513c6b6f"></a>
## `CodedSorting.LocalSorter.build._proof_128`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration) (hnormal : (swap q).condition) (fuel n : ℕ),
  ℕ →
    ∀ (buffer limit : ℕ),
      buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            max
              (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
                (CodedSorting.CommonLocalNode.rowCount n)
                (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
              (max
                (CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
                  (CodedSorting.CommonLocalNode.rowCount n)
                  (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)))
                ((swap q).space (CodedSorting.LocalShape.sizeExponent n) hnormal)) ≤
          limit →
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
              CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
                (CodedSorting.CommonLocalNode.rowCount n)
                (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)) ≤
            limit →
          buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                  max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
                CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
                  (CodedSorting.CommonLocalNode.rowCount n)
                  (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)) ≤
              limit →
            buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                  max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
                (swap q).space (CodedSorting.LocalShape.sizeExponent n) hnormal ≤
              limit
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-e5763fedbc153c93"></a>
## `CodedSorting.LocalSorter.build._proof_129`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (fuel n : ℕ),
  3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits ∧
      CodedSorting.CommonLocalRecursion.Descriptors q fuel (CodedSorting.CommonLocalNode.rowCount n) →
    CodedSorting.CommonLocalRecursion.Descriptors q fuel (CodedSorting.CommonLocalNode.rowCount n)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalRecursion.Descriptors](Program.definitions.md#def-a7cd06ce9a69e356)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `And`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-e340274ff2a4dd3a"></a>
## `CodedSorting.LocalSorter.build._proof_130`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration),
  (swap q).condition →
    ℕ →
      ∀ (n : ℕ),
        ℕ →
          ∀ (buffer : ℕ),
            ℕ →
              buffer +
                  CodedSorting.CommonRecordProgram.recordBlocks q
                    (CodedSorting.CommonLocalNode.side n * CodedSorting.CommonLocalNode.rowCount n) ≤
                buffer +
                    max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                  max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-46ebe66b364398ea"></a>
## `CodedSorting.LocalSorter.build._proof_131`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration),
  (swap q).condition →
    ℕ →
      ∀ (n : ℕ),
        ℕ →
          ∀ (buffer : ℕ),
            ℕ →
              buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                  CodedSorting.CommonRecordProgram.recordBlocks q
                    ((CodedSorting.CommonLocalNode.side n + 1) * CodedSorting.CommonLocalNode.rowCount n) ≤
                buffer +
                    max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                  max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-8ade94c5c7b4fa0a"></a>
## `CodedSorting.LocalSorter.build._proof_132`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration),
  Fin q.inventory.readers →
    ∀ (hnormal : (swap q).condition) (fuel : ℕ),
      ((n : ℕ) →
          CodedSorting.CommonLocalAdmissible.Admissible q.height fuel n →
            CodedSorting.CommonLocalRecursion.Descriptors q fuel n →
              (source buffer limit : ℕ) →
                source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
                  buffer + CodedSorting.LocalSorter.space swap q hnormal fuel n ≤ limit →
                    limit ≤ q.N ^ q.exponent → { p // p.charge ≤ CodedSorting.LocalSorter.budget swap q fuel n }) →
        ∀ (n : ℕ),
          ℕ →
            ∀ (buffer limit : ℕ),
              limit ≤ q.N ^ q.exponent →
                ¬n ≤ 512 * q.height →
                  CodedSorting.CommonLocalAdmissible.Admissible q.height fuel
                      (CodedSorting.CommonLocalNode.rowCount n) →
                    3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits ∧
                        CodedSorting.CommonLocalRecursion.Descriptors q fuel (CodedSorting.CommonLocalNode.rowCount n) →
                      buffer +
                                max 1
                                  (CodedSorting.CommonRecordProgram.recordBlocks q
                                    (CodedSorting.CommonLocalNode.small n)) +
                              max 1
                                (CodedSorting.CommonRecordProgram.recordBlocks q
                                  (CodedSorting.CommonLocalNode.large n)) +
                            CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
                              (CodedSorting.CommonLocalNode.rowCount n)
                              (CodedSorting.LocalSorter.space swap q hnormal fuel
                                (CodedSorting.CommonLocalNode.rowCount n)) ≤
                          limit →
                        buffer +
                                  max 1
                                    (CodedSorting.CommonRecordProgram.recordBlocks q
                                      (CodedSorting.CommonLocalNode.small n)) +
                                max 1
                                  (CodedSorting.CommonRecordProgram.recordBlocks q
                                    (CodedSorting.CommonLocalNode.large n)) +
                              CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
                                (CodedSorting.CommonLocalNode.rowCount n)
                                (CodedSorting.LocalSorter.space swap q hnormal fuel
                                  (CodedSorting.CommonLocalNode.rowCount n)) ≤
                            limit →
                          buffer +
                                CodedSorting.CommonRecordProgram.recordBlocks q
                                  (CodedSorting.CommonLocalNode.side n * CodedSorting.CommonLocalNode.rowCount n) ≤
                              buffer +
                                  max 1
                                    (CodedSorting.CommonRecordProgram.recordBlocks q
                                      (CodedSorting.CommonLocalNode.small n)) +
                                max 1
                                  (CodedSorting.CommonRecordProgram.recordBlocks q
                                    (CodedSorting.CommonLocalNode.large n)) →
                            buffer +
                                    max 1
                                      (CodedSorting.CommonRecordProgram.recordBlocks q
                                        (CodedSorting.CommonLocalNode.small n)) +
                                  CodedSorting.CommonRecordProgram.recordBlocks q
                                    ((CodedSorting.CommonLocalNode.side n + 1) *
                                      CodedSorting.CommonLocalNode.rowCount n) ≤
                                buffer +
                                    max 1
                                      (CodedSorting.CommonRecordProgram.recordBlocks q
                                        (CodedSorting.CommonLocalNode.small n)) +
                                  max 1
                                    (CodedSorting.CommonRecordProgram.recordBlocks q
                                      (CodedSorting.CommonLocalNode.large n)) →
                              CodedSorting.LocalShape.sizeChoice n ^ 2 * CodedSorting.LocalShape.sizeChoice n * 1 =
                                2 * (CodedSorting.LocalShape.columnLength n / 2)
```

**继续展开**

- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.LocalShape.sizeChoice](../../../Shared/Programs/LocalTrace.definitions.md#def-e17af2e11cd34d9a)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.LocalSorter.budget](Program.definitions.md#def-2a45f731bfb4e38e)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.CommonLocalAdmissible.Admissible](CostBound.definitions.md#def-5a4da9ae621ec1bb)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalRecursion.Descriptors](Program.definitions.md#def-a7cd06ce9a69e356)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.LocalShape.columnLength](../../../Shared/Programs/LocalTrace.definitions.md#def-0ba59d4f9543a5be)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `Subtype`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Not`, `instHMul`

<a id="def-98031b88a82a094a"></a>
## `CodedSorting.LocalSorter.build._proof_133`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n buffer : ℕ),
  buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) ≤
    buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n))
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Preorder.toLE`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-751efad9ddffdc5d"></a>
## `CodedSorting.LocalSorter.build._proof_134`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n buffer : ℕ),
  buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
      max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤
    buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
      max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n))
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Preorder.toLE`, `Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat.instPreorder`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-31b93cf28a636b02"></a>
## `CodedSorting.LocalSorter.build._proof_135`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (fuel n : ℕ),
  3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits ∧
      CodedSorting.CommonLocalRecursion.Descriptors q fuel (CodedSorting.CommonLocalNode.rowCount n) →
    3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLocalRecursion.Descriptors](Program.definitions.md#def-a7cd06ce9a69e356)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `And`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-5edced85acb006f8"></a>
## `CodedSorting.LocalSorter.build._proof_136`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (fuel n : ℕ),
  ¬n ≤ 512 * q.height →
    CodedSorting.CommonLocalSemantic.pipeline (CodedSorting.CommonLocalRecursion.operation q fuel) n =
      CodedSorting.CommonLocalRecursion.operation q (fuel + 1) n
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Eq`, `Not`, `instHMul`

<a id="def-9f88280375f46300"></a>
## `CodedSorting.LocalSorter.build._proof_137`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Program.lean)

**类型**

```lean
∀ (swap : (q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.LocalSorter.Exchange q)
  (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
  (hnormal : (swap q).condition) (fuel : ℕ)
  (ih :
    (n : ℕ) →
      CodedSorting.CommonLocalAdmissible.Admissible q.height fuel n →
        CodedSorting.CommonLocalRecursion.Descriptors q fuel n →
          (source buffer limit : ℕ) →
            source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
              buffer + CodedSorting.LocalSorter.space swap q hnormal fuel n ≤ limit →
                limit ≤ q.N ^ q.exponent → { p // p.charge ≤ CodedSorting.LocalSorter.budget swap q fuel n })
  (n source buffer limit : ℕ) (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
  (hl : limit ≤ q.N ^ q.exponent),
  ¬n ≤ 512 * q.height →
    ∀ (hadm : CodedSorting.CommonLocalAdmissible.Admissible q.height fuel (CodedSorting.CommonLocalNode.rowCount n))
      (hdesc :
        3 * CodedSorting.CommonLocalNode.large n < (2 ^ q.w) ^ q.digits ∧
          CodedSorting.CommonLocalRecursion.Descriptors q fuel (CodedSorting.CommonLocalNode.rowCount n))
      (hwl :
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
            max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) ≤
          limit)
      (hwa :
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n)
              (CodedSorting.CommonLocalNode.rowCount n)
              (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)) ≤
          limit)
      (hwb :
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            CodedSorting.CommonLocalRecursion.batchSpace q (CodedSorting.CommonLocalNode.side n + 1)
              (CodedSorting.CommonLocalNode.rowCount n)
              (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n)) ≤
          limit)
      (hwe :
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
              max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)) +
            (swap q).space (CodedSorting.LocalShape.sizeExponent n) hnormal ≤
          limit)
      (hsepA :
        buffer +
            CodedSorting.CommonRecordProgram.recordBlocks q
              (CodedSorting.CommonLocalNode.side n * CodedSorting.CommonLocalNode.rowCount n) ≤
          buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
            max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)))
      (hsepB :
        buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
            CodedSorting.CommonRecordProgram.recordBlocks q
              ((CodedSorting.CommonLocalNode.side n + 1) * CodedSorting.CommonLocalNode.rowCount n) ≤
          buffer + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
            max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)))
      (hr : CodedSorting.CommonLocalNode.rowCount n = 2 * CodedSorting.CommonLocalNode.half n)
      (he :
        CodedSorting.CommonLocalSemantic.pipeline (CodedSorting.CommonLocalRecursion.operation q fuel) n =
          CodedSorting.CommonLocalRecursion.operation q (fuel + 1) n),
      ((CodedSorting.CommonLocalNode.program q reader n source buffer
                (buffer +
                  max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)))
                (buffer +
                    max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                  max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)))
                limit (CodedSorting.CommonLocalRecursion.operation q fuel)
                (↑(CodedSorting.LocalSorter.batchBuild q reader fuel (CodedSorting.CommonLocalNode.side n)
                    (CodedSorting.CommonLocalNode.rowCount n)
                    (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n))
                    (CodedSorting.LocalSorter.budget swap q fuel (CodedSorting.CommonLocalNode.rowCount n))
                    (fun src bf lim hs' hw' hl' =>
                      ih (CodedSorting.CommonLocalNode.rowCount n) hadm ⋯ src bf lim hs' hw' hl')
                    buffer
                    (buffer +
                        max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                      max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)))
                    limit hsepA hwa hl))
                (↑(CodedSorting.LocalSorter.batchBuild q reader fuel (CodedSorting.CommonLocalNode.side n + 1)
                    (CodedSorting.CommonLocalNode.rowCount n)
                    (CodedSorting.LocalSorter.space swap q hnormal fuel (CodedSorting.CommonLocalNode.rowCount n))
                    (CodedSorting.LocalSorter.budget swap q fuel (CodedSorting.CommonLocalNode.rowCount n))
                    (fun src bf lim hs' hw' hl' =>
                      ih (CodedSorting.CommonLocalNode.rowCount n) hadm ⋯ src bf lim hs' hw' hl')
                    (buffer +
                      max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)))
                    (buffer +
                        max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                      max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)))
                    limit hsepB hwb hl))
                ((swap q).forward reader (CodedSorting.LocalShape.sizeExponent n) buffer
                  (buffer +
                      max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                    max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)))
                  limit hnormal hsepA hwe hl)
                ((swap q).backward reader (CodedSorting.LocalShape.sizeExponent n) buffer
                  (buffer +
                      max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.small n)) +
                    max 1 (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonLocalNode.large n)))
                  limit hnormal hsepA hwe hl)
                hs ⋯ ⋯ hwl hl ⋯ hr).changeFunction
            he).charge ≤
        CodedSorting.LocalSorter.budget swap q (fuel + 1) n
```

**继续展开**

- [CodedSorting.KeyRecordBits.recordBot](../../../Shared/Records/RecordOperations.definitions.md#def-cf0936beb1051bd4)
- [CodedSorting.CommonLocalBudget.batchBound](CostBound.definitions.md#def-fd9bae2d2f813ccf)
- [CodedSorting.CommonLocalRecursion.operation](Program.definitions.md#def-a17b930897ca503b)
- [CodedSorting.CommonLocalSemantic.batch](Semantic.definitions.md#def-2f94e0dc8bd6f005)
- [CodedSorting.CommonLocalRecursion.batchSpace](Program.definitions.md#def-8f9b5be3d5bc2c96)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.LocalSorter.batchBuild](Program.definitions.md#def-f60b3f2c17655ef0)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLocalNode.program](Program.definitions.md#def-8c86ebfd775e64cc)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.LocalSorter.Exchange](Program.definitions.md#def-16c1e07c24ee331a)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.LocalShape.sizeExponent](../../../Shared/Programs/LocalTrace.definitions.md#def-80d9b7cd708ab67c)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.LocalSorter.Exchange.condition](Program.definitions.md#def-d7d8c3e39bc20a0d)
- [CodedSorting.LocalSorter.budget](Program.definitions.md#def-2a45f731bfb4e38e)
- [CodedSorting.CommonLocalNode.small](Program.definitions.md#def-84131018030affe6)
- [CodedSorting.CommonLocalNode.large](Program.definitions.md#def-c6fe80e6c46e1fbf)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.LocalSorter.build._proof_134](Program.definitions.md#def-751efad9ddffdc5d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.LocalSorter.build._proof_129](Program.definitions.md#def-e5763fedbc153c93)
- [CodedSorting.CommonLocalNode.side](Program.definitions.md#def-a49770b9209d9457)
- [CodedSorting.LocalSorter.Exchange.backward](Program.definitions.md#def-f7c1a9048ed96238)
- [CodedSorting.LocalSorter.Exchange.space](Program.definitions.md#def-1b5706ca953c9fda)
- [CodedSorting.CommonLocalAdmissible.Admissible](CostBound.definitions.md#def-5a4da9ae621ec1bb)
- [CodedSorting.CommonLocalNode.half](Program.definitions.md#def-2a979370257be30e)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLocalRecursion.Descriptors](Program.definitions.md#def-a7cd06ce9a69e356)
- [CodedSorting.LocalSorter.space](Program.definitions.md#def-f2c3130f446c1b5e)
- [CodedSorting.LocalSorter.Exchange.forward](Program.definitions.md#def-b16e0f6352fb0bd0)
- [CodedSorting.ResidentLeafSort.recordOrder](ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.CommonRecordProgram.Program.changeFunction](../../../Shared/Records/RecordOperations.definitions.md#def-92edf0926ce9eb39)
- [CodedSorting.LocalSorter.build._proof_135](Program.definitions.md#def-31b93cf28a636b02)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.LocalSorter.build._proof_133](Program.definitions.md#def-98031b88a82a094a)
- [CodedSorting.CommonLocalNode.rowCount](Program.definitions.md#def-201a7ae73aa74a36)
- [CodedSorting.CommonLocalSemantic.pipeline](Semantic.definitions.md#def-7b92eabdfc5498d4)
- [CodedSorting.CommonRecordProgram.Program](../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.KeyRecordBits.recordTop](../../../Shared/Records/RecordOperations.definitions.md#def-d046cc432bab29e0)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `Subtype`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Subtype.val`, `Eq`, `Not`, `instHMul`
