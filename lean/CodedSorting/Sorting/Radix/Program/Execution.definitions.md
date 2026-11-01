# Execution 的定义

[源码](Execution.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-8ec3edabd6b7a7b7"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.nodeWork`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L15)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal K n =>
  max (CodedSorting.Construction.Sorting.CommonMSDChunks.space q normal n)
    (CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q) +
      CodedSorting.CommonMSDChunks.chunkCount q n * CodedSorting.CommonMSDDirectory.blocks q K)
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonMSDChunks.chunkSize](../Framework/Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.CommonMSDChunks.chunkCount](../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonMSDDirectory.blocks](../Framework/Directory.definitions.md#def-2a36fe66dfedd827)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.space](../SemanticCost.definitions.md#def-ca744a79f4318f82)

**基础库名称**

`HMul.hMul`, `Nat.instMax_mathlib`, `instMulNat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `instHMul`

<a id="def-c96715da80f3c732"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.workSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L20)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal N K =>
  (Finset.range (N + 1)).sup fun n =>
    max (CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.nodeWork q normal K n)
      (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q normal n)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space](../LocalGroups/Local.definitions.md#def-cb6c05b26fef8869)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.nodeWork](Execution.definitions.md#def-8ec3edabd6b7a7b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`Nat.instLattice`, `Lattice.toSemilatticeSup`, `Nat.instMax_mathlib`, `instOfNatNat`, `Finset.range`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `Finset.sup`, `Nat.instOrderBot`, `OfNat.ofNat`

<a id="def-f955d3ccc818eebf"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arenaSpan`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L24)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal N K =>
  3 * CodedSorting.CommonRecordProgram.recordBlocks q N +
      CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.workSize q normal N K +
    6
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.workSize](Execution.definitions.md#def-c96715da80f3c732)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-2eb8f2c2cf85fa2a"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L27)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal N K data depth =>
  data + CodedSorting.CommonRecordProgram.recordBlocks q N + 2 +
    depth * CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arenaSpan q normal N K
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arenaSpan](Execution.definitions.md#def-f955d3ccc818eebf)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-fedd49ae0f70e4a5"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L30)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal N K data depth =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q normal N K data depth +
      CodedSorting.CommonRecordProgram.recordBlocks q N +
    2
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena](Execution.definitions.md#def-2eb8f2c2cf85fa2a)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-31463af20c9419a7"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L33)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal N K data depth =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer q normal N K data depth +
    CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.workSize q normal N K
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.workSize](Execution.definitions.md#def-c96715da80f3c732)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer](Execution.definitions.md#def-fedd49ae0f70e4a5)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-83bd47cc97b83efa"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L36)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal N K data depth =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit q normal N K data depth + 2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit](Execution.definitions.md#def-31463af20c9419a7)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-41651fab68c239de"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L39)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal N K L data => CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q normal N K data (L + 1)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena](Execution.definitions.md#def-2eb8f2c2cf85fa2a)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-eb1b9d18bcf9918a"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.endAddress`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L42)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q normal N K L data =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack q normal N K L data +
    (L + 1) * CodedSorting.CommonMSDStack.frameBlocks q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonMSDStack.frameBlocks](../Framework/StackFrames.definitions.md#def-0909f815c38bd731)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack](Execution.definitions.md#def-41651fab68c239de)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-5d3551d53561f009"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Execution.lean#L45)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.RecursiveParameters.Normalized q → ℕ → ℕ → ℕ → ℕ → Prop
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity.mk](Execution.definitions.md#def-0aea59128ca012dc)

**基础库名称**

`Nat`

<a id="def-0aea59128ca012dc"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Execution.lean#L45)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  {normal : CodedSorting.Construction.RecursiveParameters.Normalized q} {N K L data : ℕ},
  N ≤ q.N →
    2 ≤ q.exponent →
      CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.endAddress q normal N K L data ≤ q.N ^ q.exponent →
        CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal N K L data
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.endAddress](Execution.definitions.md#def-eb1b9d18bcf9918a)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-57dc07ec8615b2e3"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity.exponent`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean#L47)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}
  {normal : CodedSorting.Construction.RecursiveParameters.Normalized q} {N K L data : ℕ},
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal N K L data → 2 ≤ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-fec77448207f7beb"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit_capacity`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean#L121)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (normal : CodedSorting.Construction.RecursiveParameters.Normalized q) (N K L data depth : ℕ),
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal N K L data →
    depth ≤ L →
      CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit q normal N K data depth ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit](Execution.definitions.md#def-31463af20c9419a7)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-aa3daa9aad9401e5"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L129)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (normal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
    (N K L data depth n : ℕ) →
      CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal N K L data →
        depth ≤ L → n ≤ N → CodedSorting.RadixNode.Pass.Resources q normal n K
```

**定义**

```lean
fun q normal N K L data depth n h hd hn =>
  { source := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q normal N K data depth,
    buffer := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer q normal N K data depth,
    limit := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit q normal N K data depth, exponent := ⋯,
    source_before := ⋯, prepare_space := ⋯, directory_space := ⋯, capacity := ⋯, descriptors := ⋯, counters := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_7](Execution.definitions.md#def-7c1e557bc2170c81)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_4](Execution.definitions.md#def-a5a582471ba09673)
- [CodedSorting.Construction.Sorting.CommonMSDNodePass.instChunkSorterNormalized](../Partition/Pass.definitions.md#def-a4a2740124386cfb)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_3](Execution.definitions.md#def-8fc1faa146d9f93e)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit_capacity](Execution.definitions.md#def-fec77448207f7beb)
- [CodedSorting.RadixNode.Pass.Resources.mk](../Partition/Framework/Pass.definitions.md#def-bcd7e0187e2f4441)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_6](Execution.definitions.md#def-9b4386b5d6b66525)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity.exponent](Execution.definitions.md#def-57dc07ec8615b2e3)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena](Execution.definitions.md#def-2eb8f2c2cf85fa2a)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_5](Execution.definitions.md#def-0369812046f3cdbd)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer](Execution.definitions.md#def-fedd49ae0f70e4a5)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit](Execution.definitions.md#def-31463af20c9419a7)
- [CodedSorting.RadixNode.Pass.Resources](../Partition/Framework/Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-0c0085ac85ce8641"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalControl.instLocalSorterNormalized`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L206)

**类型**

```lean
CodedSorting.RadixController.LocalSorter CodedSorting.Construction.RecursiveParameters.Normalized
```

**定义**

```lean
{ space := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space,
  charge := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge,
  program := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program,
  program_charge := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program_charge }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space](../LocalGroups/Local.definitions.md#def-cb6c05b26fef8869)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program_charge](../LocalGroups/Local.definitions.md#def-d07142e4e481d71a)
- [CodedSorting.RadixController.LocalSorter.mk](Shared/Control.definitions.md#def-74464258233c8a8d)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program](../LocalGroups/Local.definitions.md#def-6f054ddde493018b)
- [CodedSorting.RadixController.LocalSorter](Shared/Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge](../LocalGroups/Local.definitions.md#def-abd09b9ab586963a)

<a id="def-97c6580aee0dc4ba"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalControl.Components`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L213)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → Type
```

**定义**

```lean
CodedSorting.RadixController.Components CodedSorting.Construction.RecursiveParameters.Normalized
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.RadixController.Components](Shared/Control.definitions.md#def-072999d65dc88a81)

**基础库名称**

`Nat`

<a id="def-011f41b096487a85"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Execution.lean#L259)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.mk](Execution.definitions.md#def-f936302f9f48bf3e)

**基础库名称**

`Nat`

<a id="def-f936302f9f48bf3e"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Execution.lean#L259)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    Fin q.inventory.readers →
      (normal : CodedSorting.Construction.RecursiveParameters.Normalized q) →
        (source : ℕ) →
          CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal q.N
              (CodedSorting.CommonMSDParameters.radix q) L source →
            CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat`, `Fin`

<a id="def-11ddc110e589ac63"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.reader`

读取 `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters` 的 `reader` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Execution.lean#L260)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} → CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L → Fin q.inventory.readers
```

**定义**

```lean
fun q L self => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`, `Fin`

<a id="def-45954b01d31331de"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean#L261)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {L : ℕ},
  CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
    CodedSorting.Construction.RecursiveParameters.Normalized q
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)

**基础库名称**

`Nat`

<a id="def-dbc0a8b302e85d67"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.source`

读取 `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters` 的 `source` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Execution.lean#L262)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} → CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L → ℕ
```

**定义**

```lean
fun q L self => self.3
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-0ba010e389d669e6"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.capacity`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean#L263)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {L : ℕ}
  (self : CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L),
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q ⋯ q.N
    (CodedSorting.CommonMSDParameters.radix q) L self.source
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.source](Execution.definitions.md#def-dbc0a8b302e85d67)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal](Execution.definitions.md#def-45954b01d31331de)

**基础库名称**

`Nat`

<a id="def-5cb5e8413d08ce81"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L267)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    (p : CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L) →
      (j : CodedSorting.RadixController.Job q.N L) →
        CodedSorting.RadixNode.Pass.Resources q ⋯ (CodedSorting.RadixController.records j)
          (CodedSorting.CommonMSDParameters.radix q)
```

**定义**

```lean
fun {q} {L} p j =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources q ⋯ q.N
    (CodedSorting.CommonMSDParameters.radix q) L p.source (CodedSorting.RadixController.depth j)
    (CodedSorting.RadixController.records j) ⋯ ⋯ ⋯
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources._proof_10](Execution.definitions.md#def-5c7d3fe1d6cce106)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.source](Execution.definitions.md#def-dbc0a8b302e85d67)
- [CodedSorting.Construction.Sorting.CommonMSDNodePass.instChunkSorterNormalized](../Partition/Pass.definitions.md#def-a4a2740124386cfb)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.RadixController.depth](Shared/Control.definitions.md#def-6695bf5c325da18a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.capacity](Execution.definitions.md#def-0ba010e389d669e6)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources](Execution.definitions.md#def-aa3daa9aad9401e5)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal](Execution.definitions.md#def-45954b01d31331de)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources._proof_11](Execution.definitions.md#def-a924f6f1d3534669)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)
- [CodedSorting.RadixNode.Pass.Resources](../Partition/Framework/Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`Nat`

<a id="def-de8f1821ad4229a4"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.target`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L273)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
      CodedSorting.RadixController.Job q.N L → ℕ
```

**定义**

```lean
fun {q} {L} p j =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target q ⋯ q.N (CodedSorting.CommonMSDParameters.radix q)
    p.source (CodedSorting.RadixController.depth j)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.source](Execution.definitions.md#def-dbc0a8b302e85d67)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target](Execution.definitions.md#def-83bd47cc97b83efa)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.RadixController.depth](Shared/Control.definitions.md#def-6695bf5c325da18a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal](Execution.definitions.md#def-45954b01d31331de)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Nat`

<a id="def-d0b28a8e6905b6b1"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.layout`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L276)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
      (j : CodedSorting.RadixController.Job q.N L) →
        CodedSorting.CommonMSDGatherController.Layout
          (CodedSorting.CommonMSDParameters.radix q *
            CodedSorting.CommonMSDChunks.chunkCount q (CodedSorting.RadixController.records j))
```

**定义**

```lean
fun {q} {L} p j =>
  CodedSorting.CommonMSDNodeLayout.layout q (CodedSorting.RadixController.records j)
    (CodedSorting.CommonMSDParameters.radix q)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources p j).source
    (CodedSorting.RadixNode.Pass.directory q
      (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources p j).buffer)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.target p j)
```

**继续展开**

- [CodedSorting.CommonMSDNodeLayout.layout](../Partition/Framework/Semantic.definitions.md#def-4512f8319d2ae7a2)
- [CodedSorting.CommonMSDGatherController.Layout](../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.Construction.Sorting.CommonMSDNodePass.instChunkSorterNormalized](../Partition/Pass.definitions.md#def-a4a2740124386cfb)
- [CodedSorting.RadixNode.Pass.Resources.source](../Partition/Framework/Pass.definitions.md#def-c21ef7c63575f8b9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources](Execution.definitions.md#def-5cb5e8413d08ce81)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.RadixNode.Pass.directory](../Partition/Framework/Pass.definitions.md#def-5d7e0afd280f2f9d)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.target](Execution.definitions.md#def-de8f1821ad4229a4)
- [CodedSorting.CommonMSDChunks.chunkCount](../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.RadixNode.Pass.Resources.buffer](../Partition/Framework/Pass.definitions.md#def-39e4c91d6c7020f5)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal](Execution.definitions.md#def-45954b01d31331de)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-b35290d37ccd5853"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.inner`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L281)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
      (j : CodedSorting.RadixController.Job q.N L) →
        CodedSorting.CommonMSDRoutine.Routine q
          (CodedSorting.RadixNode.Controller.tagCount
            (CodedSorting.CommonMSDParameters.radix q *
              CodedSorting.CommonMSDChunks.chunkCount q (CodedSorting.RadixController.records j))
            (3 * CodedSorting.RadixController.records j))
```

**定义**

```lean
fun {q} {L} p j =>
  CodedSorting.RadixNode.Controller.routine q p.reader
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources p j) ⋯
    (CodedSorting.CommonMSDRecordDigits.wordDigit q (CodedSorting.CommonMSDParameters.radix q) ⋯
      (CodedSorting.RadixController.level j - 1))
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.layout p j)
```

**继续展开**

- [CodedSorting.CommonMSDParameters.directory_fits](../Framework/Directory.definitions.md#def-a41af147cea47d2a)
- [CodedSorting.RadixNode.Controller.routine](../Partition/Framework/Pass.definitions.md#def-da05d003cbe1e9a6)
- [CodedSorting.Construction.Sorting.CommonMSDNodePass.instChunkSorterNormalized](../Partition/Pass.definitions.md#def-a4a2740124386cfb)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources](Execution.definitions.md#def-5cb5e8413d08ce81)
- [CodedSorting.RadixNode.Controller.tagCount](../Partition/Framework/Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.CommonMSDRoutine.Routine](../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.RadixController.level](Shared/Control.definitions.md#def-c5e0bd5ef519c49d)
- [CodedSorting.CommonMSDChunks.chunkCount](../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonMSDRecordDigits.wordDigit](../Framework/RadixCost.definitions.md#def-ceb2aa51e1b9fa44)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.reader](Execution.definitions.md#def-11ddc110e589ac63)
- [CodedSorting.CommonMSDRadixCost.radixPositive](../Framework/RadixCost.definitions.md#def-f72ab7395f5a785c)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal](Execution.definitions.md#def-45954b01d31331de)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.layout](Execution.definitions.md#def-d0b28a8e6905b6b1)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `instSubNat`, `instMulNat`, `instOfNatNat`, `instHSub`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-b80082e88635c19d"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.interval`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L288)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
      (j : CodedSorting.RadixController.Job q.N L) →
        CodedSorting.CommonMSDRoutine.Routine q
          (CodedSorting.RadixNode.Controller.tagCount
              (CodedSorting.CommonMSDParameters.radix q *
                CodedSorting.CommonMSDChunks.chunkCount q (CodedSorting.RadixController.records j))
              (3 * CodedSorting.RadixController.records j) +
            3)
```

**定义**

```lean
fun {q} {L} p j =>
  CodedSorting.CommonMSDIntervalRoutine.routine q p.reader (CodedSorting.RadixController.records j) p.source
    (CodedSorting.RadixController.offset j)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources p j).source
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.target p j)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.inner p j)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.source](Execution.definitions.md#def-dbc0a8b302e85d67)
- [CodedSorting.Construction.Sorting.CommonMSDNodePass.instChunkSorterNormalized](../Partition/Pass.definitions.md#def-a4a2740124386cfb)
- [CodedSorting.RadixNode.Pass.Resources.source](../Partition/Framework/Pass.definitions.md#def-c21ef7c63575f8b9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources](Execution.definitions.md#def-5cb5e8413d08ce81)
- [CodedSorting.RadixController.offset](Shared/Control.definitions.md#def-99ba717ce1accffc)
- [CodedSorting.RadixNode.Controller.tagCount](../Partition/Framework/Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.target](Execution.definitions.md#def-de8f1821ad4229a4)
- [CodedSorting.CommonMSDRoutine.Routine](../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonMSDChunks.chunkCount](../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonMSDIntervalRoutine.routine](../LocalGroups/Framework/Routine.definitions.md#def-9448d2fdb0ad3d1a)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.reader](Execution.definitions.md#def-11ddc110e589ac63)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.inner](Execution.definitions.md#def-b35290d37ccd5853)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal](Execution.definitions.md#def-45954b01d31331de)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-4ea0f88ff2a2dde5"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.node`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L294)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
      CodedSorting.RadixController.Job q.N L →
        CodedSorting.CommonMSDRoutine.Routine q
          (CodedSorting.CommonMSDNodeTagBound.bound q (CodedSorting.CommonMSDParameters.radix q))
```

**定义**

```lean
fun {q} {L} p j =>
  CodedSorting.CommonMSDRoutinePad.extend (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.interval p j) ⋯
```

**继续展开**

- [CodedSorting.RadixNode.Controller.tagCount](../Partition/Framework/Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.node._proof_12](Execution.definitions.md#def-943924b4c6c9ede7)
- [CodedSorting.CommonMSDRoutine.Routine](../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonMSDChunks.chunkCount](../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.interval](Execution.definitions.md#def-b80082e88635c19d)
- [CodedSorting.CommonMSDRoutinePad.extend](../Framework/Routine.definitions.md#def-46914cb3fda49d20)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-0a402263c394c7a4"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.directories`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L299)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
      CodedSorting.RadixController.Job q.N L → List ℕ
```

**定义**

```lean
fun {q} {L} p j =>
  List.ofFn fun i =>
    CodedSorting.CommonMSDRowDirectoryBatch.target q (CodedSorting.CommonMSDParameters.radix q)
      (CodedSorting.RadixNode.Pass.directory q
        (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources p j).buffer)
      ↑i
```

**继续展开**

- [CodedSorting.CommonMSDRowDirectoryBatch.target](../Framework/ChunkRows.definitions.md#def-75bc861f3912fc86)
- [CodedSorting.Construction.Sorting.CommonMSDNodePass.instChunkSorterNormalized](../Partition/Pass.definitions.md#def-a4a2740124386cfb)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources](Execution.definitions.md#def-5cb5e8413d08ce81)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.RadixNode.Pass.directory](../Partition/Framework/Pass.definitions.md#def-5d7e0afd280f2f9d)
- [CodedSorting.CommonMSDChunks.chunkCount](../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.RadixNode.Pass.Resources.buffer](../Partition/Framework/Pass.definitions.md#def-39e4c91d6c7020f5)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal](Execution.definitions.md#def-45954b01d31331de)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`List.ofFn`, `Fin.val`, `List`, `Nat`, `Fin`

<a id="def-2df61f9a0707429d"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L304)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
      CodedSorting.Construction.Sorting.CommonMSDGlobalControl.Components q L
        (CodedSorting.CommonMSDNodeTagBound.bound q (CodedSorting.CommonMSDParameters.radix q))
```

**定义**

```lean
fun {q} {L} p =>
  { reader := p.reader, normal := ⋯, exponent := ⋯, source := p.source,
    stack :=
      CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack q ⋯ q.N
        (CodedSorting.CommonMSDParameters.radix q) L p.source,
    buffer := fun j => (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources p j).buffer,
    limit := fun j => (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources p j).limit,
    directories := CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.directories p,
    node := CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.node p }
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.source](Execution.definitions.md#def-dbc0a8b302e85d67)
- [CodedSorting.Construction.Sorting.CommonMSDNodePass.instChunkSorterNormalized](../Partition/Pass.definitions.md#def-a4a2740124386cfb)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components._proof_13](Execution.definitions.md#def-623ac95ae2c43b0c)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.directories](Execution.definitions.md#def-0a402263c394c7a4)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources](Execution.definitions.md#def-5cb5e8413d08ce81)
- [CodedSorting.RadixController.Components.mk](Shared/Control.definitions.md#def-5b801c4fa7a74f67)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalControl.Components](Execution.definitions.md#def-97c6580aee0dc4ba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.node](Execution.definitions.md#def-4ea0f88ff2a2dde5)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.RadixNode.Pass.Resources.buffer](../Partition/Framework/Pass.definitions.md#def-39e4c91d6c7020f5)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixNode.Pass.Resources.limit](../Partition/Framework/Pass.definitions.md#def-7f32fd4b3e3bda8a)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.reader](Execution.definitions.md#def-11ddc110e589ac63)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack](Execution.definitions.md#def-41651fab68c239de)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters.normal](Execution.definitions.md#def-45954b01d31331de)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Nat`

<a id="def-e5bd311acccb40c9"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L362)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L →
      CodedSorting.RadixController.Job q.N L →
        CodedSorting.CommonMSDRoutine.Routine q
          (CodedSorting.RadixController.tagCount q.N L
            (CodedSorting.CommonMSDNodeTagBound.bound q (CodedSorting.CommonMSDParameters.radix q))
            (CodedSorting.CommonMSDParameters.radix q))
```

**定义**

```lean
fun {q} {L} p root =>
  CodedSorting.RadixController.routine (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) root
```

**继续展开**

- [CodedSorting.RadixController.routine](Shared/Control.definitions.md#def-322bc5d4a2146055)
- [CodedSorting.RadixController.tagCount](Shared/Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.CommonMSDRoutine.Routine](../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components](Execution.definitions.md#def-2df61f9a0707429d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalControl.instLocalSorterNormalized](Execution.definitions.md#def-0c0085ac85ce8641)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Nat`

<a id="def-1725342c01d2dfb1"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L381)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.CommonMSDRadixCost.depth q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDRadixCost.depth](../Framework/RadixCost.definitions.md#def-a15d9000a7ef719c)

**基础库名称**

`Nat`

<a id="def-bc829cae6a788927"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L382)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q
    (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

<a id="def-4e4aaaa1d1a412bc"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L384)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (n : ℕ) →
    n ≤ q.N → CodedSorting.RadixController.Job q.N (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
```

**定义**

```lean
fun q n hn => (⟨CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q, ⋯⟩, 0, ⟨n, ⋯⟩, 0)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root._proof_16](Execution.definitions.md#def-80cc8d488960bdb8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root._proof_19](Execution.definitions.md#def-17ad51060ae21af1)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root._proof_17](Execution.definitions.md#def-eb764451f07db909)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root._proof_18](Execution.definitions.md#def-d2c330fba8455cc7)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fin.mk`, `Fin.instOfNat`, `Prod.mk`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-35bd519ad31cff35"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L387)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q →
    (n : ℕ) →
      n ≤ q.N →
        CodedSorting.CommonMSDRoutine.Routine q
          (CodedSorting.RadixController.tagCount q.N (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
            (CodedSorting.CommonMSDNodeTagBound.bound q (CodedSorting.CommonMSDParameters.radix q))
            (CodedSorting.CommonMSDParameters.radix q))
```

**定义**

```lean
fun q p n hn =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p
    (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root q n hn)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine](Execution.definitions.md#def-e5bd311acccb40c9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root](Execution.definitions.md#def-4e4aaaa1d1a412bc)
- [CodedSorting.RadixController.tagCount](Shared/Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters](Execution.definitions.md#def-bc829cae6a788927)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonMSDRoutine.Routine](../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-0112a46e99039243"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.strideConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L680)

**类型**

```lean
ℕ
```

**定义**

```lean
CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.nodeConstant +
    CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.leafConstant +
  101
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.nodeConstant](../CodePolynomial.definitions.md#def-0300e71df7b4911d)
- [CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.leafConstant](../CodePolynomial.definitions.md#def-8381e32da2a6e08e)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-efe5674e12eef232"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L683)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun κ => 406 * (κ + 1) ^ 2 * CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.strideConstant
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.strideConstant](Execution.definitions.md#def-0112a46e99039243)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-c3b72f2d74ffa04b"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.threshold`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Execution.lean#L685)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun κ => 2 ^ 16 * CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant](Execution.definitions.md#def-efe5674e12eef232)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-8fc1faa146d9f93e"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (normal : CodedSorting.Construction.RecursiveParameters.Normalized q) (N K : ℕ),
  ℕ →
    ∀ (data depth n : ℕ),
      n ≤ N →
        CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q normal N K data depth +
              CodedSorting.CommonRecordProgram.recordBlocks q n +
            2 ≤
          CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer q normal N K data depth
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena](Execution.definitions.md#def-2eb8f2c2cf85fa2a)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer](Execution.definitions.md#def-fedd49ae0f70e4a5)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-a5a582471ba09673"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (normal : CodedSorting.Construction.RecursiveParameters.Normalized q) (N K data depth n : ℕ),
  n ≤ N →
    CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer q normal N K data depth +
        CodedSorting.Construction.Sorting.CommonMSDChunks.space q normal n ≤
      CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer q normal N K data depth +
        CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.workSize q normal N K
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.workSize](Execution.definitions.md#def-c96715da80f3c732)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.Construction.Sorting.CommonMSDChunks.space](../SemanticCost.definitions.md#def-ca744a79f4318f82)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer](Execution.definitions.md#def-fedd49ae0f70e4a5)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-0369812046f3cdbd"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (normal : CodedSorting.Construction.RecursiveParameters.Normalized q) (N K : ℕ),
  ℕ →
    ∀ (data depth n : ℕ),
      n ≤ N →
        CodedSorting.RadixNode.Pass.directory q
              (CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer q normal N K data depth) +
            CodedSorting.CommonMSDChunks.chunkCount q n * CodedSorting.CommonMSDDirectory.blocks q K ≤
          CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit q normal N K data depth
```

**继续展开**

- [CodedSorting.RadixNode.Pass.directory](../Partition/Framework/Pass.definitions.md#def-5d7e0afd280f2f9d)
- [CodedSorting.CommonMSDChunks.chunkCount](../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonMSDDirectory.blocks](../Framework/Directory.definitions.md#def-2a36fe66dfedd827)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer](Execution.definitions.md#def-fedd49ae0f70e4a5)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit](Execution.definitions.md#def-31463af20c9419a7)

**基础库名称**

`HMul.hMul`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-9b4386b5d6b66525"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (normal : CodedSorting.Construction.RecursiveParameters.Normalized q) (N K L data n : ℕ),
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal N K L data →
    n ≤ N → 3 * CodedSorting.CommonMSDChunks.paddedSize q n < (2 ^ q.w) ^ q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonMSDChunks.paddedSize](../Framework/Chunks.definitions.md#def-1c4eec1b43cf54c2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-7c1e557bc2170c81"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration)
  (normal : CodedSorting.Construction.RecursiveParameters.Normalized q) (N K L data : ℕ),
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal N K L data →
    CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q) * q.block <
      (2 ^ q.w) ^ q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonMSDChunks.chunkSize](../Framework/Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity](Execution.definitions.md#def-5d3551d53561f009)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveParameters.Normalized](../../../Interchange/Recursion/Workspace.definitions.md#def-28a0e406b8961cb8)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-623ac95ae2c43b0c"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {L : ℕ},
  CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q L → 2 ≤ q.exponent
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters](Execution.definitions.md#def-011f41b096487a85)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-943924b4c6c9ede7"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.node._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {L : ℕ} (j : CodedSorting.RadixController.Job q.N L),
  CodedSorting.RadixNode.Controller.tagCount
        (CodedSorting.CommonMSDParameters.radix q *
          CodedSorting.CommonMSDChunks.chunkCount q (CodedSorting.RadixController.records j))
        (3 * CodedSorting.RadixController.records j) +
      3 ≤
    CodedSorting.CommonMSDNodeTagBound.bound q (CodedSorting.CommonMSDParameters.radix q)
```

**继续展开**

- [CodedSorting.RadixNode.Controller.tagCount](../Partition/Framework/Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.CommonMSDChunks.chunkCount](../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonMSDParameters.radix](../Framework/Directory.definitions.md#def-c229910078c8e8d8)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMSDNodeTagBound.bound](../Partition/Framework/Pass.definitions.md#def-66e6403c817548ea)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-5c7d3fe1d6cce106"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {L : ℕ} (j : CodedSorting.RadixController.Job q.N L),
  CodedSorting.RadixController.depth j ≤ L
```

**继续展开**

- [CodedSorting.RadixController.depth](Shared/Control.definitions.md#def-6695bf5c325da18a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-a924f6f1d3534669"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.resources._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {L : ℕ} (j : CodedSorting.RadixController.Job q.N L),
  CodedSorting.RadixController.records j ≤ q.N
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.records](Shared/Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Job](Shared/Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-80cc8d488960bdb8"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root._proof_16`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  ℕ →
    CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q <
      CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q + 1
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-eb764451f07db909"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root._proof_17`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), NeZero (q.N + 1)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-d2c330fba8455cc7"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root._proof_18`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), ∀ n ≤ q.N, n < q.N + 1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-17ad51060ae21af1"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.root._proof_19`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Execution.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  NeZero (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q + 1)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels](Execution.definitions.md#def-1725342c01d2dfb1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`
