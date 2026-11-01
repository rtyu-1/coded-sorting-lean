# Exchange 的定义

[源码](Exchange.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-19fe65f6429dabe1"></a>
## `CodedSorting.Construction.OneLevelExchange.Setup`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L28)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun q f rows G S source temporary =>
  CodedSorting.Construction.OneLevelAssembly.Setup q (CodedSorting.Construction.ExchangeSpecialization.radix ^ f) rows G
    S source temporary
```

**继续展开**

- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-9c481fea80d256ae"></a>
## `CodedSorting.Construction.OneLevelExchange.parentCall`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L33)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {f rows G S source temporary : ℕ} →
    CodedSorting.Construction.OneLevelExchange.Setup q f rows G S source temporary →
      CodedSorting.Construction.ExchangeInterface.Call
```

**定义**

```lean
fun {q} {f rows G S source temporary} a =>
  { fieldWidth := CodedSorting.Construction.ambientDimension * f,
    prefixCount := rows * CodedSorting.Construction.streamCount, gap := G, suffix := S * q.w, source := source,
    buffer := temporary, limit := a.network.limit }
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.mk](../Bounds/ExchangeInterface.definitions.md#def-88d363c434138873)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelExchange.Setup](Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `HPow.hPow`, `Nat`, `instHPow`, `instHMul`

<a id="def-3ef9465e080c9484"></a>
## `CodedSorting.Construction.OneLevelExchange.childRow`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L36)

**类型**

```lean
CodedSorting.Construction.OneLevelChildren.Child → Fin 512
```

**定义**

```lean
fun c =>
  (CodedSorting.Construction.RankPartialSwapExecution.supports
      (CodedSorting.Construction.ExchangeSpecialization.decomposition c.fst)
      ((CodedSorting.Construction.ExchangeSpecialization.childIndex c.fst).symm c.snd)).first
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.childIndex](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-c207797430c73a26)
- [CodedSorting.Construction.OneLevelChildren.Edge](Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](../Local/ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.OneLevelChildren.Child](Children.definitions.md#def-e64350cb13f8e2d9)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.first](../Local/ExchangeFramePermutation.definitions.md#def-02149a90db5345cd)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`Equiv.instFunLike`, `Rat`, `Matrix.rank`, `Equiv`, `Sigma.fst`, `instOfNatNat`, `Fin.fintype`, `Nat`, `Equiv.symm`, `OfNat.ofNat`, `Sigma.snd`, `Fin`, `DFunLike.coe`, `Rat.commRing`

<a id="def-c9896be8e5bdae4d"></a>
## `CodedSorting.Construction.OneLevelExchange.childCol`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L39)

**类型**

```lean
CodedSorting.Construction.OneLevelChildren.Child → Fin 512
```

**定义**

```lean
fun c =>
  (CodedSorting.Construction.RankPartialSwapExecution.supports
      (CodedSorting.Construction.ExchangeSpecialization.decomposition c.fst)
      ((CodedSorting.Construction.ExchangeSpecialization.childIndex c.fst).symm c.snd)).last
```

**继续展开**

- [CodedSorting.Construction.ExchangeSpecialization.childIndex](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-c207797430c73a26)
- [CodedSorting.Construction.OneLevelChildren.Edge](Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.RankPartialSwapExecution.Support.last](../Local/ExchangeFramePermutation.definitions.md#def-4b353d14d6766402)
- [CodedSorting.Construction.ProjectionRankDecomposition.RankDecomposition.vectors](../../Circuit/Labels/ProjectionRankDecomposition.definitions.md#def-b5c5757d55a96708)
- [CodedSorting.Construction.ExchangeSpecialization.edgeProjection](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-5d2a2c893152e568)
- [CodedSorting.Construction.RankPartialSwapExecution.supports](../Local/ExchangeFramePermutation.definitions.md#def-f9dfb60db9c80af6)
- [CodedSorting.Construction.OneLevelChildren.Child](Children.definitions.md#def-e64350cb13f8e2d9)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.Construction.ExchangeSpecialization.decomposition](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-cb79f0bb8a242ac3)

**基础库名称**

`Equiv.instFunLike`, `Rat`, `Matrix.rank`, `Equiv`, `Sigma.fst`, `instOfNatNat`, `Fin.fintype`, `Nat`, `Equiv.symm`, `OfNat.ofNat`, `Sigma.snd`, `Fin`, `DFunLike.coe`, `Rat.commRing`

<a id="def-c44b5f6f2dd5dc0f"></a>
## `CodedSorting.Construction.OneLevelExchange.edgeSource`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L42)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {f rows G S : ℕ} →
    CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout q f rows G (S * q.w) →
      CodedSorting.Construction.OneLevelChildren.Edge → ℕ
```

**定义**

```lean
fun {q} {f rows G S} layout e =>
  CodedSorting.Construction.MachineNetwork.Layout.base layout
    (CodedSorting.Construction.MachineNetworkActualEdges.edgeFile e)
```

**继续展开**

- [CodedSorting.Construction.OneLevelChildren.Edge](Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetworkActualEdges.FileVolume](../../Circuit/NetworkModel/Adapter.definitions.md#def-144522652fb8afb5)
- [CodedSorting.Construction.MachineNetwork.Layout.base](../../Circuit/NetworkModel/Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.MachineNetworkActualEdges.edgeFile](../../Circuit/NetworkModel/Adapter.definitions.md#def-86cc50413ebfb416)
- [CodedSorting.Construction.MachineNetworkActualEdges.NetworkLayout](../../Circuit/NetworkModel/Adapter.definitions.md#def-0fcc35f8c0cdcb8a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkActualEdges.NodeCount](../../Circuit/NetworkModel/Adapter.definitions.md#def-f0b5bd767df80c65)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-3343cdc150a25701"></a>
## `CodedSorting.Construction.OneLevelExchange.childCall`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L48)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {f rows G S source temporary : ℕ} →
    CodedSorting.Construction.OneLevelExchange.Setup q f rows G S source temporary →
      CodedSorting.Construction.OneLevelChildren.Child → CodedSorting.Construction.ExchangeInterface.Call
```

**定义**

```lean
fun {q} {f rows G S source temporary} a c =>
  CodedSorting.Construction.StreamSplitLayout.selectedCall CodedSorting.Construction.ExchangeSpecialization.radix 512 f
    rows G (S * q.w) (CodedSorting.Construction.OneLevelExchange.childRow c)
    (CodedSorting.Construction.OneLevelExchange.childCol c)
    (CodedSorting.Construction.OneLevelExchange.edgeSource a.network c.fst) a.network.buffer a.network.limit
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.buffer](../../Circuit/NetworkModel/Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.OneLevelChildren.Edge](Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelExchange.childRow](Exchange.definitions.md#def-3ef9465e080c9484)
- [CodedSorting.Construction.OneLevelExchange.Setup](Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.OneLevelExchange.edgeSource](Exchange.definitions.md#def-c44b5f6f2dd5dc0f)
- [CodedSorting.Construction.OneLevelExchange.childCol](Exchange.definitions.md#def-c9896be8e5bdae4d)
- [CodedSorting.Construction.StreamSplitLayout.selectedCall](../Streams/StreamParentProgram.definitions.md#def-dcc489e2f022255b)
- [CodedSorting.Construction.OneLevelChildren.Child](Children.definitions.md#def-e64350cb13f8e2d9)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Sigma.fst`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-8c69d438c4744692"></a>
## `CodedSorting.Construction.OneLevelExchange.Children`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L52)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {f rows G S source temporary : ℕ} →
    CodedSorting.Construction.OneLevelExchange.Setup q f rows G S source temporary → Type
```

**定义**

```lean
fun {q} {f rows G S source temporary} a =>
  (c : CodedSorting.Construction.OneLevelChildren.Child) →
    CodedSorting.Construction.ExchangeInterface.Program q CodedSorting.Construction.ExchangeSpecialization.radix
      (CodedSorting.Construction.OneLevelExchange.childCall a c)
```

**继续展开**

- [CodedSorting.Construction.OneLevelExchange.childCall](Exchange.definitions.md#def-3343cdc150a25701)
- [CodedSorting.Construction.OneLevelExchange.Setup](Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.OneLevelChildren.Child](Children.definitions.md#def-e64350cb13f8e2d9)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat`

<a id="def-298c45e5c2d34912"></a>
## `CodedSorting.Construction.OneLevelExchange.selectedChildren`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L55)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {f rows G S source temporary : ℕ} →
    (a : CodedSorting.Construction.OneLevelExchange.Setup q f rows G S source temporary) →
      CodedSorting.Construction.OneLevelExchange.Children a →
        CodedSorting.Construction.MachineNetworkActualEdges.NetworkChildren q f rows G (S * q.w) a.network
```

**定义**

```lean
fun {q} {f rows G S source temporary} a children e i =>
  CodedSorting.Construction.StreamSplitLayout.selectedChildProgram q
    CodedSorting.Construction.ExchangeSpecialization.radix 512 f rows G (S * q.w)
    (CodedSorting.Construction.OneLevelExchange.childRow ⟨e, i⟩)
    (CodedSorting.Construction.OneLevelExchange.childCol ⟨e, i⟩)
    (CodedSorting.Construction.OneLevelExchange.edgeSource a.network e) a.network.buffer a.network.limit
    (children ⟨e, i⟩)
```

**继续展开**

- [CodedSorting.Construction.OneLevelExchange.Children](Exchange.definitions.md#def-8c69d438c4744692)
- [CodedSorting.Construction.MachineNetwork.Layout.buffer](../../Circuit/NetworkModel/Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.OneLevelChildren.Edge](Children.definitions.md#def-299c106d65a6a02a)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelExchange.childRow](Exchange.definitions.md#def-3ef9465e080c9484)
- [CodedSorting.Construction.OneLevelExchange.Setup](Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.OneLevelExchange.edgeSource](Exchange.definitions.md#def-c44b5f6f2dd5dc0f)
- [CodedSorting.Construction.OneLevelExchange.childCol](Exchange.definitions.md#def-c9896be8e5bdae4d)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelChildren.edgeRank](Children.definitions.md#def-30d83915a3eba2c8)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.StreamSplitLayout.selectedChildProgram](../Streams/StreamParentProgram.definitions.md#def-00a3279ded565a44)
- [CodedSorting.Construction.MachineNetworkActualEdges.NetworkChildren](../../Circuit/NetworkModel/Adapter.definitions.md#def-fe923d3731d18bb4)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `Sigma.mk`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-090e1fe1072f0c50"></a>
## `CodedSorting.Construction.OneLevelExchange.edgePrograms`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L68)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {f rows G S source temporary : ℕ} →
    Fin q.inventory.readers →
      0 < G →
        0 < S →
          (a : CodedSorting.Construction.OneLevelExchange.Setup q f rows G S source temporary) →
            a.network.buffer +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.Construction.OneLevelAssembly.localVolume q
                      (CodedSorting.Construction.ExchangeSpecialization.radix ^ f) rows G S) ≤
                a.network.limit →
              CodedSorting.Construction.OneLevelExchange.Children a →
                CodedSorting.Construction.MachineNetwork.Programs
                  (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit
                    (CodedSorting.Construction.ExchangeSpecialization.location f rows G (S * q.w)))
                  a.network
```

**定义**

```lean
fun {q} {f rows G S source temporary} reader hG hS a hroom children =>
  CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms f rows G (S * q.w) q reader hG ⋯ a.network hroom
    (CodedSorting.Construction.OneLevelExchange.selectedChildren a children)
```

**继续展开**

- [CodedSorting.Construction.OneLevelExchange.Children](Exchange.definitions.md#def-8c69d438c4744692)
- [CodedSorting.Construction.MachineNetwork.Layout.buffer](../../Circuit/NetworkModel/Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelExchange.Setup](Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.OneLevelExchange.selectedChildren](Exchange.definitions.md#def-298c45e5c2d34912)
- [CodedSorting.Construction.OneLevelExchange.edgePrograms._proof_2](Exchange.definitions.md#def-9313594443c1de7a)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.Construction.ExchangeSpecialization.location](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-ccfe084da8739a92)
- [CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms](../../Circuit/NetworkModel/Adapter.definitions.md#def-29921c75fb0340a9)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.fintype`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-03466009551b1898"></a>
## `CodedSorting.Construction.OneLevelExchange.longProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L75)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {f rows G S source temporary : ℕ} →
    Fin q.inventory.readers →
      0 < G →
        0 < S →
          (a : CodedSorting.Construction.OneLevelExchange.Setup q f rows G S source temporary) →
            a.network.buffer +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.Construction.OneLevelAssembly.localVolume q
                      (CodedSorting.Construction.ExchangeSpecialization.radix ^ f) rows G S) ≤
                a.network.limit →
              CodedSorting.Construction.OneLevelExchange.Children a →
                CodedSorting.CommonFinitePermutation.Program q
                  (CodedSorting.Construction.OneLevelAssembly.parentVolume q
                    (CodedSorting.Construction.ExchangeSpecialization.radix ^ f) rows G S)
                  source temporary a.network.limit
                  (CodedSorting.Construction.OneLevelAssembly.exchangePermutation
                    CodedSorting.Construction.ambientDimension
                    (CodedSorting.Construction.ExchangeSpecialization.radix ^ f)
                    (rows * CodedSorting.Construction.streamCount) G (S * q.w))
```

**定义**

```lean
fun {q} {f rows G S source temporary} reader hG hS a hroom children =>
  CodedSorting.Construction.OneLevelAssembly.program
    (CodedSorting.Construction.ExchangeSpecialization.location f rows G (S * q.w)) reader ⋯ a
    (CodedSorting.Construction.OneLevelExchange.edgePrograms reader hG hS a hroom children)
```

**继续展开**

- [CodedSorting.Construction.OneLevelExchange.Children](Exchange.definitions.md#def-8c69d438c4744692)
- [CodedSorting.Construction.MachineNetwork.Layout.buffer](../../Circuit/NetworkModel/Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelExchange.Setup](Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.OneLevelExchange.edgePrograms](Exchange.definitions.md#def-090e1fe1072f0c50)
- [CodedSorting.Construction.OneLevelExchange.longProgram._proof_3](Exchange.definitions.md#def-3c0c3913c98da204)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.ExchangeSpecialization.location](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-ccfe084da8739a92)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.OneLevelAssembly.parentVolume](Allocation.definitions.md#def-ad8e35ea98d92149)
- [CodedSorting.Construction.OneLevelAssembly.program](Allocation.definitions.md#def-bc744f3b286c2721)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.OneLevelAssembly.exchangePermutation](Allocation.definitions.md#def-c543f81cf060dc2a)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-5bcd2618b1c4ba4c"></a>
## `CodedSorting.Construction.OneLevelExchange.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Exchange.lean#L82)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {f rows G S source temporary : ℕ} →
    Fin q.inventory.readers →
      0 < G →
        0 < S →
          (a : CodedSorting.Construction.OneLevelExchange.Setup q f rows G S source temporary) →
            a.network.buffer +
                  CodedSorting.CommonPermutationPairs.count q
                    (CodedSorting.Construction.OneLevelAssembly.localVolume q
                      (CodedSorting.Construction.ExchangeSpecialization.radix ^ f) rows G S) ≤
                a.network.limit →
              CodedSorting.Construction.OneLevelExchange.Children a →
                CodedSorting.Construction.ExchangeInterface.Program q
                  CodedSorting.Construction.ExchangeSpecialization.radix
                  (CodedSorting.Construction.OneLevelExchange.parentCall a)
```

**定义**

```lean
fun {q} {f rows G S source temporary} reader hG hS a hroom children =>
  CodedSorting.Construction.StreamParentProgram.parentProgram q CodedSorting.Construction.ExchangeSpecialization.radix
    CodedSorting.Construction.ambientDimension f (rows * CodedSorting.Construction.streamCount) G (S * q.w) source
    temporary a.network.limit (CodedSorting.Construction.OneLevelExchange.longProgram reader hG hS a hroom children)
```

**继续展开**

- [CodedSorting.Construction.OneLevelExchange.longProgram](Exchange.definitions.md#def-03466009551b1898)
- [CodedSorting.Construction.OneLevelExchange.Children](Exchange.definitions.md#def-8c69d438c4744692)
- [CodedSorting.Construction.MachineNetwork.Layout.buffer](../../Circuit/NetworkModel/Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelExchange.Setup](Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.Construction.StreamParentProgram.parentProgram](../Streams/StreamParentProgram.definitions.md#def-75a80ebc49d33ab7)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.OneLevelExchange.parentCall](Exchange.definitions.md#def-9c481fea80d256ae)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-9313594443c1de7a"></a>
## `CodedSorting.Construction.OneLevelExchange.edgePrograms._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Exchange.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {f rows G S source temporary : ℕ},
  0 < S → CodedSorting.Construction.OneLevelExchange.Setup q f rows G S source temporary → S * q.w > 0
```

**继续展开**

- [CodedSorting.Construction.OneLevelExchange.Setup](Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `GT.gt`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-3c0c3913c98da204"></a>
## `CodedSorting.Construction.OneLevelExchange.longProgram._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Exchange.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {f rows G S : ℕ}
  (r : CodedSorting.Construction.ThreeCopySchedule.IndependentStream),
  (Equiv.symm
          (CodedSorting.Construction.ExchangeSpecialization.location f rows G (S * q.w)
            (CodedSorting.ProgramNetwork.Vertex.sink
              (Sum.inl (CodedSorting.Construction.TensorThreeRound.originalSwap r))))).trans
      (CodedSorting.Construction.ExchangeSpecialization.location f rows G (S * q.w)
        (CodedSorting.ProgramNetwork.Vertex.source (Sum.inl r))) =
    CodedSorting.Construction.ExchangeFramePermutation.numericExchange rows G (S * q.w)
```

**继续展开**

- [CodedSorting.Construction.TensorThreeRound.originalSwap](../../Circuit/Composition/TensorThreeRound.definitions.md#def-8b3c0826e8b41aa5)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.ProgramNetwork.Vertex.source](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.ExchangeFramePermutation.numericExchange](../Local/ExchangeFramePermutation.definitions.md#def-04231f8608859801)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.ProgramNetwork.Vertex.sink](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.Construction.ExchangeSpecialization.location](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-ccfe084da8739a92)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instMulNat`, `instOfNatNat`, `Sum.inl`, `Fin.fintype`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Eq`, `List.length`, `DFunLike.coe`, `instHMul`
