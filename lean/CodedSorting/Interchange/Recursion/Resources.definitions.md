# Resources 的定义

[源码](Resources.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-8ce9177484f1f849"></a>
## `CodedSorting.Construction.RecursiveCostRate.exists_rate`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Resources.lean#L137)

**类型**

```lean
∃ K,
  0 ≤ K ∧
    ∀ (b cutoff k V : ℕ),
      0 < b →
        CodedSorting.Construction.streamCount * b ≤ cutoff →
          ↑(CodedSorting.Construction.ExchangeInterface.costBound
                (24 * CodedSorting.Construction.streamCount + 36 +
                  CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
                b cutoff k V) ≤
            K *
              (1 +
                ↑V / ↑b * ↑CodedSorting.Construction.ambientDimension ^ (↑k * (1 - ↑CodedSorting.Construction.epsilon)))
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.epsilon](../../Circuit/Parameters/Exponent.definitions.md#def-38e0b13c0209d8a9)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`Real.instPow`, `Real.instLE`, `Real`, `instHDiv`, `HMul.hMul`, `Real.instZero`, `Real.instDivInvMonoid`, `Real.instSub`, `Real.instRatCast`, `HSub.hSub`, `Exists`, `HDiv.hDiv`, `Rat.cast`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.cast`, `Real.instAdd`, `Real.instOne`, `instHAdd`, `And`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `LT.lt`, `DivInvMonoid.toDiv`, `One.toOfNat1`, `instAddNat`, `Zero.toOfNat0`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`, `Real.instNatCast`

<a id="def-19e9fc3555794e23"></a>
## `CodedSorting.Construction.RecursiveCostRate.rateConstant`

从已证明的存在性命题中选取一个满足条件的对象。下面链接的命题列出选取条件；阅读时需要看清先选取对象、后允许哪些参数变化。

[源码位置](Resources.lean#L147)

**类型**

```lean
ℝ
```

**定义**

```lean
Classical.choose CodedSorting.Construction.RecursiveCostRate.exists_rate
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.epsilon](../../Circuit/Parameters/Exponent.definitions.md#def-38e0b13c0209d8a9)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.RecursiveCostRate.exists_rate](Resources.definitions.md#def-8ce9177484f1f849)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`Real.instPow`, `Real.instLE`, `Real`, `instHDiv`, `HMul.hMul`, `Real.instZero`, `Real.instDivInvMonoid`, `Real.instSub`, `Real.instRatCast`, `HSub.hSub`, `HDiv.hDiv`, `Rat.cast`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.cast`, `Real.instAdd`, `Real.instOne`, `instHAdd`, `And`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `LT.lt`, `DivInvMonoid.toDiv`, `Classical.choose`, `One.toOfNat1`, `instAddNat`, `Zero.toOfNat0`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`, `Real.instNatCast`

<a id="def-a17a2c8065f3c894"></a>
## `CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Resources.lean#L489)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q V =>
  (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
          CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program +
        3) *
      (V / CodedSorting.CommonPermutationPairs.width q + 1) +
    3
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-02c29912b3c6e22e"></a>
## `CodedSorting.Construction.RecursiveWorkspaceProgram.ready_of_linear`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Resources.lean#L503)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (cutoff base k : ℕ)
  (c : CodedSorting.Construction.ExchangeInterface.Call),
  CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters q cutoff base →
    CodedSorting.CommonPermutationPairs.width q ≤ cutoff →
      CodedSorting.Construction.RecursiveCallShape.ShapeDepth q k c →
        c.fieldWidth = CodedSorting.Construction.ambientDimension ^ k * base →
          c.source +
                CodedSorting.CommonPermutationPairs.count q
                  (CodedSorting.Construction.ExchangeInterface.volume
                    CodedSorting.Construction.ExchangeSpecialization.radix c) ≤
              c.buffer →
            c.buffer +
                  CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
                    (CodedSorting.Construction.ExchangeInterface.volume
                      CodedSorting.Construction.ExchangeSpecialization.radix c) ≤
                c.limit →
              c.limit ≤ q.N ^ q.exponent → CodedSorting.Construction.RecursiveBuildConditions.Ready q cutoff k c
```

**继续展开**

- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.RecursiveBuildConditions.Ready](Build.definitions.md#def-ec5a8673d7f93825)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters](Workspace.definitions.md#def-ccdb4faa2250afa6)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Eq`, `instHMul`

<a id="def-ecb93c574fcd450c"></a>
## `CodedSorting.Construction.RecursiveWorkspaceProgram.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Resources.lean#L515)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    (cutoff base k : ℕ) →
      (c : CodedSorting.Construction.ExchangeInterface.Call) →
        CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters q cutoff base →
          CodedSorting.CommonPermutationPairs.width q ≤ cutoff →
            CodedSorting.Construction.RecursiveCallShape.ShapeDepth q k c →
              c.fieldWidth = CodedSorting.Construction.ambientDimension ^ k * base →
                c.source +
                      CodedSorting.CommonPermutationPairs.count q
                        (CodedSorting.Construction.ExchangeInterface.volume
                          CodedSorting.Construction.ExchangeSpecialization.radix c) ≤
                    c.buffer →
                  c.buffer +
                        CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve q
                          (CodedSorting.Construction.ExchangeInterface.volume
                            CodedSorting.Construction.ExchangeSpecialization.radix c) ≤
                      c.limit →
                    c.limit ≤ q.N ^ q.exponent →
                      CodedSorting.Construction.ExchangeInterface.Program q
                        CodedSorting.Construction.ExchangeSpecialization.radix c
```

**定义**

```lean
fun q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk =>
  CodedSorting.Construction.RecursiveBuild.build q reader cutoff k c ⋯
```

**继续展开**

- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.RecursiveWorkspaceBudget.LeafParameters](Workspace.definitions.md#def-ccdb4faa2250afa6)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.ready_of_linear](Resources.definitions.md#def-02c29912b3c6e22e)
- [CodedSorting.Construction.RecursiveBuild.build](Build.definitions.md#def-6eaefa37259d3a83)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.CommonPermutationPairs.width](../Framework/Memory/Reflection.definitions.md#def-cf4f87b7a0e5726b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveWorkspaceProgram.linearReserve](Resources.definitions.md#def-a17a2c8065f3c894)
- [CodedSorting.Construction.ExchangeInterface.volume](../Bounds/ExchangeInterface.definitions.md#def-2265644281f87336)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Fin`, `Eq`, `instHMul`
