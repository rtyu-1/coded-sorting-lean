# Allocation 的定义

[源码](Allocation.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-18e194898352b8ed"></a>
## `CodedSorting.Construction.OneLevelAssembly.localVolume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L28)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q Q rows G S =>
  CodedSorting.CommonAddressLayout.Volume (Fin CodedSorting.Construction.ambientDimension) rows Q G (S * q.w)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `Nat`, `Fin`, `instHMul`

<a id="def-ad8e35ea98d92149"></a>
## `CodedSorting.Construction.OneLevelAssembly.parentVolume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L31)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q Q rows G S =>
  CodedSorting.CommonAddressLayout.Volume (Fin CodedSorting.Construction.ambientDimension)
    (rows * CodedSorting.Construction.streamCount) Q G (S * q.w)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.fintype`, `Nat`, `Fin`, `instHMul`

<a id="def-c543f81cf060dc2a"></a>
## `CodedSorting.Construction.OneLevelAssembly.exchangePermutation`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L37)

**类型**

```lean
(m Q rows G S : ℕ) → Equiv.Perm (Fin (CodedSorting.CommonAddressLayout.Volume (Fin m) rows Q G S))
```

**定义**

```lean
fun m Q rows G S =>
  CodedSorting.CommonAddressLayout.longLayout.symm.trans
    (CodedSorting.Address.exchangeEquiv.trans CodedSorting.CommonAddressLayout.longLayout)
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.exchangeEquiv](../../Shared/Memory/Address.definitions.md#def-fad92f68940cdb8b)
- [CodedSorting.CommonAddressLayout.longLayout](../Framework/Memory/AddressLayout.definitions.md#def-6ebf2402101b2f28)
- [CodedSorting.Construction.OneLevelAssembly.exchangePermutation._proof_1](Allocation.definitions.md#def-03821d92287ba9f3)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)

**基础库名称**

`Equiv.trans`, `Fin.fintype`, `Fin.instLinearOrder`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`

<a id="def-e9291a74eb66b4de"></a>
## `CodedSorting.Construction.OneLevelAssembly.Setup`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Allocation.lean#L47)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.Construction.OneLevelAssembly.Setup.mk](Allocation.definitions.md#def-5714161b00708e26)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-5714161b00708e26"></a>
## `CodedSorting.Construction.OneLevelAssembly.Setup.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Allocation.lean#L47)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {Q rows G S source temporary : ℕ} →
    (network :
        CodedSorting.Construction.MachineNetwork.Layout q CodedSorting.Construction.MachineNetworkAdapter.physicalInputs
          (CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)
          (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)) →
      source +
            CodedSorting.CommonPermutationPairs.count q
              (CodedSorting.Construction.OneLevelAssembly.parentVolume q Q rows G S) ≤
          temporary →
        temporary +
              CodedSorting.CommonPermutationPairs.count q
                (CodedSorting.Construction.OneLevelAssembly.parentVolume q Q rows G S) ≤
            network.workspace →
          CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.Construction.MachineNetwork.Layout.workspace](../../Circuit/NetworkModel/Definitions.definitions.md#def-a6f26d9ff32e3cb9)
- [CodedSorting.Construction.MachineNetwork.Layout](../../Circuit/NetworkModel/Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.OneLevelAssembly.parentVolume](Allocation.definitions.md#def-ad8e35ea98d92149)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-5f40cc5c5136d5e1"></a>
## `CodedSorting.Construction.OneLevelAssembly.Setup.network`

读取 `CodedSorting.Construction.OneLevelAssembly.Setup` 的 `network` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Allocation.lean#L48)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {Q rows G S source temporary : ℕ} →
    CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary →
      CodedSorting.Construction.MachineNetwork.Layout q CodedSorting.Construction.MachineNetworkAdapter.physicalInputs
        (CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)
        (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)
```

**定义**

```lean
fun q Q rows G S source temporary self => self.1
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.Construction.MachineNetwork.Layout](../../Circuit/NetworkModel/Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`Nat`

<a id="def-11a7f654a60e800f"></a>
## `CodedSorting.Construction.OneLevelAssembly.Setup.workspace_fits`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean#L54)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {Q rows G S source temporary : ℕ}
  (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary),
  a.network.workspace +
      (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
          CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program) *
        a.network.stride ≤
    q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.Construction.MachineNetwork.Layout.workspace](../../Circuit/NetworkModel/Definitions.definitions.md#def-a6f26d9ff32e3cb9)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.MachineNetwork.Layout.stride](../../Circuit/NetworkModel/Definitions.definitions.md#def-2516d89bed459156)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `instHMul`

<a id="def-d5fc5585180e069e"></a>
## `CodedSorting.Construction.OneLevelAssembly.inputSlot`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L66)

**类型**

```lean
Fin CodedSorting.Construction.streamCount →
  Fin
    (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
      CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)
```

**定义**

```lean
CodedSorting.Construction.MachineNetworkAdapter.inputSlot
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.MachineNetworkAdapter.inputSlot](../../Circuit/NetworkModel/Adapter.definitions.md#def-89ed902f7aacf974)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-ad010355ec5e3af9"></a>
## `CodedSorting.Construction.OneLevelAssembly.outputSlot`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L69)

**类型**

```lean
Fin CodedSorting.Construction.streamCount →
  Fin
    (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
      CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program)
```

**定义**

```lean
CodedSorting.Construction.MachineNetworkAdapter.outputSlot
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.MachineNetworkAdapter.outputSlot](../../Circuit/NetworkModel/Adapter.definitions.md#def-a4493f235434aee1)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-90ab2eeeae419101"></a>
## `CodedSorting.Construction.OneLevelAssembly.inputSlot_injective`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean#L71)

**类型**

```lean
Function.Injective CodedSorting.Construction.OneLevelAssembly.inputSlot
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.OneLevelAssembly.inputSlot](Allocation.definitions.md#def-d5fc5585180e069e)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Function.Injective`, `Fin`

<a id="def-7aed789ccf9e04a0"></a>
## `CodedSorting.Construction.OneLevelAssembly.outputSlot_injective`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean#L74)

**类型**

```lean
Function.Injective CodedSorting.Construction.OneLevelAssembly.outputSlot
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.OneLevelAssembly.outputSlot](Allocation.definitions.md#def-ad010355ec5e3af9)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Function.Injective`, `Fin`

<a id="def-cd7c1a2999f10911"></a>
## `CodedSorting.Construction.OneLevelAssembly.slabs`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L77)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {Q rows G S source temporary : ℕ} →
    CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary →
      (slot :
          Fin CodedSorting.Construction.streamCount →
            Fin
              (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
                CodedSorting.Construction.MachineNetworkAdapter.nodes
                  CodedSorting.Construction.TensorFrameNetwork.program)) →
        Function.Injective slot →
          CodedSorting.Construction.StreamSplitMachine.Slabs q CodedSorting.Construction.streamCount
            (CodedSorting.CommonAddressLayout.Volume (Fin CodedSorting.Construction.ambientDimension) rows Q G S)
```

**定义**

```lean
fun {q} {Q rows G S source temporary} a slot hinj =>
  CodedSorting.Construction.StreamSplitMachine.allocatedSlabs q
    (CodedSorting.CommonAddressLayout.Volume (Fin CodedSorting.Construction.ambientDimension) rows Q G S)
    a.network.workspace a.network.stride slot hinj ⋯ ⋯
```

**继续展开**

- [CodedSorting.Construction.OneLevelAssembly.Setup.workspace_fits](Allocation.definitions.md#def-11a7f654a60e800f)
- [CodedSorting.Construction.StreamSplitMachine.Slabs](../Streams/StreamParentProgram.definitions.md#def-2de8638d376413a2)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.Construction.MachineNetwork.Layout.workspace](../../Circuit/NetworkModel/Definitions.definitions.md#def-a6f26d9ff32e3cb9)
- [CodedSorting.Construction.StreamSplitMachine.allocatedSlabs](../Streams/StreamParentProgram.definitions.md#def-7dd58b8187823e96)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetwork.Layout.stride](../../Circuit/NetworkModel/Definitions.definitions.md#def-2516d89bed459156)
- [CodedSorting.Construction.OneLevelAssembly.slabs._proof_3](Allocation.definitions.md#def-8da035480264fdb1)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`Fin.fintype`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Function.Injective`, `Fin`

<a id="def-614ab06fe55d34ab"></a>
## `CodedSorting.Construction.OneLevelAssembly.scatter`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L121)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {Q rows G S source temporary : ℕ} →
    Fin q.inventory.readers →
      CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary →
        List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} {Q rows G S source temporary} reader a =>
  CodedSorting.Construction.StreamSplitMachine.scatterCode q reader CodedSorting.Construction.ambientDimension Q rows
    CodedSorting.Construction.streamCount G S source temporary
    (CodedSorting.Construction.OneLevelAssembly.slabs a CodedSorting.Construction.OneLevelAssembly.inputSlot
      CodedSorting.Construction.OneLevelAssembly.inputSlot_injective)
```

**继续展开**

- [CodedSorting.Construction.OneLevelAssembly.slabs](Allocation.definitions.md#def-cd7c1a2999f10911)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.OneLevelAssembly.inputSlot](Allocation.definitions.md#def-d5fc5585180e069e)
- [CodedSorting.Construction.StreamSplitMachine.scatterCode](../Streams/StreamParentProgram.definitions.md#def-191e2647e0d0fa34)
- [CodedSorting.Construction.OneLevelAssembly.inputSlot_injective](Allocation.definitions.md#def-90ab2eeeae419101)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`List`, `Nat`, `Fin`

<a id="def-79958cdaef3a98fd"></a>
## `CodedSorting.Construction.OneLevelAssembly.gather`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L125)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {Q rows G S source temporary : ℕ} →
    Fin q.inventory.readers →
      CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary →
        List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} {Q rows G S source temporary} reader a =>
  CodedSorting.Construction.StreamSplitMachine.gatherCode q reader CodedSorting.Construction.ambientDimension Q rows
    CodedSorting.Construction.streamCount G S source temporary
    (CodedSorting.Construction.OneLevelAssembly.slabs a CodedSorting.Construction.OneLevelAssembly.outputSlot
      CodedSorting.Construction.OneLevelAssembly.outputSlot_injective)
```

**继续展开**

- [CodedSorting.Construction.OneLevelAssembly.slabs](Allocation.definitions.md#def-cd7c1a2999f10911)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.Construction.StreamSplitMachine.gatherCode](../Streams/StreamParentProgram.definitions.md#def-73904b67bd0e52df)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.OneLevelAssembly.outputSlot_injective](Allocation.definitions.md#def-7aed789ccf9e04a0)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.OneLevelAssembly.outputSlot](Allocation.definitions.md#def-ad010355ec5e3af9)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`List`, `Nat`, `Fin`

<a id="def-532fdc73d5b8f566"></a>
## `CodedSorting.Construction.OneLevelAssembly.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L132)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {Q rows G S source temporary : ℕ} →
    (location :
        CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
            CodedSorting.Construction.TensorFrameNetwork.program.length →
          Equiv.Perm (Fin (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S))) →
      Fin q.inventory.readers →
        (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary) →
          CodedSorting.Construction.MachineNetwork.Programs
              (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network →
            List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} {Q rows G S source temporary} location reader a ep =>
  CodedSorting.Construction.OneLevelAssembly.scatter reader a ++
      CodedSorting.Construction.MachineNetwork.code reader
        (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network ep ++
    CodedSorting.Construction.OneLevelAssembly.gather reader a
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.OneLevelAssembly.gather](Allocation.definitions.md#def-79958cdaef3a98fd)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.OneLevelAssembly.scatter](Allocation.definitions.md#def-614ab06fe55d34ab)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetwork.code](../../Circuit/NetworkModel/Definitions.definitions.md#def-ef454091d0a5ca92)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`instHAppendOfAppend`, `List`, `Equiv.Perm`, `Nat`, `List.instAppend`, `Fin`, `List.length`, `HAppend.hAppend`

<a id="def-608cae63802c433d"></a>
## `CodedSorting.Construction.OneLevelAssembly.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L136)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {Q rows G S source temporary : ℕ} →
    (location :
        CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
            CodedSorting.Construction.TensorFrameNetwork.program.length →
          Equiv.Perm (Fin (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S))) →
      (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary) →
        CodedSorting.Construction.MachineNetwork.Programs
            (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network →
          ℕ
```

**定义**

```lean
fun {q} {Q rows G S source temporary} location a ep =>
  CodedSorting.Construction.StreamSplitMachine.distributionCharge q CodedSorting.Construction.ambientDimension Q rows
        CodedSorting.Construction.streamCount G S +
      CodedSorting.Construction.MachineNetwork.charge
        (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network ep +
    CodedSorting.Construction.StreamSplitMachine.distributionCharge q CodedSorting.Construction.ambientDimension Q rows
      CodedSorting.Construction.streamCount G S
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.Construction.MachineNetwork.charge](../../Circuit/NetworkModel/Definitions.definitions.md#def-8633871da83ccc78)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.StreamSplitMachine.distributionCharge](../Streams/StreamParentProgram.definitions.md#def-8ea9c03ba6fdcc48)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `Fin`, `List.length`

<a id="def-6ccc248ff5a4f4cc"></a>
## `CodedSorting.Construction.OneLevelAssembly.raw_frame`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean#L173)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {Q rows G S source temporary : ℕ}
  (location :
    CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
        CodedSorting.Construction.TensorFrameNetwork.program.length →
      Equiv.Perm (Fin (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)))
  (reader : Fin q.inventory.readers)
  (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary)
  (ep :
    CodedSorting.Construction.MachineNetwork.Programs
      (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network)
  (s : CodedSorting.CommonLeafProgram.Machine q) (i : Fin (q.N ^ q.exponent)),
  ↑i < source ∨
      source +
          CodedSorting.CommonPermutationPairs.count q
            (CodedSorting.Construction.OneLevelAssembly.parentVolume q Q rows G S) ≤
        ↑i →
    ↑i < temporary ∨ a.network.limit ≤ ↑i →
      (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.Construction.OneLevelAssembly.code location reader a ep) s).1.disk
          i =
        s.disk i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.OneLevelAssembly.code](Allocation.definitions.md#def-532fdc73d5b8f566)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.OneLevelAssembly.parentVolume](Allocation.definitions.md#def-ad8e35ea98d92149)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `Or`, `instHPow`, `instLTNat`, `Fin`, `Eq`, `List.length`

<a id="def-bc744f3b286c2721"></a>
## `CodedSorting.Construction.OneLevelAssembly.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L231)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {Q rows G S source temporary : ℕ} →
    (location :
        CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
            CodedSorting.Construction.TensorFrameNetwork.program.length →
          Equiv.Perm (Fin (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S))) →
      Fin q.inventory.readers →
        (∀ (r : CodedSorting.Construction.ThreeCopySchedule.IndependentStream),
            (Equiv.symm
                    (location
                      (CodedSorting.ProgramNetwork.Vertex.sink
                        (Sum.inl (CodedSorting.Construction.TensorThreeRound.originalSwap r))))).trans
                (location (CodedSorting.ProgramNetwork.Vertex.source (Sum.inl r))) =
              CodedSorting.Construction.OneLevelAssembly.exchangePermutation CodedSorting.Construction.ambientDimension
                Q rows G (S * q.w)) →
          (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary) →
            CodedSorting.Construction.MachineNetwork.Programs
                (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network →
              CodedSorting.CommonFinitePermutation.Program q
                (CodedSorting.Construction.OneLevelAssembly.parentVolume q Q rows G S) source temporary a.network.limit
                (CodedSorting.Construction.OneLevelAssembly.exchangePermutation
                  CodedSorting.Construction.ambientDimension Q (rows * CodedSorting.Construction.streamCount) G
                  (S * q.w))
```

**定义**

```lean
fun {q} {Q rows G S source temporary} location reader hframe a ep =>
  { instructions := CodedSorting.Construction.OneLevelAssembly.code location reader a ep,
    charge := CodedSorting.Construction.OneLevelAssembly.charge location a ep, correct := ⋯, frame := ⋯, safe := ⋯,
    cost_le := ⋯, length_le := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.OneLevelAssembly.program._proof_7](Allocation.definitions.md#def-281ec90e1d1349e7)
- [CodedSorting.Construction.OneLevelAssembly.raw_frame](Allocation.definitions.md#def-6ccc248ff5a4f4cc)
- [CodedSorting.Construction.TensorThreeRound.originalSwap](../../Circuit/Composition/TensorThreeRound.definitions.md#def-8b3c0826e8b41aa5)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.OneLevelAssembly.program._proof_5](Allocation.definitions.md#def-ec3194aefc9b544f)
- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.ProgramNetwork.Vertex.source](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.OneLevelAssembly.charge](Allocation.definitions.md#def-608cae63802c433d)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.OneLevelAssembly.code](Allocation.definitions.md#def-532fdc73d5b8f566)
- [CodedSorting.CommonFinitePermutation.Program](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.ProgramNetwork.Vertex.sink](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.Construction.OneLevelAssembly.program._proof_4](Allocation.definitions.md#def-ca88be563ac7005a)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.OneLevelAssembly.parentVolume](Allocation.definitions.md#def-ad8e35ea98d92149)
- [CodedSorting.Construction.OneLevelAssembly.program._proof_6](Allocation.definitions.md#def-dd71343e1a574d60)
- [CodedSorting.CommonFinitePermutation.Program.mk](../Framework/Memory/ExchangeShapeProgram.definitions.md#def-9d0f3517055893f6)
- [CodedSorting.Construction.OneLevelAssembly.exchangePermutation](Allocation.definitions.md#def-c543f81cf060dc2a)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv.trans`, `Equiv`, `instMulNat`, `Sum.inl`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `Eq`, `List.length`, `DFunLike.coe`, `instHMul`

<a id="def-f97df3b9a3e7a810"></a>
## `CodedSorting.Construction.OneLevelAllocation.localBlocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L295)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q Q rows G S =>
  CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat`

<a id="def-16c1646abbedcd66"></a>
## `CodedSorting.Construction.OneLevelAllocation.parentBlocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L298)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q Q rows G S =>
  CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.OneLevelAssembly.parentVolume q Q rows G S)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.parentVolume](Allocation.definitions.md#def-ad8e35ea98d92149)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat`

<a id="def-f034750dbdfc6967"></a>
## `CodedSorting.Construction.OneLevelAllocation.canonicalWorkspace`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L320)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q Q rows G S temporary => temporary + CodedSorting.Construction.OneLevelAllocation.parentBlocks q Q rows G S
```

**继续展开**

- [CodedSorting.Construction.OneLevelAllocation.parentBlocks](Allocation.definitions.md#def-16c1646abbedcd66)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-020d32a9b62e267a"></a>
## `CodedSorting.Construction.OneLevelAllocation.canonicalBuffer`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L323)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q Q rows G S temporary =>
  CodedSorting.Construction.OneLevelAllocation.canonicalWorkspace q Q rows G S temporary +
    (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
        CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program) *
      CodedSorting.Construction.OneLevelAllocation.localBlocks q Q rows G S
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAllocation.canonicalWorkspace](Allocation.definitions.md#def-f034750dbdfc6967)
- [CodedSorting.Construction.OneLevelAllocation.localBlocks](Allocation.definitions.md#def-f97df3b9a3e7a810)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHMul`

<a id="def-6710b6757167a503"></a>
## `CodedSorting.Construction.OneLevelAllocation.canonicalLimit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Allocation.lean#L328)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q Q rows G S temporary extra =>
  CodedSorting.Construction.OneLevelAllocation.canonicalBuffer q Q rows G S temporary +
      CodedSorting.Construction.OneLevelAllocation.localBlocks q Q rows G S +
    extra
```

**继续展开**

- [CodedSorting.Construction.OneLevelAllocation.canonicalBuffer](Allocation.definitions.md#def-020d32a9b62e267a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAllocation.localBlocks](Allocation.definitions.md#def-f97df3b9a3e7a810)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-03821d92287ba9f3"></a>
## `CodedSorting.Construction.OneLevelAssembly.exchangePermutation._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean)

**类型**

```lean
∀ (m : ℕ), IsWellFounded (Fin m) fun x1 x2 => x1 < x2
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.instLinearOrder`, `Nat`, `LT.lt`, `Fin`, `IsWellFounded`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-ca88be563ac7005a"></a>
## `CodedSorting.Construction.OneLevelAssembly.program._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {Q rows G S source temporary : ℕ}
  (location :
    CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
        CodedSorting.Construction.TensorFrameNetwork.program.length →
      Equiv.Perm (Fin (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)))
  (reader : Fin q.inventory.readers),
  (∀ (r : CodedSorting.Construction.ThreeCopySchedule.IndependentStream),
      (Equiv.symm
              (location
                (CodedSorting.ProgramNetwork.Vertex.sink
                  (Sum.inl (CodedSorting.Construction.TensorThreeRound.originalSwap r))))).trans
          (location (CodedSorting.ProgramNetwork.Vertex.source (Sum.inl r))) =
        CodedSorting.Construction.OneLevelAssembly.exchangePermutation CodedSorting.Construction.ambientDimension Q rows
          G (S * q.w)) →
    ∀ (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary)
      (ep :
        CodedSorting.Construction.MachineNetwork.Programs
          (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network)
      (s : CodedSorting.CommonLeafProgram.Machine q)
      (y : Fin (CodedSorting.Construction.OneLevelAssembly.parentVolume q Q rows G S)),
      CodedSorting.CommonPermutationPairs.readBit q
          (CodedSorting.CommonStaticSchedule.executeRaw q
                (CodedSorting.Construction.OneLevelAssembly.code location reader a ep) s).1.disk
          source ↑y =
        CodedSorting.CommonPermutationPairs.readBit q s.disk source
          ↑((CodedSorting.Construction.OneLevelAssembly.exchangePermutation CodedSorting.Construction.ambientDimension Q
                (rows * CodedSorting.Construction.streamCount) G (S * q.w))
              y)
```

**继续展开**

- [CodedSorting.Construction.TensorThreeRound.originalSwap](../../Circuit/Composition/TensorThreeRound.definitions.md#def-8b3c0826e8b41aa5)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.ProgramNetwork.Vertex.source](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-e888b38289e13ef4)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.CommonPermutationPairs.readBit](../Framework/Memory/Reflection.definitions.md#def-96a76826e3991d5f)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Circuit.Bit](../../Circuit/Framework/Circuit.definitions.md#def-a59aaf4e7156da2a)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonLeafProgram.Machine](../../Shared/Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.CommonStaticSchedule.executeRaw](../../Shared/Programs/Static/Fusion.definitions.md#def-17e56d39295b586c)
- [CodedSorting.Construction.OneLevelAssembly.code](Allocation.definitions.md#def-532fdc73d5b8f566)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.ProgramNetwork.Vertex.sink](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-7c6267025a776389)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.OneLevelAssembly.parentVolume](Allocation.definitions.md#def-ad8e35ea98d92149)
- [CodedSorting.Construction.OneLevelAssembly.exchangePermutation](Allocation.definitions.md#def-c543f81cf060dc2a)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)
- [CodedSorting.Normalization.LogicalState.disk](../../Shared/Programs/Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instMulNat`, `Sum.inl`, `Fin.val`, `Prod.fst`, `HPow.hPow`, `Equiv.Perm`, `Nat`, `instHPow`, `Equiv.symm`, `Fin`, `Eq`, `List.length`, `DFunLike.coe`, `instHMul`

<a id="def-ec3194aefc9b544f"></a>
## `CodedSorting.Construction.OneLevelAssembly.program._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {Q rows G S source temporary : ℕ}
  (location :
    CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
        CodedSorting.Construction.TensorFrameNetwork.program.length →
      Equiv.Perm (Fin (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)))
  (reader : Fin q.inventory.readers)
  (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary)
  (ep :
    CodedSorting.Construction.MachineNetwork.Programs
      (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network),
  ∀ i ∈ CodedSorting.Construction.OneLevelAssembly.code location reader a ep,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.OneLevelAssembly.code](Allocation.definitions.md#def-532fdc73d5b8f566)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Equiv.Perm`, `Nat`, `Fin`, `List.length`

<a id="def-dd71343e1a574d60"></a>
## `CodedSorting.Construction.OneLevelAssembly.program._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {Q rows G S source temporary : ℕ}
  (location :
    CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
        CodedSorting.Construction.TensorFrameNetwork.program.length →
      Equiv.Perm (Fin (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)))
  (reader : Fin q.inventory.readers)
  (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary)
  (ep :
    CodedSorting.Construction.MachineNetwork.Programs
      (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network),
  CodedSorting.CommonStaticSchedule.cost q (CodedSorting.Construction.OneLevelAssembly.code location reader a ep) ≤
    CodedSorting.Construction.OneLevelAssembly.charge location a ep
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.OneLevelAssembly.charge](Allocation.definitions.md#def-608cae63802c433d)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.OneLevelAssembly.code](Allocation.definitions.md#def-532fdc73d5b8f566)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.CommonStaticSchedule.cost](../../Shared/Programs/Static/Fusion.definitions.md#def-77f08c2e53ea257e)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`LE.le`, `instLENat`, `Equiv.Perm`, `Nat`, `Fin`, `List.length`

<a id="def-281ec90e1d1349e7"></a>
## `CodedSorting.Construction.OneLevelAssembly.program._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {Q rows G S source temporary : ℕ}
  (location :
    CodedSorting.ProgramNetwork.Vertex CodedSorting.Construction.TensorLiftProgram.GlobalReg
        CodedSorting.Construction.TensorFrameNetwork.program.length →
      Equiv.Perm (Fin (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)))
  (reader : Fin q.inventory.readers)
  (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary)
  (ep :
    CodedSorting.Construction.MachineNetwork.Programs
      (CodedSorting.Construction.MachineNetworkAdapter.actualCircuit location) a.network),
  (CodedSorting.Construction.OneLevelAssembly.code location reader a ep).length ≤
    CodedSorting.Construction.OneLevelAssembly.charge location a ep
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Programs](../../Circuit/NetworkModel/Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CircuitProgram.XorGate](../../Circuit/Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.OneLevelAssembly.charge](Allocation.definitions.md#def-608cae63802c433d)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.OneLevelAssembly.code](Allocation.definitions.md#def-532fdc73d5b8f566)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.actualCircuit](../../Circuit/NetworkModel/Adapter.definitions.md#def-3645220e02de1fc0)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.ProgramNetwork.Vertex](../../Circuit/NetworkModel/Framework/ProgramNetwork.definitions.md#def-5a51334008fa08b7)

**基础库名称**

`LE.le`, `instLENat`, `Equiv.Perm`, `Nat`, `Fin`, `List.length`

<a id="def-8da035480264fdb1"></a>
## `CodedSorting.Construction.OneLevelAssembly.slabs._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Allocation.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {Q rows G S source temporary : ℕ}
  (a : CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary),
  CodedSorting.PhysicalStreamCursor.blockCount q.block
      (CodedSorting.CommonAddressLayout.Volume (Fin CodedSorting.Construction.ambientDimension) rows Q G S) ≤
    a.network.stride
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAssembly.Setup](Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetwork.Layout.stride](../../Circuit/NetworkModel/Definitions.definitions.md#def-2516d89bed459156)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.CommonAddressLayout.Volume](../Framework/Memory/AddressLayout.definitions.md#def-b3dff48de4627bef)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`LE.le`, `instLENat`, `Fin.fintype`, `Nat`, `Fin`
