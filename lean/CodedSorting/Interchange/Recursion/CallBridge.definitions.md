# CallBridge 的定义

[源码](CallBridge.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-71049aa090f6481a"></a>
## `CodedSorting.Construction.RecursiveCallAddress.atLimitSetup`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CallBridge.lean#L94)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (Q rows G S source temporary limit : ℕ) →
    source + CodedSorting.Construction.OneLevelAllocation.parentBlocks q Q rows G S ≤ temporary →
      CodedSorting.Construction.OneLevelAllocation.canonicalLimit q Q rows G S temporary 0 ≤ limit →
        limit ≤ q.N ^ q.exponent → CodedSorting.Construction.OneLevelAssembly.Setup q Q rows G S source temporary
```

**定义**

```lean
fun q Q rows G S source temporary limit hsource hreserve hfit =>
  {
    network :=
      { workspace := CodedSorting.Construction.OneLevelAllocation.canonicalWorkspace q Q rows G S temporary,
        stride := CodedSorting.Construction.OneLevelAllocation.localBlocks q Q rows G S,
        buffer := CodedSorting.Construction.OneLevelAllocation.canonicalBuffer q Q rows G S temporary, limit := limit,
        count_le_stride := ⋯, files_le_buffer := ⋯, buffer_le_limit := ⋯, fit := hfit },
    source_separate := hsource, temporary_separate := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.OneLevelAllocation.canonicalBuffer](../OneLevel/Allocation.definitions.md#def-020d32a9b62e267a)
- [CodedSorting.Construction.MachineNetwork.Layout.mk](../../Circuit/NetworkModel/Definitions.definitions.md#def-9796ff5df1c75daa)
- [CodedSorting.Construction.RecursiveCallAddress.atLimitSetup._proof_4](CallBridge.definitions.md#def-e69cbf13a033fb9b)
- [CodedSorting.Construction.OneLevelAssembly.Setup.mk](../OneLevel/Allocation.definitions.md#def-5714161b00708e26)
- [CodedSorting.Construction.RecursiveCallAddress.atLimitSetup._proof_2](CallBridge.definitions.md#def-efbb3f6ea3331de0)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.OneLevelAllocation.canonicalLimit](../OneLevel/Allocation.definitions.md#def-6710b6757167a503)
- [CodedSorting.Construction.OneLevelAllocation.parentBlocks](../OneLevel/Allocation.definitions.md#def-16c1646abbedcd66)
- [CodedSorting.Construction.OneLevelAssembly.Setup](../OneLevel/Allocation.definitions.md#def-e9291a74eb66b4de)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.RecursiveCallAddress.atLimitSetup._proof_3](CallBridge.definitions.md#def-3c460ad82b9eb564)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAllocation.canonicalWorkspace](../OneLevel/Allocation.definitions.md#def-f034750dbdfc6967)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](../OneLevel/Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.OneLevelAllocation.localBlocks](../OneLevel/Allocation.definitions.md#def-f97df3b9a3e7a810)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Construction.RecursiveCallAddress.atLimitSetup._proof_1](CallBridge.definitions.md#def-144a40a6bc51aca7)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-2c7544d6b319e9d2"></a>
## `CodedSorting.Construction.RecursiveCallShape.ShapeDepth`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](CallBridge.lean#L165)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → CodedSorting.Construction.ExchangeInterface.Call → Prop
```

**继续展开**

- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth.mk](CallBridge.definitions.md#def-e343b07743be71fa)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-e343b07743be71fa"></a>
## `CodedSorting.Construction.RecursiveCallShape.ShapeDepth.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](CallBridge.lean#L167)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.ambientDimension ^ k ∣ c.fieldWidth →
    CodedSorting.Construction.streamCount ^ k ∣ c.prefixCount →
      0 < c.fieldWidth →
        0 < c.gap → (∃ S, 0 < S ∧ c.suffix = S * q.w) → CodedSorting.Construction.RecursiveCallShape.ShapeDepth q k c
```

**继续展开**

- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.Construction.ExchangeInterface.Call.prefixCount](../Bounds/ExchangeInterface.definitions.md#def-c6970b08eef740c9)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.Call.suffix](../Bounds/ExchangeInterface.definitions.md#def-f885a54e84cd2206)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`Dvd.dvd`, `HMul.hMul`, `Nat.instMonoid`, `Exists`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `And`, `HPow.hPow`, `Nat.instDvd`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-dbbfbcb97759b7f8"></a>
## `CodedSorting.Construction.RecursiveCallShape.shortWidth`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CallBridge.lean#L195)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun c => c.fieldWidth / CodedSorting.Construction.ambientDimension
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.fieldWidth](../Bounds/ExchangeInterface.definitions.md#def-f09839abbd91973c)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `Nat`, `Nat.instDiv`

<a id="def-dd9a675713fcde76"></a>
## `CodedSorting.Construction.RecursiveCallShape.rows`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CallBridge.lean#L196)

**类型**

```lean
CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun c => c.prefixCount / CodedSorting.Construction.streamCount
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.prefixCount](../Bounds/ExchangeInterface.definitions.md#def-c6970b08eef740c9)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `Nat`, `Nat.instDiv`

<a id="def-cb390fd72974409d"></a>
## `CodedSorting.Construction.RecursiveCallShape.suffixWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CallBridge.lean#L197)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun q c => c.suffix / q.w
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.Call.suffix](../Bounds/ExchangeInterface.definitions.md#def-f885a54e84cd2206)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `Nat`, `Nat.instDiv`

<a id="def-6e22cf5475ac82d9"></a>
## `CodedSorting.Construction.RecursiveCallBridge.requiredLimit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CallBridge.lean#L354)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → CodedSorting.Construction.ExchangeInterface.Call → ℕ
```

**定义**

```lean
fun q c =>
  CodedSorting.Construction.OneLevelAllocation.canonicalLimit q
    (CodedSorting.Construction.ExchangeSpecialization.radix ^ CodedSorting.Construction.RecursiveCallShape.shortWidth c)
    (CodedSorting.Construction.RecursiveCallShape.rows c) c.gap
    (CodedSorting.Construction.RecursiveCallShape.suffixWords q c) c.buffer 0
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.OneLevelAllocation.canonicalLimit](../OneLevel/Allocation.definitions.md#def-6710b6757167a503)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-d3c3da1d4241dace"></a>
## `CodedSorting.Construction.RecursiveCallBridge.next_source_separate`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean#L372)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c →
    CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c →
      c.source +
          CodedSorting.Construction.OneLevelAllocation.parentBlocks q
            (CodedSorting.Construction.ExchangeSpecialization.radix ^
              CodedSorting.Construction.RecursiveCallShape.shortWidth c)
            (CodedSorting.Construction.RecursiveCallShape.rows c) c.gap
            (CodedSorting.Construction.RecursiveCallShape.suffixWords q c) ≤
        c.buffer
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.OneLevelAllocation.parentBlocks](../OneLevel/Allocation.definitions.md#def-16c1646abbedcd66)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-cee33bf01bfa59c7"></a>
## `CodedSorting.Construction.RecursiveCallBridge.nextSetup`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CallBridge.lean#L380)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {k : ℕ} →
    {c : CodedSorting.Construction.ExchangeInterface.Call} →
      CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c →
        CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix
            c →
          CodedSorting.Construction.RecursiveCallBridge.requiredLimit q c ≤ c.limit →
            CodedSorting.Construction.OneLevelExchange.Setup q
              (CodedSorting.Construction.RecursiveCallShape.shortWidth c)
              (CodedSorting.Construction.RecursiveCallShape.rows c) c.gap
              (CodedSorting.Construction.RecursiveCallShape.suffixWords q c) c.source c.buffer
```

**定义**

```lean
fun {q} {k} {c} h allocation hreserve =>
  CodedSorting.Construction.RecursiveCallAddress.atLimitSetup q
    (CodedSorting.Construction.ExchangeSpecialization.radix ^ CodedSorting.Construction.RecursiveCallShape.shortWidth c)
    (CodedSorting.Construction.RecursiveCallShape.rows c) c.gap
    (CodedSorting.Construction.RecursiveCallShape.suffixWords q c) c.source c.buffer c.limit ⋯ hreserve ⋯
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.RecursiveCallBridge.requiredLimit](CallBridge.definitions.md#def-6e22cf5475ac82d9)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.RecursiveCallAddress.atLimitSetup](CallBridge.definitions.md#def-71049aa090f6481a)
- [CodedSorting.Construction.OneLevelExchange.Setup](../OneLevel/Exchange.definitions.md#def-19fe65f6429dabe1)
- [CodedSorting.Construction.RecursiveCallBridge.next_source_separate](CallBridge.definitions.md#def-d3c3da1d4241dace)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.Allocation.limit_fits](../Bounds/ExchangeInterface.definitions.md#def-a9d74d6c18a3bf8f)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-8e919a46ff8c671e"></a>
## `CodedSorting.Construction.RecursiveCallBridge.nextSetup_parent_eq`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean#L390)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call}
  (h : CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c)
  (allocation :
    CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c)
  (hreserve : CodedSorting.Construction.RecursiveCallBridge.requiredLimit q c ≤ c.limit),
  CodedSorting.Construction.OneLevelExchange.parentCall
      (CodedSorting.Construction.RecursiveCallBridge.nextSetup h allocation hreserve) =
    c
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.RecursiveCallBridge.requiredLimit](CallBridge.definitions.md#def-6e22cf5475ac82d9)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.OneLevelExchange.parentCall](../OneLevel/Exchange.definitions.md#def-9c481fea80d256ae)
- [CodedSorting.Construction.RecursiveCallBridge.nextSetup](CallBridge.definitions.md#def-cee33bf01bfa59c7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Eq`

<a id="def-c6c8514bbabf3794"></a>
## `CodedSorting.Construction.RecursiveCallBridge.nextSetup_room`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean#L396)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call}
  (h : CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c)
  (allocation :
    CodedSorting.Construction.ExchangeInterface.Allocation q CodedSorting.Construction.ExchangeSpecialization.radix c)
  (hreserve : CodedSorting.Construction.RecursiveCallBridge.requiredLimit q c ≤ c.limit),
  (CodedSorting.Construction.RecursiveCallBridge.nextSetup h allocation hreserve).network.buffer +
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.Construction.OneLevelAssembly.localVolume q
          (CodedSorting.Construction.ExchangeSpecialization.radix ^
            CodedSorting.Construction.RecursiveCallShape.shortWidth c)
          (CodedSorting.Construction.RecursiveCallShape.rows c) c.gap
          (CodedSorting.Construction.RecursiveCallShape.suffixWords q c)) ≤
    (CodedSorting.Construction.RecursiveCallBridge.nextSetup h allocation hreserve).network.limit
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.MachineNetwork.Layout.buffer](../../Circuit/NetworkModel/Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.RecursiveCallBridge.requiredLimit](CallBridge.definitions.md#def-6e22cf5475ac82d9)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](../../Circuit/NetworkModel/Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.RecursiveCallBridge.nextSetup](CallBridge.definitions.md#def-cee33bf01bfa59c7)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](../OneLevel/Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.OneLevelAssembly.Setup.network](../OneLevel/Allocation.definitions.md#def-5f40cc5c5136d5e1)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-051c1bc0b09d12bc"></a>
## `CodedSorting.Construction.RecursiveCallBridge.castCall`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CallBridge.lean#L406)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {c d : CodedSorting.Construction.ExchangeInterface.Call} →
    c = d →
      CodedSorting.Construction.ExchangeInterface.Program q CodedSorting.Construction.ExchangeSpecialization.radix c →
        CodedSorting.Construction.ExchangeInterface.Program q CodedSorting.Construction.ExchangeSpecialization.radix d
```

**定义**

```lean
fun {q} {c d} h p => h ▸ p
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Eq.rec`, `Eq`

<a id="def-5537eed977da1c36"></a>
## `CodedSorting.Construction.RecursiveCallBridge.nextProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](CallBridge.lean#L420)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {k : ℕ} →
    Fin q.inventory.readers →
      {c : CodedSorting.Construction.ExchangeInterface.Call} →
        (h : CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c) →
          (allocation :
              CodedSorting.Construction.ExchangeInterface.Allocation q
                CodedSorting.Construction.ExchangeSpecialization.radix c) →
            (hreserve : CodedSorting.Construction.RecursiveCallBridge.requiredLimit q c ≤ c.limit) →
              CodedSorting.Construction.OneLevelExchange.Children
                  (CodedSorting.Construction.RecursiveCallBridge.nextSetup h allocation hreserve) →
                CodedSorting.Construction.ExchangeInterface.Program q
                  CodedSorting.Construction.ExchangeSpecialization.radix c
```

**定义**

```lean
fun {q} {k} reader {c} h allocation hreserve children =>
  CodedSorting.Construction.RecursiveCallBridge.castCall ⋯
    (CodedSorting.Construction.OneLevelExchange.program reader ⋯ ⋯
      (CodedSorting.Construction.RecursiveCallBridge.nextSetup h allocation hreserve) ⋯ children)
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.Allocation](../Bounds/ExchangeInterface.definitions.md#def-d25bf8911134460c)
- [CodedSorting.Construction.RecursiveCallBridge.castCall](CallBridge.definitions.md#def-051c1bc0b09d12bc)
- [CodedSorting.Construction.OneLevelExchange.Children](../OneLevel/Exchange.definitions.md#def-8c69d438c4744692)
- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.RecursiveCallBridge.nextSetup_room](CallBridge.definitions.md#def-c6c8514bbabf3794)
- [CodedSorting.Construction.RecursiveCallBridge.requiredLimit](CallBridge.definitions.md#def-6e22cf5475ac82d9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.OneLevelExchange.program](../OneLevel/Exchange.definitions.md#def-5bcd2618b1c4ba4c)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.Construction.ExchangeInterface.Call.buffer](../Bounds/ExchangeInterface.definitions.md#def-a29f8f671ec8e5d7)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.RecursiveCallBridge.nextSetup_parent_eq](CallBridge.definitions.md#def-8e919a46ff8c671e)
- [CodedSorting.Construction.RecursiveCallBridge.nextProgram._proof_11](CallBridge.definitions.md#def-86717fd30a1d3c8a)
- [CodedSorting.Construction.OneLevelExchange.parentCall](../OneLevel/Exchange.definitions.md#def-9c481fea80d256ae)
- [CodedSorting.Construction.RecursiveCallBridge.nextSetup](CallBridge.definitions.md#def-cee33bf01bfa59c7)
- [CodedSorting.Construction.ExchangeInterface.Program](../Bounds/ExchangeInterface.definitions.md#def-5c2c8be0965caaed)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.Call.source](../Bounds/ExchangeInterface.definitions.md#def-be4ab17220402aee)
- [CodedSorting.Construction.RecursiveCallShape.shortWidth](CallBridge.definitions.md#def-dbbfbcb97759b7f8)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)
- [CodedSorting.Construction.RecursiveCallShape.rows](CallBridge.definitions.md#def-dd9a675713fcde76)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.RecursiveCallBridge.nextProgram._proof_12](CallBridge.definitions.md#def-646914c13348f58a)
- [CodedSorting.Construction.ExchangeInterface.Call.limit](../Bounds/ExchangeInterface.definitions.md#def-d41482827313e1e3)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-144a40a6bc51aca7"></a>
## `CodedSorting.Construction.RecursiveCallAddress.atLimitSetup._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (Q rows G S : ℕ),
  CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S) ≤
    CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.OneLevelAssembly.localVolume q Q rows G S)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.localVolume](../OneLevel/Allocation.definitions.md#def-18e194898352b8ed)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Preorder.toLE`, `LE.le`, `Nat.instPreorder`, `Nat`

<a id="def-efbb3f6ea3331de0"></a>
## `CodedSorting.Construction.RecursiveCallAddress.atLimitSetup._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (Q rows G S temporary : ℕ),
  CodedSorting.Construction.OneLevelAllocation.canonicalWorkspace q Q rows G S temporary +
      (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
          CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program) *
        CodedSorting.Construction.OneLevelAllocation.localBlocks q Q rows G S ≤
    CodedSorting.Construction.OneLevelAllocation.canonicalWorkspace q Q rows G S temporary +
      (CodedSorting.Construction.MachineNetworkAdapter.physicalInputs +
          CodedSorting.Construction.MachineNetworkAdapter.nodes CodedSorting.Construction.TensorFrameNetwork.program) *
        CodedSorting.Construction.OneLevelAllocation.localBlocks q Q rows G S
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](../../Circuit/Composition/TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAllocation.canonicalWorkspace](../OneLevel/Allocation.definitions.md#def-f034750dbdfc6967)
- [CodedSorting.Construction.OneLevelAllocation.localBlocks](../OneLevel/Allocation.definitions.md#def-f97df3b9a3e7a810)
- [CodedSorting.Construction.TensorFrameNetwork.program](../../Circuit/Composition/TensorFrameNetwork.definitions.md#def-831c8f924acdba89)
- [CodedSorting.Construction.MachineNetworkAdapter.physicalInputs](../../Circuit/NetworkModel/Adapter.definitions.md#def-61b11b4c2aee2759)
- [CodedSorting.Construction.MachineNetworkAdapter.nodes](../../Circuit/NetworkModel/Adapter.definitions.md#def-b4406b1e1be178ef)

**基础库名称**

`HMul.hMul`, `Preorder.toLE`, `instMulNat`, `LE.le`, `instHAdd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`, `instHMul`

<a id="def-3c460ad82b9eb564"></a>
## `CodedSorting.Construction.RecursiveCallAddress.atLimitSetup._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (Q rows G S temporary limit : ℕ),
  CodedSorting.Construction.OneLevelAllocation.canonicalLimit q Q rows G S temporary 0 ≤ limit →
    CodedSorting.Construction.OneLevelAllocation.canonicalBuffer q Q rows G S temporary ≤ limit
```

**继续展开**

- [CodedSorting.Construction.OneLevelAllocation.canonicalBuffer](../OneLevel/Allocation.definitions.md#def-020d32a9b62e267a)
- [CodedSorting.Construction.OneLevelAllocation.canonicalLimit](../OneLevel/Allocation.definitions.md#def-6710b6757167a503)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-e69cbf13a033fb9b"></a>
## `CodedSorting.Construction.RecursiveCallAddress.atLimitSetup._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (Q rows G S temporary : ℕ),
  temporary +
      CodedSorting.CommonPermutationPairs.count q
        (CodedSorting.Construction.OneLevelAssembly.parentVolume q Q rows G S) ≤
    temporary +
      CodedSorting.CommonPermutationPairs.count q (CodedSorting.Construction.OneLevelAssembly.parentVolume q Q rows G S)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.OneLevelAssembly.parentVolume](../OneLevel/Allocation.definitions.md#def-ad8e35ea98d92149)
- [CodedSorting.CommonPermutationPairs.count](../Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`Preorder.toLE`, `LE.le`, `instHAdd`, `HAdd.hAdd`, `Nat.instPreorder`, `Nat`, `instAddNat`

<a id="def-86717fd30a1d3c8a"></a>
## `CodedSorting.Construction.RecursiveCallBridge.nextProgram._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c → 0 < c.gap
```

**继续展开**

- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.ExchangeInterface.Call.gap](../Bounds/ExchangeInterface.definitions.md#def-2a660b38466586e9)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-646914c13348f58a"></a>
## `CodedSorting.Construction.RecursiveCallBridge.nextProgram._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](CallBridge.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {k : ℕ}
  {c : CodedSorting.Construction.ExchangeInterface.Call},
  CodedSorting.Construction.RecursiveCallShape.ShapeDepth q (k + 1) c →
    0 < CodedSorting.Construction.RecursiveCallShape.suffixWords q c
```

**继续展开**

- [CodedSorting.Construction.RecursiveCallShape.ShapeDepth](CallBridge.definitions.md#def-2c7544d6b319e9d2)
- [CodedSorting.Construction.ExchangeInterface.Call](../Bounds/ExchangeInterface.definitions.md#def-c6473a9159649804)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.RecursiveCallShape.suffixWords](CallBridge.definitions.md#def-cb390fd72974409d)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`
