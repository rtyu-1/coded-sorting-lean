# PhysicalHalted 的定义

[源码](PhysicalHalted.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-129cc4c709eafa04"></a>
## `CodedSorting.CommonIntegerPhysical.blocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalHalted.lean#L14)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q n => CodedSorting.PhysicalStreamCursor.blockCount q.block n
```

**继续展开**

- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat`

<a id="def-460cd4e0577a8aad"></a>
## `CodedSorting.CommonIntegerPhysical.start`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalHalted.lean#L16)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonSortingNormalization.SourcePolicy q →
    CodedSorting.CommonLeafProgram.Store q →
      (n : ℕ) →
        CodedSorting.CommonIntegerPhysical.blocks q n < q.N ^ q.exponent →
          CodedSorting.CommonNormalizationController.Disk (q.N ^ q.exponent) q.B q.w →
            CodedSorting.CommonSortingNormalization.MachineState q
```

**定义**

```lean
fun q policy store n hn disk =>
  CodedSorting.CommonSortingNormalization.initialState q policy store ⟨CodedSorting.CommonIntegerPhysical.blocks q n, ⋯⟩
    ⟨CodedSorting.CommonIntegerPhysical.blocks q n, hn⟩ disk
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourcePolicy](../../Resources/Framework/NormalizationFrames.definitions.md#def-1812a6349a1bc9a7)
- [CodedSorting.CommonNormalizationController.Disk](../../../Shared/Memory/NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.CommonSortingNormalization.initialState](../../Resources/Framework/NormalizationFrames.definitions.md#def-2425cae72dbf61a5)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonIntegerPhysical.start._proof_2](PhysicalHalted.definitions.md#def-d96cfdbb3ad6a575)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.MachineState](../../Resources/Framework/NormalizationFrames.definitions.md#def-90721c68825dbf3f)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonIntegerPhysical.blocks](PhysicalHalted.definitions.md#def-129cc4c709eafa04)
- [CodedSorting.CommonSortingNormalization.Configuration.B](../../Resources/Framework/NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-bf3f17317564f236"></a>
## `CodedSorting.CommonIntegerPhysical.inputWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalHalted.lean#L21)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonNormalizationController.Disk (q.N ^ q.exponent) q.B q.w → ℕ → CodedSorting.WordControl.Word q.w
```

**定义**

```lean
fun q disk i => if h : i / q.B < q.N ^ q.exponent then disk (Sum.inl ⟨i / q.B, h⟩) ⟨i % q.B, ⋯⟩ else 0
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Disk](../../../Shared/Memory/NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonIntegerPhysical.inputWord._proof_4](PhysicalHalted.definitions.md#def-14276fd3218840c6)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonIntegerPhysical.inputWord._proof_3](PhysicalHalted.definitions.md#def-95c899df9db88c92)
- [CodedSorting.CommonSortingNormalization.Configuration.B](../../Resources/Framework/NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`instHDiv`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `Sum`, `Fin.instOfNat`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `Sum.inl`, `dite`, `HMod.hMod`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instDiv`, `Nat.decLt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`

<a id="def-d768a06a6e018cb4"></a>
## `CodedSorting.CommonIntegerPhysical.InputFile`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalHalted.lean#L27)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonNormalizationController.Disk (q.N ^ q.exponent) q.B q.w →
    List (CodedSorting.WordControl.Word q.w) → Prop
```

**定义**

```lean
fun q disk xs => ∀ (i : Fin xs.length), CodedSorting.CommonIntegerPhysical.inputWord q disk ↑i = xs.get i
```

**继续展开**

- [CodedSorting.CommonNormalizationController.Disk](../../../Shared/Memory/NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonIntegerPhysical.inputWord](PhysicalHalted.definitions.md#def-bf3f17317564f236)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.B](../../Resources/Framework/NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`List.get`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.val`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `Eq`, `List.length`

<a id="def-95c899df9db88c92"></a>
## `CodedSorting.CommonIntegerPhysical.inputWord._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalHalted.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (i : ℕ), i % q.B < q.B
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.B](../../Resources/Framework/NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`

<a id="def-14276fd3218840c6"></a>
## `CodedSorting.CommonIntegerPhysical.inputWord._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalHalted.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), NeZero (2 ^ q.w)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `OfNat.ofNat`, `MulZeroClass.toZero`

<a id="def-d96cfdbb3ad6a575"></a>
## `CodedSorting.CommonIntegerPhysical.start._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalHalted.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  CodedSorting.CommonIntegerPhysical.blocks q n < q.N ^ q.exponent →
    CodedSorting.CommonIntegerPhysical.blocks q n < q.N ^ q.exponent + 1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonIntegerPhysical.blocks](PhysicalHalted.definitions.md#def-129cc4c709eafa04)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`
