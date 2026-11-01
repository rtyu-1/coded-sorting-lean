# TaggedController 的定义

[源码](TaggedController.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-055b97896ab03ac7"></a>
## `CodedSorting.CommonTaggedSchedule.instrument`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TaggedController.lean#L247)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → ℕ → CodedSorting.CommonStaticSchedule.Instruction q → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q stride tag offset i =>
  { operation := i.operation,
    resume := fun ram => CodedSorting.CommonStaticSchedule.setPC q (tag * stride + (offset + 1)) (i.resume ram) }
```

**继续展开**

- [CodedSorting.ControlledNormalization.Instruction.resume](../Programs/ControlledNormalization.definitions.md#def-f9b13fabe559e990)
- [CodedSorting.ControlledNormalization.Instruction.operation](../Programs/ControlledNormalization.definitions.md#def-3d5141c25fe6587d)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonStaticSchedule.setPC](../Programs/Static/Fusion.definitions.md#def-8019447113f5daf6)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.ControlledNormalization.Instruction.mk](../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-2aa68f130c0943c6"></a>
## `CodedSorting.CommonTaggedController.policy`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TaggedController.lean#L430)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {K : ℕ} →
    ℕ →
      (Fin K → List (CodedSorting.CommonStaticSchedule.Instruction q)) →
        (Fin K → Bool) →
          (Fin K → CodedSorting.CommonLeafProgram.RAM q → CodedSorting.CommonLeafProgram.RAM q) →
            CodedSorting.CommonSortingNormalization.SourcePolicy q
```

**定义**

```lean
fun q {K} stride code terminal next ram =>
  if h : CodedSorting.CommonStaticSchedule.pc q ram / stride < K then
    let tag := ⟨CodedSorting.CommonStaticSchedule.pc q ram / stride, h⟩;
    match (code tag)[CodedSorting.CommonStaticSchedule.pc q ram % stride]? with
    | some i =>
      some
        (CodedSorting.CommonTaggedSchedule.instrument q stride (↑tag)
          (CodedSorting.CommonStaticSchedule.pc q ram % stride) i)
    | none =>
      if terminal tag = true then none
      else some { operation := CodedSorting.Normalization.Command.localOp (next tag), resume := id }
  else none
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonSortingNormalization.SourcePolicy](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1812a6349a1bc9a7)
- [CodedSorting.CommonTaggedSchedule.instrument](TaggedController.definitions.md#def-055b97896ab03ac7)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonTaggedController.policy.match_1](TaggedController.definitions.md#def-5569df6729503bd8)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.ControlledNormalization.Instruction.mk](../Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonStaticSchedule.pc](../Programs/Static/Fusion.definitions.md#def-1a4b4c98150dd06a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ControlledNormalization.Instruction](../Programs/ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`instHDiv`, `Nat.instMonoid`, `List.instGetElem?NatLtLength`, `Option.some`, `Monoid.toNatPow`, `Fin.mk`, `id`, `HDiv.hDiv`, `Nat.instMod`, `instDecidableEqBool`, `instHMod`, `Fin.val`, `dite`, `Bool.true`, `Option.none`, `List`, `HMod.hMod`, `Unit`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instDiv`, `Bool`, `Nat.decLt`, `instHPow`, `instLTNat`, `GetElem?.getElem?`, `Fin`, `Eq`, `List.length`, `Not`, `Option`, `ite`

<a id="def-5569df6729503bd8"></a>
## `CodedSorting.CommonTaggedController.policy.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TaggedController.lean)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (motive : Option (CodedSorting.CommonStaticSchedule.Instruction q) → Sort u_1) →
    (x : Option (CodedSorting.CommonStaticSchedule.Instruction q)) →
      ((i : CodedSorting.CommonStaticSchedule.Instruction q) → motive (some i)) → (Unit → motive none) → motive x
```

**定义**

```lean
fun q motive x h_1 h_2 => Option.casesOn x (h_2 ()) fun val => h_1 val
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`Unit.unit`, `Option.casesOn`, `Option.some`, `Option.none`, `Unit`, `Option`
