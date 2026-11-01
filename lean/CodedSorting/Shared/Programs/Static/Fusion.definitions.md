# Fusion 的定义

[源码](Fusion.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-155a585971955476"></a>
## `CodedSorting.CommonStaticSchedule.Instruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L24)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q =>
  CodedSorting.ControlledNormalization.Instruction q.ramWords q.block (q.N ^ q.exponent)
    (CodedSorting.WordControl.Word q.w)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ControlledNormalization.Instruction](../ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-1a4b4c98150dd06a"></a>
## `CodedSorting.CommonStaticSchedule.pc`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L27)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonLeafProgram.RAM q → ℕ
```

**定义**

```lean
fun q ram => CodedSorting.WordControl.decodeWords (CodedSorting.CommonSortingNormalization.unpack ram).top
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.decodeWords](../../Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat`

<a id="def-8019447113f5daf6"></a>
## `CodedSorting.CommonStaticSchedule.setPC`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L29)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → CodedSorting.CommonLeafProgram.RAM q → CodedSorting.CommonLeafProgram.RAM q
```

**定义**

```lean
fun q k ram =>
  CodedSorting.CommonSortingNormalization.pack
    (let __src := CodedSorting.CommonSortingNormalization.unpack ram;
    { leaf := __src.leaf, readers := __src.readers, writers := __src.writers, transfer := __src.transfer,
      scalars := __src.scalars, directories := __src.directories, shapes := __src.shapes,
      top := CodedSorting.PhysicalStreamCursor.encodeNat q.digits q.w k, pcs := __src.pcs })
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.PhysicalStreamCursor.encodeNat](../../Memory/PhysicalStreamCursor.definitions.md#def-0b39ac6782c7ab72)
- [CodedSorting.CommonSortingNormalization.pack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat`

<a id="def-77f08c2e53ea257e"></a>
## `CodedSorting.CommonStaticSchedule.cost`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L83)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → List (CodedSorting.CommonStaticSchedule.Instruction q) → ℕ
```

**定义**

```lean
fun q x =>
  List.brecOn x fun x f =>
    (match (motive := (x : List (CodedSorting.CommonStaticSchedule.Instruction q)) → List.below x → ℕ) x with
      | [] => fun x => 0
      | i :: is => fun x => CodedSorting.Normalization.transferCost i.operation + x.1)
      f
```

**继续展开**

- [CodedSorting.ControlledNormalization.Instruction.operation](../ControlledNormalization.definitions.md#def-3d5141c25fe6587d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonStaticSchedule.cost.match_1](Fusion.definitions.md#def-287b35752636a175)
- [CodedSorting.Normalization.transferCost](../Normalization.definitions.md#def-84f9b0413bed823d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`List.brecOn`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `List.cons`, `List`, `instHAdd`, `Unit`, `PProd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.below`, `instHPow`, `OfNat.ofNat`, `List.nil`

<a id="def-17e56d39295b586c"></a>
## `CodedSorting.CommonStaticSchedule.executeRaw`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L154)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  List (CodedSorting.CommonStaticSchedule.Instruction q) →
    CodedSorting.CommonLeafProgram.Machine q → CodedSorting.CommonLeafProgram.Machine q × ℕ
```

**定义**

```lean
fun q x x_1 =>
  List.brecOn (motive := fun x =>
    CodedSorting.CommonLeafProgram.Machine q → CodedSorting.CommonLeafProgram.Machine q × ℕ) x
    (fun x f x_2 =>
      (match (motive :=
          (x : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
            CodedSorting.CommonLeafProgram.Machine q →
              List.below (motive := fun x =>
                  CodedSorting.CommonLeafProgram.Machine q → CodedSorting.CommonLeafProgram.Machine q × ℕ) x →
                CodedSorting.CommonLeafProgram.Machine q × ℕ)
          x, x_2 with
        | [], s => fun x => (s, 0)
        | i :: is, s => fun x =>
          let out := x.1 (CodedSorting.ControlledNormalization.logicalStep i s);
          (out.1, CodedSorting.Normalization.transferCost i.operation + out.2))
        f)
    x_1
```

**继续展开**

- [CodedSorting.CommonStaticSchedule.executeRaw.match_1](Fusion.definitions.md#def-900a1a2a3ae5d733)
- [CodedSorting.ControlledNormalization.Instruction.operation](../ControlledNormalization.definitions.md#def-3d5141c25fe6587d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Normalization.transferCost](../Normalization.definitions.md#def-84f9b0413bed823d)
- [CodedSorting.CommonLeafProgram.Machine](../../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ControlledNormalization.logicalStep](../ControlledNormalization.definitions.md#def-66ac60db55b282bd)

**基础库名称**

`List.brecOn`, `Nat.instMonoid`, `Monoid.toNatPow`, `Prod.mk`, `instOfNatNat`, `Prod.fst`, `List.cons`, `List`, `instHAdd`, `PProd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.below`, `instHPow`, `Prod`, `OfNat.ofNat`, `Prod.snd`, `List.nil`

<a id="def-e447dc042985b438"></a>
## `CodedSorting.CommonStaticSchedule.erasePC`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L165)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonLeafProgram.Machine q → CodedSorting.CommonLeafProgram.Machine q
```

**定义**

```lean
fun q s => { ram := CodedSorting.CommonStaticSchedule.setPC q 0 s.ram, disk := s.disk }
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonStaticSchedule.setPC](Fusion.definitions.md#def-8019447113f5daf6)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Normalization.LogicalState.ram](../Normalization.definitions.md#def-234012a079102e4e)
- [CodedSorting.CommonLeafProgram.Machine](../../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Normalization.LogicalState.mk](../Normalization.definitions.md#def-406ff6c0f82deb9d)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.Normalization.LogicalState.disk](../Normalization.definitions.md#def-0daf3d2d8ddbdccc)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-c88ad398120526c1"></a>
## `CodedSorting.CommonStaticSchedule.RespectsPC`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L169)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonStaticSchedule.Instruction q → Prop
```

**定义**

```lean
fun q i =>
  ∀ (s t : CodedSorting.CommonLeafProgram.Machine q),
    CodedSorting.CommonStaticSchedule.erasePC q s = CodedSorting.CommonStaticSchedule.erasePC q t →
      CodedSorting.CommonStaticSchedule.erasePC q (CodedSorting.ControlledNormalization.logicalStep i s) =
        CodedSorting.CommonStaticSchedule.erasePC q (CodedSorting.ControlledNormalization.logicalStep i t)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonStaticSchedule.erasePC](Fusion.definitions.md#def-e447dc042985b438)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonLeafProgram.Machine](../../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ControlledNormalization.logicalStep](../ControlledNormalization.definitions.md#def-66ac60db55b282bd)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Eq`

<a id="def-46b6915bd75a01d6"></a>
## `CodedSorting.CommonStaticFusion.mergeLocal`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L237)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonStaticSchedule.Instruction q →
    (CodedSorting.CommonLeafProgram.RAM q → CodedSorting.CommonLeafProgram.RAM q) →
      (CodedSorting.CommonLeafProgram.RAM q → CodedSorting.CommonLeafProgram.RAM q) →
        CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q i f r => { operation := i.operation, resume := fun ram => r (f (i.resume ram)) }
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.ControlledNormalization.Instruction.resume](../ControlledNormalization.definitions.md#def-f9b13fabe559e990)
- [CodedSorting.ControlledNormalization.Instruction.operation](../ControlledNormalization.definitions.md#def-3d5141c25fe6587d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.ControlledNormalization.Instruction.mk](../ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-cd6af02ae4b971eb"></a>
## `CodedSorting.CommonStaticFusion.attach`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L257)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonStaticSchedule.Instruction q →
    List (CodedSorting.CommonStaticSchedule.Instruction q) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q i x =>
  match x with
  | [] => [i]
  | j :: js =>
    match j.operation with
    | CodedSorting.Normalization.Command.localOp f => CodedSorting.CommonStaticFusion.mergeLocal q i f j.resume :: js
    | CodedSorting.Normalization.Command.read address window => i :: j :: js
    | CodedSorting.Normalization.Command.write address window => i :: j :: js
```

**继续展开**

- [CodedSorting.ControlledNormalization.Instruction.resume](../ControlledNormalization.definitions.md#def-f9b13fabe559e990)
- [CodedSorting.ControlledNormalization.Instruction.operation](../ControlledNormalization.definitions.md#def-3d5141c25fe6587d)
- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonStaticSchedule.cost.match_1](Fusion.definitions.md#def-287b35752636a175)
- [CodedSorting.Normalization.Window](../Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticFusion.mergeLocal](Fusion.definitions.md#def-46b6915bd75a01d6)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Normalization.Command](../Normalization.definitions.md#def-5d1402e119d2b0bd)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonStaticFusion.attach.match_1](Fusion.definitions.md#def-3763aca37ed45033)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `List.cons`, `List`, `Unit`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`, `List.nil`

<a id="def-a8d53d872c4a7e53"></a>
## `CodedSorting.CommonStaticFusion.fuse`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Fusion.lean#L266)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  List (CodedSorting.CommonStaticSchedule.Instruction q) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q x =>
  List.brecOn x fun x f =>
    (match (motive :=
        (x : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
          List.below x → List (CodedSorting.CommonStaticSchedule.Instruction q))
        x with
      | [] => fun x => []
      | i :: is => fun x => CodedSorting.CommonStaticFusion.attach q i x.1)
      f
```

**继续展开**

- [CodedSorting.CommonStaticFusion.attach](Fusion.definitions.md#def-cd6af02ae4b971eb)
- [CodedSorting.CommonStaticSchedule.cost.match_1](Fusion.definitions.md#def-287b35752636a175)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List.brecOn`, `List.cons`, `List`, `Unit`, `PProd`, `List.below`, `List.nil`

<a id="def-3763aca37ed45033"></a>
## `CodedSorting.CommonStaticFusion.attach.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Fusion.lean)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (motive :
      CodedSorting.Normalization.Command q.ramWords q.block (q.N ^ q.exponent) (CodedSorting.WordControl.Word q.w) →
        Sort u_1) →
    (x : CodedSorting.Normalization.Command q.ramWords q.block (q.N ^ q.exponent) (CodedSorting.WordControl.Word q.w)) →
      ((f :
            CodedSorting.Normalization.Words q.ramWords (CodedSorting.WordControl.Word q.w) →
              CodedSorting.Normalization.Words q.ramWords (CodedSorting.WordControl.Word q.w)) →
          motive (CodedSorting.Normalization.Command.localOp f)) →
        ((address : Fin (q.N ^ q.exponent)) →
            (window : CodedSorting.Normalization.Window q.ramWords q.block) →
              motive (CodedSorting.Normalization.Command.read address window)) →
          ((address : Fin (q.N ^ q.exponent)) →
              (window : CodedSorting.Normalization.Window q.ramWords q.block) →
                motive (CodedSorting.Normalization.Command.write address window)) →
            motive x
```

**定义**

```lean
fun q motive x h_1 h_2 h_3 =>
  CodedSorting.Normalization.Command.casesOn x (fun f => h_1 f) (fun address window => h_2 address window)
    fun address window => h_3 address window
```

**继续展开**

- [CodedSorting.WordControl.Word](../../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.Normalization.Command.write](../Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.Normalization.Command.casesOn](../Normalization.definitions.md#def-d5874f9d23d9c310)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Normalization.Command.read](../Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.Normalization.Window](../Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command.localOp](../Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.Normalization.Command](../Normalization.definitions.md#def-5d1402e119d2b0bd)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-287b35752636a175"></a>
## `CodedSorting.CommonStaticSchedule.cost.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Fusion.lean)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (motive : List (CodedSorting.CommonStaticSchedule.Instruction q) → Sort u_1) →
    (x : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
      (Unit → motive []) →
        ((i : CodedSorting.CommonStaticSchedule.Instruction q) →
            (is : List (CodedSorting.CommonStaticSchedule.Instruction q)) → motive (i :: is)) →
          motive x
```

**定义**

```lean
fun q motive x h_1 h_2 => List.casesOn x (h_1 ()) fun head tail => h_2 head tail
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `List.casesOn`, `List.nil`

<a id="def-900a1a2a3ae5d733"></a>
## `CodedSorting.CommonStaticSchedule.executeRaw.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Fusion.lean)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  (motive :
      List (CodedSorting.CommonStaticSchedule.Instruction q) → CodedSorting.CommonLeafProgram.Machine q → Sort u_1) →
    (x : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
      (x_1 : CodedSorting.CommonLeafProgram.Machine q) →
        ((s : CodedSorting.CommonLeafProgram.Machine q) → motive [] s) →
          ((i : CodedSorting.CommonStaticSchedule.Instruction q) →
              (is : List (CodedSorting.CommonStaticSchedule.Instruction q)) →
                (s : CodedSorting.CommonLeafProgram.Machine q) → motive (i :: is) s) →
            motive x x_1
```

**定义**

```lean
fun q motive x x_1 h_1 h_2 => List.casesOn x (h_1 x_1) fun head tail => h_2 head tail x_1
```

**继续展开**

- [CodedSorting.CommonLeafProgram.Machine](../../Memory/Leaf/Program.definitions.md#def-e2ceb047c19cf684)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List.cons`, `List`, `List.casesOn`, `List.nil`
