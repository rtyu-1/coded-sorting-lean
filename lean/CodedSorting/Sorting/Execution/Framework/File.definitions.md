# File 的定义

[源码](File.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-10bf3dbef7b83d76"></a>
## `CodedSorting.CommonIntegerFile.input`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L17)

**类型**

```lean
{w : ℕ} → List (CodedSorting.WordControl.Word w) → List (CodedSorting.KeyRecordWords.Record w)
```

**定义**

```lean
fun {w} xs => List.map (fun x => CodedSorting.KeyRecordWords.Record.data x x) xs
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record.data](../../../Shared/Records/KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)

**基础库名称**

`List.map`, `List`, `Nat`

<a id="def-325e073a4333ad07"></a>
## `CodedSorting.CommonIntegerFile.keyWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L20)

**类型**

```lean
{w : ℕ} → CodedSorting.KeyRecordWords.Record w → CodedSorting.WordControl.Word w
```

**定义**

```lean
fun {w} x =>
  match x with
  | CodedSorting.KeyRecordWords.Record.bottom => 0
  | CodedSorting.KeyRecordWords.Record.data k payload => k
  | CodedSorting.KeyRecordWords.Record.top => 0
```

**继续展开**

- [CodedSorting.CommonIntegerFile.keyWord._proof_1](File.definitions.md#def-cc57e9fde715e118)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonIntegerFile.keyWord.match_1](File.definitions.md#def-de0d1e7cb8427974)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.instOfNat`, `instOfNatNat`, `Unit`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-3c532eb1dc6742b7"></a>
## `CodedSorting.CommonIntegerFile.project`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L25)

**类型**

```lean
{w : ℕ} → List (CodedSorting.KeyRecordWords.Record w) → List (CodedSorting.WordControl.Word w)
```

**定义**

```lean
fun {w} rs => List.map CodedSorting.CommonIntegerFile.keyWord rs
```

**继续展开**

- [CodedSorting.CommonIntegerFile.keyWord](File.definitions.md#def-325e073a4333ad07)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)

**基础库名称**

`List.map`, `List`, `Nat`

<a id="def-22e1c41173dbab7f"></a>
## `CodedSorting.CommonIntegerFile.output`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L74)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  List (CodedSorting.WordControl.Word q.w) → List (CodedSorting.WordControl.Word q.w)
```

**定义**

```lean
fun q xs =>
  CodedSorting.CommonIntegerFile.project
    (CodedSorting.CommonMSDSortingRun.output q (CodedSorting.CommonIntegerFile.input xs))
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDSortingRun.output](../../Radix/Framework/SortingPower.definitions.md#def-162ad3c71821ad20)
- [CodedSorting.CommonIntegerFile.project](File.definitions.md#def-3c532eb1dc6742b7)
- [CodedSorting.CommonIntegerFile.input](File.definitions.md#def-10bf3dbef7b83d76)

**基础库名称**

`List`

<a id="def-4e8a7732db4e6068"></a>
## `CodedSorting.CommonIntegerProjectionChunk.keyIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L109)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.block → Fin (CodedSorting.CommonExchangeLeaf.bankWords q)
```

**定义**

```lean
fun q j => ⟨3 * ↑j + 1, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonIntegerProjectionChunk.keyIndex._proof_3](File.definitions.md#def-0c4ef384e1499132)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Fin.mk`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-046630da1413953e"></a>
## `CodedSorting.CommonIntegerProjectionChunk.selected`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L112)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonLeafProgram.Store q → CodedSorting.WordControl.Words q.block q.w
```

**定义**

```lean
fun q s j => CodedSorting.ResidentLeafBank.raw s.leaf (CodedSorting.CommonIntegerProjectionChunk.keyIndex q j)
```

**继续展开**

- [CodedSorting.ResidentLeafBank.raw](../../../Shared/Memory/ResidentLeafBank.definitions.md#def-d1d4a603610970b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonIntegerProjectionChunk.keyIndex](File.definitions.md#def-4e8a7732db4e6068)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-42bc89208dfd30ab"></a>
## `CodedSorting.CommonIntegerProjectionChunk.select`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L118)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        let s := CodedSorting.CommonSortingNormalization.unpack ram;
        CodedSorting.CommonSortingNormalization.pack
          { leaf := s.leaf, readers := s.readers, writers := s.writers,
            transfer := CodedSorting.CommonIntegerProjectionChunk.selected q s, scalars := s.scalars,
            directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs },
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../../Shared/Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonIntegerProjectionChunk.selected](File.definitions.md#def-046630da1413953e)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonSortingNormalization.SourceState](../../Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.Normalization.Command.localOp](../../../Shared/Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-17f424be9c235400"></a>
## `CodedSorting.CommonIntegerProjectionChunk.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L122)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q k =>
  CodedSorting.CommonStaticLeaf.readCode q (3 * k) (3 * q.block) 3 ++
    [CodedSorting.CommonIntegerProjectionChunk.select q, CodedSorting.CommonStaticLeaf.writeAt q k 0]
```

**继续展开**

- [CodedSorting.CommonIntegerProjectionChunk.select](File.definitions.md#def-42bc89208dfd30ab)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticLeaf.writeAt](../../../Shared/Programs/Static/Leaf.definitions.md#def-042043b77ced7fe8)
- [CodedSorting.CommonStaticLeaf.readCode](../../../Shared/Programs/Static/Leaf.definitions.md#def-292caf1044d209bc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List.cons`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `HAppend.hAppend`, `instHMul`, `List.nil`

<a id="def-8fa0bfff89a6d788"></a>
## `CodedSorting.CommonIntegerExpandBlock.expanded`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L211)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonBlockPair.Block q → ℕ → CodedSorting.CommonBlockPair.Block q
```

**定义**

```lean
fun q block j i =>
  let z := j * q.block + ↑i;
  let x := block ⟨z / 3 % q.block, ⋯⟩;
  CodedSorting.KeyRecordWords.encode q.w ⋯ (CodedSorting.KeyRecordWords.Record.data x x) ⟨z % 3, ⋯⟩
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonIntegerExpandBlock.expanded._proof_7](File.definitions.md#def-6cbc66c18cbbb607)
- [CodedSorting.CommonIntegerExpandBlock.expanded._proof_9](File.definitions.md#def-a68b595de16b96b3)
- [CodedSorting.CommonIntegerExpandBlock.expanded._proof_8](File.definitions.md#def-7a02df9282559a13)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.KeyRecordWords.Record.data](../../../Shared/Records/KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonBlockPair.Block](../../../Shared/Memory/BlockPair.definitions.md#def-31b415875e0e521a)
- [CodedSorting.KeyRecordWords.encode](../../../Shared/Records/KeyRecordWords.definitions.md#def-db8b85b6def9e34c)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Fin.mk`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-d9bec1b8694f1d84"></a>
## `CodedSorting.CommonIntegerExpandBlock.stage`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L216)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q reader j =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        let s := CodedSorting.CommonSortingNormalization.unpack ram;
        CodedSorting.CommonSortingNormalization.pack
          { leaf := s.leaf, readers := s.readers, writers := s.writers,
            transfer :=
              CodedSorting.CommonIntegerExpandBlock.expanded q (CodedSorting.CommonBlockPair.buffer q reader s) j,
            scalars := s.scalars, directories := s.directories, shapes := s.shapes, top := s.top, pcs := s.pcs },
    resume := id }
```

**继续展开**

- [CodedSorting.CommonBlockPair.buffer](../../../Shared/Memory/BlockPair.definitions.md#def-af60041b169cb3ab)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../../Shared/Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonSortingNormalization.SourceState](../../Resources/Framework/NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.Normalization.Command.localOp](../../../Shared/Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonIntegerExpandBlock.expanded](File.definitions.md#def-8fa0bfff89a6d788)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-1e2036c0b9c2b585"></a>
## `CodedSorting.CommonIntegerExpandBlock.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L234)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader base k =>
  if h : base + 3 * k + 3 ≤ q.N ^ q.exponent then
    [CodedSorting.CommonBlockPair.sourceRead q reader ⟨base + k, ⋯⟩,
      CodedSorting.CommonIntegerExpandBlock.stage q reader 0,
      CodedSorting.CommonBlockPair.targetWrite q ⟨base + 3 * k, ⋯⟩,
      CodedSorting.CommonIntegerExpandBlock.stage q reader 1,
      CodedSorting.CommonBlockPair.targetWrite q ⟨base + 3 * k + 1, ⋯⟩,
      CodedSorting.CommonIntegerExpandBlock.stage q reader 2,
      CodedSorting.CommonBlockPair.targetWrite q ⟨base + 3 * k + 2, ⋯⟩]
  else []
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonIntegerExpandBlock.code._proof_14](File.definitions.md#def-5b2f8616290b6267)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonIntegerExpandBlock.code._proof_17](File.definitions.md#def-f8ee195507d4e52d)
- [CodedSorting.CommonBlockPair.sourceRead](../../../Shared/Memory/BlockPair.definitions.md#def-5dc5b806044bea03)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonIntegerExpandBlock.code._proof_15](File.definitions.md#def-5046d464c70409f3)
- [CodedSorting.CommonBlockPair.targetWrite](../../../Shared/Memory/BlockPair.definitions.md#def-3b05497ae0c5b9b7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonIntegerExpandBlock.code._proof_16](File.definitions.md#def-cf3e60666f22baaf)
- [CodedSorting.CommonIntegerExpandBlock.stage](File.definitions.md#def-d9bec1b8694f1d84)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `dite`, `List.cons`, `List`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Not`, `Nat.decLe`, `instHMul`, `List.nil`

<a id="def-061ed3c9fb58fbbe"></a>
## `CodedSorting.CommonIntegerProjection.blocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L343)

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

<a id="def-e93c8d61e73a3970"></a>
## `CodedSorting.CommonIntegerProjection.scanPrefix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L345)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q k => List.flatMap (CodedSorting.CommonIntegerProjectionChunk.code q) (List.range k)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonIntegerProjectionChunk.code](File.definitions.md#def-17f424be9c235400)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List.range`, `List`, `Nat`, `List.flatMap`

<a id="def-acb6500e31fe8928"></a>
## `CodedSorting.CommonIntegerProjection.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L348)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q n => CodedSorting.CommonIntegerProjection.scanPrefix q (CodedSorting.CommonIntegerProjection.blocks q n)
```

**继续展开**

- [CodedSorting.CommonIntegerProjection.blocks](File.definitions.md#def-061ed3c9fb58fbbe)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonIntegerProjection.scanPrefix](File.definitions.md#def-e93c8d61e73a3970)

**基础库名称**

`List`, `Nat`

<a id="def-d8bf223ac75bbc0f"></a>
## `CodedSorting.CommonIntegerProjection.safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean#L395)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (n : ℕ),
  ∀ i ∈ CodedSorting.CommonIntegerProjection.code q n, CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonIntegerProjection.code](File.definitions.md#def-acb6500e31fe8928)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)

**基础库名称**

`Membership.mem`, `List`, `List.instMembership`, `Nat`

<a id="def-0ff54eacb6eb81dd"></a>
## `CodedSorting.CommonIntegerExpand.loops`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L511)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader base x =>
  Nat.brecOn x fun x f =>
    (match (motive := (x : ℕ) → Nat.below x → List (CodedSorting.CommonStaticSchedule.Instruction q)) x with
      | 0 => fun x => []
      | K.succ => fun x => CodedSorting.CommonIntegerExpandBlock.code q reader base K ++ x.1)
      f
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonIntegerExpand.loops.match_1](File.definitions.md#def-04f0de976e5a966d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonIntegerExpandBlock.code](File.definitions.md#def-1e2036c0b9c2b585)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`Nat.brecOn`, `instOfNatNat`, `Nat.below`, `instHAppendOfAppend`, `List`, `Unit`, `PProd`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `HAppend.hAppend`, `List.nil`

<a id="def-1aaeea12e0f45624"></a>
## `CodedSorting.CommonIntegerExpand.blocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L516)

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

<a id="def-9fbe4953afb337fe"></a>
## `CodedSorting.CommonIntegerExpand.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](File.lean#L518)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader n base =>
  CodedSorting.CommonIntegerExpand.loops q reader base (CodedSorting.CommonIntegerExpand.blocks q n)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonIntegerExpand.blocks](File.definitions.md#def-1aaeea12e0f45624)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonIntegerExpand.loops](File.definitions.md#def-0ff54eacb6eb81dd)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List`, `Nat`, `Fin`

<a id="def-04f0de976e5a966d"></a>
## `CodedSorting.CommonIntegerExpand.loops.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](File.lean)

**类型**

```lean
(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((K : ℕ) → motive K.succ) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 => Nat.casesOn x (h_1 ()) fun n => h_2 n
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `instOfNatNat`, `Unit`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-5b2f8616290b6267"></a>
## `CodedSorting.CommonIntegerExpandBlock.code._proof_14`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base k : ℕ),
  base + 3 * k + 3 ≤ q.N ^ q.exponent → base + k < q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-5046d464c70409f3"></a>
## `CodedSorting.CommonIntegerExpandBlock.code._proof_15`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base k : ℕ),
  base + 3 * k + 3 ≤ q.N ^ q.exponent → base + 3 * k < q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-cf3e60666f22baaf"></a>
## `CodedSorting.CommonIntegerExpandBlock.code._proof_16`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base k : ℕ),
  base + 3 * k + 3 ≤ q.N ^ q.exponent → base + 3 * k + 1 < q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-f8ee195507d4e52d"></a>
## `CodedSorting.CommonIntegerExpandBlock.code._proof_17`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (base k : ℕ),
  base + 3 * k + 3 ≤ q.N ^ q.exponent → base + 3 * k + 2 < q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-6cbc66c18cbbb607"></a>
## `CodedSorting.CommonIntegerExpandBlock.expanded._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (j : ℕ) (i : Fin q.block),
  (j * q.block + ↑i) / 3 % q.block < q.block
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-7a02df9282559a13"></a>
## `CodedSorting.CommonIntegerExpandBlock.expanded._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), 2 ≤ q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-a68b595de16b96b3"></a>
## `CodedSorting.CommonIntegerExpandBlock.expanded._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (j : ℕ) (i : Fin q.block), (j * q.block + ↑i) % 3 < 3
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `Nat.instMod`, `instHMod`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-cc57e9fde715e118"></a>
## `CodedSorting.CommonIntegerFile.keyWord._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ {w : ℕ}, NeZero (2 ^ w)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `OfNat.ofNat`, `MulZeroClass.toZero`

<a id="def-de0d1e7cb8427974"></a>
## `CodedSorting.CommonIntegerFile.keyWord.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](File.lean)

**类型**

```lean
{w : ℕ} →
  (motive : CodedSorting.KeyRecordWords.Record w → Sort u_1) →
    (x : CodedSorting.KeyRecordWords.Record w) →
      (Unit → motive CodedSorting.KeyRecordWords.Record.bottom) →
        ((k payload : CodedSorting.WordControl.Word w) → motive (CodedSorting.KeyRecordWords.Record.data k payload)) →
          (Unit → motive CodedSorting.KeyRecordWords.Record.top) → motive x
```

**定义**

```lean
fun {w} motive x h_1 h_2 h_3 =>
  CodedSorting.KeyRecordWords.Record.casesOn x (h_1 ()) (fun key payload => h_2 key payload) (h_3 ())
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record.casesOn](../../../Shared/Records/KeyRecordWords.definitions.md#def-ad7ef446def9fade)
- [CodedSorting.KeyRecordWords.Record.data](../../../Shared/Records/KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](../../../Shared/Records/KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.KeyRecordWords.Record.top](../../../Shared/Records/KeyRecordWords.definitions.md#def-dfff22d085934d4b)

**基础库名称**

`Unit.unit`, `Unit`, `Nat`

<a id="def-0c4ef384e1499132"></a>
## `CodedSorting.CommonIntegerProjectionChunk.keyIndex._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](File.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (j : Fin q.block),
  3 * ↑j + 1 < CodedSorting.CommonExchangeLeaf.bankWords q
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`
