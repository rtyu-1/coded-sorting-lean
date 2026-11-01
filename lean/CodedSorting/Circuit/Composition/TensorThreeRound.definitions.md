# TensorThreeRound 的定义

[源码](TensorThreeRound.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-83372085a1b0abcf"></a>
## `CodedSorting.Construction.TensorThreeRound.roundAssignment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorThreeRound.lean#L79)

**类型**

```lean
Equiv.Perm CodedSorting.Construction.ThreeCopySchedule.Line →
  CodedSorting.Construction.TensorLiftProgram.Round →
    CodedSorting.Construction.ThreeCopySchedule.Pool ≃ CodedSorting.Construction.ThreeCopySchedule.Block
```

**定义**

```lean
fun pi x =>
  match x with
  | CodedSorting.Construction.TensorLiftProgram.Round.first => CodedSorting.Construction.ThreeCopySchedule.roundOne
  | CodedSorting.Construction.TensorLiftProgram.Round.second => CodedSorting.Construction.ThreeCopySchedule.roundTwo pi
  | CodedSorting.Construction.TensorLiftProgram.Round.third => CodedSorting.Construction.ThreeCopySchedule.roundThree pi
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.roundThree](TensorLiftProgram.definitions.md#def-b14c6a710cfeed94)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.roundTwo](TensorLiftProgram.definitions.md#def-5c27d20aeb3a3342)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorThreeRound.round_data_zero.match_1](TensorThreeRound.definitions.md#def-3444b2aacf2e85b1)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.ThreeCopySchedule.roundOne](TensorLiftProgram.definitions.md#def-c0e72db768c66f93)

**基础库名称**

`Equiv`, `Unit`, `Equiv.Perm`

<a id="def-ca4a87271cd10a88"></a>
## `CodedSorting.Construction.TensorThreeRound.threeRoundProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorThreeRound.lean#L85)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg) →
  List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg) →
    List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg) →
      Equiv.Perm CodedSorting.Construction.ThreeCopySchedule.Line →
        List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.GlobalReg)
```

**定义**

```lean
fun wordOne wordTwo wordThree pi =>
  CodedSorting.Construction.TensorLiftProgram.roundProgram wordOne
        CodedSorting.Construction.TensorLiftProgram.Round.first
        (CodedSorting.Construction.TensorThreeRound.roundAssignment pi
          CodedSorting.Construction.TensorLiftProgram.Round.first) ++
      CodedSorting.Construction.TensorLiftProgram.roundProgram wordTwo
        CodedSorting.Construction.TensorLiftProgram.Round.second
        (CodedSorting.Construction.TensorThreeRound.roundAssignment pi
          CodedSorting.Construction.TensorLiftProgram.Round.second) ++
    CodedSorting.Construction.TensorLiftProgram.roundProgram wordThree
      CodedSorting.Construction.TensorLiftProgram.Round.third
      (CodedSorting.Construction.TensorThreeRound.roundAssignment pi
        CodedSorting.Construction.TensorLiftProgram.Round.third)
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.roundProgram](TensorLiftProgram.definitions.md#def-4e558b6f3c1dd8ee)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorThreeRound.roundAssignment](TensorThreeRound.definitions.md#def-83372085a1b0abcf)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

**基础库名称**

`instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Sum.instDecidableEq`, `instOfNatNat`, `instHAppendOfAppend`, `List`, `Equiv.Perm`, `Nat`, `List.instAppend`, `Prod`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`

<a id="def-8b3c0826e8b41aa5"></a>
## `CodedSorting.Construction.TensorThreeRound.originalSwap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorThreeRound.lean#L126)

**类型**

```lean
Equiv.Perm CodedSorting.Construction.ThreeCopySchedule.IndependentStream
```

**定义**

```lean
((Equiv.refl CodedSorting.Construction.ThreeCopySchedule.Copy).prodCongr
      (Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl CodedSorting.Construction.TensorLiftProgram.Coordinates))).sumCongr
  (Equiv.refl CodedSorting.Construction.ThreeCopySchedule.HelperStream)
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Coordinates](TensorLiftProgram.definitions.md#def-b93298813069e8c3)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorThreeRound.originalSwap._proof_1](TensorThreeRound.definitions.md#def-1f5a55018e1e31b4)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`instDecidableEqFin`, `Equiv.swap`, `Fin.instOfNat`, `instOfNatNat`, `Equiv.sumCongr`, `Equiv.Perm`, `Nat`, `Prod`, `Equiv.prodCongr`, `OfNat.ofNat`, `Fin`, `Equiv.refl`

<a id="def-1f5a55018e1e31b4"></a>
## `CodedSorting.Construction.TensorThreeRound.originalSwap._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorThreeRound.lean)

**类型**

```lean
NeZero (1 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-3444b2aacf2e85b1"></a>
## `CodedSorting.Construction.TensorThreeRound.round_data_zero.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TensorThreeRound.lean)

**类型**

```lean
(motive : CodedSorting.Construction.TensorLiftProgram.Round → Sort u_1) →
  (round : CodedSorting.Construction.TensorLiftProgram.Round) →
    (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.first) →
      (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.second) →
        (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.third) → motive round
```

**定义**

```lean
fun motive round h_1 h_2 h_3 =>
  CodedSorting.Construction.TensorLiftProgram.Round.casesOn round (h_1 ()) (h_2 ()) (h_3 ())
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.casesOn](TensorLiftProgram.definitions.md#def-81b2db8aedad1210)
- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

**基础库名称**

`Unit.unit`, `Unit`
