# TensorLiftProgram 的定义

[源码](TensorLiftProgram.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-1264fff0ec0bb152"></a>
## `CodedSorting.Construction.ThreeCopySchedule.Copy`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L27)

**类型**

```lean
Type
```

**定义**

```lean
Fin 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-0d839a35fa97d067"></a>
## `CodedSorting.Construction.ThreeCopySchedule.Line`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L28)

**类型**

```lean
Type
```

**定义**

```lean
Fin 111
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-7c00b43778d69908"></a>
## `CodedSorting.Construction.ThreeCopySchedule.Pool`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L29)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.ThreeCopySchedule.Copy ×
  CodedSorting.Construction.ThreeCopySchedule.Line × CodedSorting.Construction.ThreeCopySchedule.Line
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Prod`

<a id="def-cb083799392a946e"></a>
## `CodedSorting.Construction.ThreeCopySchedule.Block`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L30)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.ThreeCopySchedule.Copy ×
  CodedSorting.Construction.ThreeCopySchedule.Line × CodedSorting.Construction.ThreeCopySchedule.Line
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Prod`

<a id="def-709e995148360e96"></a>
## `CodedSorting.Construction.ThreeCopySchedule.DataStream`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L31)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.ThreeCopySchedule.Copy ×
  Fin 2 ×
    CodedSorting.Construction.ThreeCopySchedule.Line ×
      CodedSorting.Construction.ThreeCopySchedule.Line × CodedSorting.Construction.ThreeCopySchedule.Line
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`instOfNatNat`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-de2624a13ceae317"></a>
## `CodedSorting.Construction.ThreeCopySchedule.HelperStream`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L32)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.ThreeCopySchedule.Pool × Fin 439
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)

**基础库名称**

`instOfNatNat`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-59b37f8e42d90966"></a>
## `CodedSorting.Construction.ThreeCopySchedule.IndependentStream`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L33)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.ThreeCopySchedule.DataStream ⊕ CodedSorting.Construction.ThreeCopySchedule.HelperStream
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](TensorLiftProgram.definitions.md#def-de2624a13ceae317)

**基础库名称**

`Sum`

<a id="def-a9652f9d06da2a51"></a>
## `CodedSorting.Construction.ThreeCopySchedule.nextCopy`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L35)

**类型**

```lean
Equiv.Perm CodedSorting.Construction.ThreeCopySchedule.Copy
```

**定义**

```lean
{ toFun := fun i => ⟨(↑i + 1) % 3, ⋯⟩, invFun := fun i => ⟨(↑i + 2) % 3, ⋯⟩,
  left_inv := CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_3,
  right_inv := CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_4 }
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_4](TensorLiftProgram.definitions.md#def-ff30273516264483)
- [CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_2](TensorLiftProgram.definitions.md#def-75a11ae27ce5cf0e)
- [CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_3](TensorLiftProgram.definitions.md#def-80236977868d91cf)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_1](TensorLiftProgram.definitions.md#def-b9404bf0d393954f)

**基础库名称**

`Equiv.mk`, `Fin.mk`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-c0e72db768c66f93"></a>
## `CodedSorting.Construction.ThreeCopySchedule.roundOne`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L46)

**类型**

```lean
CodedSorting.Construction.ThreeCopySchedule.Pool ≃ CodedSorting.Construction.ThreeCopySchedule.Block
```

**定义**

```lean
Equiv.refl CodedSorting.Construction.ThreeCopySchedule.Pool
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)

**基础库名称**

`Equiv`, `Equiv.refl`

<a id="def-5c27d20aeb3a3342"></a>
## `CodedSorting.Construction.ThreeCopySchedule.roundTwo`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L48)

**类型**

```lean
Equiv.Perm CodedSorting.Construction.ThreeCopySchedule.Line →
  CodedSorting.Construction.ThreeCopySchedule.Pool ≃ CodedSorting.Construction.ThreeCopySchedule.Block
```

**定义**

```lean
fun pi =>
  (Equiv.symm CodedSorting.Construction.ThreeCopySchedule.nextCopy).prodCongr
    ((Equiv.refl CodedSorting.Construction.ThreeCopySchedule.Line).prodCongr pi)
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.ThreeCopySchedule.nextCopy](TensorLiftProgram.definitions.md#def-a9652f9d06da2a51)

**基础库名称**

`Equiv`, `Equiv.Perm`, `Equiv.symm`, `Prod`, `Equiv.prodCongr`, `Equiv.refl`

<a id="def-b14c6a710cfeed94"></a>
## `CodedSorting.Construction.ThreeCopySchedule.roundThree`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L51)

**类型**

```lean
Equiv.Perm CodedSorting.Construction.ThreeCopySchedule.Line →
  CodedSorting.Construction.ThreeCopySchedule.Pool ≃ CodedSorting.Construction.ThreeCopySchedule.Block
```

**定义**

```lean
fun pi => Equiv.prodCongr CodedSorting.Construction.ThreeCopySchedule.nextCopy (Equiv.prodCongr pi pi)
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.ThreeCopySchedule.nextCopy](TensorLiftProgram.definitions.md#def-a9652f9d06da2a51)

**基础库名称**

`Equiv`, `Equiv.Perm`, `Prod`, `Equiv.prodCongr`

<a id="def-2eaf92ac720f7636"></a>
## `CodedSorting.Construction.ThreeCopySchedule.independent_stream_count`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean#L119)

**类型**

```lean
Fintype.card CodedSorting.Construction.ThreeCopySchedule.IndependentStream = CodedSorting.Construction.streamCount
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.streamCount](../Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`instFintypeSum`, `Fintype.card`, `instOfNatNat`, `Fin.fintype`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`

<a id="def-4ed3891a984aeec8"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](TensorLiftProgram.lean#L148)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

<a id="def-81b2db8aedad1210"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round.casesOn`

读取 `CodedSorting.Construction.TensorLiftProgram.Round` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](TensorLiftProgram.lean#L148)

**类型**

```lean
{motive : CodedSorting.Construction.TensorLiftProgram.Round → Sort u} →
  (t : CodedSorting.Construction.TensorLiftProgram.Round) →
    motive CodedSorting.Construction.TensorLiftProgram.Round.first →
      motive CodedSorting.Construction.TensorLiftProgram.Round.second →
        motive CodedSorting.Construction.TensorLiftProgram.Round.third → motive t
```

**定义**

```lean
fun {motive} t first second third => CodedSorting.Construction.TensorLiftProgram.Round.rec first second third t
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.rec](TensorLiftProgram.definitions.md#def-0756ded43aea635a)
- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

<a id="def-0756ded43aea635a"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](TensorLiftProgram.lean#L148)

**类型**

```lean
{motive : CodedSorting.Construction.TensorLiftProgram.Round → Sort u} →
  motive CodedSorting.Construction.TensorLiftProgram.Round.first →
    motive CodedSorting.Construction.TensorLiftProgram.Round.second →
      motive CodedSorting.Construction.TensorLiftProgram.Round.third →
        (t : CodedSorting.Construction.TensorLiftProgram.Round) → motive t
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

<a id="def-d720b8b1634db154"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round.first`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](TensorLiftProgram.lean#L149)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)

<a id="def-5e51e999de8f97b0"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round.second`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](TensorLiftProgram.lean#L149)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)

<a id="def-317025dd1bb44223"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round.third`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](TensorLiftProgram.lean#L149)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)

<a id="def-4e29313a6d76909b"></a>
## `CodedSorting.Construction.TensorLiftProgram.instDecidableEqRound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L150)

**类型**

```lean
DecidableEq CodedSorting.Construction.TensorLiftProgram.Round
```

**定义**

```lean
fun x y => if h : x.toCtorIdx = y.toCtorIdx then isTrue ⋯ else isFalse ⋯
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.instDecidableEqRound._proof_6](TensorLiftProgram.definitions.md#def-5bf2c617c40e6a13)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.instDecidableEqRound._proof_5](TensorLiftProgram.definitions.md#def-3fe584ef1befc79d)
- [CodedSorting.Construction.TensorLiftProgram.Round.toCtorIdx](TensorLiftProgram.definitions.md#def-b6860a0ad4158931)

**基础库名称**

`Decidable.isTrue`, `Decidable`, `dite`, `Nat`, `instDecidableEqNat`, `Decidable.isFalse`, `Eq`, `Not`, `DecidableEq`

<a id="def-9d47e1f47feb55c7"></a>
## `CodedSorting.Construction.TensorLiftProgram.instFintypeRound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L150)

**类型**

```lean
Fintype CodedSorting.Construction.TensorLiftProgram.Round
```

**定义**

```lean
{
  elems :=
    { val := ↑CodedSorting.Construction.TensorLiftProgram.Round.enumList,
      nodup := CodedSorting.Construction.TensorLiftProgram.Round.enumList_nodup },
  complete := CodedSorting.Construction.TensorLiftProgram.instFintypeRound._proof_7 }
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.instFintypeRound._proof_7](TensorLiftProgram.definitions.md#def-44508ba7f93ef650)
- [CodedSorting.Construction.TensorLiftProgram.Round.enumList](TensorLiftProgram.definitions.md#def-f45cd2d506eb989d)
- [CodedSorting.Construction.TensorLiftProgram.Round.enumList_nodup](TensorLiftProgram.definitions.md#def-87f11ac3a087ecd5)

**基础库名称**

`Multiset.ofList`, `Fintype`, `Fintype.mk`, `Finset.mk`

<a id="def-b93298813069e8c3"></a>
## `CodedSorting.Construction.TensorLiftProgram.Coordinates`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L152)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.ThreeCopySchedule.Line ×
  CodedSorting.Construction.ThreeCopySchedule.Line × CodedSorting.Construction.ThreeCopySchedule.Line
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)

**基础库名称**

`Prod`

<a id="def-457787d4c5210d35"></a>
## `CodedSorting.Construction.TensorLiftProgram.LocalReg`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L153)

**类型**

```lean
Type
```

**定义**

```lean
Fin 2 × CodedSorting.Construction.ThreeCopySchedule.Line ⊕ Fin 439 ⊕ Fin 9
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)

**基础库名称**

`Sum`, `instOfNatNat`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-f6ff16bd9f6b23da"></a>
## `CodedSorting.Construction.TensorLiftProgram.TemporaryStream`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L154)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.TensorLiftProgram.Round × CodedSorting.Construction.ThreeCopySchedule.Block × Fin 9
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)

**基础库名称**

`instOfNatNat`, `Nat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-e76d203076293c86"></a>
## `CodedSorting.Construction.TensorLiftProgram.GlobalReg`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L155)

**类型**

```lean
Type
```

**定义**

```lean
CodedSorting.Construction.ThreeCopySchedule.IndependentStream ⊕
  CodedSorting.Construction.TensorLiftProgram.TemporaryStream
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)

**基础库名称**

`Sum`

<a id="def-15a1fd47fc7a9c44"></a>
## `CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L157)

**类型**

```lean
DecidableEq CodedSorting.Construction.TensorLiftProgram.GlobalReg
```

**定义**

```lean
Classical.decEq CodedSorting.Construction.TensorLiftProgram.GlobalReg
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)

**基础库名称**

`Classical.decEq`, `DecidableEq`

<a id="def-f2a12032c7a10f95"></a>
## `CodedSorting.Construction.TensorLiftProgram.localOriginalIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L159)

**类型**

```lean
Fin 2 × CodedSorting.Construction.ThreeCopySchedule.Line ⊕ Fin 439 ≃
  CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg
```

**定义**

```lean
(finProdFinEquiv.sumCongr (Equiv.refl (Fin 439))).trans finSumFinEquiv
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](../Local/LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Sum`, `Equiv`, `instMulNat`, `instOfNatNat`, `Equiv.sumCongr`, `Nat`, `finSumFinEquiv`, `finProdFinEquiv`, `Prod`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `instHMul`

<a id="def-3f174a6e4eb935de"></a>
## `CodedSorting.Construction.TensorLiftProgram.localPhysicalIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L163)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.LocalReg ≃ CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg
```

**定义**

```lean
(Equiv.sumAssoc (Fin 2 × CodedSorting.Construction.ThreeCopySchedule.Line) (Fin 439) (Fin 9)).symm.trans
  (CodedSorting.Construction.TensorLiftProgram.localOriginalIndex.sumCongr (Equiv.refl (Fin 9)))
```

**继续展开**

- [CodedSorting.Construction.LocalPhysicalSemantics.OriginalReg](../Local/LocalPhysicalSemantics.definitions.md#def-9d780c699bf6c5ab)
- [CodedSorting.Construction.LocalPhysicalSemantics.PhysicalReg](../Local/LocalPhysicalSemantics.definitions.md#def-8ab4657853f928aa)
- [CodedSorting.Construction.TensorLiftProgram.localOriginalIndex](TensorLiftProgram.definitions.md#def-f2a12032c7a10f95)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.LocalPhysicalSemantics.TemporaryReg](../Local/LocalPhysicalSemantics.definitions.md#def-b31f6a3a15f6fe7a)

**基础库名称**

`Equiv.trans`, `Sum`, `Equiv`, `instOfNatNat`, `Equiv.sumCongr`, `Nat`, `Equiv.sumAssoc`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Equiv.refl`

<a id="def-8f9978d9b5dd8eb5"></a>
## `CodedSorting.Construction.TensorLiftProgram.coordinateView`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L167)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.TensorLiftProgram.Coordinates ≃ CodedSorting.Construction.TensorLiftProgram.Coordinates
```

**定义**

```lean
fun x =>
  match x with
  | CodedSorting.Construction.TensorLiftProgram.Round.first =>
    Equiv.refl CodedSorting.Construction.TensorLiftProgram.Coordinates
  | CodedSorting.Construction.TensorLiftProgram.Round.second =>
    { toFun := fun p => (p.2.1, p.2.2, p.1), invFun := fun p => (p.2.2, p.1, p.2.1),
      left_inv := CodedSorting.Construction.TensorLiftProgram.coordinateView._proof_8,
      right_inv := CodedSorting.Construction.TensorLiftProgram.coordinateView._proof_9 }
  | CodedSorting.Construction.TensorLiftProgram.Round.third =>
    { toFun := fun p => (p.2.2, p.1, p.2.1), invFun := fun p => (p.2.1, p.2.2, p.1),
      left_inv := CodedSorting.Construction.TensorLiftProgram.coordinateView._proof_9,
      right_inv := CodedSorting.Construction.TensorLiftProgram.coordinateView._proof_8 }
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Coordinates](TensorLiftProgram.definitions.md#def-b93298813069e8c3)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.coordinateView._proof_9](TensorLiftProgram.definitions.md#def-a9c1fd887527f143)
- [CodedSorting.Construction.TensorLiftProgram.coordinateView.match_1](TensorLiftProgram.definitions.md#def-6200ea44ceeec65f)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorLiftProgram.coordinateView._proof_8](TensorLiftProgram.definitions.md#def-5fea05fe0d35ce82)

**基础库名称**

`Equiv.mk`, `Equiv`, `Prod.mk`, `Prod.fst`, `Unit`, `Prod`, `Equiv.refl`, `Prod.snd`

<a id="def-da080c5a5be96a1b"></a>
## `CodedSorting.Construction.TensorLiftProgram.bankView`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L182)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round → Equiv.Perm (Fin 2)
```

**定义**

```lean
fun x =>
  match x with
  | CodedSorting.Construction.TensorLiftProgram.Round.first => Equiv.refl (Fin 2)
  | CodedSorting.Construction.TensorLiftProgram.Round.second => Equiv.swap 0 1
  | CodedSorting.Construction.TensorLiftProgram.Round.third => Equiv.refl (Fin 2)
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.coordinateView.match_1](TensorLiftProgram.definitions.md#def-6200ea44ceeec65f)
- [CodedSorting.Construction.TensorLiftProgram.bankView._proof_10](TensorLiftProgram.definitions.md#def-66fef3202e7d0017)

**基础库名称**

`instDecidableEqFin`, `Equiv.swap`, `Fin.instOfNat`, `instOfNatNat`, `Unit`, `Equiv.Perm`, `Nat`, `OfNat.ofNat`, `Fin`, `Equiv.refl`

<a id="def-88546747689b44d4"></a>
## `CodedSorting.Construction.TensorLiftProgram.fiberDataEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L188)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Block × Fin 2 × CodedSorting.Construction.ThreeCopySchedule.Line ≃
    CodedSorting.Construction.ThreeCopySchedule.DataStream
```

**定义**

```lean
fun round =>
  {
    toFun := fun p =>
      (p.1.1, (CodedSorting.Construction.TensorLiftProgram.bankView round) p.2.1,
        (CodedSorting.Construction.TensorLiftProgram.coordinateView round).symm (p.2.2, p.1.2)),
    invFun := fun q =>
      ((q.1, ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) q.2.2).2),
        (Equiv.symm (CodedSorting.Construction.TensorLiftProgram.bankView round)) q.2.1,
        ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) q.2.2).1),
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Coordinates](TensorLiftProgram.definitions.md#def-b93298813069e8c3)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.coordinateView](TensorLiftProgram.definitions.md#def-8f9978d9b5dd8eb5)
- [CodedSorting.Construction.TensorLiftProgram.bankView](TensorLiftProgram.definitions.md#def-da080c5a5be96a1b)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorLiftProgram.fiberDataEquiv._proof_12](TensorLiftProgram.definitions.md#def-f4ea7221de77dd22)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.TensorLiftProgram.fiberDataEquiv._proof_11](TensorLiftProgram.definitions.md#def-cf70e40d4798c372)

**基础库名称**

`Equiv.instFunLike`, `Equiv.mk`, `Equiv`, `Prod.mk`, `instOfNatNat`, `Prod.fst`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`, `DFunLike.coe`

<a id="def-0449174bfea7ca20"></a>
## `CodedSorting.Construction.TensorLiftProgram.fiberMap`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L202)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Pool ≃ CodedSorting.Construction.ThreeCopySchedule.Block →
    CodedSorting.Construction.ThreeCopySchedule.Block × CodedSorting.Construction.TensorLiftProgram.LocalReg →
      CodedSorting.Construction.TensorLiftProgram.GlobalReg
```

**定义**

```lean
fun round assignment x =>
  match x with
  | (block, Sum.inl data) =>
    Sum.inl (Sum.inl ((CodedSorting.Construction.TensorLiftProgram.fiberDataEquiv round) (block, data)))
  | (block, Sum.inr (Sum.inl helper)) => Sum.inl (Sum.inr (assignment.symm block, helper))
  | (block, Sum.inr (Sum.inr temporary)) => Sum.inr (round, block, temporary)
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.fiberMap.match_1](TensorLiftProgram.definitions.md#def-459d7da6aea4cc1f)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.HelperStream](TensorLiftProgram.definitions.md#def-de2624a13ceae317)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.ThreeCopySchedule.IndependentStream](TensorLiftProgram.definitions.md#def-59b37f8e42d90966)
- [CodedSorting.Construction.TensorLiftProgram.TemporaryStream](TensorLiftProgram.definitions.md#def-f6ff16bd9f6b23da)
- [CodedSorting.Construction.TensorLiftProgram.fiberDataEquiv](TensorLiftProgram.definitions.md#def-88546747689b44d4)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Prod.mk`, `instOfNatNat`, `Sum.inl`, `Sum.inr`, `Nat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-d4e1275444897c04"></a>
## `CodedSorting.Construction.TensorLiftProgram.fiberEmbedding`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L223)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round →
  CodedSorting.Construction.ThreeCopySchedule.Pool ≃ CodedSorting.Construction.ThreeCopySchedule.Block →
    CodedSorting.Construction.ThreeCopySchedule.Block →
      CodedSorting.Construction.TensorLiftProgram.LocalReg ↪ CodedSorting.Construction.TensorLiftProgram.GlobalReg
```

**定义**

```lean
fun round assignment block =>
  { toFun := fun r => CodedSorting.Construction.TensorLiftProgram.fiberMap round assignment (block, r), inj' := ⋯ }
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorLiftProgram.fiberMap](TensorLiftProgram.definitions.md#def-0449174bfea7ca20)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.TensorLiftProgram.fiberEmbedding._proof_13](TensorLiftProgram.definitions.md#def-2ef794056a06535b)

**基础库名称**

`Function.Embedding.mk`, `Equiv`, `Prod.mk`, `Function.Embedding`

<a id="def-4e558b6f3c1dd8ee"></a>
## `CodedSorting.Construction.TensorLiftProgram.roundProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLiftProgram.lean#L236)

**类型**

```lean
List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.LocalReg) →
  CodedSorting.Construction.TensorLiftProgram.Round →
    CodedSorting.Construction.ThreeCopySchedule.Pool ≃ CodedSorting.Construction.ThreeCopySchedule.Block →
      List (CodedSorting.CircuitProgram.XorGate CodedSorting.Construction.TensorLiftProgram.GlobalReg)
```

**定义**

```lean
fun word round assignment =>
  CodedSorting.CircuitProgram.partitionProgram
    (CodedSorting.Construction.TensorLiftProgram.fiberEmbedding round assignment) Finset.univ.toList word
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.fiberEmbedding](TensorLiftProgram.definitions.md#def-d4e1275444897c04)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.globalRegDecidableEq](TensorLiftProgram.definitions.md#def-15a1fd47fc7a9c44)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.CircuitProgram.XorGate](../Framework/CircuitProgram.definitions.md#def-53636b8dd9e7f863)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.CircuitProgram.partitionProgram](../Framework/CircuitProgram.definitions.md#def-7cacfe701ea2402a)

**基础库名称**

`instFintypeSum`, `Finset.univ`, `instDecidableEqProd`, `instDecidableEqFin`, `Sum`, `Equiv`, `Sum.instDecidableEq`, `instOfNatNat`, `Finset.toList`, `Fin.fintype`, `List`, `Nat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-f45cd2d506eb989d"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round.enumList`

读取 `CodedSorting.Construction.TensorLiftProgram.Round` 的 `enumList` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
List CodedSorting.Construction.TensorLiftProgram.Round
```

**定义**

```lean
[CodedSorting.Construction.TensorLiftProgram.Round.first, CodedSorting.Construction.TensorLiftProgram.Round.second,
  CodedSorting.Construction.TensorLiftProgram.Round.third]
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

**基础库名称**

`List.cons`, `List`, `List.nil`

<a id="def-87f11ac3a087ecd5"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round.enumList_nodup`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round.enumList.Nodup
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.enumList](TensorLiftProgram.definitions.md#def-f45cd2d506eb989d)

**基础库名称**

`List.Nodup`

<a id="def-b6860a0ad4158931"></a>
## `CodedSorting.Construction.TensorLiftProgram.Round.toCtorIdx`

读取 `CodedSorting.Construction.TensorLiftProgram.Round` 的 `toCtorIdx` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
CodedSorting.Construction.TensorLiftProgram.Round → ℕ
```

**定义**

```lean
fun x => CodedSorting.Construction.TensorLiftProgram.Round.casesOn x 0 1 2
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.casesOn](TensorLiftProgram.definitions.md#def-81b2db8aedad1210)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`

<a id="def-66fef3202e7d0017"></a>
## `CodedSorting.Construction.TensorLiftProgram.bankView._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
NeZero (1 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-5fea05fe0d35ce82"></a>
## `CodedSorting.Construction.TensorLiftProgram.coordinateView._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (x : CodedSorting.Construction.TensorLiftProgram.Coordinates),
  ((x.2.1, x.2.2, x.1).2.2, (x.2.1, x.2.2, x.1).1, (x.2.1, x.2.2, x.1).2.1) = x
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Coordinates](TensorLiftProgram.definitions.md#def-b93298813069e8c3)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Prod`, `Eq`, `Prod.snd`

<a id="def-a9c1fd887527f143"></a>
## `CodedSorting.Construction.TensorLiftProgram.coordinateView._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (x : CodedSorting.Construction.TensorLiftProgram.Coordinates),
  ((x.2.2, x.1, x.2.1).2.1, (x.2.2, x.1, x.2.1).2.2, (x.2.2, x.1, x.2.1).1) = x
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Coordinates](TensorLiftProgram.definitions.md#def-b93298813069e8c3)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Prod`, `Eq`, `Prod.snd`

<a id="def-6200ea44ceeec65f"></a>
## `CodedSorting.Construction.TensorLiftProgram.coordinateView.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
(motive : CodedSorting.Construction.TensorLiftProgram.Round → Sort u_1) →
  (x : CodedSorting.Construction.TensorLiftProgram.Round) →
    (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.first) →
      (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.second) →
        (Unit → motive CodedSorting.Construction.TensorLiftProgram.Round.third) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 => CodedSorting.Construction.TensorLiftProgram.Round.casesOn x (h_1 ()) (h_2 ()) (h_3 ())
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.casesOn](TensorLiftProgram.definitions.md#def-81b2db8aedad1210)
- [CodedSorting.Construction.TensorLiftProgram.Round.first](TensorLiftProgram.definitions.md#def-d720b8b1634db154)
- [CodedSorting.Construction.TensorLiftProgram.Round.third](TensorLiftProgram.definitions.md#def-317025dd1bb44223)
- [CodedSorting.Construction.TensorLiftProgram.Round.second](TensorLiftProgram.definitions.md#def-5e51e999de8f97b0)

**基础库名称**

`Unit.unit`, `Unit`

<a id="def-cf70e40d4798c372"></a>
## `CodedSorting.Construction.TensorLiftProgram.fiberDataEquiv._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (round : CodedSorting.Construction.TensorLiftProgram.Round)
  (x : CodedSorting.Construction.ThreeCopySchedule.Block × Fin 2 × CodedSorting.Construction.ThreeCopySchedule.Line),
  (((x.1.1, (CodedSorting.Construction.TensorLiftProgram.bankView round) x.2.1,
            (CodedSorting.Construction.TensorLiftProgram.coordinateView round).symm (x.2.2, x.1.2)).1,
        ((CodedSorting.Construction.TensorLiftProgram.coordinateView round)
            (x.1.1, (CodedSorting.Construction.TensorLiftProgram.bankView round) x.2.1,
                  (CodedSorting.Construction.TensorLiftProgram.coordinateView round).symm (x.2.2, x.1.2)).2.2).2),
      (Equiv.symm (CodedSorting.Construction.TensorLiftProgram.bankView round))
        (x.1.1, (CodedSorting.Construction.TensorLiftProgram.bankView round) x.2.1,
              (CodedSorting.Construction.TensorLiftProgram.coordinateView round).symm (x.2.2, x.1.2)).2.1,
      ((CodedSorting.Construction.TensorLiftProgram.coordinateView round)
          (x.1.1, (CodedSorting.Construction.TensorLiftProgram.bankView round) x.2.1,
                (CodedSorting.Construction.TensorLiftProgram.coordinateView round).symm (x.2.2, x.1.2)).2.2).1) =
    x
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Coordinates](TensorLiftProgram.definitions.md#def-b93298813069e8c3)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.coordinateView](TensorLiftProgram.definitions.md#def-8f9978d9b5dd8eb5)
- [CodedSorting.Construction.TensorLiftProgram.bankView](TensorLiftProgram.definitions.md#def-da080c5a5be96a1b)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Prod.mk`, `instOfNatNat`, `Prod.fst`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`

<a id="def-f4ea7221de77dd22"></a>
## `CodedSorting.Construction.TensorLiftProgram.fiberDataEquiv._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (round : CodedSorting.Construction.TensorLiftProgram.Round)
  (x : CodedSorting.Construction.ThreeCopySchedule.DataStream),
  (((x.1, ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) x.2.2).2),
            (Equiv.symm (CodedSorting.Construction.TensorLiftProgram.bankView round)) x.2.1,
            ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) x.2.2).1).1.1,
      (CodedSorting.Construction.TensorLiftProgram.bankView round)
        ((x.1, ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) x.2.2).2),
              (Equiv.symm (CodedSorting.Construction.TensorLiftProgram.bankView round)) x.2.1,
              ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) x.2.2).1).2.1,
      (CodedSorting.Construction.TensorLiftProgram.coordinateView round).symm
        (((x.1, ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) x.2.2).2),
                (Equiv.symm (CodedSorting.Construction.TensorLiftProgram.bankView round)) x.2.1,
                ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) x.2.2).1).2.2,
          ((x.1, ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) x.2.2).2),
                (Equiv.symm (CodedSorting.Construction.TensorLiftProgram.bankView round)) x.2.1,
                ((CodedSorting.Construction.TensorLiftProgram.coordinateView round) x.2.2).1).1.2)) =
    x
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Coordinates](TensorLiftProgram.definitions.md#def-b93298813069e8c3)
- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.coordinateView](TensorLiftProgram.definitions.md#def-8f9978d9b5dd8eb5)
- [CodedSorting.Construction.TensorLiftProgram.bankView](TensorLiftProgram.definitions.md#def-da080c5a5be96a1b)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.ThreeCopySchedule.DataStream](TensorLiftProgram.definitions.md#def-709e995148360e96)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Prod.mk`, `instOfNatNat`, `Prod.fst`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`

<a id="def-2ef794056a06535b"></a>
## `CodedSorting.Construction.TensorLiftProgram.fiberEmbedding._proof_13`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (round : CodedSorting.Construction.TensorLiftProgram.Round)
  (assignment : CodedSorting.Construction.ThreeCopySchedule.Pool ≃ CodedSorting.Construction.ThreeCopySchedule.Block)
  (block : CodedSorting.Construction.ThreeCopySchedule.Block)
  ⦃r s : CodedSorting.Construction.TensorLiftProgram.LocalReg⦄,
  CodedSorting.Construction.TensorLiftProgram.fiberMap round assignment (block, r) =
      CodedSorting.Construction.TensorLiftProgram.fiberMap round assignment (block, s) →
    (block, r).2 = (block, s).2
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorLiftProgram.fiberMap](TensorLiftProgram.definitions.md#def-0449174bfea7ca20)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.TensorLiftProgram.GlobalReg](TensorLiftProgram.definitions.md#def-e76d203076293c86)
- [CodedSorting.Construction.ThreeCopySchedule.Pool](TensorLiftProgram.definitions.md#def-7c00b43778d69908)

**基础库名称**

`Equiv`, `Prod.mk`, `Eq`, `Prod.snd`

<a id="def-459d7da6aea4cc1f"></a>
## `CodedSorting.Construction.TensorLiftProgram.fiberMap.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
(motive :
    CodedSorting.Construction.ThreeCopySchedule.Block × CodedSorting.Construction.TensorLiftProgram.LocalReg →
      Sort u_1) →
  (x : CodedSorting.Construction.ThreeCopySchedule.Block × CodedSorting.Construction.TensorLiftProgram.LocalReg) →
    ((block : CodedSorting.Construction.ThreeCopySchedule.Block) →
        (data : Fin 2 × CodedSorting.Construction.ThreeCopySchedule.Line) → motive (block, Sum.inl data)) →
      ((block : CodedSorting.Construction.ThreeCopySchedule.Block) →
          (helper : Fin 439) → motive (block, Sum.inr (Sum.inl helper))) →
        ((block : CodedSorting.Construction.ThreeCopySchedule.Block) →
            (temporary : Fin 9) → motive (block, Sum.inr (Sum.inr temporary))) →
          motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 =>
  Prod.casesOn x fun fst snd =>
    Sum.casesOn snd (fun val => h_1 fst val) fun val => Sum.casesOn val (fun val => h_2 fst val) fun val => h_3 fst val
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Block](TensorLiftProgram.definitions.md#def-cb083799392a946e)
- [CodedSorting.Construction.TensorLiftProgram.LocalReg](TensorLiftProgram.definitions.md#def-457787d4c5210d35)
- [CodedSorting.Construction.ThreeCopySchedule.Line](TensorLiftProgram.definitions.md#def-0d839a35fa97d067)

**基础库名称**

`Sum.casesOn`, `Sum`, `Prod.mk`, `instOfNatNat`, `Sum.inl`, `Sum.inr`, `Nat`, `Prod`, `Prod.casesOn`, `OfNat.ofNat`, `Fin`

<a id="def-3fe584ef1befc79d"></a>
## `CodedSorting.Construction.TensorLiftProgram.instDecidableEqRound._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (x y : CodedSorting.Construction.TensorLiftProgram.Round), x.toCtorIdx = y.toCtorIdx → x = y
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.toCtorIdx](TensorLiftProgram.definitions.md#def-b6860a0ad4158931)

**基础库名称**

`Nat`, `Eq`

<a id="def-5bf2c617c40e6a13"></a>
## `CodedSorting.Construction.TensorLiftProgram.instDecidableEqRound._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (x y : CodedSorting.Construction.TensorLiftProgram.Round), ¬x.toCtorIdx = y.toCtorIdx → x = y → False
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.toCtorIdx](TensorLiftProgram.definitions.md#def-b6860a0ad4158931)

**基础库名称**

`False`, `Nat`, `Eq`, `Not`

<a id="def-44508ba7f93ef650"></a>
## `CodedSorting.Construction.TensorLiftProgram.instFintypeRound._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (x : CodedSorting.Construction.TensorLiftProgram.Round),
  x ∈
    { val := ↑CodedSorting.Construction.TensorLiftProgram.Round.enumList,
      nodup := CodedSorting.Construction.TensorLiftProgram.Round.enumList_nodup }
```

**继续展开**

- [CodedSorting.Construction.TensorLiftProgram.Round](TensorLiftProgram.definitions.md#def-4ed3891a984aeec8)
- [CodedSorting.Construction.TensorLiftProgram.Round.enumList](TensorLiftProgram.definitions.md#def-f45cd2d506eb989d)
- [CodedSorting.Construction.TensorLiftProgram.Round.enumList_nodup](TensorLiftProgram.definitions.md#def-87f11ac3a087ecd5)

**基础库名称**

`Finset`, `Membership.mem`, `Finset.instMembership`, `Multiset.ofList`, `Finset.mk`

<a id="def-b9404bf0d393954f"></a>
## `CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (i : CodedSorting.Construction.ThreeCopySchedule.Copy), (↑i + 1) % 3 < 3
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Nat.instMod`, `instHMod`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-75a11ae27ce5cf0e"></a>
## `CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
∀ (i : CodedSorting.Construction.ThreeCopySchedule.Copy), (↑i + 2) % 3 < 3
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)

**基础库名称**

`Nat.instMod`, `instHMod`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-80236977868d91cf"></a>
## `CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
Function.LeftInverse (fun i => ⟨(↑i + 2) % 3, ⋯⟩) fun i => ⟨(↑i + 1) % 3, ⋯⟩
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_2](TensorLiftProgram.definitions.md#def-75a11ae27ce5cf0e)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_1](TensorLiftProgram.definitions.md#def-b9404bf0d393954f)

**基础库名称**

`Function.LeftInverse`, `Fin.mk`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-ff30273516264483"></a>
## `CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](TensorLiftProgram.lean)

**类型**

```lean
Function.RightInverse (fun i => ⟨(↑i + 2) % 3, ⋯⟩) fun i => ⟨(↑i + 1) % 3, ⋯⟩
```

**继续展开**

- [CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_2](TensorLiftProgram.definitions.md#def-75a11ae27ce5cf0e)
- [CodedSorting.Construction.ThreeCopySchedule.Copy](TensorLiftProgram.definitions.md#def-1264fff0ec0bb152)
- [CodedSorting.Construction.ThreeCopySchedule.nextCopy._proof_1](TensorLiftProgram.definitions.md#def-b9404bf0d393954f)

**基础库名称**

`Fin.mk`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `Function.RightInverse`, `instAddNat`, `OfNat.ofNat`
