# GatherController 的定义

[源码](GatherController.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-3ed09f82a7a70d4e"></a>
## `CodedSorting.CommonMSDGatherController.Tag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherController.lean#L17)

**类型**

```lean
ℕ → ℕ → Type
```

**定义**

```lean
fun F C => Fin (F + 1) × Bool × Fin (C + 1) × Fin (C + 1) × Fin (C + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Bool`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-8dfe78b0999fb1f6"></a>
## `CodedSorting.CommonMSDGatherController.ready`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherController.lean#L22)

**类型**

```lean
{F C : ℕ} → Fin (F + 1) → Fin (C + 1) → CodedSorting.CommonMSDGatherController.Tag F C
```

**定义**

```lean
fun {F C} j D => (j, false, D, 0, 0)
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.ready._proof_1](GatherController.definitions.md#def-44cbdf3d2df89dbe)
- [CodedSorting.CommonMSDGatherController.Tag](GatherController.definitions.md#def-3ed09f82a7a70d4e)

**基础库名称**

`Fin.instOfNat`, `Prod.mk`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Bool`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Bool.false`, `Fin`

<a id="def-03b806402001485c"></a>
## `CodedSorting.CommonMSDGatherController.copying`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherController.lean#L24)

**类型**

```lean
{F C : ℕ} → Fin F → Fin (C + 1) → Fin (C + 1) → Fin (C + 1) → CodedSorting.CommonMSDGatherController.Tag F C
```

**定义**

```lean
fun {F C} j D O N => (j.castSucc, true, D, O, N)
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Tag](GatherController.definitions.md#def-3ed09f82a7a70d4e)

**基础库名称**

`Prod.mk`, `instOfNatNat`, `Bool.true`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Bool`, `instAddNat`, `Fin.castSucc`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-35f7e01806ec7cb9"></a>
## `CodedSorting.CommonMSDGatherController.bounded`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherController.lean#L26)

**类型**

```lean
(C : ℕ) → ℕ → Fin (C + 1)
```

**定义**

```lean
fun C n => ⟨n % (C + 1), ⋯⟩
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.bounded._proof_3](GatherController.definitions.md#def-0e4651da0c43eaa7)

**基础库名称**

`Fin.mk`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-047c526530ef9455"></a>
## `CodedSorting.CommonMSDGatherController.Layout`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](GatherController.lean#L28)

**类型**

```lean
ℕ → Type
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout.mk](GatherController.definitions.md#def-13df2c0a5ba23091)

**基础库名称**

`Nat`

<a id="def-13df2c0a5ba23091"></a>
## `CodedSorting.CommonMSDGatherController.Layout.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](GatherController.lean#L28)

**类型**

```lean
{F : ℕ} → (Fin F → ℕ) → (Fin F → ℕ) → (Fin F → ℕ) → (Fin F → ℕ) → ℕ → CodedSorting.CommonMSDGatherController.Layout F
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout](GatherController.definitions.md#def-047c526530ef9455)

**基础库名称**

`Nat`, `Fin`

<a id="def-69fc94777401f22e"></a>
## `CodedSorting.CommonMSDGatherController.Layout.source`

读取 `CodedSorting.CommonMSDGatherController.Layout` 的 `source` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](GatherController.lean#L29)

**类型**

```lean
{F : ℕ} → CodedSorting.CommonMSDGatherController.Layout F → Fin F → ℕ
```

**定义**

```lean
fun F self => self.1
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout](GatherController.definitions.md#def-047c526530ef9455)

**基础库名称**

`Nat`, `Fin`

<a id="def-e2aa55840ed1e326"></a>
## `CodedSorting.CommonMSDGatherController.Layout.offset`

读取 `CodedSorting.CommonMSDGatherController.Layout` 的 `offset` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](GatherController.lean#L30)

**类型**

```lean
{F : ℕ} → CodedSorting.CommonMSDGatherController.Layout F → Fin F → ℕ
```

**定义**

```lean
fun F self => self.2
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout](GatherController.definitions.md#def-047c526530ef9455)

**基础库名称**

`Nat`, `Fin`

<a id="def-f6dc9542efa6ea2c"></a>
## `CodedSorting.CommonMSDGatherController.Layout.directory`

读取 `CodedSorting.CommonMSDGatherController.Layout` 的 `directory` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](GatherController.lean#L31)

**类型**

```lean
{F : ℕ} → CodedSorting.CommonMSDGatherController.Layout F → Fin F → ℕ
```

**定义**

```lean
fun F self => self.3
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout](GatherController.definitions.md#def-047c526530ef9455)

**基础库名称**

`Nat`, `Fin`

<a id="def-a2018e036d6ee1c1"></a>
## `CodedSorting.CommonMSDGatherController.Layout.entry`

读取 `CodedSorting.CommonMSDGatherController.Layout` 的 `entry` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](GatherController.lean#L32)

**类型**

```lean
{F : ℕ} → CodedSorting.CommonMSDGatherController.Layout F → Fin F → ℕ
```

**定义**

```lean
fun F self => self.4
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout](GatherController.definitions.md#def-047c526530ef9455)

**基础库名称**

`Nat`, `Fin`

<a id="def-7d32e25f1e7f3cdb"></a>
## `CodedSorting.CommonMSDGatherController.Layout.target`

读取 `CodedSorting.CommonMSDGatherController.Layout` 的 `target` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](GatherController.lean#L33)

**类型**

```lean
{F : ℕ} → CodedSorting.CommonMSDGatherController.Layout F → ℕ
```

**定义**

```lean
fun F self => self.5
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout](GatherController.definitions.md#def-047c526530ef9455)

**基础库名称**

`Nat`

<a id="def-9378534b7df0ea1d"></a>
## `CodedSorting.CommonMSDGatherController.body`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherController.lean#L35)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  Fin q.inventory.readers →
    {F C : ℕ} →
      CodedSorting.CommonMSDGatherController.Layout F →
        CodedSorting.CommonMSDGatherController.Tag F C → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q reader {F C} layout t =>
  if h : ↑t.1 < F then
    if t.2.1 = true then
      CodedSorting.CommonIntervalCopy.code q reader (↑t.2.2.2.1) (↑t.2.2.1) (↑t.2.2.2.2) (layout.source ⟨↑t.1, h⟩)
        layout.target
    else CodedSorting.CommonMSDDirectoryRead.code q (layout.directory ⟨↑t.1, h⟩) (layout.entry ⟨↑t.1, h⟩)
  else []
```

**继续展开**

- [CodedSorting.CommonIntervalCopy.code](../../../Shared/Memory/IntervalCopyBounds.definitions.md#def-873421a048c5b5e6)
- [CodedSorting.CommonMSDGatherController.Layout](GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonMSDGatherController.Layout.directory](GatherController.definitions.md#def-f6dc9542efa6ea2c)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonMSDGatherController.Layout.entry](GatherController.definitions.md#def-a2018e036d6ee1c1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDGatherController.Layout.source](GatherController.definitions.md#def-69fc94777401f22e)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDGatherController.Layout.target](GatherController.definitions.md#def-7d32e25f1e7f3cdb)
- [CodedSorting.CommonMSDGatherController.Tag](GatherController.definitions.md#def-3ed09f82a7a70d4e)
- [CodedSorting.CommonMSDDirectoryRead.code](Directory.definitions.md#def-7b106aceec8b4ea3)

**基础库名称**

`Fin.mk`, `instDecidableEqBool`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `dite`, `Bool.true`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instAddNat`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `Not`, `List.nil`, `ite`

<a id="def-c4eaa7a54c94828c"></a>
## `CodedSorting.CommonMSDGatherController.nextTag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](GatherController.lean#L51)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {F C : ℕ} →
    CodedSorting.CommonMSDGatherController.Layout F →
      CodedSorting.CommonMSDGatherController.Tag F C →
        CodedSorting.CommonLeafProgram.RAM q → CodedSorting.CommonMSDGatherController.Tag F C
```

**定义**

```lean
fun q {F C} layout t ram =>
  if h : ↑t.1 < F then
    if t.2.1 = true then
      CodedSorting.CommonMSDGatherController.ready ⟨↑t.1 + 1, ⋯⟩
        (CodedSorting.CommonMSDGatherController.bounded C (↑t.2.2.1 + ↑t.2.2.2.2))
    else
      CodedSorting.CommonMSDGatherController.copying ⟨↑t.1, h⟩ t.2.2.1
        (CodedSorting.CommonMSDGatherController.bounded C
          (layout.offset ⟨↑t.1, h⟩ +
            3 *
              CodedSorting.CommonMSDDirectoryRead.field q (layout.entry ⟨↑t.1, h⟩) 0
                (CodedSorting.CommonSortingNormalization.unpack ram)))
        (CodedSorting.CommonMSDGatherController.bounded C
          (3 *
            CodedSorting.CommonMSDDirectoryRead.field q (layout.entry ⟨↑t.1, h⟩) 1
              (CodedSorting.CommonSortingNormalization.unpack ram)))
  else t
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.CommonMSDGatherController.Layout](GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonMSDGatherController.copying](GatherController.definitions.md#def-03b806402001485c)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonMSDGatherController.Layout.entry](GatherController.definitions.md#def-a2018e036d6ee1c1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDGatherController.Tag](GatherController.definitions.md#def-3ed09f82a7a70d4e)
- [CodedSorting.CommonMSDGatherController.nextTag._proof_5](GatherController.definitions.md#def-8a7a1196a3ed4687)
- [CodedSorting.CommonMSDGatherController.bounded](GatherController.definitions.md#def-35f7e01806ec7cb9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMSDGatherController.Layout.offset](GatherController.definitions.md#def-e2aa55840ed1e326)
- [CodedSorting.CommonMSDGatherController.ready](GatherController.definitions.md#def-8dfe78b0999fb1f6)
- [CodedSorting.CommonMSDGatherController.nextTag._proof_6](GatherController.definitions.md#def-62332480bd0f2d1d)
- [CodedSorting.CommonMSDDirectoryRead.field](Directory.definitions.md#def-7259c12452aec226)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`HMul.hMul`, `Fin.mk`, `Fin.instOfNat`, `instDecidableEqBool`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `dite`, `Bool.true`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instAddNat`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `Not`, `instHMul`, `ite`

<a id="def-0e4651da0c43eaa7"></a>
## `CodedSorting.CommonMSDGatherController.bounded._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GatherController.lean)

**类型**

```lean
∀ (C n : ℕ), n % (C + 1) < C + 1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMod`, `instHMod`, `instOfNatNat`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-8a7a1196a3ed4687"></a>
## `CodedSorting.CommonMSDGatherController.nextTag._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GatherController.lean)

**类型**

```lean
∀ {F C : ℕ} (t : CodedSorting.CommonMSDGatherController.Tag F C), ↑t.1 < F → ↑t.1 + 1 < F + 1
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Tag](GatherController.definitions.md#def-3ed09f82a7a70d4e)

**基础库名称**

`instOfNatNat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Bool`, `instAddNat`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-62332480bd0f2d1d"></a>
## `CodedSorting.CommonMSDGatherController.nextTag._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GatherController.lean)

**类型**

```lean
NeZero (1 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-44cbdf3d2df89dbe"></a>
## `CodedSorting.CommonMSDGatherController.ready._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](GatherController.lean)

**类型**

```lean
∀ {C : ℕ}, NeZero (C + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`
