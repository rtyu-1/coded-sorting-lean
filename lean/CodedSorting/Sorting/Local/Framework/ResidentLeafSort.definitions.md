# ResidentLeafSort 的定义

[源码](ResidentLeafSort.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-d2b11bb114609f13"></a>
## `CodedSorting.ResidentLeafSort.recordOrder`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafSort.lean#L14)

**类型**

```lean
(w : ℕ) → LinearOrder (CodedSorting.KeyRecordWords.Record w)
```

**定义**

```lean
fun w => LinearOrder.lift' CodedSorting.KeyRecordWords.abstract ⋯
```

**继续展开**

- [CodedSorting.KeyRecordWords.abstract](../../../Shared/Records/KeyRecordWords.definitions.md#def-6f337235d082695a)
- [CodedSorting.KeyRecordWords.abstract_injective](../../../Shared/Records/KeyRecordWords.definitions.md#def-28947ec3b2347acc)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-da9a81f7a1b37843)

**基础库名称**

`Lex`, `LinearOrder`, `LinearOrder.lift'`, `Prod.Lex.instLinearOrder`, `WithBot.linearOrder`, `Nat`, `WithTop.linearOrder`, `Prod`, `WithTop`, `Nat.instLinearOrder`

<a id="def-2fda3d29689ad340"></a>
## `CodedSorting.ResidentLeafSort.residentWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafSort.lean#L19)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun cap d => d + cap * 3
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-351ba66701581e98"></a>
## `CodedSorting.ResidentLeafSort.RAM`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafSort.lean#L21)

**类型**

```lean
ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun cap d w => CodedSorting.WordControl.Words (CodedSorting.ResidentLeafSort.residentWords cap d) w
```

**继续展开**

- [CodedSorting.ResidentLeafSort.residentWords](ResidentLeafSort.definitions.md#def-2fda3d29689ad340)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-8e5c767d09c080c6"></a>
## `CodedSorting.ResidentLeafSort.header`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafSort.lean#L23)

**类型**

```lean
{cap d w : ℕ} → CodedSorting.ResidentLeafSort.RAM cap d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun {cap d w} ram i => ram (Fin.castAdd (cap * 3) i)
```

**继续展开**

- [CodedSorting.ResidentLeafSort.RAM](ResidentLeafSort.definitions.md#def-351ba66701581e98)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `Fin.castAdd`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-a9cafcc8feea7341"></a>
## `CodedSorting.ResidentLeafSort.recordAt`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ResidentLeafSort.lean#L33)

**类型**

```lean
{cap d w : ℕ} → CodedSorting.ResidentLeafSort.RAM cap d w → Fin cap → CodedSorting.KeyRecordWords.Record w
```

**定义**

```lean
fun {cap d w} ram i => CodedSorting.KeyRecordWords.decode fun j => ram (Fin.natAdd d (finProdFinEquiv (i, j)))
```

**继续展开**

- [CodedSorting.ResidentLeafSort.RAM](ResidentLeafSort.definitions.md#def-351ba66701581e98)
- [CodedSorting.KeyRecordWords.decode](../../../Shared/Records/KeyRecordWords.definitions.md#def-3f469f7bb48913b3)
- [CodedSorting.KeyRecordWords.Record](../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)

**基础库名称**

`Equiv.instFunLike`, `Fin.natAdd`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `instOfNatNat`, `Nat`, `finProdFinEquiv`, `Prod`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`
