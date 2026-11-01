# Definitions 的定义

[源码](Definitions.lean) · [主定理导读](../../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-598ce34cf2b20028"></a>
## `CodedSorting.CommonWordMSD.key`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L13)

**类型**

```lean
{w : ℕ} → CodedSorting.KeyRecordWords.Record w → ℕ
```

**定义**

```lean
fun {w} x =>
  match x with
  | CodedSorting.KeyRecordWords.Record.bottom => 0
  | CodedSorting.KeyRecordWords.Record.data k payload => ↑k
  | CodedSorting.KeyRecordWords.Record.top => 2 ^ w
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record](../../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonWordMSD.key.match_1](Definitions.definitions.md#def-8ad91d0a433a27d0)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `Fin.val`, `Unit`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-ded94dd20cf6d84b"></a>
## `CodedSorting.CommonWordMSD.localSort`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L47)

**类型**

```lean
{w : ℕ} → List (CodedSorting.KeyRecordWords.Record w) → List (CodedSorting.KeyRecordWords.Record w)
```

**定义**

```lean
fun {w} xs => List.ofFn (CodedSorting.Columnsort.sortColumn xs.get)
```

**继续展开**

- [CodedSorting.KeyRecordWords.Record](../../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.Columnsort.sortColumn](../../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.ResidentLeafSort.recordOrder](../../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)

**基础库名称**

`List.get`, `List.ofFn`, `List`, `Nat`, `List.length`

<a id="def-8ad91d0a433a27d0"></a>
## `CodedSorting.CommonWordMSD.key.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Definitions.lean)

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

- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.KeyRecordWords.Record.casesOn](../../../../Shared/Records/KeyRecordWords.definitions.md#def-ad7ef446def9fade)
- [CodedSorting.KeyRecordWords.Record.data](../../../../Shared/Records/KeyRecordWords.definitions.md#def-4ed08201e01cac90)
- [CodedSorting.KeyRecordWords.Record](../../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.KeyRecordWords.Record.bottom](../../../../Shared/Records/KeyRecordWords.definitions.md#def-8224b0db2863a7d3)
- [CodedSorting.KeyRecordWords.Record.top](../../../../Shared/Records/KeyRecordWords.definitions.md#def-dfff22d085934d4b)

**基础库名称**

`Unit.unit`, `Unit`, `Nat`
