# LocalSortingCost 的定义

[源码](LocalSortingCost.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-05df3efddf58db36"></a>
## `CodedSorting.LocalSortingCost.blockCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LocalSortingCost.lean#L145)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun B n => (n + B - 1) / B
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HSub.hSub`, `HDiv.hDiv`, `instSubNat`, `instOfNatNat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`
