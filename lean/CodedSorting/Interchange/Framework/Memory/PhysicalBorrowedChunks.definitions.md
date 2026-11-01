# PhysicalBorrowedChunks 的定义

[源码](PhysicalBorrowedChunks.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-d759513570ef8f00"></a>
## `CodedSorting.PhysicalPrefixPadding.volume_mono`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalBorrowedChunks.lean#L226)

**类型**

```lean
∀ {P P' Q G S : ℕ}, P ≤ P' → CodedSorting.BinaryPadding.Volume P Q G S ≤ CodedSorting.BinaryPadding.Volume P' Q G S
```

**继续展开**

- [CodedSorting.BinaryPadding.Volume](../Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)

**基础库名称**

`LE.le`, `instLENat`, `Nat`
