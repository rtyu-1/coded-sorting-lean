# AllocatedCapacity 的定义

[源码](AllocatedCapacity.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-757bca28dc1a3373"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.coefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllocatedCapacity.lean#L15)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun C κ => (κ + 1) * (C + 16) + 5
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-579c2468933b9e00"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.threshold`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllocatedCapacity.lean#L17)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun C D κ => CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.coefficient C κ * 2 ^ (D + 1)
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.coefficient](AllocatedCapacity.definitions.md#def-757bca28dc1a3373)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-687c304c9f79f086"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.workspaceCoefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllocatedCapacity.lean#L121)

**类型**

```lean
ℕ
```

**定义**

```lean
CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.coefficient
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.coefficient](../ConcreteWorkspace.definitions.md#def-9ac8e29c0a861d94)

**基础库名称**

`Nat`

<a id="def-3f47c9d86edca801"></a>
## `CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.diskThreshold`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](AllocatedCapacity.lean#L123)

**类型**

```lean
ℕ → ℕ
```

**定义**

```lean
fun κ =>
  CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.threshold
    CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.workspaceCoefficient 5 κ
```

**继续展开**

- [CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.threshold](AllocatedCapacity.definitions.md#def-579c2468933b9e00)
- [CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.workspaceCoefficient](AllocatedCapacity.definitions.md#def-687c304c9f79f086)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`
