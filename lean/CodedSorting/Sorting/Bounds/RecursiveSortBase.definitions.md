# RecursiveSortBase 的定义

[源码](RecursiveSortBase.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-d78b1bf2145627c4"></a>
## `CodedSorting.RecursiveColumnsort.CallTree`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](RecursiveSortBase.lean#L10)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree.node](RecursiveSortBase.definitions.md#def-c9b7e3677f9f6480)
- [CodedSorting.RecursiveColumnsort.CallTree.leaf](RecursiveSortBase.definitions.md#def-f7c82018bada47e5)

<a id="def-f7c82018bada47e5"></a>
## `CodedSorting.RecursiveColumnsort.CallTree.leaf`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](RecursiveSortBase.lean#L13)

**类型**

```lean
ℕ → CodedSorting.RecursiveColumnsort.CallTree
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)

**基础库名称**

`Nat`

<a id="def-c9b7e3677f9f6480"></a>
## `CodedSorting.RecursiveColumnsort.CallTree.node`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](RecursiveSortBase.lean#L14)

**类型**

```lean
ℕ →
  ℕ →
    List CodedSorting.RecursiveColumnsort.CallTree →
      List CodedSorting.RecursiveColumnsort.CallTree →
        List CodedSorting.RecursiveColumnsort.CallTree →
          List CodedSorting.RecursiveColumnsort.CallTree → CodedSorting.RecursiveColumnsort.CallTree
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)

**基础库名称**

`List`, `Nat`

<a id="def-b896814d19d1eb69"></a>
## `CodedSorting.RecursiveColumnsort.Run`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](RecursiveSortBase.lean#L18)

**类型**

```lean
Type u_1 → ℕ → Type u_1
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.Run.mk](RecursiveSortBase.definitions.md#def-b4442984defa943d)

**基础库名称**

`Nat`

<a id="def-b4442984defa943d"></a>
## `CodedSorting.RecursiveColumnsort.Run.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](RecursiveSortBase.lean#L19)

**类型**

```lean
{α : Type u_1} →
  {n : ℕ} → (Fin n → α) → CodedSorting.RecursiveColumnsort.CallTree → CodedSorting.RecursiveColumnsort.Run α n
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)
- [CodedSorting.RecursiveColumnsort.Run](RecursiveSortBase.definitions.md#def-b896814d19d1eb69)

**基础库名称**

`Nat`, `Fin`

<a id="def-f8d4919f40a96246"></a>
## `CodedSorting.RecursiveColumnsort.Run.output`

读取 `CodedSorting.RecursiveColumnsort.Run` 的 `output` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](RecursiveSortBase.lean#L20)

**类型**

```lean
{α : Type u_1} → {n : ℕ} → CodedSorting.RecursiveColumnsort.Run α n → Fin n → α
```

**定义**

```lean
fun α n self => self.1
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.Run](RecursiveSortBase.definitions.md#def-b896814d19d1eb69)

**基础库名称**

`Nat`, `Fin`

<a id="def-481ca50755f2ed2e"></a>
## `CodedSorting.RecursiveColumnsort.Run.trace`

读取 `CodedSorting.RecursiveColumnsort.Run` 的 `trace` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](RecursiveSortBase.lean#L21)

**类型**

```lean
{α : Type u_1} → {n : ℕ} → CodedSorting.RecursiveColumnsort.Run α n → CodedSorting.RecursiveColumnsort.CallTree
```

**定义**

```lean
fun α n self => self.2
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.CallTree](RecursiveSortBase.definitions.md#def-d78b1bf2145627c4)
- [CodedSorting.RecursiveColumnsort.Run](RecursiveSortBase.definitions.md#def-b896814d19d1eb69)

**基础库名称**

`Nat`

<a id="def-e90528ad227dadd9"></a>
## `CodedSorting.RecursiveColumnsort.Sorter`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecursiveSortBase.lean#L23)

**类型**

```lean
Type u_1 → Type u_1
```

**定义**

```lean
fun α => (n : ℕ) → (Fin n → α) → CodedSorting.RecursiveColumnsort.Run α n
```

**继续展开**

- [CodedSorting.RecursiveColumnsort.Run](RecursiveSortBase.definitions.md#def-b896814d19d1eb69)

**基础库名称**

`Nat`, `Fin`

<a id="def-fd3cc139d7f2794c"></a>
## `CodedSorting.RecursiveColumnsort.pad`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecursiveSortBase.lean#L27)

**类型**

```lean
{α : Type u_1} → [inst : LinearOrder α] → [inst : OrderTop α] → {n N : ℕ} → (Fin n → α) → Fin N → α
```

**定义**

```lean
fun {α} [LinearOrder α] [OrderTop α] {n N} f i => if hi : ↑i < n then f ⟨↑i, hi⟩ else ⊤
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`LinearOrder`, `PartialOrder.toPreorder`, `Preorder.toLE`, `SemilatticeInf.toPartialOrder`, `DistribLattice.toLattice`, `Fin.mk`, `Fin.val`, `OrderTop`, `dite`, `OrderTop.toTop`, `Nat`, `LT.lt`, `Nat.decLt`, `instLTNat`, `Top.top`, `Fin`, `Not`, `instDistribLatticeOfLinearOrder`, `Lattice.toSemilatticeInf`

<a id="def-2695ace6fd03771d"></a>
## `CodedSorting.RecursiveColumnsort.trim`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](RecursiveSortBase.lean#L85)

**类型**

```lean
{α : Type u_1} → {n N : ℕ} → n ≤ N → (Fin N → α) → Fin n → α
```

**定义**

```lean
fun {α} {n N} h f i => f (Fin.castLE h i)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Fin.castLE`, `LE.le`, `instLENat`, `Nat`, `Fin`
