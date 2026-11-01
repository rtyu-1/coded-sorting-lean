# Address 的定义

[源码](Address.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-dfc18ad24150a538"></a>
## `CodedSorting.Address.FullAddress`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Address.lean#L18)

**类型**

```lean
Type u_1 → Type u_2 → Type u_3 → Type u_4 → Type (max (max (max u_1 u_2) u_3) u_4)
```

**继续展开**

- [CodedSorting.Address.FullAddress.mk](Address.definitions.md#def-fcedbd9acc430fdc)

<a id="def-fcedbd9acc430fdc"></a>
## `CodedSorting.Address.FullAddress.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Address.lean#L20)

**类型**

```lean
{Prefix : Type u_1} →
  {Field : Type u_2} →
    {Gap : Type u_3} →
      {Suffix : Type u_4} →
        Prefix → Field → Gap → Field → Suffix → CodedSorting.Address.FullAddress Prefix Field Gap Suffix
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)

<a id="def-f205e926ba038664"></a>
## `CodedSorting.Address.FullAddress.prefixCoord`

读取 `CodedSorting.Address.FullAddress` 的 `prefixCoord` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Address.lean#L21)

**类型**

```lean
{Prefix : Type u_1} →
  {Field : Type u_2} →
    {Gap : Type u_3} → {Suffix : Type u_4} → CodedSorting.Address.FullAddress Prefix Field Gap Suffix → Prefix
```

**定义**

```lean
fun Prefix Field Gap Suffix self => self.1
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)

<a id="def-d2c6338ca38bb153"></a>
## `CodedSorting.Address.FullAddress.high`

读取 `CodedSorting.Address.FullAddress` 的 `high` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Address.lean#L22)

**类型**

```lean
{Prefix : Type u_1} →
  {Field : Type u_2} →
    {Gap : Type u_3} → {Suffix : Type u_4} → CodedSorting.Address.FullAddress Prefix Field Gap Suffix → Field
```

**定义**

```lean
fun Prefix Field Gap Suffix self => self.2
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)

<a id="def-1ec749640a60fa5b"></a>
## `CodedSorting.Address.FullAddress.gap`

读取 `CodedSorting.Address.FullAddress` 的 `gap` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Address.lean#L23)

**类型**

```lean
{Prefix : Type u_1} →
  {Field : Type u_2} →
    {Gap : Type u_3} → {Suffix : Type u_4} → CodedSorting.Address.FullAddress Prefix Field Gap Suffix → Gap
```

**定义**

```lean
fun Prefix Field Gap Suffix self => self.3
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)

<a id="def-5d73b599bd447e5e"></a>
## `CodedSorting.Address.FullAddress.low`

读取 `CodedSorting.Address.FullAddress` 的 `low` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Address.lean#L24)

**类型**

```lean
{Prefix : Type u_1} →
  {Field : Type u_2} →
    {Gap : Type u_3} → {Suffix : Type u_4} → CodedSorting.Address.FullAddress Prefix Field Gap Suffix → Field
```

**定义**

```lean
fun Prefix Field Gap Suffix self => self.4
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)

<a id="def-106f0219962d2f0f"></a>
## `CodedSorting.Address.FullAddress.suffix`

读取 `CodedSorting.Address.FullAddress` 的 `suffix` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Address.lean#L25)

**类型**

```lean
{Prefix : Type u_1} →
  {Field : Type u_2} →
    {Gap : Type u_3} → {Suffix : Type u_4} → CodedSorting.Address.FullAddress Prefix Field Gap Suffix → Suffix
```

**定义**

```lean
fun Prefix Field Gap Suffix self => self.5
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)

<a id="def-840ffce97b2075fa"></a>
## `CodedSorting.Address.exchange`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Address.lean#L30)

**类型**

```lean
{Prefix : Type u_1} →
  {Field : Type u_2} →
    {Gap : Type u_3} →
      {Suffix : Type u_4} →
        CodedSorting.Address.FullAddress Prefix Field Gap Suffix →
          CodedSorting.Address.FullAddress Prefix Field Gap Suffix
```

**定义**

```lean
fun {Prefix} {Field} {Gap} {Suffix} a =>
  { prefixCoord := a.prefixCoord, high := a.low, gap := a.gap, low := a.high, suffix := a.suffix }
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.FullAddress.low](Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.Address.FullAddress.high](Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.Address.FullAddress.gap](Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](Address.definitions.md#def-106f0219962d2f0f)

<a id="def-dbdfb64823fe33e6"></a>
## `CodedSorting.Address.exchange_twice`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Address.lean#L35)

**类型**

```lean
∀ {Prefix : Type u_1} {Field : Type u_2} {Gap : Type u_3} {Suffix : Type u_4}
  (a : CodedSorting.Address.FullAddress Prefix Field Gap Suffix),
  CodedSorting.Address.exchange (CodedSorting.Address.exchange a) = a
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.exchange](Address.definitions.md#def-840ffce97b2075fa)

**基础库名称**

`Eq`

<a id="def-fad92f68940cdb8b"></a>
## `CodedSorting.Address.exchangeEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Address.lean#L50)

**类型**

```lean
{Prefix : Type u_1} →
  {Field : Type u_2} →
    {Gap : Type u_3} →
      {Suffix : Type u_4} →
        CodedSorting.Address.FullAddress Prefix Field Gap Suffix ≃
          CodedSorting.Address.FullAddress Prefix Field Gap Suffix
```

**定义**

```lean
fun {Prefix} {Field} {Gap} {Suffix} =>
  { toFun := CodedSorting.Address.exchange, invFun := CodedSorting.Address.exchange, left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.Address.FullAddress](Address.definitions.md#def-dfc18ad24150a538)
- [CodedSorting.Address.exchange_twice](Address.definitions.md#def-dbdfb64823fe33e6)
- [CodedSorting.Address.exchange](Address.definitions.md#def-840ffce97b2075fa)

**基础库名称**

`Equiv.mk`, `Equiv`
