# NormalizationStreams 的定义

[源码](NormalizationStreams.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-b79f1ea17c6ea9af"></a>
## `CodedSorting.CommonSortingNormalizationStreams.Resident`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationStreams.lean#L13)

**类型**

```lean
ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun B d w => CodedSorting.WordControl.Words (B + d + d) w
```

**继续展开**

- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-c9dd272a76ec9d14"></a>
## `CodedSorting.CommonSortingNormalizationStreams.payload`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationStreams.lean#L27)

**类型**

```lean
{B d w : ℕ} → CodedSorting.CommonSortingNormalizationStreams.Resident B d w → CodedSorting.WordControl.Words B w
```

**定义**

```lean
fun {B d w} ram i => ram (Fin.castAdd d (Fin.castAdd d i))
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.Resident](NormalizationStreams.definitions.md#def-b79f1ea17c6ea9af)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Fin.castAdd`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-08c958193c72d21a"></a>
## `CodedSorting.CommonSortingNormalizationStreams.lengthWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationStreams.lean#L30)

**类型**

```lean
{B d w : ℕ} → CodedSorting.CommonSortingNormalizationStreams.Resident B d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun {B d w} ram i => ram (Fin.castAdd d (Fin.natAdd B i))
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.Resident](NormalizationStreams.definitions.md#def-b79f1ea17c6ea9af)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Fin.natAdd`, `Fin.castAdd`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-05d4c3b81554a68a"></a>
## `CodedSorting.CommonSortingNormalizationStreams.cursorWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationStreams.lean#L36)

**类型**

```lean
{B d w : ℕ} → CodedSorting.CommonSortingNormalizationStreams.Resident B d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun {B d w} ram i => ram (Fin.natAdd (B + d) i)
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.Resident](NormalizationStreams.definitions.md#def-b79f1ea17c6ea9af)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Fin.natAdd`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-d8fda97797b4a0c0"></a>
## `CodedSorting.CommonSortingNormalizationStreams.InputState`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](NormalizationStreams.lean#L259)

**类型**

```lean
ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.InputState.mk](NormalizationStreams.definitions.md#def-616c4e863be5bc33)

**基础库名称**

`Nat`

<a id="def-616c4e863be5bc33"></a>
## `CodedSorting.CommonSortingNormalizationStreams.InputState.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](NormalizationStreams.lean#L261)

**类型**

```lean
{B d w : ℕ} →
  CodedSorting.WordControl.Words d w →
    CodedSorting.WordControl.Words d w →
      CodedSorting.CommonSortingNormalizationStreams.Resident B d w →
        CodedSorting.CommonSortingNormalizationStreams.InputState B d w
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.Resident](NormalizationStreams.definitions.md#def-b79f1ea17c6ea9af)
- [CodedSorting.CommonSortingNormalizationStreams.InputState](NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-707b2982a343dd0c"></a>
## `CodedSorting.CommonSortingNormalizationStreams.InputState.base`

读取 `CodedSorting.CommonSortingNormalizationStreams.InputState` 的 `base` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationStreams.lean#L262)

**类型**

```lean
{B d w : ℕ} → CodedSorting.CommonSortingNormalizationStreams.InputState B d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun B d w self => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.InputState](NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-84c098bea2a6f007"></a>
## `CodedSorting.CommonSortingNormalizationStreams.InputState.records`

读取 `CodedSorting.CommonSortingNormalizationStreams.InputState` 的 `records` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationStreams.lean#L263)

**类型**

```lean
{B d w : ℕ} → CodedSorting.CommonSortingNormalizationStreams.InputState B d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun B d w self => self.2
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.InputState](NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-b265f9ce048f8da7"></a>
## `CodedSorting.CommonSortingNormalizationStreams.InputState.resident`

读取 `CodedSorting.CommonSortingNormalizationStreams.InputState` 的 `resident` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationStreams.lean#L264)

**类型**

```lean
{B d w : ℕ} →
  CodedSorting.CommonSortingNormalizationStreams.InputState B d w →
    CodedSorting.CommonSortingNormalizationStreams.Resident B d w
```

**定义**

```lean
fun B d w self => self.3
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.Resident](NormalizationStreams.definitions.md#def-b79f1ea17c6ea9af)
- [CodedSorting.CommonSortingNormalizationStreams.InputState](NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)

**基础库名称**

`Nat`

<a id="def-370ec70e27fe1332"></a>
## `CodedSorting.CommonSortingNormalizationStreams.OutputState`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](NormalizationStreams.lean#L387)

**类型**

```lean
ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.OutputState.mk](NormalizationStreams.definitions.md#def-72ef445ba827a0ea)

**基础库名称**

`Nat`

<a id="def-72ef445ba827a0ea"></a>
## `CodedSorting.CommonSortingNormalizationStreams.OutputState.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](NormalizationStreams.lean#L388)

**类型**

```lean
{B d w : ℕ} →
  CodedSorting.WordControl.Words d w →
    CodedSorting.CommonSortingNormalizationStreams.Resident B d w →
      CodedSorting.CommonSortingNormalizationStreams.OutputState B d w
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.Resident](NormalizationStreams.definitions.md#def-b79f1ea17c6ea9af)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState](NormalizationStreams.definitions.md#def-370ec70e27fe1332)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-4ef78d807013b9b2"></a>
## `CodedSorting.CommonSortingNormalizationStreams.OutputState.base`

读取 `CodedSorting.CommonSortingNormalizationStreams.OutputState` 的 `base` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationStreams.lean#L389)

**类型**

```lean
{B d w : ℕ} → CodedSorting.CommonSortingNormalizationStreams.OutputState B d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun B d w self => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.OutputState](NormalizationStreams.definitions.md#def-370ec70e27fe1332)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-9ff03fcbedf9a9c9"></a>
## `CodedSorting.CommonSortingNormalizationStreams.OutputState.resident`

读取 `CodedSorting.CommonSortingNormalizationStreams.OutputState` 的 `resident` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationStreams.lean#L390)

**类型**

```lean
{B d w : ℕ} →
  CodedSorting.CommonSortingNormalizationStreams.OutputState B d w →
    CodedSorting.CommonSortingNormalizationStreams.Resident B d w
```

**定义**

```lean
fun B d w self => self.2
```

**继续展开**

- [CodedSorting.CommonSortingNormalizationStreams.Resident](NormalizationStreams.definitions.md#def-b79f1ea17c6ea9af)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState](NormalizationStreams.definitions.md#def-370ec70e27fe1332)

**基础库名称**

`Nat`
