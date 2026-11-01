# NormalizationFrames 的定义

[源码](NormalizationFrames.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-66244596aea2da86"></a>
## `CodedSorting.CommonSortingNormalization.inputCells`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L16)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun b d => d + (d + (b + d + d))
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-0d3ffcc712372781"></a>
## `CodedSorting.CommonSortingNormalization.outputCells`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L17)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun b d => d + (b + d + d)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-3989647baacf876e"></a>
## `CodedSorting.CommonSortingNormalization.inputWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L19)

**类型**

```lean
{b d w : ℕ} →
  CodedSorting.CommonSortingNormalizationStreams.InputState b d w →
    CodedSorting.WordControl.Words (CodedSorting.CommonSortingNormalization.inputCells b d) w
```

**定义**

```lean
fun {b d w} s => Fin.append s.base (Fin.append s.records s.resident)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.inputCells](NormalizationFrames.definitions.md#def-66244596aea2da86)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.records](NormalizationStreams.definitions.md#def-84c098bea2a6f007)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.base](NormalizationStreams.definitions.md#def-707b2982a343dd0c)
- [CodedSorting.CommonSortingNormalizationStreams.InputState](NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.resident](NormalizationStreams.definitions.md#def-b265f9ce048f8da7)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin.append`

<a id="def-50efb14fab2389ff"></a>
## `CodedSorting.CommonSortingNormalization.outputWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L21)

**类型**

```lean
{b d w : ℕ} →
  CodedSorting.CommonSortingNormalizationStreams.OutputState b d w →
    CodedSorting.WordControl.Words (CodedSorting.CommonSortingNormalization.outputCells b d) w
```

**定义**

```lean
fun {b d w} s => Fin.append s.base s.resident
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.outputCells](NormalizationFrames.definitions.md#def-0d3ffcc712372781)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState.resident](NormalizationStreams.definitions.md#def-9ff03fcbedf9a9c9)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState.base](NormalizationStreams.definitions.md#def-4ef78d807013b9b2)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState](NormalizationStreams.definitions.md#def-370ec70e27fe1332)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin.append`

<a id="def-37acc7218c07b823"></a>
## `CodedSorting.CommonSortingNormalization.first`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L24)

**类型**

```lean
{a z w : ℕ} → CodedSorting.WordControl.Words (a + z) w → CodedSorting.WordControl.Words a w
```

**定义**

```lean
fun {a z w} ram i => ram (Fin.castAdd z i)
```

**继续展开**

- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Fin.castAdd`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-eeca6dc44276808b"></a>
## `CodedSorting.CommonSortingNormalization.rest`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L25)

**类型**

```lean
{a z w : ℕ} → CodedSorting.WordControl.Words (a + z) w → CodedSorting.WordControl.Words z w
```

**定义**

```lean
fun {a z w} ram i => ram (Fin.natAdd a i)
```

**继续展开**

- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Fin.natAdd`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-e5acca4221eb57e7"></a>
## `CodedSorting.CommonSortingNormalization.inputOfWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L31)

**类型**

```lean
{b d w : ℕ} →
  CodedSorting.WordControl.Words (CodedSorting.CommonSortingNormalization.inputCells b d) w →
    CodedSorting.CommonSortingNormalizationStreams.InputState b d w
```

**定义**

```lean
fun {b d w} ram =>
  { base := CodedSorting.CommonSortingNormalization.first ram,
    records := CodedSorting.CommonSortingNormalization.first (CodedSorting.CommonSortingNormalization.rest ram),
    resident := CodedSorting.CommonSortingNormalization.rest (CodedSorting.CommonSortingNormalization.rest ram) }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.inputCells](NormalizationFrames.definitions.md#def-66244596aea2da86)
- [CodedSorting.CommonSortingNormalization.rest](NormalizationFrames.definitions.md#def-eeca6dc44276808b)
- [CodedSorting.CommonSortingNormalizationStreams.InputState.mk](NormalizationStreams.definitions.md#def-616c4e863be5bc33)
- [CodedSorting.CommonSortingNormalizationStreams.InputState](NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)
- [CodedSorting.CommonSortingNormalization.first](NormalizationFrames.definitions.md#def-37acc7218c07b823)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-4ade5c5e9a851cef"></a>
## `CodedSorting.CommonSortingNormalization.outputOfWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L33)

**类型**

```lean
{b d w : ℕ} →
  CodedSorting.WordControl.Words (CodedSorting.CommonSortingNormalization.outputCells b d) w →
    CodedSorting.CommonSortingNormalizationStreams.OutputState b d w
```

**定义**

```lean
fun {b d w} ram =>
  { base := CodedSorting.CommonSortingNormalization.first ram,
    resident := CodedSorting.CommonSortingNormalization.rest ram }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.outputCells](NormalizationFrames.definitions.md#def-0d3ffcc712372781)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState.mk](NormalizationStreams.definitions.md#def-72ef445ba827a0ea)
- [CodedSorting.CommonSortingNormalization.rest](NormalizationFrames.definitions.md#def-eeca6dc44276808b)
- [CodedSorting.CommonSortingNormalization.first](NormalizationFrames.definitions.md#def-37acc7218c07b823)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState](NormalizationStreams.definitions.md#def-370ec70e27fe1332)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-e889a8cc1af89e2d"></a>
## `CodedSorting.CommonSortingNormalization.family`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L40)

**类型**

```lean
{k a w : ℕ} → (Fin k → CodedSorting.WordControl.Words a w) → CodedSorting.WordControl.Words (k * a) w
```

**定义**

```lean
fun {k a w} x i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
```

**继续展开**

- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `Equiv.symm`, `Prod`, `Fin`, `Prod.snd`, `DFunLike.coe`, `instHMul`

<a id="def-a80e6efedb830ce4"></a>
## `CodedSorting.CommonSortingNormalization.familyOfWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L42)

**类型**

```lean
{k a w : ℕ} → CodedSorting.WordControl.Words (k * a) w → Fin k → CodedSorting.WordControl.Words a w
```

**定义**

```lean
fun {k a w} ram i j => ram (finProdFinEquiv (i, j))
```

**继续展开**

- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `Prod.mk`, `instMulNat`, `Nat`, `finProdFinEquiv`, `Prod`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-0fd983710d51c239"></a>
## `CodedSorting.CommonSortingNormalization.SourceState`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](NormalizationFrames.lean#L47)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.mk](NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat`

<a id="def-72de523b32bd3bcb"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](NormalizationFrames.lean#L47)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.ResidentLeafSort.RAM (512 * H) d w →
      (Fin v.readers → CodedSorting.CommonSortingNormalizationStreams.InputState b d w) →
        (Fin v.writers → CodedSorting.CommonSortingNormalizationStreams.OutputState b d w) →
          CodedSorting.WordControl.Words b w →
            CodedSorting.WordControl.Words (1 + d) w →
              (Fin 3 → CodedSorting.WordControl.Words (2 * v.keys * d) w) →
                (Fin 3 → CodedSorting.WordControl.Words (13 * d) w) →
                  CodedSorting.WordControl.Words d w →
                    (Fin 3 → CodedSorting.WordControl.Words v.pc w) →
                      CodedSorting.CommonSortingNormalization.SourceState v H b d w
```

**继续展开**

- [CodedSorting.ResidentLeafSort.RAM](../../Local/Framework/ResidentLeafSort.definitions.md#def-351ba66701581e98)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.SortingResourceBudget.Inventory.writers](../../Bounds/SortingResourceBudget.definitions.md#def-05f5194f09efb8fc)
- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonSortingNormalizationStreams.InputState](NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.Inventory.pc](../../Bounds/SortingResourceBudget.definitions.md#def-42f9d44e4c026d81)
- [CodedSorting.SortingResourceBudget.Inventory.keys](../../Bounds/SortingResourceBudget.definitions.md#def-b107122480bc6937)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState](NormalizationStreams.definitions.md#def-370ec70e27fe1332)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-c74201da4a42b2fb"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.leaf`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `leaf` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L48)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.CommonSortingNormalization.SourceState v H b d w → CodedSorting.ResidentLeafSort.RAM (512 * H) d w
```

**定义**

```lean
fun v H b d w self => self.1
```

**继续展开**

- [CodedSorting.ResidentLeafSort.RAM](../../Local/Framework/ResidentLeafSort.definitions.md#def-351ba66701581e98)
- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-1ce3f0d449f8cfec"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.readers`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `readers` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L49)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.CommonSortingNormalization.SourceState v H b d w →
      Fin v.readers → CodedSorting.CommonSortingNormalizationStreams.InputState b d w
```

**定义**

```lean
fun v H b d w self => self.2
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonSortingNormalizationStreams.InputState](NormalizationStreams.definitions.md#def-d8fda97797b4a0c0)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`Nat`, `Fin`

<a id="def-c3d33757cbee4c66"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.writers`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `writers` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L50)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.CommonSortingNormalization.SourceState v H b d w →
      Fin v.writers → CodedSorting.CommonSortingNormalizationStreams.OutputState b d w
```

**定义**

```lean
fun v H b d w self => self.3
```

**继续展开**

- [CodedSorting.SortingResourceBudget.Inventory.writers](../../Bounds/SortingResourceBudget.definitions.md#def-05f5194f09efb8fc)
- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.CommonSortingNormalizationStreams.OutputState](NormalizationStreams.definitions.md#def-370ec70e27fe1332)

**基础库名称**

`Nat`, `Fin`

<a id="def-5af33a923e775e41"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.transfer`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `transfer` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L51)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} → CodedSorting.CommonSortingNormalization.SourceState v H b d w → CodedSorting.WordControl.Words b w
```

**定义**

```lean
fun v H b d w self => self.4
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-e8ae6388c01bfd91"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.scalars`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `scalars` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L52)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.CommonSortingNormalization.SourceState v H b d w → CodedSorting.WordControl.Words (1 + d) w
```

**定义**

```lean
fun v H b d w self => self.5
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-443c651ce7b31bd4"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.directories`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `directories` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L53)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.CommonSortingNormalization.SourceState v H b d w →
      Fin 3 → CodedSorting.WordControl.Words (2 * v.keys * d) w
```

**定义**

```lean
fun v H b d w self => self.6
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.Inventory.keys](../../Bounds/SortingResourceBudget.definitions.md#def-b107122480bc6937)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-8b7d876f6d0e844e"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.shapes`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `shapes` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L54)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.CommonSortingNormalization.SourceState v H b d w → Fin 3 → CodedSorting.WordControl.Words (13 * d) w
```

**定义**

```lean
fun v H b d w self => self.7
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-61729c1e88340c1b"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.top`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `top` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L55)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} → CodedSorting.CommonSortingNormalization.SourceState v H b d w → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun v H b d w self => self.8
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-5b02f957dea973c7"></a>
## `CodedSorting.CommonSortingNormalization.SourceState.pcs`

读取 `CodedSorting.CommonSortingNormalization.SourceState` 的 `pcs` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L56)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.CommonSortingNormalization.SourceState v H b d w → Fin 3 → CodedSorting.WordControl.Words v.pc w
```

**定义**

```lean
fun v H b d w self => self.9
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.Inventory.pc](../../Bounds/SortingResourceBudget.definitions.md#def-42f9d44e4c026d81)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-91f4c57732154132"></a>
## `CodedSorting.CommonSortingNormalization.tailCells`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L58)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ → ℕ → ℕ
```

**定义**

```lean
fun v b d =>
  v.readers * CodedSorting.CommonSortingNormalization.inputCells b d +
    (v.writers * CodedSorting.CommonSortingNormalization.outputCells b d +
      (b + (1 + d + (3 * (2 * v.keys * d) + (3 * (13 * d) + (d + 3 * v.pc))))))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.inputCells](NormalizationFrames.definitions.md#def-66244596aea2da86)
- [CodedSorting.CommonSortingNormalization.outputCells](NormalizationFrames.definitions.md#def-0d3ffcc712372781)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.SortingResourceBudget.Inventory.writers](../../Bounds/SortingResourceBudget.definitions.md#def-05f5194f09efb8fc)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.Inventory.pc](../../Bounds/SortingResourceBudget.definitions.md#def-42f9d44e4c026d81)
- [CodedSorting.SortingResourceBudget.Inventory.keys](../../Bounds/SortingResourceBudget.definitions.md#def-b107122480bc6937)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-ebda39f020ddec43"></a>
## `CodedSorting.CommonSortingNormalization.sourceCells`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L61)

**类型**

```lean
CodedSorting.SortingResourceBudget.Inventory → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun v H b d =>
  CodedSorting.ResidentLeafSort.residentWords (512 * H) d + CodedSorting.CommonSortingNormalization.tailCells v b d
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.tailCells](NormalizationFrames.definitions.md#def-91f4c57732154132)
- [CodedSorting.ResidentLeafSort.residentWords](../../Local/Framework/ResidentLeafSort.definitions.md#def-2fda3d29689ad340)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-1890a68cf8f15384"></a>
## `CodedSorting.CommonSortingNormalization.pack`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L64)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.CommonSortingNormalization.SourceState v H b d w →
      CodedSorting.WordControl.Words (CodedSorting.CommonSortingNormalization.sourceCells v H b d) w
```

**定义**

```lean
fun {v} {H b d w} s =>
  Fin.append s.leaf
    (Fin.append
      (CodedSorting.CommonSortingNormalization.family fun i =>
        CodedSorting.CommonSortingNormalization.inputWords (s.readers i))
      (Fin.append
        (CodedSorting.CommonSortingNormalization.family fun i =>
          CodedSorting.CommonSortingNormalization.outputWords (s.writers i))
        (Fin.append s.transfer
          (Fin.append s.scalars
            (Fin.append (CodedSorting.CommonSortingNormalization.family s.directories)
              (Fin.append (CodedSorting.CommonSortingNormalization.family s.shapes)
                (Fin.append s.top (CodedSorting.CommonSortingNormalization.family s.pcs))))))))
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.inputCells](NormalizationFrames.definitions.md#def-66244596aea2da86)
- [CodedSorting.CommonSortingNormalization.outputCells](NormalizationFrames.definitions.md#def-0d3ffcc712372781)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.tailCells](NormalizationFrames.definitions.md#def-91f4c57732154132)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.inputWords](NormalizationFrames.definitions.md#def-3989647baacf876e)
- [CodedSorting.ResidentLeafSort.residentWords](../../Local/Framework/ResidentLeafSort.definitions.md#def-2fda3d29689ad340)
- [CodedSorting.CommonSortingNormalization.outputWords](NormalizationFrames.definitions.md#def-50efb14fab2389ff)
- [CodedSorting.SortingResourceBudget.Inventory.writers](../../Bounds/SortingResourceBudget.definitions.md#def-05f5194f09efb8fc)
- [CodedSorting.CommonSortingNormalization.SourceState.top](NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.family](NormalizationFrames.definitions.md#def-e889a8cc1af89e2d)
- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.sourceCells](NormalizationFrames.definitions.md#def-ebda39f020ddec43)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.Inventory.pc](../../Bounds/SortingResourceBudget.definitions.md#def-42f9d44e4c026d81)
- [CodedSorting.SortingResourceBudget.Inventory.keys](../../Bounds/SortingResourceBudget.definitions.md#def-b107122480bc6937)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `Fin.append`, `instHMul`

<a id="def-8a0c8f74cc8bea51"></a>
## `CodedSorting.CommonSortingNormalization.unpack`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L70)

**类型**

```lean
{v : CodedSorting.SortingResourceBudget.Inventory} →
  {H b d w : ℕ} →
    CodedSorting.WordControl.Words (CodedSorting.CommonSortingNormalization.sourceCells v H b d) w →
      CodedSorting.CommonSortingNormalization.SourceState v H b d w
```

**定义**

```lean
fun {v} {H b d w} ram =>
  { leaf := CodedSorting.CommonSortingNormalization.first ram,
    readers := fun i =>
      CodedSorting.CommonSortingNormalization.inputOfWords
        (CodedSorting.CommonSortingNormalization.familyOfWords
          (CodedSorting.CommonSortingNormalization.first (CodedSorting.CommonSortingNormalization.rest ram)) i),
    writers := fun i =>
      CodedSorting.CommonSortingNormalization.outputOfWords
        (CodedSorting.CommonSortingNormalization.familyOfWords
          (CodedSorting.CommonSortingNormalization.first
            (CodedSorting.CommonSortingNormalization.rest (CodedSorting.CommonSortingNormalization.rest ram)))
          i),
    transfer :=
      CodedSorting.CommonSortingNormalization.first
        (CodedSorting.CommonSortingNormalization.rest
          (CodedSorting.CommonSortingNormalization.rest (CodedSorting.CommonSortingNormalization.rest ram))),
    scalars :=
      CodedSorting.CommonSortingNormalization.first
        (CodedSorting.CommonSortingNormalization.rest
          (CodedSorting.CommonSortingNormalization.rest
            (CodedSorting.CommonSortingNormalization.rest (CodedSorting.CommonSortingNormalization.rest ram)))),
    directories :=
      CodedSorting.CommonSortingNormalization.familyOfWords
        (CodedSorting.CommonSortingNormalization.first
          (CodedSorting.CommonSortingNormalization.rest
            (CodedSorting.CommonSortingNormalization.rest
              (CodedSorting.CommonSortingNormalization.rest
                (CodedSorting.CommonSortingNormalization.rest (CodedSorting.CommonSortingNormalization.rest ram)))))),
    shapes :=
      CodedSorting.CommonSortingNormalization.familyOfWords
        (CodedSorting.CommonSortingNormalization.first
          (CodedSorting.CommonSortingNormalization.rest
            (CodedSorting.CommonSortingNormalization.rest
              (CodedSorting.CommonSortingNormalization.rest
                (CodedSorting.CommonSortingNormalization.rest
                  (CodedSorting.CommonSortingNormalization.rest
                    (CodedSorting.CommonSortingNormalization.rest ram))))))),
    top :=
      CodedSorting.CommonSortingNormalization.first
        (CodedSorting.CommonSortingNormalization.rest
          (CodedSorting.CommonSortingNormalization.rest
            (CodedSorting.CommonSortingNormalization.rest
              (CodedSorting.CommonSortingNormalization.rest
                (CodedSorting.CommonSortingNormalization.rest
                  (CodedSorting.CommonSortingNormalization.rest
                    (CodedSorting.CommonSortingNormalization.rest ram))))))),
    pcs :=
      CodedSorting.CommonSortingNormalization.familyOfWords
        (CodedSorting.CommonSortingNormalization.rest
          (CodedSorting.CommonSortingNormalization.rest
            (CodedSorting.CommonSortingNormalization.rest
              (CodedSorting.CommonSortingNormalization.rest
                (CodedSorting.CommonSortingNormalization.rest
                  (CodedSorting.CommonSortingNormalization.rest
                    (CodedSorting.CommonSortingNormalization.rest
                      (CodedSorting.CommonSortingNormalization.rest ram)))))))) }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.inputCells](NormalizationFrames.definitions.md#def-66244596aea2da86)
- [CodedSorting.CommonSortingNormalization.outputCells](NormalizationFrames.definitions.md#def-0d3ffcc712372781)
- [CodedSorting.CommonSortingNormalization.tailCells](NormalizationFrames.definitions.md#def-91f4c57732154132)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.outputOfWords](NormalizationFrames.definitions.md#def-4ade5c5e9a851cef)
- [CodedSorting.ResidentLeafSort.residentWords](../../Local/Framework/ResidentLeafSort.definitions.md#def-2fda3d29689ad340)
- [CodedSorting.SortingResourceBudget.Inventory.writers](../../Bounds/SortingResourceBudget.definitions.md#def-05f5194f09efb8fc)
- [CodedSorting.CommonSortingNormalization.familyOfWords](NormalizationFrames.definitions.md#def-a80e6efedb830ce4)
- [CodedSorting.CommonSortingNormalization.rest](NormalizationFrames.definitions.md#def-eeca6dc44276808b)
- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.sourceCells](NormalizationFrames.definitions.md#def-ebda39f020ddec43)
- [CodedSorting.CommonSortingNormalization.first](NormalizationFrames.definitions.md#def-37acc7218c07b823)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)
- [CodedSorting.SortingResourceBudget.Inventory.pc](../../Bounds/SortingResourceBudget.definitions.md#def-42f9d44e4c026d81)
- [CodedSorting.SortingResourceBudget.Inventory.keys](../../Bounds/SortingResourceBudget.definitions.md#def-b107122480bc6937)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)
- [CodedSorting.CommonSortingNormalization.inputOfWords](NormalizationFrames.definitions.md#def-e5acca4221eb57e7)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-c17122391d7f01c9"></a>
## `CodedSorting.CommonSortingNormalization.Configuration`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](NormalizationFrames.lean#L126)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.mk](NormalizationFrames.definitions.md#def-fedce2cf7e9f973a)

<a id="def-fedce2cf7e9f973a"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](NormalizationFrames.lean#L128)

**类型**

```lean
(inventory : CodedSorting.SortingResourceBudget.Inventory) →
  (N M B w c exponent : ℕ) →
    2 ≤ N →
      M ≤ N →
        0 < B →
          2 * B ≤ M →
            1 ≤ exponent →
              CodedSorting.WordConvention.Covers N w c →
                CodedSorting.SortingResourceBudget.reserve inventory c
                        (CodedSorting.SortingResourceBudget.digits c exponent) ^
                      2 ≤
                    M →
                  CodedSorting.CommonSortingNormalization.Configuration
```

**继续展开**

- [CodedSorting.SortingResourceBudget.digits](../../Bounds/SortingResourceBudget.definitions.md#def-ea371db150e4467a)
- [CodedSorting.SortingResourceBudget.reserve](../../Bounds/SortingResourceBudget.definitions.md#def-9e7e2eeee9930238)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.WordConvention.Covers](../../../Shared/Words/WordConvention.definitions.md#def-a9dbb84e85202da9)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-b7bca164f5a6f55d"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.inventory`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `inventory` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L129)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → CodedSorting.SortingResourceBudget.Inventory
```

**定义**

```lean
fun self => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.SortingResourceBudget.Inventory](../../Bounds/SortingResourceBudget.definitions.md#def-c75060ed230df145)

<a id="def-a0f8cfde18f80cba"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.N`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `N` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L130)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun self => self.2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-6f6ccc314083aa03"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.M`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `M` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L131)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun self => self.3
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-eb9fa6eed55dcdac"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.B`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `B` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L132)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun self => self.4
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-d94a6ee84fc22f76"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.w`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `w` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L133)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun self => self.5
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-4ad0ae0cc65348bb"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.c`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `c` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L134)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun self => self.6
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-441ef1e5176fbf68"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.exponent`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `exponent` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L135)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun self => self.7
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-eed5a6cf1c2fc36b"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.input_large`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationFrames.lean#L136)

**类型**

```lean
∀ (self : CodedSorting.CommonSortingNormalization.Configuration), 2 ≤ self.N
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-89b87a4f8cd3c4fe"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.block_pos`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationFrames.lean#L138)

**类型**

```lean
∀ (self : CodedSorting.CommonSortingNormalization.Configuration), 0 < self.B
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.B](NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-78ccf64a37ef5c44"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.word_convention`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationFrames.lean#L141)

**类型**

```lean
∀ (self : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.WordConvention.Covers self.N self.w self.c
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.WordConvention.Covers](../../../Shared/Words/WordConvention.definitions.md#def-a9dbb84e85202da9)
- [CodedSorting.CommonSortingNormalization.Configuration.c](NormalizationFrames.definitions.md#def-4ad0ae0cc65348bb)
- [CodedSorting.CommonSortingNormalization.Configuration.N](NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

<a id="def-c767b1894cb4c907"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.digits`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `digits` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L144)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.SortingResourceBudget.digits q.c q.exponent
```

**继续展开**

- [CodedSorting.SortingResourceBudget.digits](../../Bounds/SortingResourceBudget.definitions.md#def-ea371db150e4467a)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.c](NormalizationFrames.definitions.md#def-4ad0ae0cc65348bb)

**基础库名称**

`Nat`

<a id="def-a956e2f48d4f9cd2"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.height`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `height` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L145)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.SortingResourceBudget.H q.inventory q.c q.digits q.M
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.M](NormalizationFrames.definitions.md#def-6f6ccc314083aa03)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.SortingResourceBudget.H](../../Bounds/SortingResourceBudget.definitions.md#def-c389dd4158f0ee74)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.c](NormalizationFrames.definitions.md#def-4ad0ae0cc65348bb)

**基础库名称**

`Nat`

<a id="def-32bdace0e0767974"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.block`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `block` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L146)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.SortingResourceBudget.block q.inventory q.c q.digits q.B
```

**继续展开**

- [CodedSorting.SortingResourceBudget.block](../../Bounds/SortingResourceBudget.definitions.md#def-49532a5e2a2934bc)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.c](NormalizationFrames.definitions.md#def-4ad0ae0cc65348bb)
- [CodedSorting.CommonSortingNormalization.Configuration.B](NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Nat`

<a id="def-7d7f7ce8536ebbdd"></a>
## `CodedSorting.CommonSortingNormalization.Configuration.ramWords`

读取 `CodedSorting.CommonSortingNormalization.Configuration` 的 `ramWords` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](NormalizationFrames.lean#L147)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => CodedSorting.CommonSortingNormalization.sourceCells q.inventory q.height q.block q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.sourceCells](NormalizationFrames.definitions.md#def-ebda39f020ddec43)
- [CodedSorting.CommonSortingNormalization.Configuration.block](NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat`

<a id="def-1812a6349a1bc9a7"></a>
## `CodedSorting.CommonSortingNormalization.SourcePolicy`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L149)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q =>
  CodedSorting.ControlledNormalization.Policy q.ramWords q.block (q.N ^ q.exponent) (CodedSorting.WordControl.Word q.w)
```

**继续展开**

- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.ControlledNormalization.Policy](../../../Shared/Programs/ControlledNormalization.definitions.md#def-311feb3c44e69784)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-0d844079adca6559"></a>
## `CodedSorting.CommonSortingNormalization.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L156)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonSortingNormalization.SourcePolicy q →
    CodedSorting.CommonNormalizationController.Program q.ramWords (q.N ^ q.exponent) q.B q.block q.digits q.w
```

**定义**

```lean
fun q policy =>
  { positive_region := ⋯, positive_block := ⋯, block_ratio := ⋯, counter_capacity := ⋯, phase_capacity := ⋯,
    padding := 0, policy := policy }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourcePolicy](NormalizationFrames.definitions.md#def-1812a6349a1bc9a7)
- [CodedSorting.CommonNormalizationController.Program](../../../Shared/Memory/NormalizationController.definitions.md#def-8e30ae3ef69cec39)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.program._proof_5](NormalizationFrames.definitions.md#def-01c3e7716f2d7644)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonNormalizationController.Program.mk](../../../Shared/Memory/NormalizationController.definitions.md#def-c8f48bd4c9348d9c)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.program._proof_3](NormalizationFrames.definitions.md#def-bde82b8167f23001)
- [CodedSorting.CommonSortingNormalization.Configuration.N](NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.program._proof_6](NormalizationFrames.definitions.md#def-a370f075f64e0cfc)
- [CodedSorting.CommonSortingNormalization.Configuration.block](NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.program._proof_4](NormalizationFrames.definitions.md#def-9ac1350c8d2ec013)
- [CodedSorting.CommonSortingNormalization.Configuration.block_pos](NormalizationFrames.definitions.md#def-89b87a4f8cd3c4fe)
- [CodedSorting.CommonSortingNormalization.program._proof_2](NormalizationFrames.definitions.md#def-ff9df0f144d7cc36)
- [CodedSorting.CommonSortingNormalization.Configuration.B](NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.instOfNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-90721c68825dbf3f"></a>
## `CodedSorting.CommonSortingNormalization.MachineState`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L171)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.CommonNormalizationController.State q.ramWords (q.N ^ q.exponent) q.B q.block q.digits q.w
```

**继续展开**

- [CodedSorting.CommonNormalizationController.State](../../../Shared/Memory/NormalizationController.definitions.md#def-f2e4d72f6ceee1dd)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.Configuration.B](NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-8a95fd2c7fba5be8"></a>
## `CodedSorting.CommonSortingNormalization.ResidentIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L174)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q =>
  (Fin q.ramWords ⊕ Fin q.B) ⊕ (Fin q.block ⊕ Fin q.digits) ⊕ (Fin q.digits ⊕ Fin q.digits) ⊕ Fin 2 ⊕ Fin (q.digits + 1)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.Configuration.B](NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Sum`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-2425cae72dbf61a5"></a>
## `CodedSorting.CommonSortingNormalization.initialState`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](NormalizationFrames.lean#L223)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonSortingNormalization.SourcePolicy q →
    CodedSorting.CommonSortingNormalization.SourceState q.inventory q.height q.block q.digits q.w →
      Fin (q.N ^ q.exponent + 1) →
        Fin (q.N ^ q.exponent) →
          CodedSorting.CommonNormalizationController.Disk (q.N ^ q.exponent) q.B q.w →
            CodedSorting.CommonSortingNormalization.MachineState q
```

**定义**

```lean
fun q policy s nIn nOut disk =>
  CodedSorting.CommonNormalizationController.initial (CodedSorting.CommonSortingNormalization.program q policy)
    (CodedSorting.CommonSortingNormalization.pack s) (CodedSorting.WordConvention.encode q.N q.w q.c q.exponent ⋯ ⋯ nIn)
    (CodedSorting.WordConvention.encode q.N q.w q.c q.exponent ⋯ ⋯ nOut.castSucc) disk
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourcePolicy](NormalizationFrames.definitions.md#def-1812a6349a1bc9a7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonNormalizationController.Disk](../../../Shared/Memory/NormalizationController.definitions.md#def-ad6b8f91b6dfa7db)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration.input_large](NormalizationFrames.definitions.md#def-eed5a6cf1c2fc36b)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState](NormalizationFrames.definitions.md#def-0fd983710d51c239)
- [CodedSorting.CommonSortingNormalization.program](NormalizationFrames.definitions.md#def-0d844079adca6559)
- [CodedSorting.CommonSortingNormalization.Configuration.c](NormalizationFrames.definitions.md#def-4ad0ae0cc65348bb)
- [CodedSorting.CommonSortingNormalization.MachineState](NormalizationFrames.definitions.md#def-90721c68825dbf3f)
- [CodedSorting.CommonNormalizationController.initial](../../../Shared/Memory/NormalizationController.definitions.md#def-26af14d29c13c568)
- [CodedSorting.CommonSortingNormalization.Configuration.N](NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.WordConvention.encode](../../../Shared/Words/WordConvention.definitions.md#def-b25382c90b106b24)
- [CodedSorting.CommonSortingNormalization.Configuration.word_convention](NormalizationFrames.definitions.md#def-78ccf64a37ef5c44)
- [CodedSorting.CommonSortingNormalization.Configuration.B](NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Fin.castSucc`, `OfNat.ofNat`, `Fin`

<a id="def-ff9df0f144d7cc36"></a>
## `CodedSorting.CommonSortingNormalization.program._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationFrames.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), 0 < q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `Monoid.toNatPow`, `Nat.instMonoidWithZero`, `MonoidWithZero.toMulZeroOneClass`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instPartialOrder`, `Zero.toOfNat0`, `instHPow`, `MulZeroOneClass.toMulZeroClass`, `OfNat.ofNat`, `MonoidWithZero.toMonoid`, `MulZeroClass.toZero`

<a id="def-bde82b8167f23001"></a>
## `CodedSorting.CommonSortingNormalization.program._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationFrames.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.Normalization.logicalBlockSize q.B
      (CodedSorting.SortingResourceBudget.reserve q.inventory q.c q.digits ^ 2) ≤
    q.B
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.reserve](../../Bounds/SortingResourceBudget.definitions.md#def-9e7e2eeee9930238)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.logicalBlockSize](../../../Shared/Programs/Normalization.definitions.md#def-bb8eed12be50f878)
- [CodedSorting.CommonSortingNormalization.Configuration.c](NormalizationFrames.definitions.md#def-4ad0ae0cc65348bb)
- [CodedSorting.CommonSortingNormalization.Configuration.B](NormalizationFrames.definitions.md#def-eb9fa6eed55dcdac)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-9ac1350c8d2ec013"></a>
## `CodedSorting.CommonSortingNormalization.program._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationFrames.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), q.N ^ q.exponent < (2 ^ q.w) ^ q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-01c3e7716f2d7644"></a>
## `CodedSorting.CommonSortingNormalization.program._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationFrames.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), 8 ≤ 2 ^ q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-a370f075f64e0cfc"></a>
## `CodedSorting.CommonSortingNormalization.program._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](NormalizationFrames.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), NeZero (2 ^ q.w)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `OfNat.ofNat`, `MulZeroClass.toZero`
