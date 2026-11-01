# Control 的定义

[源码](Control.lean) · [主定理导读](../../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-3a0b99259a2e477e"></a>
## `CodedSorting.RadixController.LocalSorter`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Control.lean#L12)

**类型**

```lean
(CodedSorting.CommonSortingNormalization.Configuration → Prop) → Type
```

**继续展开**

- [CodedSorting.RadixController.LocalSorter.mk](Control.definitions.md#def-74464258233c8a8d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

<a id="def-74464258233c8a8d"></a>
## `CodedSorting.RadixController.LocalSorter.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Control.lean#L12)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  (space : (q : CodedSorting.CommonSortingNormalization.Configuration) → Normal q → ℕ → ℕ) →
    (charge : CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ) →
      (program :
          (q : CodedSorting.CommonSortingNormalization.Configuration) →
            Fin q.inventory.readers →
              (normal : Normal q) →
                (n : ℕ) →
                  n ≤ q.height ^ 2 →
                    2 ≤ q.exponent →
                      (source offset buffer limit : ℕ) →
                        source + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * offset + 3 * n) + 2 ≤
                            buffer →
                          buffer + space q normal n ≤ limit →
                            limit ≤ q.N ^ q.exponent →
                              CodedSorting.CommonRecordInterval.Program q n source offset buffer limit
                                CodedSorting.Columnsort.sortColumn) →
        (∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
            (normal : Normal q) (n : ℕ) (hn : n ≤ q.height ^ 2) (he : 2 ≤ q.exponent) (source offset buffer limit : ℕ)
            (hs : source + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * offset + 3 * n) + 2 ≤ buffer)
            (hw : buffer + space q normal n ≤ limit) (hc : limit ≤ q.N ^ q.exponent),
            (program q reader normal n hn he source offset buffer limit hs hw hc).charge = charge q n) →
          CodedSorting.RadixController.LocalSorter Normal
```

**继续展开**

- [CodedSorting.CommonRecordInterval.Program](../../../../Shared/Records/RecordOperations.definitions.md#def-2721e3818979b9a7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.KeyRecordWords.Record](../../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonRecordInterval.Program.charge](../../../../Shared/Records/RecordOperations.definitions.md#def-63452802ff71011d)
- [CodedSorting.Columnsort.sortColumn](../../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`

<a id="def-6cf03463d6968e87"></a>
## `CodedSorting.RadixController.LocalSorter.space`

读取 `CodedSorting.RadixController.LocalSorter` 的 `space` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L13)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [self : CodedSorting.RadixController.LocalSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) → Normal q → ℕ → ℕ
```

**定义**

```lean
fun Normal [self : CodedSorting.RadixController.LocalSorter Normal] => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)

**基础库名称**

`Nat`

<a id="def-76093a467738e684"></a>
## `CodedSorting.RadixController.LocalSorter.program`

读取 `CodedSorting.RadixController.LocalSorter` 的 `program` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L15)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [self : CodedSorting.RadixController.LocalSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) →
      Fin q.inventory.readers →
        (normal : Normal q) →
          (n : ℕ) →
            n ≤ q.height ^ 2 →
              2 ≤ q.exponent →
                (source offset buffer limit : ℕ) →
                  source + CodedSorting.PhysicalStreamCursor.blockCount q.block (3 * offset + 3 * n) + 2 ≤ buffer →
                    buffer + CodedSorting.RadixController.LocalSorter.space q normal n ≤ limit →
                      limit ≤ q.N ^ q.exponent →
                        CodedSorting.CommonRecordInterval.Program q n source offset buffer limit
                          CodedSorting.Columnsort.sortColumn
```

**定义**

```lean
fun Normal [self : CodedSorting.RadixController.LocalSorter Normal] => self.3
```

**继续展开**

- [CodedSorting.CommonRecordInterval.Program](../../../../Shared/Records/RecordOperations.definitions.md#def-2721e3818979b9a7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.KeyRecordWords.Record](../../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LocalSorter.space](Control.definitions.md#def-6cf03463d6968e87)
- [CodedSorting.Columnsort.sortColumn](../../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.ResidentLeafSort.recordOrder](../../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-5217c2ac1a71759a"></a>
## `CodedSorting.RadixController.Job`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L46)

**类型**

```lean
ℕ → ℕ → Type
```

**定义**

```lean
fun N L => Fin (L + 1) × Fin (N + 1) × Fin (N + 1) × Fin (L + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-c5e0bd5ef519c49d"></a>
## `CodedSorting.RadixController.level`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L48)

**类型**

```lean
{N L : ℕ} → CodedSorting.RadixController.Job N L → ℕ
```

**定义**

```lean
fun {N L} j => ↑j.1
```

**继续展开**

- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`instOfNatNat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-99ba717ce1accffc"></a>
## `CodedSorting.RadixController.offset`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L49)

**类型**

```lean
{N L : ℕ} → CodedSorting.RadixController.Job N L → ℕ
```

**定义**

```lean
fun {N L} j => ↑j.2.1
```

**继续展开**

- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`instOfNatNat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`

<a id="def-40e139ab4c013c5d"></a>
## `CodedSorting.RadixController.records`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L50)

**类型**

```lean
{N L : ℕ} → CodedSorting.RadixController.Job N L → ℕ
```

**定义**

```lean
fun {N L} j => ↑j.2.2.1
```

**继续展开**

- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`instOfNatNat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`

<a id="def-6695bf5c325da18a"></a>
## `CodedSorting.RadixController.depth`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L51)

**类型**

```lean
{N L : ℕ} → CodedSorting.RadixController.Job N L → ℕ
```

**定义**

```lean
fun {N L} j => ↑j.2.2.2
```

**继续展开**

- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Prod.snd`

<a id="def-f6b6bc34e6e28edd"></a>
## `CodedSorting.RadixController.bounded`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L52)

**类型**

```lean
(N : ℕ) → ℕ → Fin (N + 1)
```

**定义**

```lean
fun N n => ⟨n % (N + 1), ⋯⟩
```

**继续展开**

- [CodedSorting.RadixController.bounded._proof_2](Control.definitions.md#def-2f540cac2df4a324)

**基础库名称**

`Fin.mk`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-072999d65dc88a81"></a>
## `CodedSorting.RadixController.Components`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Control.lean#L54)

**类型**

```lean
(CodedSorting.CommonSortingNormalization.Configuration → Prop) →
  CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.RadixController.Components.mk](Control.definitions.md#def-5b801c4fa7a74f67)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-5b801c4fa7a74f67"></a>
## `CodedSorting.RadixController.Components.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Control.lean#L54)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A : ℕ} →
      Fin q.inventory.readers →
        Normal q →
          2 ≤ q.exponent →
            ℕ →
              ℕ →
                (CodedSorting.RadixController.Job q.N L → ℕ) →
                  (CodedSorting.RadixController.Job q.N L → ℕ) →
                    (CodedSorting.RadixController.Job q.N L → List ℕ) →
                      (CodedSorting.RadixController.Job q.N L → CodedSorting.CommonMSDRoutine.Routine q A) →
                        CodedSorting.RadixController.Components Normal q L A
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonMSDRoutine.Routine](../../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-3f09655e0addc3cb"></a>
## `CodedSorting.RadixController.Components.reader`

读取 `CodedSorting.RadixController.Components` 的 `reader` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L55)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A : ℕ} → CodedSorting.RadixController.Components Normal q L A → Fin q.inventory.readers
```

**定义**

```lean
fun Normal q L A self => self.1
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)

**基础库名称**

`Nat`, `Fin`

<a id="def-99514af40dcc92de"></a>
## `CodedSorting.RadixController.Components.normal`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean#L56)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  {q : CodedSorting.CommonSortingNormalization.Configuration} {L A : ℕ},
  CodedSorting.RadixController.Components Normal q L A → Normal q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)

**基础库名称**

`Nat`

<a id="def-135a8c8ab84d1f53"></a>
## `CodedSorting.RadixController.Components.exponent`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean#L57)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  {q : CodedSorting.CommonSortingNormalization.Configuration} {L A : ℕ},
  CodedSorting.RadixController.Components Normal q L A → 2 ≤ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-dbce9da1ee6af2a8"></a>
## `CodedSorting.RadixController.Components.source`

读取 `CodedSorting.RadixController.Components` 的 `source` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L58)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A : ℕ} → CodedSorting.RadixController.Components Normal q L A → ℕ
```

**定义**

```lean
fun Normal q L A self => self.4
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)

**基础库名称**

`Nat`

<a id="def-a95e0bf05241caec"></a>
## `CodedSorting.RadixController.Components.stack`

读取 `CodedSorting.RadixController.Components` 的 `stack` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L59)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A : ℕ} → CodedSorting.RadixController.Components Normal q L A → ℕ
```

**定义**

```lean
fun Normal q L A self => self.5
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)

**基础库名称**

`Nat`

<a id="def-783554a77b3fbf5d"></a>
## `CodedSorting.RadixController.Components.buffer`

读取 `CodedSorting.RadixController.Components` 的 `buffer` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L60)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A : ℕ} → CodedSorting.RadixController.Components Normal q L A → CodedSorting.RadixController.Job q.N L → ℕ
```

**定义**

```lean
fun Normal q L A self => self.6
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Nat`

<a id="def-bd8fd007739a669a"></a>
## `CodedSorting.RadixController.Components.limit`

读取 `CodedSorting.RadixController.Components` 的 `limit` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L61)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A : ℕ} → CodedSorting.RadixController.Components Normal q L A → CodedSorting.RadixController.Job q.N L → ℕ
```

**定义**

```lean
fun Normal q L A self => self.7
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Nat`

<a id="def-5e9c18ba0d4274f8"></a>
## `CodedSorting.RadixController.Components.directories`

读取 `CodedSorting.RadixController.Components` 的 `directories` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L62)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A : ℕ} → CodedSorting.RadixController.Components Normal q L A → CodedSorting.RadixController.Job q.N L → List ℕ
```

**定义**

```lean
fun Normal q L A self => self.8
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`List`, `Nat`

<a id="def-80176d7ff3e59321"></a>
## `CodedSorting.RadixController.Components.node`

读取 `CodedSorting.RadixController.Components` 的 `node` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Control.lean#L63)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L → CodedSorting.CommonMSDRoutine.Routine q A
```

**定义**

```lean
fun Normal q L A self => self.9
```

**继续展开**

- [CodedSorting.CommonMSDRoutine.Routine](../../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Nat`

<a id="def-50b80b4dabab5327"></a>
## `CodedSorting.RadixController.Tag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L67)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → Type
```

**定义**

```lean
fun N L A K => CodedSorting.RadixController.Job N L × Fin 7 × Fin A × Fin (K + 1) × Fin (N + 1) × Fin (N + 1)
```

**继续展开**

- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-4c216c264e72a338"></a>
## `CodedSorting.RadixController.tagCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L71)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun N L A K => Fintype.card (CodedSorting.RadixController.Tag N L A K)
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fintype.card`, `instOfNatNat`, `Fin.fintype`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-3360707b00d06e6d"></a>
## `CodedSorting.RadixController.tagEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L72)

**类型**

```lean
(N L A K : ℕ) → CodedSorting.RadixController.Tag N L A K ≃ Fin (CodedSorting.RadixController.tagCount N L A K)
```

**定义**

```lean
fun N L A K => Fintype.equivFin (CodedSorting.RadixController.Tag N L A K)
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.tagCount](Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Equiv`, `instOfNatNat`, `Fin.fintype`, `Fintype.equivFin`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-c079a7796e14c34b"></a>
## `CodedSorting.RadixController.state`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L74)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L A K : ℕ} →
    CodedSorting.RadixController.Job q.N L →
      Fin 7 → Fin A → Fin (K + 1) → Fin (q.N + 1) → Fin (q.N + 1) → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {q} {L A K} j phase inner key cursor count => (j, phase, inner, key, cursor, count)
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Prod.mk`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-db84d33dd1cddc46"></a>
## `CodedSorting.RadixController.visit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L77)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c j => CodedSorting.RadixController.state j 0 (c.node j).entry 0 0 0
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Components.node](Control.definitions.md#def-80176d7ff3e59321)
- [CodedSorting.RadixController.state](Control.definitions.md#def-c079a7796e14c34b)
- [CodedSorting.RadixController.visit._proof_4](Control.definitions.md#def-9cdfe3992b736b2e)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.visit._proof_3](Control.definitions.md#def-eb616259008a27c7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.visit._proof_5](Control.definitions.md#def-52485cfb421a423c)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-44fcc60a8800f797"></a>
## `CodedSorting.RadixController.nodeState`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L79)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L → Fin A → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c j inner => CodedSorting.RadixController.state j 1 inner 0 0 0
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.state](Control.definitions.md#def-c079a7796e14c34b)
- [CodedSorting.RadixController.visit._proof_4](Control.definitions.md#def-9cdfe3992b736b2e)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.visit._proof_3](Control.definitions.md#def-eb616259008a27c7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.visit._proof_5](Control.definitions.md#def-52485cfb421a423c)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-ce73f0e7743a6be0"></a>
## `CodedSorting.RadixController.counting`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L81)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L →
          Fin (K + 1) → Fin (q.N + 1) → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c j key cursor => CodedSorting.RadixController.state j 2 (c.node j).entry key cursor 0
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Components.node](Control.definitions.md#def-80176d7ff3e59321)
- [CodedSorting.RadixController.state](Control.definitions.md#def-c079a7796e14c34b)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.visit._proof_3](Control.definitions.md#def-eb616259008a27c7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.visit._proof_5](Control.definitions.md#def-52485cfb421a423c)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-38966574aa774d6e"></a>
## `CodedSorting.RadixController.pushing`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L84)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L →
          Fin (K + 1) → Fin (q.N + 1) → Fin (q.N + 1) → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c j key cursor count =>
  CodedSorting.RadixController.state j 3 (c.node j).entry key cursor count
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Components.node](Control.definitions.md#def-80176d7ff3e59321)
- [CodedSorting.RadixController.state](Control.definitions.md#def-c079a7796e14c34b)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.visit._proof_3](Control.definitions.md#def-eb616259008a27c7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-f8e91a40b83158fd"></a>
## `CodedSorting.RadixController.leaf`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L87)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c j => CodedSorting.RadixController.state j 4 (c.node j).entry 0 0 0
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Components.node](Control.definitions.md#def-80176d7ff3e59321)
- [CodedSorting.RadixController.state](Control.definitions.md#def-c079a7796e14c34b)
- [CodedSorting.RadixController.visit._proof_4](Control.definitions.md#def-9cdfe3992b736b2e)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.visit._proof_3](Control.definitions.md#def-eb616259008a27c7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.visit._proof_5](Control.definitions.md#def-52485cfb421a423c)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-1a89477201c99aff"></a>
## `CodedSorting.RadixController.returning`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L89)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c j => CodedSorting.RadixController.state j 5 (c.node j).entry 0 0 0
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Components.node](Control.definitions.md#def-80176d7ff3e59321)
- [CodedSorting.RadixController.state](Control.definitions.md#def-c079a7796e14c34b)
- [CodedSorting.RadixController.visit._proof_4](Control.definitions.md#def-9cdfe3992b736b2e)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.visit._proof_3](Control.definitions.md#def-eb616259008a27c7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.visit._proof_5](Control.definitions.md#def-52485cfb421a423c)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-94eed47482c67241"></a>
## `CodedSorting.RadixController.halted`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L91)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c j => CodedSorting.RadixController.state j 6 (c.node j).entry 0 0 0
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Components.node](Control.definitions.md#def-80176d7ff3e59321)
- [CodedSorting.RadixController.state](Control.definitions.md#def-c079a7796e14c34b)
- [CodedSorting.RadixController.visit._proof_4](Control.definitions.md#def-9cdfe3992b736b2e)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.visit._proof_3](Control.definitions.md#def-eb616259008a27c7)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.visit._proof_5](Control.definitions.md#def-52485cfb421a423c)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-c9459046ef42cf6b"></a>
## `CodedSorting.RadixController.child`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L94)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L : ℕ} →
    CodedSorting.RadixController.Job q.N L → Fin (q.N + 1) → Fin (q.N + 1) → CodedSorting.RadixController.Job q.N L
```

**定义**

```lean
fun {q} {L} j cursor count =>
  (CodedSorting.RadixController.bounded L (CodedSorting.RadixController.level j - 1),
    CodedSorting.RadixController.bounded q.N (CodedSorting.RadixController.offset j + ↑cursor), count,
    CodedSorting.RadixController.bounded L (CodedSorting.RadixController.depth j + 1))
```

**继续展开**

- [CodedSorting.RadixController.bounded](Control.definitions.md#def-f6b6bc34e6e28edd)
- [CodedSorting.RadixController.offset](Control.definitions.md#def-99ba717ce1accffc)
- [CodedSorting.RadixController.depth](Control.definitions.md#def-6695bf5c325da18a)
- [CodedSorting.RadixController.level](Control.definitions.md#def-c5e0bd5ef519c49d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`HSub.hSub`, `Prod.mk`, `instSubNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-87f1f558a3d26b56"></a>
## `CodedSorting.RadixController.resume`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L97)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Job q.N L →
          Fin (K + 1) → Fin (q.N + 1) → Fin (q.N + 1) → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c j key cursor count =>
  CodedSorting.RadixController.counting c j (CodedSorting.RadixController.bounded K (↑key + 1))
    (CodedSorting.RadixController.bounded q.N (↑cursor + ↑count))
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.bounded](Control.definitions.md#def-f6b6bc34e6e28edd)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.counting](Control.definitions.md#def-ce73f0e7743a6be0)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-e6ba4b514ac09b38"></a>
## `CodedSorting.RadixController.LeafFits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L101)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixController.LocalSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {L A : ℕ} → CodedSorting.RadixController.Components Normal q L A → CodedSorting.RadixController.Job q.N L → Prop
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixController.LocalSorter Normal] {q} {L A} c j =>
  CodedSorting.RadixController.records j ≤ q.height ^ 2 ∧
    c.source +
            CodedSorting.PhysicalStreamCursor.blockCount q.block
              (3 * CodedSorting.RadixController.offset j + 3 * CodedSorting.RadixController.records j) +
          2 ≤
        c.buffer j ∧
      c.buffer j + CodedSorting.RadixController.LocalSorter.space q ⋯ (CodedSorting.RadixController.records j) ≤
          c.limit j ∧
        c.limit j ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.RadixController.offset](Control.definitions.md#def-99ba717ce1accffc)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.RadixController.Components.buffer](Control.definitions.md#def-783554a77b3fbf5d)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.RadixController.Components.source](Control.definitions.md#def-dbce9da1ee6af2a8)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LocalSorter.space](Control.definitions.md#def-6cf03463d6968e87)
- [CodedSorting.RadixController.records](Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.RadixController.Components.normal](Control.definitions.md#def-99514af40dcc92de)
- [CodedSorting.RadixController.Components.limit](Control.definitions.md#def-bd8fd007739a669a)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-f17341a81fdcc792"></a>
## `CodedSorting.RadixController.instDecidableLeafFits`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L107)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixController.LocalSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {L A : ℕ} →
        (c : CodedSorting.RadixController.Components Normal q L A) →
          (j : CodedSorting.RadixController.Job q.N L) → Decidable (CodedSorting.RadixController.LeafFits c j)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixController.LocalSorter Normal] {q} {L A} c j => id inferInstance
```

**继续展开**

- [CodedSorting.RadixController.offset](Control.definitions.md#def-99ba717ce1accffc)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.RadixController.Components.buffer](Control.definitions.md#def-783554a77b3fbf5d)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.RadixController.Components.source](Control.definitions.md#def-dbce9da1ee6af2a8)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LocalSorter.space](Control.definitions.md#def-6cf03463d6968e87)
- [CodedSorting.RadixController.LeafFits](Control.definitions.md#def-e6ba4b514ac09b38)
- [CodedSorting.RadixController.records](Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.RadixController.Components.normal](Control.definitions.md#def-99514af40dcc92de)
- [CodedSorting.RadixController.Components.limit](Control.definitions.md#def-bd8fd007739a669a)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Decidable`, `Monoid.toNatPow`, `inferInstance`, `id`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `And`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `instDecidableAnd`, `OfNat.ofNat`, `Nat.decLe`, `instHMul`

<a id="def-84790e859a2b1949"></a>
## `CodedSorting.RadixController.leafCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L111)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixController.LocalSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {L A : ℕ} →
        CodedSorting.RadixController.Components Normal q L A →
          CodedSorting.RadixController.Job q.N L → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixController.LocalSorter Normal] {q} {L A} c j =>
  if h : CodedSorting.RadixController.LeafFits c j then
    (CodedSorting.RadixController.LocalSorter.program q c.reader ⋯ (CodedSorting.RadixController.records j) ⋯ ⋯ c.source
        (CodedSorting.RadixController.offset j) (c.buffer j) (c.limit j) ⋯ ⋯ ⋯).instructions
  else []
```

**继续展开**

- [CodedSorting.RadixController.LocalSorter.program](Control.definitions.md#def-76093a467738e684)
- [CodedSorting.RadixController.leafCode._proof_8](Control.definitions.md#def-db483f2583391e27)
- [CodedSorting.RadixController.leafCode._proof_7](Control.definitions.md#def-24ce9044a946881f)
- [CodedSorting.RadixController.offset](Control.definitions.md#def-99ba717ce1accffc)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonRecordInterval.Program.instructions](../../../../Shared/Records/RecordOperations.definitions.md#def-16d82df30e410adf)
- [CodedSorting.KeyRecordWords.Record](../../../../Shared/Records/KeyRecordWords.definitions.md#def-54535a8f09e69570)
- [CodedSorting.RadixController.Components.exponent](Control.definitions.md#def-135a8c8ab84d1f53)
- [CodedSorting.RadixController.Components.buffer](Control.definitions.md#def-783554a77b3fbf5d)
- [CodedSorting.RadixController.Components.source](Control.definitions.md#def-dbce9da1ee6af2a8)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LeafFits](Control.definitions.md#def-e6ba4b514ac09b38)
- [CodedSorting.RadixController.leafCode._proof_9](Control.definitions.md#def-3086301a8cc9582a)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.RadixController.records](Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.RadixController.instDecidableLeafFits](Control.definitions.md#def-f17341a81fdcc792)
- [CodedSorting.Columnsort.sortColumn](../../../Local/Columnsort/Columnsort.definitions.md#def-96b08db6c27899aa)
- [CodedSorting.RadixController.Components.reader](Control.definitions.md#def-3f09655e0addc3cb)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Components.normal](Control.definitions.md#def-99514af40dcc92de)
- [CodedSorting.ResidentLeafSort.recordOrder](../../../Local/Framework/ResidentLeafSort.definitions.md#def-d2b11bb114609f13)
- [CodedSorting.RadixController.Components.limit](Control.definitions.md#def-bd8fd007739a669a)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.leafCode._proof_6](Control.definitions.md#def-d1eb0bca6e272ba2)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`dite`, `List`, `Nat`, `Not`, `List.nil`

<a id="def-baa7b3c411a9f662"></a>
## `CodedSorting.RadixController.body`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L117)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixController.LocalSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {L A K : ℕ} →
        CodedSorting.RadixController.Components Normal q L A →
          CodedSorting.RadixController.Tag q.N L A K → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixController.LocalSorter Normal] {q} {L A K} c t =>
  let j := t.1;
  let phase := ↑t.2.1;
  if phase = 1 then (c.node j).body t.2.2.1
  else
    if phase = 2 then
      if ↑t.2.2.2.1 < K then CodedSorting.CommonMSDChildCount.code q (c.directories j) ↑t.2.2.2.1 else []
    else
      if phase = 3 then
        CodedSorting.CommonMSDStack.pushCode q c.stack (CodedSorting.RadixController.depth j)
          ↑((CodedSorting.RadixController.tagEquiv q.N L A K)
              (CodedSorting.RadixController.resume c j t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2))
      else
        if phase = 4 then CodedSorting.RadixController.leafCode c j
        else
          if phase = 5 then
            if CodedSorting.RadixController.depth j = 0 then []
            else CodedSorting.CommonMSDStack.popCode q c.stack (CodedSorting.RadixController.depth j - 1)
          else []
```

**继续展开**

- [CodedSorting.CommonMSDChildCount.code](../../Framework/Directory.definitions.md#def-9c5b1d8ac2d0db62)
- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Components.node](Control.definitions.md#def-80176d7ff3e59321)
- [CodedSorting.RadixController.tagCount](Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.CommonMSDStack.popCode](../../Framework/StackFrames.definitions.md#def-46134f2140237a51)
- [CodedSorting.CommonMSDRoutine.Routine.body](../../Framework/Routine.definitions.md#def-b2d665a14c5d2a8a)
- [CodedSorting.RadixController.depth](Control.definitions.md#def-6695bf5c325da18a)
- [CodedSorting.CommonMSDStack.pushCode](../../Framework/StackFrames.definitions.md#def-51f30c29b49e7b20)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.Components.directories](Control.definitions.md#def-5e9c18ba0d4274f8)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.RadixController.tagEquiv](Control.definitions.md#def-3360707b00d06e6d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Components.stack](Control.definitions.md#def-a95e0bf05241caec)
- [CodedSorting.RadixController.leafCode](Control.definitions.md#def-84790e859a2b1949)
- [CodedSorting.RadixController.resume](Control.definitions.md#def-87f1f558a3d26b56)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Equiv.instFunLike`, `HSub.hSub`, `Equiv`, `instSubNat`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `List`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `List.nil`, `ite`

<a id="def-6193f01fedb13428"></a>
## `CodedSorting.RadixController.next`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L129)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  {q : CodedSorting.CommonSortingNormalization.Configuration} →
    {L A K : ℕ} →
      CodedSorting.RadixController.Components Normal q L A →
        CodedSorting.RadixController.Tag q.N L A K →
          CodedSorting.CommonLeafProgram.RAM q → CodedSorting.RadixController.Tag q.N L A K
```

**定义**

```lean
fun {Normal} {q} {L A K} c t ram =>
  let j := t.1;
  let phase := ↑t.2.1;
  if phase = 0 then
    if CodedSorting.RadixController.level j = 0 then CodedSorting.RadixController.returning c j
    else
      if CodedSorting.RadixController.records j ≤ q.height ^ 2 then CodedSorting.RadixController.leaf c j
      else CodedSorting.RadixController.nodeState c j (c.node j).entry
  else
    if phase = 1 then
      if (c.node j).terminal t.2.2.1 = true then CodedSorting.RadixController.counting c j 0 0
      else CodedSorting.RadixController.nodeState c j ((c.node j).successor t.2.2.1 ram)
    else
      if phase = 2 then
        if ↑t.2.2.2.1 < K then
          let count :=
            CodedSorting.RadixController.bounded q.N
              (CodedSorting.CommonMSDChildCount.acc q (CodedSorting.CommonSortingNormalization.unpack ram));
          if ↑count = 0 then CodedSorting.RadixController.resume c j t.2.2.2.1 t.2.2.2.2.1 count
          else CodedSorting.RadixController.pushing c j t.2.2.2.1 t.2.2.2.2.1 count
        else CodedSorting.RadixController.returning c j
      else
        if phase = 3 then
          CodedSorting.RadixController.visit c (CodedSorting.RadixController.child j t.2.2.2.2.1 t.2.2.2.2.2)
        else
          if phase = 4 then CodedSorting.RadixController.returning c j
          else
            if phase = 5 then
              if CodedSorting.RadixController.depth j = 0 then CodedSorting.RadixController.halted c j
              else
                (CodedSorting.RadixController.tagEquiv q.N L A K).symm
                  ⟨CodedSorting.CommonMSDStack.loaded q (CodedSorting.CommonSortingNormalization.unpack ram) %
                      CodedSorting.RadixController.tagCount q.N L A K,
                    ⋯⟩
            else t
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.RadixController.returning](Control.definitions.md#def-1a89477201c99aff)
- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.Components.node](Control.definitions.md#def-80176d7ff3e59321)
- [CodedSorting.CommonMSDRoutine.Routine.terminal](../../Framework/Routine.definitions.md#def-d011f4b47a3678f6)
- [CodedSorting.RadixController.tagCount](Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.RadixController.bounded](Control.definitions.md#def-f6b6bc34e6e28edd)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonMSDStack.loaded](../../Framework/StackFrames.definitions.md#def-dcc5f7389307e9a0)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.RadixController.visit._proof_4](Control.definitions.md#def-9cdfe3992b736b2e)
- [CodedSorting.RadixController.depth](Control.definitions.md#def-6695bf5c325da18a)
- [CodedSorting.CommonMSDRoutine.Routine.entry](../../Framework/Routine.definitions.md#def-647a853c84302453)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonMSDRoutine.Routine.successor](../../Framework/Routine.definitions.md#def-e146f1f041d7ef5a)
- [CodedSorting.RadixController.level](Control.definitions.md#def-c5e0bd5ef519c49d)
- [CodedSorting.RadixController.pushing](Control.definitions.md#def-38966574aa774d6e)
- [CodedSorting.CommonMSDChildCount.acc](../../Framework/Directory.definitions.md#def-6019ebd193440039)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.RadixController.visit](Control.definitions.md#def-db84d33dd1cddc46)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.records](Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.RadixController.leaf](Control.definitions.md#def-f8e91a40b83158fd)
- [CodedSorting.RadixController.tagEquiv](Control.definitions.md#def-3360707b00d06e6d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.child](Control.definitions.md#def-c9459046ef42cf6b)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.RadixController.nodeState](Control.definitions.md#def-44fcc60a8800f797)
- [CodedSorting.RadixController.halted](Control.definitions.md#def-94eed47482c67241)
- [CodedSorting.RadixController.counting](Control.definitions.md#def-ce73f0e7743a6be0)
- [CodedSorting.RadixController.resume](Control.definitions.md#def-87f1f558a3d26b56)
- [CodedSorting.RadixController.visit._proof_5](Control.definitions.md#def-52485cfb421a423c)
- [CodedSorting.RadixController.next._proof_10](Control.definitions.md#def-06f56a0399c12004)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `Fin.instOfNat`, `Equiv`, `Nat.instMod`, `instDecidableEqBool`, `instHMod`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `Bool.true`, `instHAdd`, `HMod.hMod`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Bool`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instHPow`, `instLTNat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `Nat.decLe`, `ite`

<a id="def-f068cf36fb9644b1"></a>
## `CodedSorting.RadixController.terminal`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L181)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {L A K : ℕ} → CodedSorting.RadixController.Tag q.N L A K → Bool
```

**定义**

```lean
fun {q} {L A K} t => decide (↑t.2.1 = 6)
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`instOfNatNat`, `Fin.val`, `Prod.fst`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Bool`, `instAddNat`, `instDecidableEqNat`, `Prod`, `OfNat.ofNat`, `Fin`, `Decidable.decide`, `Eq`, `Prod.snd`

<a id="def-322bc5d4a2146055"></a>
## `CodedSorting.RadixController.routine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Control.lean#L189)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixController.LocalSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {L A K : ℕ} →
        CodedSorting.RadixController.Components Normal q L A →
          CodedSorting.RadixController.Job q.N L →
            CodedSorting.CommonMSDRoutine.Routine q (CodedSorting.RadixController.tagCount q.N L A K)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixController.LocalSorter Normal] {q} {L A K} c root =>
  { entry := (CodedSorting.RadixController.tagEquiv q.N L A K) (CodedSorting.RadixController.visit c root),
    body := fun tag => CodedSorting.RadixController.body c ((CodedSorting.RadixController.tagEquiv q.N L A K).symm tag),
    next := fun tag ram =>
      (CodedSorting.RadixController.tagEquiv q.N L A K)
        (CodedSorting.RadixController.next c ((CodedSorting.RadixController.tagEquiv q.N L A K).symm tag) ram),
    terminal := fun tag =>
      CodedSorting.RadixController.terminal ((CodedSorting.RadixController.tagEquiv q.N L A K).symm tag),
    safe := ⋯, terminal_empty := ⋯ }
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.tagCount](Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.RadixController.next](Control.definitions.md#def-6193f01fedb13428)
- [CodedSorting.RadixController.routine._proof_12](Control.definitions.md#def-02c37ce898683e16)
- [CodedSorting.RadixController.terminal](Control.definitions.md#def-f068cf36fb9644b1)
- [CodedSorting.CommonMSDRoutine.Routine](../../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.RadixController.visit](Control.definitions.md#def-db84d33dd1cddc46)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDRoutine.Routine.mk](../../Framework/Routine.definitions.md#def-e820937768ee9afd)
- [CodedSorting.RadixController.tagEquiv](Control.definitions.md#def-3360707b00d06e6d)
- [CodedSorting.RadixController.routine._proof_11](Control.definitions.md#def-13b65bfd235e1896)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)
- [CodedSorting.RadixController.body](Control.definitions.md#def-baa7b3c411a9f662)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Nat`, `Equiv.symm`, `Fin`, `DFunLike.coe`

<a id="def-2f540cac2df4a324"></a>
## `CodedSorting.RadixController.bounded._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ (N n : ℕ), n % (N + 1) < N + 1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMod`, `instHMod`, `instOfNatNat`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-d1eb0bca6e272ba2"></a>
## `CodedSorting.RadixController.leafCode._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixController.LocalSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {L A : ℕ} (c : CodedSorting.RadixController.Components Normal q L A) (j : CodedSorting.RadixController.Job q.N L),
  CodedSorting.RadixController.LeafFits c j → CodedSorting.RadixController.records j ≤ q.height ^ 2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LeafFits](Control.definitions.md#def-e6ba4b514ac09b38)
- [CodedSorting.RadixController.records](Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-24ce9044a946881f"></a>
## `CodedSorting.RadixController.leafCode._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixController.LocalSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {L A : ℕ} (c : CodedSorting.RadixController.Components Normal q L A) (j : CodedSorting.RadixController.Job q.N L),
  CodedSorting.RadixController.LeafFits c j →
    c.source +
          CodedSorting.PhysicalStreamCursor.blockCount q.block
            (3 * CodedSorting.RadixController.offset j + 3 * CodedSorting.RadixController.records j) +
        2 ≤
      c.buffer j
```

**继续展开**

- [CodedSorting.RadixController.offset](Control.definitions.md#def-99ba717ce1accffc)
- [CodedSorting.RadixController.Components.buffer](Control.definitions.md#def-783554a77b3fbf5d)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.RadixController.Components.source](Control.definitions.md#def-dbce9da1ee6af2a8)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LeafFits](Control.definitions.md#def-e6ba4b514ac09b38)
- [CodedSorting.RadixController.records](Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-db483f2583391e27"></a>
## `CodedSorting.RadixController.leafCode._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixController.LocalSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {L A : ℕ} (c : CodedSorting.RadixController.Components Normal q L A) (j : CodedSorting.RadixController.Job q.N L),
  CodedSorting.RadixController.LeafFits c j →
    c.buffer j + CodedSorting.RadixController.LocalSorter.space q ⋯ (CodedSorting.RadixController.records j) ≤ c.limit j
```

**继续展开**

- [CodedSorting.RadixController.Components.buffer](Control.definitions.md#def-783554a77b3fbf5d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LocalSorter.space](Control.definitions.md#def-6cf03463d6968e87)
- [CodedSorting.RadixController.LeafFits](Control.definitions.md#def-e6ba4b514ac09b38)
- [CodedSorting.RadixController.records](Control.definitions.md#def-40e139ab4c013c5d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Components.normal](Control.definitions.md#def-99514af40dcc92de)
- [CodedSorting.RadixController.Components.limit](Control.definitions.md#def-bd8fd007739a669a)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-3086301a8cc9582a"></a>
## `CodedSorting.RadixController.leafCode._proof_9`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixController.LocalSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {L A : ℕ} (c : CodedSorting.RadixController.Components Normal q L A) (j : CodedSorting.RadixController.Job q.N L),
  CodedSorting.RadixController.LeafFits c j → c.limit j ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixController.LeafFits](Control.definitions.md#def-e6ba4b514ac09b38)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.Components.limit](Control.definitions.md#def-bd8fd007739a669a)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.Job](Control.definitions.md#def-5217c2ac1a71759a)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-06f56a0399c12004"></a>
## `CodedSorting.RadixController.next._proof_10`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {L A K : ℕ},
  CodedSorting.RadixController.Tag q.N L A K →
    ∀ (ram : CodedSorting.CommonLeafProgram.RAM q),
      CodedSorting.CommonMSDStack.loaded q (CodedSorting.CommonSortingNormalization.unpack ram) %
          CodedSorting.RadixController.tagCount q.N L A K <
        CodedSorting.RadixController.tagCount q.N L A K
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.tagCount](Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonMSDStack.loaded](../../Framework/StackFrames.definitions.md#def-dcc5f7389307e9a0)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`

<a id="def-13b65bfd235e1896"></a>
## `CodedSorting.RadixController.routine._proof_11`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixController.LocalSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {L A K : ℕ} (c : CodedSorting.RadixController.Components Normal q L A)
  (tag : Fin (CodedSorting.RadixController.tagCount q.N L A K)),
  ∀ i ∈ CodedSorting.RadixController.body c ((CodedSorting.RadixController.tagEquiv q.N L A K).symm tag),
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.tagCount](Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.RadixController.tagEquiv](Control.definitions.md#def-3360707b00d06e6d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.body](Control.definitions.md#def-baa7b3c411a9f662)

**基础库名称**

`Equiv.instFunLike`, `Membership.mem`, `Equiv`, `List`, `List.instMembership`, `Nat`, `Equiv.symm`, `Fin`, `DFunLike.coe`

<a id="def-02c37ce898683e16"></a>
## `CodedSorting.RadixController.routine._proof_12`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixController.LocalSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {L A K : ℕ} (c : CodedSorting.RadixController.Components Normal q L A)
  (tag : Fin (CodedSorting.RadixController.tagCount q.N L A K)),
  CodedSorting.RadixController.terminal ((CodedSorting.RadixController.tagEquiv q.N L A K).symm tag) = true →
    CodedSorting.RadixController.body c ((CodedSorting.RadixController.tagEquiv q.N L A K).symm tag) = []
```

**继续展开**

- [CodedSorting.RadixController.Tag](Control.definitions.md#def-50b80b4dabab5327)
- [CodedSorting.RadixController.tagCount](Control.definitions.md#def-4c216c264e72a338)
- [CodedSorting.RadixController.terminal](Control.definitions.md#def-f068cf36fb9644b1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.RadixController.tagEquiv](Control.definitions.md#def-3360707b00d06e6d)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixController.Components](Control.definitions.md#def-072999d65dc88a81)
- [CodedSorting.RadixController.LocalSorter](Control.definitions.md#def-3a0b99259a2e477e)
- [CodedSorting.RadixController.body](Control.definitions.md#def-baa7b3c411a9f662)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Bool.true`, `List`, `Nat`, `Bool`, `Equiv.symm`, `Fin`, `Eq`, `DFunLike.coe`, `List.nil`

<a id="def-eb616259008a27c7"></a>
## `CodedSorting.RadixController.visit._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
NeZero (6 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-9cdfe3992b736b2e"></a>
## `CodedSorting.RadixController.visit._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {K : ℕ}, NeZero (K + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-52485cfb421a423c"></a>
## `CodedSorting.RadixController.visit._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Control.lean)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration}, NeZero (q.N + 1)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`
