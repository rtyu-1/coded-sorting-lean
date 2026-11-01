# Pass 的定义

[源码](Pass.lean) · [主定理导读](../../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-adf56b3fbfdf240f"></a>
## `CodedSorting.RadixNode.ChunkSorter`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Pass.lean#L12)

**类型**

```lean
(CodedSorting.CommonSortingNormalization.Configuration → Prop) → Type
```

**继续展开**

- [CodedSorting.RadixNode.ChunkSorter.mk](Pass.definitions.md#def-950b58602165129a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

<a id="def-950b58602165129a"></a>
## `CodedSorting.RadixNode.ChunkSorter.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Pass.lean#L12)

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
                  2 ≤ q.exponent →
                    (source buffer limit : ℕ) →
                      source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
                        buffer + space q normal n ≤ limit →
                          limit ≤ q.N ^ q.exponent →
                            3 * CodedSorting.CommonMSDChunks.paddedSize q n < (2 ^ q.w) ^ q.digits →
                              CodedSorting.CommonRecordProgram.Program q n source buffer limit
                                (CodedSorting.CommonMSDChunks.operation q n)) →
        (∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (reader : Fin q.inventory.readers)
            (normal : Normal q) (n : ℕ) (he : 2 ≤ q.exponent) (source buffer limit : ℕ)
            (hs : source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer)
            (hw : buffer + space q normal n ≤ limit) (hl : limit ≤ q.N ^ q.exponent)
            (hd : 3 * CodedSorting.CommonMSDChunks.paddedSize q n < (2 ^ q.w) ^ q.digits),
            (program q reader normal n he source buffer limit hs hw hl hd).charge ≤ charge q n) →
          CodedSorting.RadixNode.ChunkSorter Normal
```

**继续展开**

- [CodedSorting.CommonMSDChunks.operation](../../Framework/Chunks.definitions.md#def-95900b6568de0791)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDChunks.paddedSize](../../Framework/Chunks.definitions.md#def-1c4eec1b43cf54c2)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Program.charge](../../../../Shared/Records/RecordOperations.definitions.md#def-ab509acf69c03316)
- [CodedSorting.CommonRecordProgram.Program](../../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-fb9ab027a5e6f914"></a>
## `CodedSorting.RadixNode.ChunkSorter.space`

读取 `CodedSorting.RadixNode.ChunkSorter` 的 `space` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Pass.lean#L13)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [self : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) → Normal q → ℕ → ℕ
```

**定义**

```lean
fun Normal [self : CodedSorting.RadixNode.ChunkSorter Normal] => self.1
```

**继续展开**

- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-c23e3a41d771c4d8"></a>
## `CodedSorting.RadixNode.ChunkSorter.program`

读取 `CodedSorting.RadixNode.ChunkSorter` 的 `program` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Pass.lean#L15)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [self : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) →
      Fin q.inventory.readers →
        (normal : Normal q) →
          (n : ℕ) →
            2 ≤ q.exponent →
              (source buffer limit : ℕ) →
                source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ buffer →
                  buffer + CodedSorting.RadixNode.ChunkSorter.space q normal n ≤ limit →
                    limit ≤ q.N ^ q.exponent →
                      3 * CodedSorting.CommonMSDChunks.paddedSize q n < (2 ^ q.w) ^ q.digits →
                        CodedSorting.CommonRecordProgram.Program q n source buffer limit
                          (CodedSorting.CommonMSDChunks.operation q n)
```

**定义**

```lean
fun Normal [self : CodedSorting.RadixNode.ChunkSorter Normal] => self.3
```

**继续展开**

- [CodedSorting.RadixNode.ChunkSorter.space](Pass.definitions.md#def-fb9ab027a5e6f914)
- [CodedSorting.CommonMSDChunks.operation](../../Framework/Chunks.definitions.md#def-95900b6568de0791)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDChunks.paddedSize](../../Framework/Chunks.definitions.md#def-1c4eec1b43cf54c2)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonRecordProgram.Program](../../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMax_mathlib`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Max.max`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-5d7e0afd280f2f9d"></a>
## `CodedSorting.RadixNode.Pass.directory`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L45)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q buffer => buffer + CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)
```

**继续展开**

- [CodedSorting.CommonRecordProgram.recordBlocks](../../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonMSDChunks.chunkSize](../../Framework/Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-3007be7658efed0e"></a>
## `CodedSorting.RadixNode.Pass.Resources`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Pass.lean#L48)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) → Normal q → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.RadixNode.Pass.Resources.mk](Pass.definitions.md#def-bcd7e0187e2f4441)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-bcd7e0187e2f4441"></a>
## `CodedSorting.RadixNode.Pass.Resources.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Pass.lean#L48)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {hnormal : Normal q} →
        {n K : ℕ} →
          (source buffer limit : ℕ) →
            2 ≤ q.exponent →
              source + CodedSorting.CommonRecordProgram.recordBlocks q n + 2 ≤ buffer →
                buffer + CodedSorting.RadixNode.ChunkSorter.space q hnormal n ≤ limit →
                  CodedSorting.RadixNode.Pass.directory q buffer +
                        CodedSorting.CommonMSDChunks.chunkCount q n * CodedSorting.CommonMSDDirectory.blocks q K ≤
                      limit →
                    limit ≤ q.N ^ q.exponent →
                      3 * CodedSorting.CommonMSDChunks.paddedSize q n < (2 ^ q.w) ^ q.digits →
                        CodedSorting.CommonRecordProgram.recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q) *
                              q.block <
                            (2 ^ q.w) ^ q.digits →
                          CodedSorting.RadixNode.Pass.Resources q hnormal n K
```

**继续展开**

- [CodedSorting.RadixNode.ChunkSorter.space](Pass.definitions.md#def-fb9ab027a5e6f914)
- [CodedSorting.RadixNode.Pass.directory](Pass.definitions.md#def-5d7e0afd280f2f9d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonMSDChunks.chunkSize](../../Framework/Chunks.definitions.md#def-35d8fa27ffc0c23b)
- [CodedSorting.CommonMSDChunks.chunkCount](../../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDChunks.paddedSize](../../Framework/Chunks.definitions.md#def-1c4eec1b43cf54c2)
- [CodedSorting.CommonMSDDirectory.blocks](../../Framework/Directory.definitions.md#def-2a36fe66dfedd827)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-c21ef7c63575f8b9"></a>
## `CodedSorting.RadixNode.Pass.Resources.source`

读取 `CodedSorting.RadixNode.Pass.Resources` 的 `source` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Pass.lean#L49)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {hnormal : Normal q} → {n K : ℕ} → CodedSorting.RadixNode.Pass.Resources q hnormal n K → ℕ
```

**定义**

```lean
fun Normal [CodedSorting.RadixNode.ChunkSorter Normal] q hnormal n K self => self.1
```

**继续展开**

- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`Nat`

<a id="def-39e4c91d6c7020f5"></a>
## `CodedSorting.RadixNode.Pass.Resources.buffer`

读取 `CodedSorting.RadixNode.Pass.Resources` 的 `buffer` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Pass.lean#L50)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {hnormal : Normal q} → {n K : ℕ} → CodedSorting.RadixNode.Pass.Resources q hnormal n K → ℕ
```

**定义**

```lean
fun Normal [CodedSorting.RadixNode.ChunkSorter Normal] q hnormal n K self => self.2
```

**继续展开**

- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`Nat`

<a id="def-7f32fd4b3e3bda8a"></a>
## `CodedSorting.RadixNode.Pass.Resources.limit`

读取 `CodedSorting.RadixNode.Pass.Resources` 的 `limit` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Pass.lean#L51)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    {q : CodedSorting.CommonSortingNormalization.Configuration} →
      {hnormal : Normal q} → {n K : ℕ} → CodedSorting.RadixNode.Pass.Resources q hnormal n K → ℕ
```

**定义**

```lean
fun Normal [CodedSorting.RadixNode.ChunkSorter Normal] q hnormal n K self => self.3
```

**继续展开**

- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`Nat`

<a id="def-9bb7b1f134a09648"></a>
## `CodedSorting.RadixNode.Pass.Resources.exponent`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Pass.lean#L52)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {hnormal : Normal q} {n K : ℕ}, CodedSorting.RadixNode.Pass.Resources q hnormal n K → 2 ≤ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-069892734404bd7d"></a>
## `CodedSorting.RadixNode.Pass.Resources.prepare_space`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Pass.lean#L54)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {hnormal : Normal q} {n K : ℕ} (self : CodedSorting.RadixNode.Pass.Resources q hnormal n K),
  self.buffer + CodedSorting.RadixNode.ChunkSorter.space q hnormal n ≤ self.limit
```

**继续展开**

- [CodedSorting.RadixNode.ChunkSorter.space](Pass.definitions.md#def-fb9ab027a5e6f914)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Pass.Resources.buffer](Pass.definitions.md#def-39e4c91d6c7020f5)
- [CodedSorting.RadixNode.Pass.Resources.limit](Pass.definitions.md#def-7f32fd4b3e3bda8a)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-1dd4f43d09aa58a1"></a>
## `CodedSorting.RadixNode.Pass.Resources.capacity`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Pass.lean#L56)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {hnormal : Normal q} {n K : ℕ} (self : CodedSorting.RadixNode.Pass.Resources q hnormal n K),
  self.limit ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.RadixNode.Pass.Resources.limit](Pass.definitions.md#def-7f32fd4b3e3bda8a)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-a5b47c3b5405f9c4"></a>
## `CodedSorting.RadixNode.Pass.Resources.descriptors`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Pass.lean#L57)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] {q : CodedSorting.CommonSortingNormalization.Configuration}
  {hnormal : Normal q} {n K : ℕ},
  CodedSorting.RadixNode.Pass.Resources q hnormal n K →
    3 * CodedSorting.CommonMSDChunks.paddedSize q n < (2 ^ q.w) ^ q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDChunks.paddedSize](../../Framework/Chunks.definitions.md#def-1c4eec1b43cf54c2)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `instHMul`

<a id="def-78ce131f7ae90c57"></a>
## `CodedSorting.RadixNode.Pass.chunks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L60)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) →
      Fin q.inventory.readers →
        {hnormal : Normal q} →
          {n K : ℕ} →
            (r : CodedSorting.RadixNode.Pass.Resources q hnormal n K) →
              CodedSorting.CommonRecordProgram.Program q n r.source r.buffer r.limit
                (CodedSorting.CommonMSDChunks.operation q n)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixNode.ChunkSorter Normal] q reader {hnormal} {n K} r =>
  CodedSorting.RadixNode.ChunkSorter.program q reader hnormal n ⋯ r.source r.buffer r.limit ⋯ ⋯ ⋯ ⋯
```

**继续展开**

- [CodedSorting.RadixNode.Pass.Resources.exponent](Pass.definitions.md#def-9bb7b1f134a09648)
- [CodedSorting.CommonMSDChunks.operation](../../Framework/Chunks.definitions.md#def-95900b6568de0791)
- [CodedSorting.RadixNode.Pass.Resources.source](Pass.definitions.md#def-c21ef7c63575f8b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.RadixNode.Pass.chunks._proof_2](Pass.definitions.md#def-907a95b7a74cf5ea)
- [CodedSorting.RadixNode.ChunkSorter.program](Pass.definitions.md#def-c23e3a41d771c4d8)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.RadixNode.Pass.Resources.descriptors](Pass.definitions.md#def-a5b47c3b5405f9c4)
- [CodedSorting.RadixNode.Pass.Resources.prepare_space](Pass.definitions.md#def-069892734404bd7d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Pass.Resources.capacity](Pass.definitions.md#def-1dd4f43d09aa58a1)
- [CodedSorting.RadixNode.Pass.Resources.buffer](Pass.definitions.md#def-39e4c91d6c7020f5)
- [CodedSorting.RadixNode.Pass.Resources.limit](Pass.definitions.md#def-7f32fd4b3e3bda8a)
- [CodedSorting.CommonRecordProgram.Program](../../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`Nat`, `Fin`

<a id="def-ae33f6204b403481"></a>
## `CodedSorting.RadixNode.Pass.withChunks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L66)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) →
      Fin q.inventory.readers →
        {hnormal : Normal q} →
          {n K : ℕ} →
            (r : CodedSorting.RadixNode.Pass.Resources q hnormal n K) →
              CodedSorting.CommonRecordProgram.Program q n r.source r.buffer r.limit
                  (CodedSorting.CommonMSDChunks.operation q n) →
                K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
                  (CodedSorting.WordControl.Word q.w → Fin K) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixNode.ChunkSorter Normal] q reader {hnormal} {n K} r p hfit key =>
  p.instructions ++
    CodedSorting.CommonMSDRowDirectoryBatch.code q reader hfit key (CodedSorting.CommonMSDChunkRows.row q n) r.source
      r.buffer (CodedSorting.RadixNode.Pass.directory q r.buffer)
      (List.finRange (CodedSorting.CommonMSDChunks.chunkCount q n))
```

**继续展开**

- [CodedSorting.CommonMSDChunks.operation](../../Framework/Chunks.definitions.md#def-95900b6568de0791)
- [CodedSorting.RadixNode.Pass.Resources.source](Pass.definitions.md#def-c21ef7c63575f8b9)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.RadixNode.Pass.directory](Pass.definitions.md#def-5d7e0afd280f2f9d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonMSDChunkRows.row](../../Framework/ChunkRows.definitions.md#def-663dba53ac045c88)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonMSDChunks.chunkCount](../../Framework/Chunks.definitions.md#def-8b64845cabf0750d)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonRecordProgram.Program.instructions](../../../../Shared/Records/RecordOperations.definitions.md#def-32d1da6b9bab0871)
- [CodedSorting.RadixNode.Pass.Resources.buffer](Pass.definitions.md#def-39e4c91d6c7020f5)
- [CodedSorting.CommonMSDRowDirectoryBatch.code](../../Framework/ChunkRows.definitions.md#def-d2d3b105572c444c)
- [CodedSorting.RadixNode.Pass.Resources.limit](Pass.definitions.md#def-7f32fd4b3e3bda8a)
- [CodedSorting.CommonRecordProgram.Program](../../../../Shared/Records/RecordOperations.definitions.md#def-a99dc947411e91e2)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `List.finRange`, `HAppend.hAppend`, `instHMul`

<a id="def-60f9edc8f7d0ef13"></a>
## `CodedSorting.RadixNode.Pass.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L75)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) →
      Fin q.inventory.readers →
        {hnormal : Normal q} →
          {n K : ℕ} →
            CodedSorting.RadixNode.Pass.Resources q hnormal n K →
              K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
                (CodedSorting.WordControl.Word q.w → Fin K) → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixNode.ChunkSorter Normal] q reader {hnormal} {n K} r hfit key =>
  CodedSorting.RadixNode.Pass.withChunks q reader r (CodedSorting.RadixNode.Pass.chunks q reader r) hfit key
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.RadixNode.Pass.chunks](Pass.definitions.md#def-78ce131f7ae90c57)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.RadixNode.Pass.withChunks](Pass.definitions.md#def-ae33f6204b403481)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-431fcc6584e74efd"></a>
## `CodedSorting.RadixNode.Controller.Tag`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L231)

**类型**

```lean
ℕ → ℕ → Type
```

**定义**

```lean
fun F C => Option (CodedSorting.CommonMSDGatherController.Tag F C)
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)

**基础库名称**

`Nat`, `Option`

<a id="def-6f5c701514f456da"></a>
## `CodedSorting.RadixNode.Controller.tagCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L232)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun F C => Fintype.card (CodedSorting.RadixNode.Controller.Tag F C)
```

**继续展开**

- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)

**基础库名称**

`Bool.fintype`, `Fintype.card`, `instOfNatNat`, `Fin.fintype`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Bool`, `instFintypeOption`, `instAddNat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-4e273179c697cf55"></a>
## `CodedSorting.RadixNode.Controller.tagEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L233)

**类型**

```lean
(F C : ℕ) → CodedSorting.RadixNode.Controller.Tag F C ≃ Fin (CodedSorting.RadixNode.Controller.tagCount F C)
```

**定义**

```lean
fun F C => Fintype.equivFin (CodedSorting.RadixNode.Controller.Tag F C)
```

**继续展开**

- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.RadixNode.Controller.tagCount](Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)

**基础库名称**

`Bool.fintype`, `Equiv`, `instOfNatNat`, `Fin.fintype`, `Fintype.equivFin`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Bool`, `instFintypeOption`, `instAddNat`, `instFintypeProd`, `Prod`, `OfNat.ofNat`, `Fin`

<a id="def-259c65f168c2c1f2"></a>
## `CodedSorting.RadixNode.Controller.body`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L235)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) →
      Fin q.inventory.readers →
        {hnormal : Normal q} →
          {n K F C : ℕ} →
            CodedSorting.RadixNode.Pass.Resources q hnormal n K →
              K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
                (CodedSorting.WordControl.Word q.w → Fin K) →
                  CodedSorting.CommonMSDGatherController.Layout F →
                    CodedSorting.RadixNode.Controller.Tag F C → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixNode.ChunkSorter Normal] q reader {hnormal} {n K F C} r hfit key layout x =>
  match x with
  | none => CodedSorting.RadixNode.Pass.code q reader r hfit key
  | some t => CodedSorting.CommonMSDGatherController.body q reader layout t
```

**继续展开**

- [CodedSorting.RadixNode.Pass.code](Pass.definitions.md#def-60f9edc8f7d0ef13)
- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonMSDGatherController.Layout](../../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonMSDGatherController.body](../../Framework/GatherController.definitions.md#def-9378534b7df0ea1d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)
- [CodedSorting.RadixNode.Controller.body.match_1](Pass.definitions.md#def-1cc42e973fc76c83)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `Unit`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-d2ed4d0a252e0586"></a>
## `CodedSorting.RadixNode.Controller.terminal`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L242)

**类型**

```lean
{F C : ℕ} → CodedSorting.RadixNode.Controller.Tag F C → Bool
```

**定义**

```lean
fun {F C} x =>
  match x with
  | none => false
  | some t => decide (F ≤ ↑t.1)
```

**继续展开**

- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)
- [CodedSorting.RadixNode.Controller.body.match_1](Pass.definitions.md#def-1cc42e973fc76c83)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Prod.fst`, `instHAdd`, `Unit`, `HAdd.hAdd`, `Nat`, `Bool`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Bool.false`, `Fin`, `Decidable.decide`, `Nat.decLe`

<a id="def-e08b5c89528f1ae5"></a>
## `CodedSorting.RadixNode.Controller.advance`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L246)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {F C : ℕ} →
    CodedSorting.CommonMSDGatherController.Layout F →
      CodedSorting.RadixNode.Controller.Tag F C →
        CodedSorting.CommonLeafProgram.RAM q → CodedSorting.RadixNode.Controller.Tag F C
```

**定义**

```lean
fun q {F C} layout x x_1 =>
  match x, x_1 with
  | none, x => some (CodedSorting.CommonMSDGatherController.ready 0 0)
  | some t, ram => some (CodedSorting.CommonMSDGatherController.nextTag q layout t ram)
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonMSDGatherController.nextTag](../../Framework/GatherController.definitions.md#def-c4eaa7a54c94828c)
- [CodedSorting.CommonMSDGatherController.Layout](../../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Controller.advance.match_1](Pass.definitions.md#def-9ef7f9c3a02dbdc5)
- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)
- [CodedSorting.RadixNode.Controller.advance._proof_3](Pass.definitions.md#def-94100b2b431e7960)
- [CodedSorting.CommonMSDGatherController.ready](../../Framework/GatherController.definitions.md#def-8dfe78b0999fb1f6)

**基础库名称**

`Option.some`, `Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-a834bb9909bdb370"></a>
## `CodedSorting.RadixNode.Controller.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L251)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) →
      Fin q.inventory.readers →
        {hnormal : Normal q} →
          {n K F C : ℕ} →
            CodedSorting.RadixNode.Pass.Resources q hnormal n K →
              K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
                (CodedSorting.WordControl.Word q.w → Fin K) →
                  CodedSorting.CommonMSDGatherController.Layout F →
                    Fin (CodedSorting.RadixNode.Controller.tagCount F C) →
                      List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixNode.ChunkSorter Normal] q reader {hnormal} {n K F C} r hfit key layout tag =>
  CodedSorting.RadixNode.Controller.body q reader r hfit key layout
    ((CodedSorting.RadixNode.Controller.tagEquiv F C).symm tag)
```

**继续展开**

- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonMSDGatherController.Layout](../../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.RadixNode.Controller.tagCount](Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.Controller.body](Pass.definitions.md#def-259c65f168c2c1f2)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)
- [CodedSorting.RadixNode.Controller.tagEquiv](Pass.definitions.md#def-4e273179c697cf55)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `Nat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-4da3857a431bb913"></a>
## `CodedSorting.RadixNode.Controller.done`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L257)

**类型**

```lean
{F C : ℕ} → Fin (CodedSorting.RadixNode.Controller.tagCount F C) → Bool
```

**定义**

```lean
fun {F C} tag => CodedSorting.RadixNode.Controller.terminal ((CodedSorting.RadixNode.Controller.tagEquiv F C).symm tag)
```

**继续展开**

- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.RadixNode.Controller.tagCount](Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.RadixNode.Controller.terminal](Pass.definitions.md#def-d2ed4d0a252e0586)
- [CodedSorting.RadixNode.Controller.tagEquiv](Pass.definitions.md#def-4e273179c697cf55)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Nat`, `Bool`, `Equiv.symm`, `Fin`, `DFunLike.coe`

<a id="def-22a16878e6720b21"></a>
## `CodedSorting.RadixNode.Controller.next`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L259)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {F C : ℕ} →
    CodedSorting.CommonMSDGatherController.Layout F →
      Fin (CodedSorting.RadixNode.Controller.tagCount F C) →
        CodedSorting.CommonLeafProgram.RAM q → Fin (CodedSorting.RadixNode.Controller.tagCount F C)
```

**定义**

```lean
fun q {F C} layout tag ram =>
  (CodedSorting.RadixNode.Controller.tagEquiv F C)
    (CodedSorting.RadixNode.Controller.advance q layout ((CodedSorting.RadixNode.Controller.tagEquiv F C).symm tag) ram)
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonMSDGatherController.Layout](../../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.RadixNode.Controller.tagCount](Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.RadixNode.Controller.advance](Pass.definitions.md#def-e08b5c89528f1ae5)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Controller.tagEquiv](Pass.definitions.md#def-4e273179c697cf55)

**基础库名称**

`Equiv.instFunLike`, `Equiv`, `Nat`, `Equiv.symm`, `Fin`, `DFunLike.coe`

<a id="def-d3b70a94a38ca08d"></a>
## `CodedSorting.RadixNode.Controller.code_safe`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Pass.lean#L272)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] (q : CodedSorting.CommonSortingNormalization.Configuration)
  (reader : Fin q.inventory.readers) {hnormal : Normal q} {n K F C : ℕ}
  (r : CodedSorting.RadixNode.Pass.Resources q hnormal n K)
  (hfit : K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q)
  (key : CodedSorting.WordControl.Word q.w → Fin K) (layout : CodedSorting.CommonMSDGatherController.Layout F)
  (tag : Fin (CodedSorting.RadixNode.Controller.tagCount F C)),
  ∀ i ∈ CodedSorting.RadixNode.Controller.code q reader r hfit key layout tag,
    CodedSorting.CommonStaticSchedule.RespectsPC q i
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout](../../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.RadixNode.Controller.tagCount](Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.RadixNode.Controller.code](Pass.definitions.md#def-a834bb9909bdb370)
- [CodedSorting.CommonStaticSchedule.RespectsPC](../../../../Shared/Programs/Static/Fusion.definitions.md#def-c88ad398120526c1)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`HMul.hMul`, `Membership.mem`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `List.instMembership`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-da05d003cbe1e9a6"></a>
## `CodedSorting.RadixNode.Controller.routine`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L326)

**类型**

```lean
{Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop} →
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] →
    (q : CodedSorting.CommonSortingNormalization.Configuration) →
      Fin q.inventory.readers →
        {hnormal : Normal q} →
          {n K F C : ℕ} →
            CodedSorting.RadixNode.Pass.Resources q hnormal n K →
              K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
                (CodedSorting.WordControl.Word q.w → Fin K) →
                  CodedSorting.CommonMSDGatherController.Layout F →
                    CodedSorting.CommonMSDRoutine.Routine q (CodedSorting.RadixNode.Controller.tagCount F C)
```

**定义**

```lean
fun {Normal} [CodedSorting.RadixNode.ChunkSorter Normal] q reader {hnormal} {n K F C} r hfit key layout =>
  { entry := (CodedSorting.RadixNode.Controller.tagEquiv F C) none,
    body := CodedSorting.RadixNode.Controller.code q reader r hfit key layout,
    next := CodedSorting.RadixNode.Controller.next q layout, terminal := CodedSorting.RadixNode.Controller.done,
    safe := ⋯, terminal_empty := ⋯ }
```

**继续展开**

- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonMSDGatherController.Layout](../../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.RadixNode.Controller.done](Pass.definitions.md#def-4da3857a431bb913)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.RadixNode.Controller.tagCount](Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.Controller.code_safe](Pass.definitions.md#def-d3b70a94a38ca08d)
- [CodedSorting.CommonMSDRoutine.Routine](../../Framework/Routine.definitions.md#def-231701da583a9604)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Controller.routine._proof_5](Pass.definitions.md#def-acb79609d910a45b)
- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)
- [CodedSorting.CommonMSDRoutine.Routine.mk](../../Framework/Routine.definitions.md#def-e820937768ee9afd)
- [CodedSorting.RadixNode.Controller.code](Pass.definitions.md#def-a834bb9909bdb370)
- [CodedSorting.RadixNode.Controller.next](Pass.definitions.md#def-22a16878e6720b21)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)
- [CodedSorting.RadixNode.Controller.tagEquiv](Pass.definitions.md#def-4e273179c697cf55)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Option.none`, `Nat`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`, `instHMul`

<a id="def-66e6403c817548ea"></a>
## `CodedSorting.CommonMSDNodeTagBound.bound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Pass.lean#L666)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q K => CodedSorting.RadixNode.Controller.tagCount (K * q.N) (3 * q.N) + 3
```

**继续展开**

- [CodedSorting.RadixNode.Controller.tagCount](Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-94100b2b431e7960"></a>
## `CodedSorting.RadixNode.Controller.advance._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Pass.lean)

**类型**

```lean
∀ {F : ℕ}, NeZero (F + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-9ef7f9c3a02dbdc5"></a>
## `CodedSorting.RadixNode.Controller.advance.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Pass.lean)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {F C : ℕ} →
    (motive : CodedSorting.RadixNode.Controller.Tag F C → CodedSorting.CommonLeafProgram.RAM q → Sort u_1) →
      (x : CodedSorting.RadixNode.Controller.Tag F C) →
        (x_1 : CodedSorting.CommonLeafProgram.RAM q) →
          ((x : CodedSorting.CommonLeafProgram.RAM q) → motive none x) →
            ((t : CodedSorting.CommonMSDGatherController.Tag F C) →
                (ram : CodedSorting.CommonLeafProgram.RAM q) → motive (some t) ram) →
              motive x x_1
```

**定义**

```lean
fun q {F C} motive x x_1 h_1 h_2 => Option.casesOn x (h_1 x_1) fun val => h_2 val x_1
```

**继续展开**

- [CodedSorting.CommonLeafProgram.RAM](../../../../Shared/Memory/Leaf/Program.definitions.md#def-32e1e07132674e8d)
- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)

**基础库名称**

`Option.casesOn`, `Option.some`, `Option.none`, `Nat`

<a id="def-1cc42e973fc76c83"></a>
## `CodedSorting.RadixNode.Controller.body.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Pass.lean)

**类型**

```lean
{F C : ℕ} →
  (motive : CodedSorting.RadixNode.Controller.Tag F C → Sort u_1) →
    (x : CodedSorting.RadixNode.Controller.Tag F C) →
      (Unit → motive none) → ((t : CodedSorting.CommonMSDGatherController.Tag F C) → motive (some t)) → motive x
```

**定义**

```lean
fun {F C} motive x h_1 h_2 => Option.casesOn x (h_1 ()) fun val => h_2 val
```

**继续展开**

- [CodedSorting.RadixNode.Controller.Tag](Pass.definitions.md#def-431fcc6584e74efd)
- [CodedSorting.CommonMSDGatherController.Tag](../../Framework/GatherController.definitions.md#def-3ed09f82a7a70d4e)

**基础库名称**

`Unit.unit`, `Option.casesOn`, `Option.some`, `Option.none`, `Unit`, `Nat`

<a id="def-acb79609d910a45b"></a>
## `CodedSorting.RadixNode.Controller.routine._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Pass.lean)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] (q : CodedSorting.CommonSortingNormalization.Configuration)
  (reader : Fin q.inventory.readers) {hnormal : Normal q} {n K F C : ℕ}
  (r : CodedSorting.RadixNode.Pass.Resources q hnormal n K)
  (hfit : K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q)
  (key : CodedSorting.WordControl.Word q.w → Fin K) (layout : CodedSorting.CommonMSDGatherController.Layout F)
  (tag : Fin (CodedSorting.RadixNode.Controller.tagCount F C)),
  CodedSorting.RadixNode.Controller.done tag = true →
    CodedSorting.RadixNode.Controller.code q reader r hfit key layout tag = []
```

**继续展开**

- [CodedSorting.CommonMSDGatherController.Layout](../../Framework/GatherController.definitions.md#def-047c526530ef9455)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.RadixNode.Controller.done](Pass.definitions.md#def-4da3857a431bb913)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.RadixNode.Controller.tagCount](Pass.definitions.md#def-6f5c701514f456da)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../../Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.RadixNode.Controller.code](Pass.definitions.md#def-a834bb9909bdb370)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Bool.true`, `List`, `Nat`, `Bool`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`, `List.nil`

<a id="def-907a95b7a74cf5ea"></a>
## `CodedSorting.RadixNode.Pass.chunks._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Pass.lean)

**类型**

```lean
∀ {Normal : CodedSorting.CommonSortingNormalization.Configuration → Prop}
  [inst : CodedSorting.RadixNode.ChunkSorter Normal] (q : CodedSorting.CommonSortingNormalization.Configuration)
  {hnormal : Normal q} {n K : ℕ} (r : CodedSorting.RadixNode.Pass.Resources q hnormal n K),
  r.source + max 1 (CodedSorting.CommonRecordProgram.recordBlocks q n) ≤ r.buffer
```

**继续展开**

- [CodedSorting.RadixNode.Pass.Resources.source](Pass.definitions.md#def-c21ef7c63575f8b9)
- [CodedSorting.CommonRecordProgram.recordBlocks](../../../../Shared/Records/RecordOperations.definitions.md#def-ea265f1c6d0c5e70)
- [CodedSorting.RadixNode.ChunkSorter](Pass.definitions.md#def-adf56b3fbfdf240f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.RadixNode.Pass.Resources.buffer](Pass.definitions.md#def-39e4c91d6c7020f5)
- [CodedSorting.RadixNode.Pass.Resources](Pass.definitions.md#def-3007be7658efed0e)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`
