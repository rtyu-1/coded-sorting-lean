# Definitions 的定义

[源码](Definitions.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-6cbbb16b84a48533"></a>
## `CodedSorting.Construction.MachineNetwork.Circuit`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Definitions.lean#L18)

**类型**

```lean
ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Circuit.mk](Definitions.definitions.md#def-51e199272a973e37)

**基础库名称**

`Nat`

<a id="def-51e199272a973e37"></a>
## `CodedSorting.Construction.MachineNetwork.Circuit.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Definitions.lean#L18)

**类型**

```lean
{inputs nodes V : ℕ} →
  (ports : Fin nodes → List (Fin (inputs + nodes))) →
    (∀ (e : Fin nodes), ∀ p ∈ ports e, ↑p < inputs + ↑e) →
      (Fin nodes → Equiv.Perm (Fin V)) → CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)

**基础库名称**

`Membership.mem`, `Fin.val`, `List`, `instHAdd`, `List.instMembership`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`

<a id="def-b388fbc579a86576"></a>
## `CodedSorting.Construction.MachineNetwork.Circuit.ports`

读取 `CodedSorting.Construction.MachineNetwork.Circuit` 的 `ports` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Definitions.lean#L19)

**类型**

```lean
{inputs nodes V : ℕ} →
  CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V → Fin nodes → List (Fin (inputs + nodes))
```

**定义**

```lean
fun inputs nodes V self => self.1
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)

**基础库名称**

`List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-a5367bc3961a29e1"></a>
## `CodedSorting.Construction.MachineNetwork.Circuit.permutation`

读取 `CodedSorting.Construction.MachineNetwork.Circuit` 的 `permutation` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Definitions.lean#L21)

**类型**

```lean
{inputs nodes V : ℕ} → CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V → Fin nodes → Equiv.Perm (Fin V)
```

**定义**

```lean
fun inputs nodes V self => self.3
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)

**基础库名称**

`Equiv.Perm`, `Nat`, `Fin`

<a id="def-959c823048638e7d"></a>
## `CodedSorting.Construction.MachineNetwork.nodeFile`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L23)

**类型**

```lean
{inputs nodes : ℕ} → Fin nodes → Fin (inputs + nodes)
```

**定义**

```lean
fun {inputs nodes} e => ⟨inputs + ↑e, ⋯⟩
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.nodeFile._proof_2](Definitions.definitions.md#def-c43736f082a2e09a)

**基础库名称**

`Fin.mk`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-b8a62839f43f1fe7"></a>
## `CodedSorting.Construction.MachineNetwork.Layout`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](Definitions.lean#L26)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.mk](Definitions.definitions.md#def-9796ff5df1c75daa)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-9796ff5df1c75daa"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](Definitions.lean#L26)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} →
    (workspace stride buffer limit : ℕ) →
      CodedSorting.CommonPermutationPairs.count q V ≤ stride →
        workspace + (inputs + nodes) * stride ≤ buffer →
          buffer ≤ limit → limit ≤ q.N ^ q.exponent → CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `LE.le`, `instLENat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `instHMul`

<a id="def-a6f26d9ff32e3cb9"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.workspace`

读取 `CodedSorting.Construction.MachineNetwork.Layout` 的 `workspace` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Definitions.lean#L27)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} → CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V → ℕ
```

**定义**

```lean
fun q inputs nodes V self => self.1
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-2516d89bed459156"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.stride`

读取 `CodedSorting.Construction.MachineNetwork.Layout` 的 `stride` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Definitions.lean#L28)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} → CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V → ℕ
```

**定义**

```lean
fun q inputs nodes V self => self.2
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-e49e04b7c3e50b16"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.buffer`

读取 `CodedSorting.Construction.MachineNetwork.Layout` 的 `buffer` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Definitions.lean#L29)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} → CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V → ℕ
```

**定义**

```lean
fun q inputs nodes V self => self.3
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-385324ea8022e246"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.limit`

读取 `CodedSorting.Construction.MachineNetwork.Layout` 的 `limit` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Definitions.lean#L30)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} → CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V → ℕ
```

**定义**

```lean
fun q inputs nodes V self => self.4
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat`

<a id="def-efabe9dbf987dfc9"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.count_le_stride`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Definitions.lean#L31)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {inputs nodes V : ℕ}
  (self : CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V),
  CodedSorting.CommonPermutationPairs.count q V ≤ self.stride
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.MachineNetwork.Layout.stride](Definitions.definitions.md#def-2516d89bed459156)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`LE.le`, `instLENat`, `Nat`

<a id="def-44823982454c1e08"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.fit`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Definitions.lean#L34)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {inputs nodes V : ℕ}
  (self : CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V), self.limit ≤ q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.limit](Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-c20ab71968fefd64"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.base`

读取 `CodedSorting.Construction.MachineNetwork.Layout` 的 `base` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](Definitions.lean#L38)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} → CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V → Fin (inputs + nodes) → ℕ
```

**定义**

```lean
fun {q} {inputs nodes V} p file => p.workspace + ↑file * p.stride
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.workspace](Definitions.definitions.md#def-a6f26d9ff32e3cb9)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.MachineNetwork.Layout.stride](Definitions.definitions.md#def-2516d89bed459156)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`, `instHMul`

<a id="def-78f002e22b2fbc35"></a>
## `CodedSorting.Construction.MachineNetwork.Layout.base_end_le`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Definitions.lean#L41)

**类型**

```lean
∀ {q : CodedSorting.CommonSortingNormalization.Configuration} {inputs nodes V : ℕ}
  (p : CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V) (file : Fin (inputs + nodes)),
  p.base file + p.stride ≤ p.buffer
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.buffer](Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.MachineNetwork.Layout.stride](Definitions.definitions.md#def-2516d89bed459156)

**基础库名称**

`LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-747285fd8836ea6c"></a>
## `CodedSorting.Construction.MachineNetwork.Programs`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L95)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} →
    CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V →
      CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V → Type
```

**定义**

```lean
fun {q} {inputs nodes V} C p =>
  (e : Fin nodes) →
    CodedSorting.CommonFinitePermutation.Program q V (p.base (CodedSorting.Construction.MachineNetwork.nodeFile e))
      p.buffer p.limit (C.permutation e)
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.buffer](Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonFinitePermutation.Program](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-fd13f4ef35da2a03)
- [CodedSorting.Construction.MachineNetwork.Circuit.permutation](Definitions.definitions.md#def-a5367bc3961a29e1)
- [CodedSorting.Construction.MachineNetwork.nodeFile](Definitions.definitions.md#def-959c823048638e7d)

**基础库名称**

`Nat`, `Fin`

<a id="def-de946d1147b4939b"></a>
## `CodedSorting.Construction.MachineNetwork.portBases`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L112)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} →
    CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V →
      CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V → Fin nodes → List ℕ
```

**定义**

```lean
fun {q} {inputs nodes V} C p e => List.map p.base (C.ports e)
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Circuit.ports](Definitions.definitions.md#def-b388fbc579a86576)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`List.map`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Fin`

<a id="def-a577c23ea98e9382"></a>
## `CodedSorting.Construction.MachineNetwork.edgeCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L115)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} →
    Fin q.inventory.readers →
      (C : CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V) →
        (p : CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V) →
          CodedSorting.Construction.MachineNetwork.Programs C p →
            Fin nodes → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} {inputs nodes V} reader C p ep e =>
  CodedSorting.CommonXorAccumulator.code q reader V (p.base (CodedSorting.Construction.MachineNetwork.nodeFile e))
      (CodedSorting.Construction.MachineNetwork.portBases C p e) ++
    (ep e).instructions
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Layout.buffer](Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.MachineNetwork.portBases](Definitions.definitions.md#def-de946d1147b4939b)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.MachineNetwork.Programs](Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonXorAccumulator.code](../../Shared/Memory/XorAccumulator.definitions.md#def-0b3750a8a06a174e)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.MachineNetwork.Circuit.permutation](Definitions.definitions.md#def-a5367bc3961a29e1)
- [CodedSorting.CommonFinitePermutation.Program.instructions](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-5733429a20219ee2)
- [CodedSorting.Construction.MachineNetwork.nodeFile](Definitions.definitions.md#def-959c823048638e7d)

**基础库名称**

`instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `Fin`, `HAppend.hAppend`

<a id="def-d0423d3f3d348eba"></a>
## `CodedSorting.Construction.MachineNetwork.prefixCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L164)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} →
    Fin q.inventory.readers →
      (C : CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V) →
        (p : CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V) →
          CodedSorting.Construction.MachineNetwork.Programs C p →
            (n : ℕ) → n ≤ nodes → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} {inputs nodes V} reader C p ep x x_1 =>
  Nat.brecOn (motive := fun x => x ≤ nodes → List (CodedSorting.CommonStaticSchedule.Instruction q)) x
    (fun x f x_2 =>
      (match (motive :=
          (x : ℕ) →
            x ≤ nodes →
              Nat.below (motive := fun x => x ≤ nodes → List (CodedSorting.CommonStaticSchedule.Instruction q)) x →
                List (CodedSorting.CommonStaticSchedule.Instruction q))
          x, x_2 with
        | 0, x => fun x => []
        | n.succ, hn => fun x => x.1 ⋯ ++ CodedSorting.Construction.MachineNetwork.edgeCode reader C p ep ⟨n, ⋯⟩)
        f)
    x_1
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.prefixCode._proof_6](Definitions.definitions.md#def-deeca38c98e28918)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Programs](Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Construction.MachineNetwork.prefixCode.match_1](Definitions.definitions.md#def-fd688a37f1e3e794)
- [CodedSorting.Construction.MachineNetwork.edgeCode](Definitions.definitions.md#def-a577c23ea98e9382)
- [CodedSorting.Construction.MachineNetwork.prefixCode._proof_5](Definitions.definitions.md#def-7e4bfa32edf324ad)

**基础库名称**

`Fin.mk`, `Nat.brecOn`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat.below`, `instHAppendOfAppend`, `List`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `Nat.succ`, `HAppend.hAppend`, `List.nil`

<a id="def-ef454091d0a5ca92"></a>
## `CodedSorting.Construction.MachineNetwork.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L171)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} →
    Fin q.inventory.readers →
      (C : CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V) →
        (p : CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V) →
          CodedSorting.Construction.MachineNetwork.Programs C p → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {q} {inputs nodes V} reader C p ep => CodedSorting.Construction.MachineNetwork.prefixCode reader C p ep nodes ⋯
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.Construction.MachineNetwork.Programs](Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.Construction.MachineNetwork.prefixCode](Definitions.definitions.md#def-d0423d3f3d348eba)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`le_rfl`, `List`, `Nat.instPreorder`, `Nat`, `Fin`

<a id="def-b70280cc484819ef"></a>
## `CodedSorting.Construction.MachineNetwork.edgeCharge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L304)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} →
    (C : CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V) →
      (p : CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V) →
        CodedSorting.Construction.MachineNetwork.Programs C p → Fin nodes → ℕ
```

**定义**

```lean
fun {q} {inputs nodes V} C p ep e =>
  3 * ((C.ports e).length + 1) * CodedSorting.CommonPermutationPairs.count q V + (ep e).charge
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Circuit.ports](Definitions.definitions.md#def-b388fbc579a86576)
- [CodedSorting.Construction.MachineNetwork.Layout.buffer](Definitions.definitions.md#def-e49e04b7c3e50b16)
- [CodedSorting.Construction.MachineNetwork.Layout.limit](Definitions.definitions.md#def-385324ea8022e246)
- [CodedSorting.Construction.MachineNetwork.Programs](Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.MachineNetwork.Layout.base](Definitions.definitions.md#def-c20ab71968fefd64)
- [CodedSorting.CommonFinitePermutation.Program.charge](../../Interchange/Framework/Memory/ExchangeShapeProgram.definitions.md#def-ea781d269aea8c1c)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Construction.MachineNetwork.Circuit.permutation](Definitions.definitions.md#def-a5367bc3961a29e1)
- [CodedSorting.Construction.MachineNetwork.nodeFile](Definitions.definitions.md#def-959c823048638e7d)
- [CodedSorting.CommonPermutationPairs.count](../../Interchange/Framework/Memory/Reflection.definitions.md#def-3c63dad660cc6543)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `List.length`, `instHMul`

<a id="def-8633871da83ccc78"></a>
## `CodedSorting.Construction.MachineNetwork.charge`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Definitions.lean#L308)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  {inputs nodes V : ℕ} →
    (C : CodedSorting.Construction.MachineNetwork.Circuit inputs nodes V) →
      (p : CodedSorting.Construction.MachineNetwork.Layout q inputs nodes V) →
        CodedSorting.Construction.MachineNetwork.Programs C p → ℕ
```

**定义**

```lean
fun {q} {inputs nodes V} C p ep => ∑ e, CodedSorting.Construction.MachineNetwork.edgeCharge C p ep e
```

**继续展开**

- [CodedSorting.Construction.MachineNetwork.Programs](Definitions.definitions.md#def-747285fd8836ea6c)
- [CodedSorting.Construction.MachineNetwork.edgeCharge](Definitions.definitions.md#def-b70280cc484819ef)
- [CodedSorting.Construction.MachineNetwork.Layout](Definitions.definitions.md#def-b8a62839f43f1fe7)
- [CodedSorting.Construction.MachineNetwork.Circuit](Definitions.definitions.md#def-6cbbb16b84a48533)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Finset.univ`, `Fin.fintype`, `Nat`, `Nat.instAddCommMonoid`, `Fin`, `Finset.sum`

<a id="def-c43736f082a2e09a"></a>
## `CodedSorting.Construction.MachineNetwork.nodeFile._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Definitions.lean)

**类型**

```lean
∀ {inputs nodes : ℕ} (e : Fin nodes), inputs + ↑e < inputs + nodes
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`

<a id="def-7e4bfa32edf324ad"></a>
## `CodedSorting.Construction.MachineNetwork.prefixCode._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Definitions.lean)

**类型**

```lean
∀ {nodes : ℕ} (n : ℕ), n + 1 ≤ nodes → n ≤ nodes
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-deeca38c98e28918"></a>
## `CodedSorting.Construction.MachineNetwork.prefixCode._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Definitions.lean)

**类型**

```lean
∀ {nodes : ℕ} (n : ℕ), n + 1 ≤ nodes → n < nodes
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `OfNat.ofNat`

<a id="def-fd688a37f1e3e794"></a>
## `CodedSorting.Construction.MachineNetwork.prefixCode.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](Definitions.lean)

**类型**

```lean
{nodes : ℕ} →
  (motive : (x : ℕ) → x ≤ nodes → Sort u_1) →
    (x : ℕ) →
      (x_1 : x ≤ nodes) →
        ((x : 0 ≤ nodes) → motive 0 x) → ((n : ℕ) → (hn : n + 1 ≤ nodes) → motive n.succ hn) → motive x x_1
```

**定义**

```lean
fun {nodes} motive x x_1 h_1 h_2 =>
  Nat.casesOn (motive := fun x => (x_2 : x ≤ nodes) → motive x x_2) x (fun x => h_1 x) (fun n x => h_2 n x) x_1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Nat.zero`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`
