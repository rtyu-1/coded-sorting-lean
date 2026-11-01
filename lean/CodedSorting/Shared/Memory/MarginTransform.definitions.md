# MarginTransform 的定义

[源码](MarginTransform.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-1b196fc79b9f7c83"></a>
## `CodedSorting.CommonMarginGather.Shape`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L16)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**定义**

```lean
fun q => CodedSorting.WordControl.Words (13 * q.digits) q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-ae54b9a81c805d44"></a>
## `CodedSorting.CommonMarginGather.Scheme`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](MarginTransform.lean#L17)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → Type
```

**继续展开**

- [CodedSorting.CommonMarginGather.Scheme.mk](MarginTransform.definitions.md#def-045744b9b5c10832)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

<a id="def-045744b9b5c10832"></a>
## `CodedSorting.CommonMarginGather.Scheme.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](MarginTransform.lean#L17)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  (CodedSorting.CommonMarginGather.Shape q → ℕ) →
    (CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → Fin (q.N ^ q.exponent)) →
      (CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → Fin (q.N ^ q.exponent)) →
        (CodedSorting.CommonMarginGather.Shape q →
            ℕ →
              CodedSorting.WordControl.Words q.block q.w →
                CodedSorting.WordControl.Words q.block q.w → CodedSorting.WordControl.Words q.block q.w) →
          CodedSorting.CommonMarginGather.Scheme q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonMarginGather.Scheme](MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-1fac543175746adf"></a>
## `CodedSorting.CommonMarginGather.Scheme.count`

读取 `CodedSorting.CommonMarginGather.Scheme` 的 `count` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MarginTransform.lean#L18)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  CodedSorting.CommonMarginGather.Scheme q → CodedSorting.CommonMarginGather.Shape q → ℕ
```

**定义**

```lean
fun q self => self.1
```

**继续展开**

- [CodedSorting.CommonMarginGather.Scheme](MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Nat`

<a id="def-32c4d05bb49d8940"></a>
## `CodedSorting.CommonMarginGather.Scheme.first`

读取 `CodedSorting.CommonMarginGather.Scheme` 的 `first` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MarginTransform.lean#L19)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  CodedSorting.CommonMarginGather.Scheme q → CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → Fin (q.N ^ q.exponent)
```

**定义**

```lean
fun q self => self.2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonMarginGather.Scheme](MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-d83cfea00172f9a6"></a>
## `CodedSorting.CommonMarginGather.Scheme.second`

读取 `CodedSorting.CommonMarginGather.Scheme` 的 `second` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MarginTransform.lean#L20)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  CodedSorting.CommonMarginGather.Scheme q → CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → Fin (q.N ^ q.exponent)
```

**定义**

```lean
fun q self => self.3
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonMarginGather.Scheme](MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `HPow.hPow`, `Nat`, `instHPow`, `Fin`

<a id="def-825c4a6a93d18362"></a>
## `CodedSorting.CommonMarginGather.Scheme.assemble`

读取 `CodedSorting.CommonMarginGather.Scheme` 的 `assemble` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](MarginTransform.lean#L21)

**类型**

```lean
{q : CodedSorting.CommonSortingNormalization.Configuration} →
  CodedSorting.CommonMarginGather.Scheme q →
    CodedSorting.CommonMarginGather.Shape q →
      ℕ →
        CodedSorting.WordControl.Words q.block q.w →
          CodedSorting.WordControl.Words q.block q.w → CodedSorting.WordControl.Words q.block q.w
```

**定义**

```lean
fun q self => self.4
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonMarginGather.Scheme](MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Nat`

<a id="def-9a6cbc5def976691"></a>
## `CodedSorting.CommonMarginTransform.field`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L316)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Shape q → Fin 13 → ℕ
```

**定义**

```lean
fun q s i => CodedSorting.WordControl.decodeWords (CodedSorting.CommonSortingNormalization.familyOfWords s i)
```

**继续展开**

- [CodedSorting.WordControl.decodeWords](../Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.familyOfWords](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a80e6efedb830ce4)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-ba8185115bcd9e19"></a>
## `CodedSorting.CommonMarginTransform.left`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L318)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Shape q → ℕ
```

**定义**

```lean
fun q s => CodedSorting.CommonMarginTransform.field q s 0
```

**继续展开**

- [CodedSorting.CommonMarginTransform.field](MarginTransform.definitions.md#def-9a6cbc5def976691)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginTransform.left._proof_1](MarginTransform.definitions.md#def-7ed30600b85e5584)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-70ed39b88afdba8f"></a>
## `CodedSorting.CommonMarginTransform.retained`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L319)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Shape q → ℕ
```

**定义**

```lean
fun q s => CodedSorting.CommonMarginTransform.field q s 1
```

**继续展开**

- [CodedSorting.CommonMarginTransform.field](MarginTransform.definitions.md#def-9a6cbc5def976691)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginTransform.left._proof_1](MarginTransform.definitions.md#def-7ed30600b85e5584)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-ea9cebb886228f83"></a>
## `CodedSorting.CommonMarginTransform.right`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L320)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Shape q → ℕ
```

**定义**

```lean
fun q s => CodedSorting.CommonMarginTransform.field q s 2
```

**继续展开**

- [CodedSorting.CommonMarginTransform.field](MarginTransform.definitions.md#def-9a6cbc5def976691)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginTransform.left._proof_1](MarginTransform.definitions.md#def-7ed30600b85e5584)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-21948438108d5e94"></a>
## `CodedSorting.CommonMarginTransform.offset`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L321)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Shape q → ℕ
```

**定义**

```lean
fun q s => CodedSorting.CommonMarginTransform.field q s 3
```

**继续展开**

- [CodedSorting.CommonMarginTransform.field](MarginTransform.definitions.md#def-9a6cbc5def976691)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginTransform.left._proof_1](MarginTransform.definitions.md#def-7ed30600b85e5584)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-7efba4d3476dd31d"></a>
## `CodedSorting.CommonMarginTransform.outWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L322)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Shape q → ℕ
```

**定义**

```lean
fun q s =>
  CodedSorting.CommonMarginTransform.left q s + CodedSorting.CommonMarginTransform.retained q s +
    CodedSorting.CommonMarginTransform.right q s
```

**继续展开**

- [CodedSorting.CommonMarginTransform.right](MarginTransform.definitions.md#def-ea9cebb886228f83)
- [CodedSorting.CommonMarginTransform.left](MarginTransform.definitions.md#def-ba8185115bcd9e19)
- [CodedSorting.CommonMarginTransform.retained](MarginTransform.definitions.md#def-70ed39b88afdba8f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`

<a id="def-ced4c7e4b4e9ca4d"></a>
## `CodedSorting.CommonMarginTransform.inBlocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L323)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Shape q → ℕ
```

**定义**

```lean
fun q s =>
  max 1
    (CodedSorting.PhysicalStreamCursor.blockCount q.block
      (CodedSorting.CommonMarginTransform.offset q s + CodedSorting.CommonMarginTransform.retained q s))
```

**继续展开**

- [CodedSorting.CommonMarginTransform.offset](MarginTransform.definitions.md#def-21948438108d5e94)
- [CodedSorting.CommonMarginTransform.retained](MarginTransform.definitions.md#def-70ed39b88afdba8f)
- [CodedSorting.PhysicalStreamCursor.blockCount](PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Nat.instMax_mathlib`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Max.max`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-20ec75114c6f29fa"></a>
## `CodedSorting.CommonMarginTransform.firstIndex`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L325)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ
```

**定义**

```lean
fun q s k =>
  (CodedSorting.CommonMarginTransform.offset q s + (k * q.block - CodedSorting.CommonMarginTransform.left q s)) /
    q.block
```

**继续展开**

- [CodedSorting.CommonMarginTransform.offset](MarginTransform.definitions.md#def-21948438108d5e94)
- [CodedSorting.CommonMarginTransform.left](MarginTransform.definitions.md#def-ba8185115bcd9e19)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HSub.hSub`, `HDiv.hDiv`, `instSubNat`, `instMulNat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `instHMul`

<a id="def-d6067525cc278e9c"></a>
## `CodedSorting.CommonMarginTransform.address`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L327)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → Fin (q.N ^ q.exponent)
```

**定义**

```lean
fun q s source a =>
  if h : source + min a (CodedSorting.CommonMarginTransform.inBlocks q s - 1) < q.N ^ q.exponent then
    ⟨source + min a (CodedSorting.CommonMarginTransform.inBlocks q s - 1), h⟩
  else ⟨0, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonMarginTransform.inBlocks](MarginTransform.definitions.md#def-ced4c7e4b4e9ca4d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginTransform.address._proof_3](MarginTransform.definitions.md#def-1a4483f2506f39e0)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `Fin.mk`, `instSubNat`, `instOfNatNat`, `dite`, `instHAdd`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instMin_mathlib`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `Min.min`

<a id="def-1ff82e6da6523742"></a>
## `CodedSorting.CommonMarginTransform.assemble`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L334)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonMarginGather.Shape q →
    ℕ →
      CodedSorting.WordControl.Words q.block q.w →
        CodedSorting.WordControl.Words q.block q.w → CodedSorting.WordControl.Words q.block q.w
```

**定义**

```lean
fun q s k a b i =>
  let j := k * q.block + ↑i;
  if j < CodedSorting.CommonMarginTransform.left q s then 0
  else
    if j < CodedSorting.CommonMarginTransform.left q s + CodedSorting.CommonMarginTransform.retained q s then
      let word := CodedSorting.CommonMarginTransform.offset q s + (j - CodedSorting.CommonMarginTransform.left q s);
      let ix := ⟨word % q.block, ⋯⟩;
      if word / q.block = CodedSorting.CommonMarginTransform.firstIndex q s k then a ix else b ix
    else
      if
          (j - (CodedSorting.CommonMarginTransform.left q s + CodedSorting.CommonMarginTransform.retained q s)) % 3 =
            0 then
        ⟨2, ⋯⟩
      else 0
```

**继续展开**

- [CodedSorting.CommonMarginTransform.offset](MarginTransform.definitions.md#def-21948438108d5e94)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonMarginTransform.left](MarginTransform.definitions.md#def-ba8185115bcd9e19)
- [CodedSorting.CommonMarginTransform.retained](MarginTransform.definitions.md#def-70ed39b88afdba8f)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonMarginTransform.firstIndex](MarginTransform.definitions.md#def-20ec75114c6f29fa)
- [CodedSorting.CommonMarginTransform.assemble._proof_7](MarginTransform.definitions.md#def-669337551809c4c3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginTransform.assemble._proof_6](MarginTransform.definitions.md#def-c12af961dcfb6685)
- [CodedSorting.CommonMarginTransform.assemble._proof_5](MarginTransform.definitions.md#def-ed2f16cce6a14264)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`instHDiv`, `HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `Fin.mk`, `Fin.instOfNat`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instSubNat`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `instHSub`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `LT.lt`, `Nat.instDiv`, `Nat.decLt`, `instAddNat`, `instDecidableEqNat`, `instHPow`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `instHMul`, `ite`

<a id="def-6fd80bba14bc47a7"></a>
## `CodedSorting.CommonMarginTransform.scheme`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L346)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonMarginGather.Scheme q
```

**定义**

```lean
fun q =>
  {
    count := fun s =>
      CodedSorting.PhysicalStreamCursor.blockCount q.block (CodedSorting.CommonMarginTransform.outWords q s),
    first := fun s source k =>
      CodedSorting.CommonMarginTransform.address q s source (CodedSorting.CommonMarginTransform.firstIndex q s k),
    second := fun s source k =>
      CodedSorting.CommonMarginTransform.address q s source (CodedSorting.CommonMarginTransform.firstIndex q s k + 1),
    assemble := CodedSorting.CommonMarginTransform.assemble q }
```

**继续展开**

- [CodedSorting.CommonMarginTransform.outWords](MarginTransform.definitions.md#def-7efba4d3476dd31d)
- [CodedSorting.CommonMarginGather.Scheme.mk](MarginTransform.definitions.md#def-045744b9b5c10832)
- [CodedSorting.CommonMarginTransform.address](MarginTransform.definitions.md#def-d6067525cc278e9c)
- [CodedSorting.CommonMarginTransform.firstIndex](MarginTransform.definitions.md#def-20ec75114c6f29fa)
- [CodedSorting.CommonMarginGather.Scheme](MarginTransform.definitions.md#def-ae54b9a81c805d44)
- [CodedSorting.CommonMarginTransform.assemble](MarginTransform.definitions.md#def-1ff82e6da6523742)
- [CodedSorting.PhysicalStreamCursor.blockCount](PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`

<a id="def-cbb100c2961a0843"></a>
## `CodedSorting.CommonMarginTransform.wordAt`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L447)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonLeafProgram.Disk q → ℕ → ℕ → CodedSorting.WordControl.Word q.w
```

**定义**

```lean
fun q disk base j => CodedSorting.CommonLeafBatchProgram.extendDisk q disk (base + j / q.block) ⟨j % q.block, ⋯⟩
```

**继续展开**

- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonLeafProgram.Disk](Leaf/Program.definitions.md#def-e343337119cf665f)
- [CodedSorting.CommonMarginTransform.wordAt._proof_8](MarginTransform.definitions.md#def-90f02f3f0136688e)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonLeafBatchProgram.extendDisk](Batch/Program.definitions.md#def-6e4d2d5f472e641f)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`instHDiv`, `Fin.mk`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instHAdd`, `HMod.hMod`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`

<a id="def-5233771e9df465d1"></a>
## `CodedSorting.CommonMarginTransform.shape`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](MarginTransform.lean#L507)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → ℕ → ℕ → ℕ → CodedSorting.CommonMarginGather.Shape q
```

**定义**

```lean
fun q L N R O =>
  CodedSorting.CommonSortingNormalization.family fun i =>
    CodedSorting.PhysicalStreamCursor.encodeNat q.digits q.w
      (if i = 0 then L else if i = 1 then N else if i = 2 then R else if i = 3 then O else 0)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.PhysicalStreamCursor.encodeNat](PhysicalStreamCursor.definitions.md#def-0b39ac6782c7ab72)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.family](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-e889a8cc1af89e2d)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMarginTransform.left._proof_1](MarginTransform.definitions.md#def-7ed30600b85e5584)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`instDecidableEqFin`, `Fin.instOfNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`, `Eq`, `ite`

<a id="def-1a4483f2506f39e0"></a>
## `CodedSorting.CommonMarginTransform.address._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MarginTransform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.CommonMarginGather.Shape q → ℕ → ℕ → 0 < q.N ^ q.exponent
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`Preorder.toLT`, `PartialOrder.toPreorder`, `Monoid.toNatPow`, `Nat.instMonoidWithZero`, `MonoidWithZero.toMulZeroOneClass`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.instPartialOrder`, `Zero.toOfNat0`, `instHPow`, `MulZeroOneClass.toMulZeroClass`, `OfNat.ofNat`, `MonoidWithZero.toMonoid`, `MulZeroClass.toZero`

<a id="def-ed2f16cce6a14264"></a>
## `CodedSorting.CommonMarginTransform.assemble._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MarginTransform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), NeZero (2 ^ q.w)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMulZeroClass`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `NeZero`, `OfNat.ofNat`, `MulZeroClass.toZero`

<a id="def-c12af961dcfb6685"></a>
## `CodedSorting.CommonMarginTransform.assemble._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MarginTransform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (s : CodedSorting.CommonMarginGather.Shape q) (k : ℕ)
  (i : Fin q.block),
  (CodedSorting.CommonMarginTransform.offset q s + (k * q.block + ↑i - CodedSorting.CommonMarginTransform.left q s)) %
      q.block <
    q.block
```

**继续展开**

- [CodedSorting.CommonMarginTransform.offset](MarginTransform.definitions.md#def-21948438108d5e94)
- [CodedSorting.CommonMarginTransform.left](MarginTransform.definitions.md#def-ba8185115bcd9e19)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMarginGather.Shape](MarginTransform.definitions.md#def-1b196fc79b9f7c83)

**基础库名称**

`HMul.hMul`, `HSub.hSub`, `Nat.instMod`, `instHMod`, `instSubNat`, `instMulNat`, `Fin.val`, `instHAdd`, `HMod.hMod`, `instHSub`, `HAdd.hAdd`, `Nat`, `LT.lt`, `instAddNat`, `instLTNat`, `Fin`, `instHMul`

<a id="def-669337551809c4c3"></a>
## `CodedSorting.CommonMarginTransform.assemble._proof_7`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MarginTransform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), 2 < 2 ^ q.w
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`

<a id="def-7ed30600b85e5584"></a>
## `CodedSorting.CommonMarginTransform.left._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MarginTransform.lean)

**类型**

```lean
NeZero (12 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-90f02f3f0136688e"></a>
## `CodedSorting.CommonMarginTransform.wordAt._proof_8`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](MarginTransform.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (j : ℕ), j % q.block < q.block
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`
