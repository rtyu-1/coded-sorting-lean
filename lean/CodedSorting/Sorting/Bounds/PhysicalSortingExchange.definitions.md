# PhysicalSortingExchange 的定义

[源码](PhysicalSortingExchange.lean) · [主定理导读](../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-5b3c18cc48f5db74"></a>
## `CodedSorting.PhysicalSortingExchangeLayout.RecordAddress`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L14)

**类型**

```lean
ℕ → ℕ → Type
```

**定义**

```lean
fun s w => CodedSorting.ColumnsortExchange.Fields s × Fin w
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)

**基础库名称**

`Nat`, `Prod`, `Fin`

<a id="def-7783105b9f1f848c"></a>
## `CodedSorting.PhysicalSortingExchangeLayout.recordLayout`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L16)

**类型**

```lean
(s w : ℕ) → CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w ≃ Fin (s ^ 4 * w)
```

**定义**

```lean
fun s w => ((CodedSorting.ColumnsortExchange.encode s).prodCongr (Equiv.refl (Fin w))).trans finProdFinEquiv
```

**继续展开**

- [CodedSorting.ColumnsortExchange.encode](../Local/Columnsort/ColumnsortExchange.definitions.md#def-a4b5dfeae3779c74)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.PhysicalSortingExchangeLayout.RecordAddress](PhysicalSortingExchange.definitions.md#def-5b3c18cc48f5db74)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `Nat.instMonoid`, `Monoid.toNatPow`, `Equiv`, `instMulNat`, `instOfNatNat`, `HPow.hPow`, `Nat`, `finProdFinEquiv`, `instHPow`, `Prod`, `Equiv.prodCongr`, `OfNat.ofNat`, `Fin`, `Equiv.refl`, `instHMul`

<a id="def-c69aea870e136270"></a>
## `CodedSorting.PhysicalSortingExchangeLayout.swap34Record`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L94)

**类型**

```lean
(s w : ℕ) →
  CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w ≃
    CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w
```

**定义**

```lean
fun s w => (CodedSorting.ColumnsortExchange.swap34 s).prodCongr (Equiv.refl (Fin w))
```

**继续展开**

- [CodedSorting.ColumnsortExchange.swap34](../Local/Columnsort/ColumnsortExchange.definitions.md#def-bf2e3e56da5a996e)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.PhysicalSortingExchangeLayout.RecordAddress](PhysicalSortingExchange.definitions.md#def-5b3c18cc48f5db74)

**基础库名称**

`Equiv`, `Nat`, `Equiv.prodCongr`, `Fin`, `Equiv.refl`

<a id="def-fdaea8e99680eb59"></a>
## `CodedSorting.PhysicalSortingExchangeLayout.swap23Record`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L96)

**类型**

```lean
(s w : ℕ) →
  CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w ≃
    CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w
```

**定义**

```lean
fun s w => (CodedSorting.ColumnsortExchange.swap23 s).prodCongr (Equiv.refl (Fin w))
```

**继续展开**

- [CodedSorting.ColumnsortExchange.swap23](../Local/Columnsort/ColumnsortExchange.definitions.md#def-223ecff613971a53)
- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.PhysicalSortingExchangeLayout.RecordAddress](PhysicalSortingExchange.definitions.md#def-5b3c18cc48f5db74)

**基础库名称**

`Equiv`, `Nat`, `Equiv.prodCongr`, `Fin`, `Equiv.refl`

<a id="def-cfda7d4ec9924a48"></a>
## `CodedSorting.PhysicalSortingExchangeLayout.swap12Record`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L98)

**类型**

```lean
(s w : ℕ) →
  CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w ≃
    CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w
```

**定义**

```lean
fun s w => (CodedSorting.ColumnsortExchange.swap12 s).prodCongr (Equiv.refl (Fin w))
```

**继续展开**

- [CodedSorting.ColumnsortExchange.Fields](../Local/Columnsort/ColumnsortExchange.definitions.md#def-631f7a9c097d4331)
- [CodedSorting.ColumnsortExchange.swap12](../Local/Columnsort/ColumnsortExchange.definitions.md#def-57782437d8e566ea)
- [CodedSorting.PhysicalSortingExchangeLayout.RecordAddress](PhysicalSortingExchange.definitions.md#def-5b3c18cc48f5db74)

**基础库名称**

`Equiv`, `Nat`, `Equiv.prodCongr`, `Fin`, `Equiv.refl`

<a id="def-7bc87614e0c64bfd"></a>
## `CodedSorting.PhysicalSortingExchange.Swap`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](PhysicalSortingExchange.lean#L136)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap.first](PhysicalSortingExchange.definitions.md#def-6b3f2a8759a1c396)
- [CodedSorting.PhysicalSortingExchange.Swap.middle](PhysicalSortingExchange.definitions.md#def-a171b37e47af8ac3)
- [CodedSorting.PhysicalSortingExchange.Swap.last](PhysicalSortingExchange.definitions.md#def-63a8e508e0d11430)

<a id="def-08965323e9a4218b"></a>
## `CodedSorting.PhysicalSortingExchange.Swap.casesOn`

读取 `CodedSorting.PhysicalSortingExchange.Swap` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](PhysicalSortingExchange.lean#L136)

**类型**

```lean
{motive : CodedSorting.PhysicalSortingExchange.Swap → Sort u} →
  (t : CodedSorting.PhysicalSortingExchange.Swap) →
    motive CodedSorting.PhysicalSortingExchange.Swap.last →
      motive CodedSorting.PhysicalSortingExchange.Swap.middle →
        motive CodedSorting.PhysicalSortingExchange.Swap.first → motive t
```

**定义**

```lean
fun {motive} t last middle first => CodedSorting.PhysicalSortingExchange.Swap.rec last middle first t
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap.first](PhysicalSortingExchange.definitions.md#def-6b3f2a8759a1c396)
- [CodedSorting.PhysicalSortingExchange.Swap.middle](PhysicalSortingExchange.definitions.md#def-a171b37e47af8ac3)
- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.Swap.rec](PhysicalSortingExchange.definitions.md#def-d76614af52962d9d)
- [CodedSorting.PhysicalSortingExchange.Swap.last](PhysicalSortingExchange.definitions.md#def-63a8e508e0d11430)

<a id="def-d76614af52962d9d"></a>
## `CodedSorting.PhysicalSortingExchange.Swap.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](PhysicalSortingExchange.lean#L136)

**类型**

```lean
{motive : CodedSorting.PhysicalSortingExchange.Swap → Sort u} →
  motive CodedSorting.PhysicalSortingExchange.Swap.last →
    motive CodedSorting.PhysicalSortingExchange.Swap.middle →
      motive CodedSorting.PhysicalSortingExchange.Swap.first →
        (t : CodedSorting.PhysicalSortingExchange.Swap) → motive t
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap.first](PhysicalSortingExchange.definitions.md#def-6b3f2a8759a1c396)
- [CodedSorting.PhysicalSortingExchange.Swap.middle](PhysicalSortingExchange.definitions.md#def-a171b37e47af8ac3)
- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.Swap.last](PhysicalSortingExchange.definitions.md#def-63a8e508e0d11430)

<a id="def-6b3f2a8759a1c396"></a>
## `CodedSorting.PhysicalSortingExchange.Swap.first`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalSortingExchange.lean#L137)

**类型**

```lean
CodedSorting.PhysicalSortingExchange.Swap
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)

<a id="def-63a8e508e0d11430"></a>
## `CodedSorting.PhysicalSortingExchange.Swap.last`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalSortingExchange.lean#L137)

**类型**

```lean
CodedSorting.PhysicalSortingExchange.Swap
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)

<a id="def-a171b37e47af8ac3"></a>
## `CodedSorting.PhysicalSortingExchange.Swap.middle`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](PhysicalSortingExchange.lean#L137)

**类型**

```lean
CodedSorting.PhysicalSortingExchange.Swap
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)

<a id="def-5f1887d78e8d6fa1"></a>
## `CodedSorting.PhysicalSortingExchange.prefixSize`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L140)

**类型**

```lean
ℕ → CodedSorting.PhysicalSortingExchange.Swap → ℕ
```

**定义**

```lean
fun s x =>
  match x with
  | CodedSorting.PhysicalSortingExchange.Swap.last => s ^ 2
  | CodedSorting.PhysicalSortingExchange.Swap.middle => s
  | CodedSorting.PhysicalSortingExchange.Swap.first => 1
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.prefixSize.match_1](PhysicalSortingExchange.definitions.md#def-29ff32ebde0e0994)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `Unit`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-72944fee1cb2bbcf"></a>
## `CodedSorting.PhysicalSortingExchange.suffix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L142)

**类型**

```lean
ℕ → ℕ → CodedSorting.PhysicalSortingExchange.Swap → ℕ
```

**定义**

```lean
fun s w x =>
  match x with
  | CodedSorting.PhysicalSortingExchange.Swap.last => w
  | CodedSorting.PhysicalSortingExchange.Swap.middle => s * w
  | CodedSorting.PhysicalSortingExchange.Swap.first => s ^ 2 * w
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.prefixSize.match_1](PhysicalSortingExchange.definitions.md#def-29ff32ebde0e0994)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `Unit`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-506e1e347102234e"></a>
## `CodedSorting.PhysicalSortingExchange.move`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L146)

**类型**

```lean
(s w : ℕ) →
  CodedSorting.PhysicalSortingExchange.Swap →
    CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w ≃
      CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w
```

**定义**

```lean
fun s w x =>
  match x with
  | CodedSorting.PhysicalSortingExchange.Swap.last => CodedSorting.PhysicalSortingExchangeLayout.swap34Record s w
  | CodedSorting.PhysicalSortingExchange.Swap.middle => CodedSorting.PhysicalSortingExchangeLayout.swap23Record s w
  | CodedSorting.PhysicalSortingExchange.Swap.first => CodedSorting.PhysicalSortingExchangeLayout.swap12Record s w
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchangeLayout.swap34Record](PhysicalSortingExchange.definitions.md#def-c69aea870e136270)
- [CodedSorting.PhysicalSortingExchangeLayout.swap12Record](PhysicalSortingExchange.definitions.md#def-cfda7d4ec9924a48)
- [CodedSorting.PhysicalSortingExchange.prefixSize.match_1](PhysicalSortingExchange.definitions.md#def-29ff32ebde0e0994)
- [CodedSorting.PhysicalSortingExchangeLayout.RecordAddress](PhysicalSortingExchange.definitions.md#def-5b3c18cc48f5db74)
- [CodedSorting.PhysicalSortingExchangeLayout.swap23Record](PhysicalSortingExchange.definitions.md#def-fdaea8e99680eb59)

**基础库名称**

`Equiv`, `Unit`, `Nat`

<a id="def-5f47d2c3d2727164"></a>
## `CodedSorting.PhysicalSortingExchange.permute`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L224)

**类型**

```lean
(s w : ℕ) →
  List CodedSorting.PhysicalSortingExchange.Swap →
    Equiv.Perm (CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w)
```

**定义**

```lean
fun s w x =>
  List.brecOn x fun x f =>
    (match (motive :=
        (x : List CodedSorting.PhysicalSortingExchange.Swap) →
          List.below x → Equiv.Perm (CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w))
        x with
      | [] => fun x => Equiv.refl (CodedSorting.PhysicalSortingExchangeLayout.RecordAddress s w)
      | j :: js => fun x => (CodedSorting.PhysicalSortingExchange.move s w j).trans x.1)
      f
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.move](PhysicalSortingExchange.definitions.md#def-506e1e347102234e)
- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchangeLayout.RecordAddress](PhysicalSortingExchange.definitions.md#def-5b3c18cc48f5db74)
- [CodedSorting.PhysicalSortingExchange.permute.match_1](PhysicalSortingExchange.definitions.md#def-16bd25928a8422b8)

**基础库名称**

`List.brecOn`, `Equiv.trans`, `List.cons`, `List`, `Unit`, `PProd`, `Equiv.Perm`, `Nat`, `List.below`, `Equiv.refl`, `List.nil`

<a id="def-ca7c18c6bcc67751"></a>
## `CodedSorting.PhysicalSortingExchange.forwardSwaps`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L247)

**类型**

```lean
List CodedSorting.PhysicalSortingExchange.Swap
```

**定义**

```lean
[CodedSorting.PhysicalSortingExchange.Swap.last, CodedSorting.PhysicalSortingExchange.Swap.middle,
  CodedSorting.PhysicalSortingExchange.Swap.first]
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap.first](PhysicalSortingExchange.definitions.md#def-6b3f2a8759a1c396)
- [CodedSorting.PhysicalSortingExchange.Swap.middle](PhysicalSortingExchange.definitions.md#def-a171b37e47af8ac3)
- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.Swap.last](PhysicalSortingExchange.definitions.md#def-63a8e508e0d11430)

**基础库名称**

`List.cons`, `List`, `List.nil`

<a id="def-e8260471144a5190"></a>
## `CodedSorting.PhysicalSortingExchange.backwardSwaps`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalSortingExchange.lean#L248)

**类型**

```lean
List CodedSorting.PhysicalSortingExchange.Swap
```

**定义**

```lean
[CodedSorting.PhysicalSortingExchange.Swap.first, CodedSorting.PhysicalSortingExchange.Swap.middle,
  CodedSorting.PhysicalSortingExchange.Swap.last]
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap.first](PhysicalSortingExchange.definitions.md#def-6b3f2a8759a1c396)
- [CodedSorting.PhysicalSortingExchange.Swap.middle](PhysicalSortingExchange.definitions.md#def-a171b37e47af8ac3)
- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.Swap.last](PhysicalSortingExchange.definitions.md#def-63a8e508e0d11430)

**基础库名称**

`List.cons`, `List`, `List.nil`

<a id="def-16bd25928a8422b8"></a>
## `CodedSorting.PhysicalSortingExchange.permute.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PhysicalSortingExchange.lean)

**类型**

```lean
(motive : List CodedSorting.PhysicalSortingExchange.Swap → Sort u_1) →
  (x : List CodedSorting.PhysicalSortingExchange.Swap) →
    (Unit → motive []) →
      ((j : CodedSorting.PhysicalSortingExchange.Swap) →
          (js : List CodedSorting.PhysicalSortingExchange.Swap) → motive (j :: js)) →
        motive x
```

**定义**

```lean
fun motive x h_1 h_2 => List.casesOn x (h_1 ()) fun head tail => h_2 head tail
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `List.casesOn`, `List.nil`

<a id="def-29ff32ebde0e0994"></a>
## `CodedSorting.PhysicalSortingExchange.prefixSize.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PhysicalSortingExchange.lean)

**类型**

```lean
(motive : CodedSorting.PhysicalSortingExchange.Swap → Sort u_1) →
  (x : CodedSorting.PhysicalSortingExchange.Swap) →
    (Unit → motive CodedSorting.PhysicalSortingExchange.Swap.last) →
      (Unit → motive CodedSorting.PhysicalSortingExchange.Swap.middle) →
        (Unit → motive CodedSorting.PhysicalSortingExchange.Swap.first) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 => CodedSorting.PhysicalSortingExchange.Swap.casesOn x (h_1 ()) (h_2 ()) (h_3 ())
```

**继续展开**

- [CodedSorting.PhysicalSortingExchange.Swap.first](PhysicalSortingExchange.definitions.md#def-6b3f2a8759a1c396)
- [CodedSorting.PhysicalSortingExchange.Swap.casesOn](PhysicalSortingExchange.definitions.md#def-08965323e9a4218b)
- [CodedSorting.PhysicalSortingExchange.Swap.middle](PhysicalSortingExchange.definitions.md#def-a171b37e47af8ac3)
- [CodedSorting.PhysicalSortingExchange.Swap](PhysicalSortingExchange.definitions.md#def-7bc87614e0c64bfd)
- [CodedSorting.PhysicalSortingExchange.Swap.last](PhysicalSortingExchange.definitions.md#def-63a8e508e0d11430)

**基础库名称**

`Unit.unit`, `Unit`
