# LogRate 的定义

[源码](LogRate.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-e11cb71cee9e2567"></a>
## `CodedSorting.Construction.ArbitraryCalls.Call`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](LogRate.lean#L21)

**类型**

```lean
Type
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call.mk](LogRate.definitions.md#def-17b71cd6247e0c59)

<a id="def-17b71cd6247e0c59"></a>
## `CodedSorting.Construction.ArbitraryCalls.Call.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](LogRate.lean#L21)

**类型**

```lean
ℕ → ℕ → CodedSorting.Construction.ArbitraryCalls.Call
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)

**基础库名称**

`Nat`

<a id="def-5361a0343ebdff46"></a>
## `CodedSorting.Construction.ArbitraryCalls.Call.baseWidth`

读取 `CodedSorting.Construction.ArbitraryCalls.Call` 的 `baseWidth` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](LogRate.lean#L22)

**类型**

```lean
CodedSorting.Construction.ArbitraryCalls.Call → ℕ
```

**定义**

```lean
fun self => self.1
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)

**基础库名称**

`Nat`

<a id="def-37f39a085b0fc78a"></a>
## `CodedSorting.Construction.ArbitraryCalls.Call.depth`

读取 `CodedSorting.Construction.ArbitraryCalls.Call` 的 `depth` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](LogRate.lean#L23)

**类型**

```lean
CodedSorting.Construction.ArbitraryCalls.Call → ℕ
```

**定义**

```lean
fun self => self.2
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)

**基础库名称**

`Nat`

<a id="def-f981cd6d6b5942fd"></a>
## `CodedSorting.Construction.ArbitraryCalls.Call.width`

读取 `CodedSorting.Construction.ArbitraryCalls.Call` 的 `width` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](LogRate.lean#L26)

**类型**

```lean
CodedSorting.Construction.ArbitraryCalls.Call → ℕ
```

**定义**

```lean
fun c => c.baseWidth * CodedSorting.Construction.ambientDimension ^ c.depth
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call.depth](LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `HPow.hPow`, `Nat`, `instHPow`, `instHMul`

<a id="def-75983e57bda8a0ed"></a>
## `CodedSorting.Construction.ArbitraryCalls.calls`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L34)

**类型**

```lean
ℕ → ℕ → ℕ → List CodedSorting.Construction.ArbitraryCalls.Call
```

**定义**

```lean
fun base k e =>
  List.map (fun j => { baseWidth := base, depth := j })
      (CodedSorting.ArbitrarySchedule.scales CodedSorting.Construction.ambientDimension k (e / base)) ++
    [{ baseWidth := e % base, depth := 0 }]
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ArbitraryCalls.Call.mk](LogRate.definitions.md#def-17b71cd6247e0c59)
- [CodedSorting.ArbitrarySchedule.scales](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-228ed3caa863d92d)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`instHDiv`, `List.map`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `List.cons`, `instHAppendOfAppend`, `List`, `HMod.hMod`, `Nat`, `Nat.instDiv`, `List.instAppend`, `OfNat.ofNat`, `HAppend.hAppend`, `List.nil`

<a id="def-681e758eeb1b0c56"></a>
## `CodedSorting.Construction.ArbitraryCalls.baseCalls`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L38)

**类型**

```lean
ℕ → ℕ → List CodedSorting.Construction.ArbitraryCalls.Call
```

**定义**

```lean
fun base e => List.replicate (e / base) { baseWidth := base, depth := 0 } ++ [{ baseWidth := e % base, depth := 0 }]
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ArbitraryCalls.Call.mk](LogRate.definitions.md#def-17b71cd6247e0c59)

**基础库名称**

`List.replicate`, `instHDiv`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `List.cons`, `instHAppendOfAppend`, `List`, `HMod.hMod`, `Nat`, `Nat.instDiv`, `List.instAppend`, `OfNat.ofNat`, `HAppend.hAppend`, `List.nil`

<a id="def-f1b69ca3fdd61fae"></a>
## `CodedSorting.Construction.ArbitraryCalls.fieldCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L41)

**类型**

```lean
List CodedSorting.Construction.ArbitraryCalls.Call → ℕ
```

**定义**

```lean
fun x =>
  List.brecOn x fun x f =>
    (match (motive := (x : List CodedSorting.Construction.ArbitraryCalls.Call) → List.below x → ℕ) x with
      | [] => fun x => 1
      | c :: cs => fun x => CodedSorting.Construction.ExchangeSpecialization.radix ^ c.width * x.1)
      f
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.fieldCount.match_1](LogRate.definitions.md#def-f1567367cdd9a008)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ArbitraryCalls.Call.width](LogRate.definitions.md#def-f981cd6d6b5942fd)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`List.brecOn`, `HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `List.cons`, `List`, `Unit`, `PProd`, `HPow.hPow`, `Nat`, `List.below`, `instHPow`, `OfNat.ofNat`, `instHMul`, `List.nil`

<a id="def-c7f67aa83650bf20"></a>
## `CodedSorting.Construction.ArbitraryCalls.baseCalls_base`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LogRate.lean#L107)

**类型**

```lean
∀ (base e : ℕ), 0 < base → ∀ c ∈ CodedSorting.Construction.ArbitraryCalls.baseCalls base e, c.baseWidth ≤ base
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call.baseWidth](LogRate.definitions.md#def-5361a0343ebdff46)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)

**基础库名称**

`Membership.mem`, `instOfNatNat`, `LE.le`, `instLENat`, `List`, `List.instMembership`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`

<a id="def-f9bbe89ff5799074"></a>
## `CodedSorting.Construction.ArbitraryCalls.baseCalls_fit`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LogRate.lean#L127)

**类型**

```lean
∀ (P base e : ℕ),
  ∀ c ∈ CodedSorting.Construction.ArbitraryCalls.baseCalls base e, CodedSorting.Construction.streamCount ^ c.depth ∣ P
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call.depth](LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)

**基础库名称**

`Dvd.dvd`, `Nat.instMonoid`, `Membership.mem`, `Monoid.toNatPow`, `List`, `HPow.hPow`, `Nat.instDvd`, `List.instMembership`, `Nat`, `instHPow`

<a id="def-f8506f50419e099d"></a>
## `CodedSorting.Construction.ArbitraryCalls.paddedRows`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L133)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun P k => CodedSorting.ArbitraryShapes.paddedCount P (CodedSorting.Construction.streamCount ^ (k + 1))
```

**继续展开**

- [CodedSorting.ArbitraryShapes.paddedCount](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-8e40c8379fc0cf5b)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`

<a id="def-6f57d6e4febc45f1"></a>
## `CodedSorting.Construction.ArbitraryCost.tau`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L235)

**类型**

```lean
ℝ
```

**定义**

```lean
1 - ↑CodedSorting.Construction.epsilon
```

**继续展开**

- [CodedSorting.Construction.epsilon](../../Circuit/Parameters/Exponent.definitions.md#def-38e0b13c0209d8a9)

**基础库名称**

`Real`, `Real.instSub`, `Real.instRatCast`, `HSub.hSub`, `Rat.cast`, `Real.instOne`, `instHSub`, `One.toOfNat1`, `OfNat.ofNat`

<a id="def-2e6e8630deb7e16f"></a>
## `CodedSorting.Construction.ArbitraryCost.ratio`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L236)

**类型**

```lean
ℝ
```

**定义**

```lean
↑CodedSorting.Construction.ambientDimension ^ CodedSorting.Construction.ArbitraryCost.tau
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCost.tau](LogRate.definitions.md#def-6f57d6e4febc45f1)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`Real.instPow`, `Real`, `Nat.cast`, `HPow.hPow`, `instHPow`, `Real.instNatCast`

<a id="def-499e7e2cf6508472"></a>
## `CodedSorting.Construction.ArbitraryCost.totalBound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L255)

**类型**

```lean
ℕ → ℕ → List CodedSorting.Construction.ArbitraryCalls.Call → ℕ → ℕ
```

**定义**

```lean
fun cutoff b cs V =>
  (List.map
      (fun c =>
        CodedSorting.Construction.ExchangeInterface.costBound
          (24 * CodedSorting.Construction.streamCount + 36 +
            CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient)
          b cutoff c.depth V)
      cs).sum
```

**继续展开**

- [CodedSorting.Construction.ExchangeInterface.costBound](../Bounds/ExchangeInterface.definitions.md#def-caaeb667315f77f7)
- [CodedSorting.Construction.MachineNetworkActualEdges.localCoefficient](../../Circuit/NetworkModel/Adapter.definitions.md#def-e3dd033ebdbb0de7)
- [CodedSorting.Construction.ArbitraryCalls.Call.depth](LogRate.definitions.md#def-37f39a085b0fc78a)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)

**基础库名称**

`Nat.instMulZeroClass`, `HMul.hMul`, `List.map`, `List.sum`, `instMulNat`, `instOfNatNat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `MulZeroClass.toZero`, `instHMul`

<a id="def-2e8c5ea45a529ef0"></a>
## `CodedSorting.Construction.ArbitraryCost.borrowing`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L318)

**类型**

```lean
ℝ
```

**定义**

```lean
↑(CodedSorting.ArbitrarySchedule.borrowConstant CodedSorting.Construction.ExchangeSpecialization.radix
    CodedSorting.Construction.streamCount)
```

**继续展开**

- [CodedSorting.ArbitrarySchedule.borrowConstant](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-9df08906ad6d7805)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`Real`, `Nat.cast`, `Real.instNatCast`

<a id="def-ff92f8fddcb0de26"></a>
## `CodedSorting.Construction.ArbitraryCostRate.overheadBound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L384)

**类型**

```lean
ℕ → ℕ → List CodedSorting.Construction.ArbitraryCalls.Call → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun cutoff b cs V V' ρ A D F =>
  CodedSorting.Construction.ArbitraryCost.totalBound cutoff b cs V' + A * (V / b + 1) + D * (V' / b + 1) +
    F * ρ * (V / b + 1)
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.ArbitraryCost.totalBound](LogRate.definitions.md#def-499e7e2cf6508472)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `List`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-c4462a2acfb113a9"></a>
## `CodedSorting.Construction.ArbitraryCostRate.borrowCoefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L388)

**类型**

```lean
ℕ → ℕ → ℕ → ℝ
```

**定义**

```lean
fun A D F =>
  2 * CodedSorting.Construction.RecursiveCostRate.rateConstant * ↑CodedSorting.Construction.ambientDimension + ↑A +
      2 * ↑D +
    ↑F * CodedSorting.Construction.ArbitraryCost.borrowing
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCostRate.borrowCoefficient._proof_4](LogRate.definitions.md#def-38d5d731b3c22ea3)
- [CodedSorting.Construction.RecursiveCostRate.rateConstant](../Recursion/Resources.definitions.md#def-19e9fc3555794e23)
- [CodedSorting.Construction.ArbitraryCost.borrowing](LogRate.definitions.md#def-2e8c5ea45a529ef0)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`Real`, `HMul.hMul`, `Nat.cast`, `Real.instAdd`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-54c7edc323196509"></a>
## `CodedSorting.Construction.ArbitraryCostRate.borrowedBound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L458)

**类型**

```lean
ℕ → ℕ → List CodedSorting.Construction.ArbitraryCalls.Call → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun cutoff b cs P ρ P' G S A D F =>
  CodedSorting.Construction.ArbitraryCostRate.overheadBound cutoff b cs
    (CodedSorting.BinaryPadding.Volume P
      (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
        CodedSorting.Construction.ArbitraryCalls.fieldCount cs)
      G S)
    (CodedSorting.BinaryPadding.Volume P' (CodedSorting.Construction.ArbitraryCalls.fieldCount cs) G S) ρ A D F
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCostRate.overheadBound](LogRate.definitions.md#def-ff92f8fddcb0de26)
- [CodedSorting.Construction.ArbitraryCalls.fieldCount](LogRate.definitions.md#def-f1b69ca3fdd61fae)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.BinaryPadding.Volume](../Framework/Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `List`, `HPow.hPow`, `Nat`, `instHPow`, `instHMul`

<a id="def-30367d5004946d77"></a>
## `CodedSorting.Construction.ArbitraryCostRate.bound`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L475)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun base cutoff b P e G S A D F =>
  let k := CodedSorting.ArbitrarySchedule.depth CodedSorting.Construction.ambientDimension base e;
  let ρ :=
    CodedSorting.ArbitrarySchedule.borrowedWidth CodedSorting.Construction.ExchangeSpecialization.radix
      CodedSorting.Construction.streamCount k;
  if ρ < e then
    let cs := CodedSorting.Construction.ArbitraryCalls.calls base k (e - ρ);
    CodedSorting.Construction.ArbitraryCostRate.borrowedBound cutoff b cs P ρ
      (CodedSorting.Construction.ArbitraryCalls.paddedRows
        (P *
          (CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ *
            CodedSorting.Construction.ExchangeSpecialization.radix ^ ρ))
        k)
      G S A D F
  else
    CodedSorting.Construction.ArbitraryCost.totalBound cutoff b
      (CodedSorting.Construction.ArbitraryCalls.baseCalls base e)
      (CodedSorting.BinaryPadding.Volume P (CodedSorting.Construction.ExchangeSpecialization.radix ^ e) G S)
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.calls](LogRate.definitions.md#def-75983e57bda8a0ed)
- [CodedSorting.ArbitrarySchedule.depth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-994c3ec57bd87487)
- [CodedSorting.Construction.ArbitraryCostRate.borrowedBound](LogRate.definitions.md#def-54c7edc323196509)
- [CodedSorting.Construction.ArbitraryCalls.baseCalls](LogRate.definitions.md#def-681e758eeb1b0c56)
- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)
- [CodedSorting.Construction.streamCount](../../Circuit/Parameters/Counts.definitions.md#def-8dbf3b9bec362266)
- [CodedSorting.ArbitrarySchedule.borrowedWidth](../Framework/Recursion/ArbitrarySchedule.definitions.md#def-afea5e927d13a485)
- [CodedSorting.Construction.ArbitraryCost.totalBound](LogRate.definitions.md#def-499e7e2cf6508472)
- [CodedSorting.Construction.ArbitraryCalls.paddedRows](LogRate.definitions.md#def-f8506f50419e099d)
- [CodedSorting.BinaryPadding.Volume](../Framework/Fields/BinaryPaddingScan.definitions.md#def-9f78c58eb260cdb3)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `HSub.hSub`, `Monoid.toNatPow`, `instSubNat`, `instMulNat`, `List`, `instHSub`, `HPow.hPow`, `Nat`, `LT.lt`, `Nat.decLt`, `instHPow`, `instLTNat`, `instHMul`, `ite`

<a id="def-934f6f366fb164be"></a>
## `CodedSorting.Construction.ArbitraryCostRate.coefficient`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L485)

**类型**

```lean
ℕ → ℕ → ℕ → ℝ
```

**定义**

```lean
fun A D F =>
  CodedSorting.Construction.ArbitraryCostRate.borrowCoefficient A D F +
    20 * (CodedSorting.Construction.ArbitraryCost.borrowing + 1)
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCost.borrowing](LogRate.definitions.md#def-2e8c5ea45a529ef0)
- [CodedSorting.Construction.ArbitraryCostRate.borrowCoefficient](LogRate.definitions.md#def-c4462a2acfb113a9)
- [CodedSorting.Construction.ArbitraryCostRate.coefficient._proof_5](LogRate.definitions.md#def-b577f81f409eec0d)

**基础库名称**

`Real`, `HMul.hMul`, `Real.instAdd`, `Real.instOne`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Real.instMul`, `One.toOfNat1`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-dee17484e25629d3"></a>
## `CodedSorting.Construction.ArbitraryCostRate.finalConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L535)

**类型**

```lean
ℕ → ℕ → ℕ → ℝ
```

**定义**

```lean
fun A D F =>
  CodedSorting.Construction.ArbitraryCostRate.coefficient A D F *
    (CodedSorting.Construction.ArbitraryCost.ratio / (CodedSorting.Construction.ArbitraryCost.ratio - 1))
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCostRate.coefficient](LogRate.definitions.md#def-934f6f366fb164be)
- [CodedSorting.Construction.ArbitraryCost.ratio](LogRate.definitions.md#def-2e6e8630deb7e16f)

**基础库名称**

`Real`, `instHDiv`, `HMul.hMul`, `Real.instDivInvMonoid`, `Real.instSub`, `HSub.hSub`, `HDiv.hDiv`, `Real.instOne`, `instHSub`, `Nat`, `Real.instMul`, `DivInvMonoid.toDiv`, `One.toOfNat1`, `OfNat.ofNat`, `instHMul`

<a id="def-585857d4b90c0ed0"></a>
## `CodedSorting.Construction.ArbitraryLogRate.baseLogConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](LogRate.lean#L585)

**类型**

```lean
ℝ
```

**定义**

```lean
(8 * ↑CodedSorting.Construction.ambientDimension + 2) * Real.log ↑CodedSorting.Construction.ExchangeSpecialization.radix
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCostRate.borrowCoefficient._proof_4](LogRate.definitions.md#def-38d5d731b3c22ea3)
- [CodedSorting.Construction.ArbitraryLogRate.baseLogConstant._proof_6](LogRate.definitions.md#def-021e3d451821147d)
- [CodedSorting.Construction.ExchangeSpecialization.radix](../Bounds/ExchangeSpecializationEndpoints.definitions.md#def-b02b8b98752b35b8)
- [CodedSorting.Construction.ambientDimension](../../Circuit/Parameters/Counts.definitions.md#def-d9b1f0218bf392c3)

**基础库名称**

`Real`, `HMul.hMul`, `Nat.cast`, `Real.log`, `Real.instAdd`, `instHAdd`, `HAdd.hAdd`, `Real.instMul`, `OfNat.ofNat`, `instOfNatAtLeastTwo`, `instHMul`, `Real.instNatCast`

<a id="def-f1567367cdd9a008"></a>
## `CodedSorting.Construction.ArbitraryCalls.fieldCount.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](LogRate.lean)

**类型**

```lean
(motive : List CodedSorting.Construction.ArbitraryCalls.Call → Sort u_1) →
  (x : List CodedSorting.Construction.ArbitraryCalls.Call) →
    (Unit → motive []) →
      ((c : CodedSorting.Construction.ArbitraryCalls.Call) →
          (cs : List CodedSorting.Construction.ArbitraryCalls.Call) → motive (c :: cs)) →
        motive x
```

**定义**

```lean
fun motive x h_1 h_2 => List.casesOn x (h_1 ()) fun head tail => h_2 head tail
```

**继续展开**

- [CodedSorting.Construction.ArbitraryCalls.Call](LogRate.definitions.md#def-e11cb71cee9e2567)

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `List.casesOn`, `List.nil`

<a id="def-38d5d731b3c22ea3"></a>
## `CodedSorting.Construction.ArbitraryCostRate.borrowCoefficient._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LogRate.lean)

**类型**

```lean
(0 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-b577f81f409eec0d"></a>
## `CodedSorting.Construction.ArbitraryCostRate.coefficient._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LogRate.lean)

**类型**

```lean
(18 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`

<a id="def-021e3d451821147d"></a>
## `CodedSorting.Construction.ArbitraryLogRate.baseLogConstant._proof_6`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](LogRate.lean)

**类型**

```lean
(6 + 2).AtLeastTwo
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Nat.AtLeastTwo`
