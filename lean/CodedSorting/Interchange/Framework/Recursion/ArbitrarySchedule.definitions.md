# ArbitrarySchedule 的定义

[源码](ArbitrarySchedule.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2f6b3990ae076faf"></a>
## `CodedSorting.ArbitraryShapes.Original`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L229)

**类型**

```lean
{Prefix : Type u_1} →
  {High : Type u_2} →
    {Low : Type u_3} → {Gap : Type u_4} → {Suffix : Type u_5} → Type (max (max (max u_1 u_3 u_2) u_4) u_5)
```

**定义**

```lean
fun {Prefix} {High} {Low} {Gap} {Suffix} => CodedSorting.Address.FullAddress Prefix (High × Low) Gap Suffix
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)

**基础库名称**

`Prod`

<a id="def-be433f720c8f210a"></a>
## `CodedSorting.ArbitraryShapes.Borrowed`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L230)

**类型**

```lean
{Prefix : Type u_1} →
  {High : Type u_2} →
    {Low : Type u_3} → {Gap : Type u_4} → {Suffix : Type u_5} → Type (max (max (max (max u_2 u_1) u_3) u_4) u_5)
```

**定义**

```lean
fun {Prefix} {High} {Low} {Gap} {Suffix} => CodedSorting.Address.FullAddress (Prefix × High × High) Low Gap Suffix
```

**继续展开**

- [CodedSorting.Address.FullAddress](../../../Shared/Memory/Address.definitions.md#def-dfc18ad24150a538)

**基础库名称**

`Prod`

<a id="def-a27ee44d29f8c3b2"></a>
## `CodedSorting.ArbitraryShapes.borrow`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L232)

**类型**

```lean
{Prefix : Type u_1} →
  {High : Type u_2} →
    {Low : Type u_3} →
      {Gap : Type u_4} →
        {Suffix : Type u_5} → CodedSorting.ArbitraryShapes.Original → CodedSorting.ArbitraryShapes.Borrowed
```

**定义**

```lean
fun {Prefix} {High} {Low} {Gap} {Suffix} a =>
  { prefixCoord := (a.prefixCoord, a.low.1, a.high.1), high := a.high.2, gap := a.gap, low := a.low.2,
    suffix := a.suffix }
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.ArbitraryShapes.Borrowed](ArbitrarySchedule.definitions.md#def-be433f720c8f210a)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Prod`, `Prod.snd`

<a id="def-6bb74f22377adb75"></a>
## `CodedSorting.ArbitraryShapes.unborrow`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L239)

**类型**

```lean
{Prefix : Type u_1} →
  {High : Type u_2} →
    {Low : Type u_3} →
      {Gap : Type u_4} →
        {Suffix : Type u_5} → CodedSorting.ArbitraryShapes.Borrowed → CodedSorting.ArbitraryShapes.Original
```

**定义**

```lean
fun {Prefix} {High} {Low} {Gap} {Suffix} a =>
  { prefixCoord := a.prefixCoord.1, high := (a.prefixCoord.2.2, a.high), gap := a.gap,
    low := (a.prefixCoord.2.1, a.low), suffix := a.suffix }
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.ArbitraryShapes.Borrowed](ArbitrarySchedule.definitions.md#def-be433f720c8f210a)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Prod`, `Prod.snd`

<a id="def-88705031c9029134"></a>
## `CodedSorting.ArbitraryShapes.finish`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L245)

**类型**

```lean
{Prefix : Type u_1} →
  {High : Type u_2} →
    {Low : Type u_3} →
      {Gap : Type u_4} →
        {Suffix : Type u_5} → CodedSorting.ArbitraryShapes.Borrowed → CodedSorting.ArbitraryShapes.Original
```

**定义**

```lean
fun {Prefix} {High} {Low} {Gap} {Suffix} a =>
  { prefixCoord := a.prefixCoord.1, high := (a.prefixCoord.2.1, a.high), gap := a.gap,
    low := (a.prefixCoord.2.2, a.low), suffix := a.suffix }
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.ArbitraryShapes.Borrowed](ArbitrarySchedule.definitions.md#def-be433f720c8f210a)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Prod`, `Prod.snd`

<a id="def-4c1609a8168de062"></a>
## `CodedSorting.ArbitraryShapes.borrowEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L251)

**类型**

```lean
{Prefix : Type u_1} →
  {High : Type u_2} →
    {Low : Type u_3} →
      {Gap : Type u_4} →
        {Suffix : Type u_5} → CodedSorting.ArbitraryShapes.Original ≃ CodedSorting.ArbitraryShapes.Borrowed
```

**定义**

```lean
fun {Prefix} {High} {Low} {Gap} {Suffix} =>
  { toFun := CodedSorting.ArbitraryShapes.borrow, invFun := CodedSorting.ArbitraryShapes.unborrow, left_inv := ⋯,
    right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.ArbitraryShapes.borrow](ArbitrarySchedule.definitions.md#def-a27ee44d29f8c3b2)
- [CodedSorting.ArbitraryShapes.borrowEquiv._proof_1](ArbitrarySchedule.definitions.md#def-d1db9c5eef3c2f9a)
- [CodedSorting.ArbitraryShapes.unborrow](ArbitrarySchedule.definitions.md#def-6bb74f22377adb75)
- [CodedSorting.ArbitraryShapes.Borrowed](ArbitrarySchedule.definitions.md#def-be433f720c8f210a)
- [CodedSorting.ArbitraryShapes.borrowEquiv._proof_2](ArbitrarySchedule.definitions.md#def-f9520a8bc1014df6)

**基础库名称**

`Equiv.mk`, `Equiv`

<a id="def-55b9cc97d955c742"></a>
## `CodedSorting.ArbitraryShapes.finishEquiv`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L259)

**类型**

```lean
{Prefix : Type u_1} →
  {High : Type u_2} →
    {Low : Type u_3} →
      {Gap : Type u_4} →
        {Suffix : Type u_5} → CodedSorting.ArbitraryShapes.Borrowed ≃ CodedSorting.ArbitraryShapes.Original
```

**定义**

```lean
fun {Prefix} {High} {Low} {Gap} {Suffix} =>
  { toFun := CodedSorting.ArbitraryShapes.finish,
    invFun := fun a =>
      { prefixCoord := (a.prefixCoord, a.high.1, a.low.1), high := a.high.2, gap := a.gap, low := a.low.2,
        suffix := a.suffix },
    left_inv := ⋯, right_inv := ⋯ }
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.ArbitraryShapes.finishEquiv._proof_4](ArbitrarySchedule.definitions.md#def-7a7b03c4a69611ad)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.ArbitraryShapes.finish](ArbitrarySchedule.definitions.md#def-88705031c9029134)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.ArbitraryShapes.Borrowed](ArbitrarySchedule.definitions.md#def-be433f720c8f210a)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.ArbitraryShapes.finishEquiv._proof_3](ArbitrarySchedule.definitions.md#def-f1491f01e8b214df)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Equiv.mk`, `Equiv`, `Prod.mk`, `Prod.fst`, `Prod`, `Prod.snd`

<a id="def-8e40c8379fc0cf5b"></a>
## `CodedSorting.ArbitraryShapes.paddedCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L295)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun R C => C * ((R + C - 1) / C)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HMul.hMul`, `HSub.hSub`, `HDiv.hDiv`, `instSubNat`, `instMulNat`, `instOfNatNat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-228ed3caa863d92d"></a>
## `CodedSorting.ArbitrarySchedule.scales`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L369)

**类型**

```lean
ℕ → ℕ → ℕ → List ℕ
```

**定义**

```lean
fun m x x_1 =>
  Nat.brecOn (motive := fun x => ℕ → List ℕ) x
    (fun x f x_2 =>
      (match (motive := (x : ℕ) → ℕ → Nat.below (motive := fun x => ℕ → List ℕ) x → List ℕ) x, x_2 with
        | 0, n => fun x => List.replicate n 0
        | k.succ, n => fun x => List.replicate (n % m) 0 ++ List.map Nat.succ (x.1 (n / m)))
        f)
    x_1
```

**继续展开**

- [CodedSorting.ArbitrarySchedule.scales.match_1](ArbitrarySchedule.definitions.md#def-c08c8374c550d04f)

**基础库名称**

`List.replicate`, `instHDiv`, `List.map`, `Nat.brecOn`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `Nat.below`, `instHAppendOfAppend`, `List`, `HMod.hMod`, `PProd`, `Nat`, `Nat.instDiv`, `List.instAppend`, `OfNat.ofNat`, `Nat.succ`, `HAppend.hAppend`

<a id="def-994c3ec57bd87487"></a>
## `CodedSorting.ArbitrarySchedule.depth`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L490)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun m t₀ e => Nat.log m (e / t₀)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `Nat`, `Nat.instDiv`, `Nat.log`

<a id="def-9df08906ad6d7805"></a>
## `CodedSorting.ArbitrarySchedule.borrowConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L495)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun q W => Nat.clog (q ^ 2) W
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Nat.clog`

<a id="def-afea5e927d13a485"></a>
## `CodedSorting.ArbitrarySchedule.borrowedWidth`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ArbitrarySchedule.lean#L496)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q W k => CodedSorting.ArbitrarySchedule.borrowConstant q W * (k + 1)
```

**继续展开**

- [CodedSorting.ArbitrarySchedule.borrowConstant](ArbitrarySchedule.definitions.md#def-9df08906ad6d7805)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-c08c8374c550d04f"></a>
## `CodedSorting.ArbitrarySchedule.scales.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ArbitrarySchedule.lean)

**类型**

```lean
(motive : ℕ → ℕ → Sort u_1) → (x x_1 : ℕ) → ((n : ℕ) → motive 0 n) → ((k n : ℕ) → motive k.succ n) → motive x x_1
```

**定义**

```lean
fun motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-d1db9c5eef3c2f9a"></a>
## `CodedSorting.ArbitraryShapes.borrowEquiv._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ArbitrarySchedule.lean)

**类型**

```lean
∀ {Prefix : Type u_1} {High : Type u_2} {Low : Type u_3} {Gap : Type u_4} {Suffix : Type u_5}
  (a : CodedSorting.ArbitraryShapes.Original),
  CodedSorting.ArbitraryShapes.unborrow (CodedSorting.ArbitraryShapes.borrow a) = a
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.ArbitraryShapes.borrow](ArbitrarySchedule.definitions.md#def-a27ee44d29f8c3b2)
- [CodedSorting.ArbitraryShapes.unborrow](ArbitrarySchedule.definitions.md#def-6bb74f22377adb75)

**基础库名称**

`Eq`

<a id="def-f9520a8bc1014df6"></a>
## `CodedSorting.ArbitraryShapes.borrowEquiv._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ArbitrarySchedule.lean)

**类型**

```lean
∀ {Prefix : Type u_1} {High : Type u_2} {Low : Type u_3} {Gap : Type u_4} {Suffix : Type u_5}
  (a : CodedSorting.ArbitraryShapes.Borrowed),
  CodedSorting.ArbitraryShapes.borrow (CodedSorting.ArbitraryShapes.unborrow a) = a
```

**继续展开**

- [CodedSorting.ArbitraryShapes.borrow](ArbitrarySchedule.definitions.md#def-a27ee44d29f8c3b2)
- [CodedSorting.ArbitraryShapes.unborrow](ArbitrarySchedule.definitions.md#def-6bb74f22377adb75)
- [CodedSorting.ArbitraryShapes.Borrowed](ArbitrarySchedule.definitions.md#def-be433f720c8f210a)

**基础库名称**

`Eq`

<a id="def-f1491f01e8b214df"></a>
## `CodedSorting.ArbitraryShapes.finishEquiv._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ArbitrarySchedule.lean)

**类型**

```lean
∀ {Prefix : Type u_1} {High : Type u_2} {Low : Type u_3} {Gap : Type u_4} {Suffix : Type u_5}
  (a : CodedSorting.ArbitraryShapes.Borrowed),
  {
      prefixCoord :=
        ((CodedSorting.ArbitraryShapes.finish a).prefixCoord, (CodedSorting.ArbitraryShapes.finish a).high.1,
          (CodedSorting.ArbitraryShapes.finish a).low.1),
      high := (CodedSorting.ArbitraryShapes.finish a).high.2, gap := (CodedSorting.ArbitraryShapes.finish a).gap,
      low := (CodedSorting.ArbitraryShapes.finish a).low.2, suffix := (CodedSorting.ArbitraryShapes.finish a).suffix } =
    a
```

**继续展开**

- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.ArbitraryShapes.finish](ArbitrarySchedule.definitions.md#def-88705031c9029134)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.ArbitraryShapes.Borrowed](ArbitrarySchedule.definitions.md#def-be433f720c8f210a)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Prod`, `Eq`, `Prod.snd`

<a id="def-7a7b03c4a69611ad"></a>
## `CodedSorting.ArbitraryShapes.finishEquiv._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ArbitrarySchedule.lean)

**类型**

```lean
∀ {Prefix : Type u_1} {High : Type u_2} {Low : Type u_3} {Gap : Type u_4} {Suffix : Type u_5}
  (a : CodedSorting.ArbitraryShapes.Original),
  CodedSorting.ArbitraryShapes.finish
      { prefixCoord := (a.prefixCoord, a.high.1, a.low.1), high := a.high.2, gap := a.gap, low := a.low.2,
        suffix := a.suffix } =
    a
```

**继续展开**

- [CodedSorting.ArbitraryShapes.Original](ArbitrarySchedule.definitions.md#def-2f6b3990ae076faf)
- [CodedSorting.Address.FullAddress.low](../../../Shared/Memory/Address.definitions.md#def-5d73b599bd447e5e)
- [CodedSorting.ArbitraryShapes.finish](ArbitrarySchedule.definitions.md#def-88705031c9029134)
- [CodedSorting.Address.FullAddress.high](../../../Shared/Memory/Address.definitions.md#def-d2c6338ca38bb153)
- [CodedSorting.Address.FullAddress.mk](../../../Shared/Memory/Address.definitions.md#def-fcedbd9acc430fdc)
- [CodedSorting.Address.FullAddress.prefixCoord](../../../Shared/Memory/Address.definitions.md#def-f205e926ba038664)
- [CodedSorting.Address.FullAddress.gap](../../../Shared/Memory/Address.definitions.md#def-1ec749640a60fa5b)
- [CodedSorting.Address.FullAddress.suffix](../../../Shared/Memory/Address.definitions.md#def-106f0219962d2f0f)

**基础库名称**

`Prod.mk`, `Prod.fst`, `Prod`, `Eq`, `Prod.snd`
