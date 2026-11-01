# PhysicalStreamCursor 的定义

[源码](PhysicalStreamCursor.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-0b39ac6782c7ab72"></a>
## `CodedSorting.PhysicalStreamCursor.encodeNat`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalStreamCursor.lean#L354)

**类型**

```lean
(d w : ℕ) → ℕ → CodedSorting.WordControl.Words d w
```

**定义**

```lean
fun d w n => finFunctionFinEquiv.symm ⟨n % (2 ^ w) ^ d, ⋯⟩
```

**继续展开**

- [CodedSorting.StreamResidentEncoding.encode._proof_3](PhysicalStreamCursor.definitions.md#def-2c11bc295658ab29)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`Equiv.instFunLike`, `Nat.instMonoid`, `finFunctionFinEquiv`, `Monoid.toNatPow`, `Fin.mk`, `Equiv`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `HMod.hMod`, `HPow.hPow`, `Nat`, `instHPow`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `DFunLike.coe`

<a id="def-e3e2890b8a9b4db3"></a>
## `CodedSorting.PhysicalStreamCursor.blockCount`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalStreamCursor.lean#L385)

**类型**

```lean
ℕ → ℕ → ℕ
```

**定义**

```lean
fun B records => (records + B - 1) / B
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`instHDiv`, `HSub.hSub`, `HDiv.hDiv`, `instSubNat`, `instOfNatNat`, `instHAdd`, `instHSub`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`, `OfNat.ofNat`

<a id="def-2c11bc295658ab29"></a>
## `CodedSorting.StreamResidentEncoding.encode._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalStreamCursor.lean)

**类型**

```lean
∀ (d w cursor : ℕ), cursor % (2 ^ w) ^ d < (2 ^ w) ^ d
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.instMod`, `instHMod`, `instOfNatNat`, `HMod.hMod`, `HPow.hPow`, `Nat`, `LT.lt`, `instHPow`, `instLTNat`, `OfNat.ofNat`
