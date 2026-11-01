# BlockDigitMove 的定义

[源码](BlockDigitMove.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-834654c29111ab0e"></a>
## `CodedSorting.BlockDigitMove.castPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockDigitMove.lean#L12)

**类型**

```lean
{V W : ℕ} → V = W → CodedSorting.ScanProgram.Pass V → CodedSorting.ScanProgram.Pass W
```

**定义**

```lean
fun {V W} h => Eq.ndrec (motive := fun {W} => CodedSorting.ScanProgram.Pass V → CodedSorting.ScanProgram.Pass W) id h
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`id`, `Nat`, `Eq.ndrec`, `Eq`

<a id="def-a3f79c8b1137cbb3"></a>
## `CodedSorting.BlockDigitMove.castProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockDigitMove.lean#L18)

**类型**

```lean
{V W : ℕ} → V = W → List (CodedSorting.ScanProgram.Pass V) → List (CodedSorting.ScanProgram.Pass W)
```

**定义**

```lean
fun {V W} h ps => List.map (CodedSorting.BlockDigitMove.castPass h) ps
```

**继续展开**

- [CodedSorting.BlockDigitMove.castPass](BlockDigitMove.definitions.md#def-834654c29111ab0e)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List.map`, `List`, `Nat`, `Eq`

<a id="def-33fd6bed08500715"></a>
## `CodedSorting.BlockDigitMove.digitPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockDigitMove.lean#L31)

**类型**

```lean
(Outer P q S : ℕ) → CodedSorting.ScanProgram.Pass (Outer * (P * (q * S)))
```

**定义**

```lean
fun Outer P q S =>
  CodedSorting.ScanProgram.Pass.streams q (CodedSorting.DigitMove.insidePrefix Outer P q S)
    (CodedSorting.DigitMove.insideKey Outer P q S) ⋯
```

**继续展开**

- [CodedSorting.DigitMove.insidePrefix](../Programs/DigitMove.definitions.md#def-9388cc212aa85359)
- [CodedSorting.DigitMove.insidePrefix_increasing](../Programs/DigitMove.definitions.md#def-29d68fd962bf0a88)
- [CodedSorting.ScanProgram.Pass.streams](../Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.DigitMove.insideKey](../Programs/DigitMove.definitions.md#def-48aa15b586e4acde)

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `instHMul`

<a id="def-750c71c1cda4fe46"></a>
## `CodedSorting.BlockDigitMove.program`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockDigitMove.lean#L35)

**类型**

```lean
(Outer P q S ρ : ℕ) → List (CodedSorting.ScanProgram.Pass (Outer * (P * (q ^ ρ * S))))
```

**定义**

```lean
fun Outer P q S x =>
  Nat.brecOn (motive := fun x => (Outer : ℕ) → List (CodedSorting.ScanProgram.Pass (Outer * (P * (q ^ x * S))))) x
    (fun x f Outer =>
      (match (motive :=
          (x : ℕ) →
            Nat.below (motive := fun x =>
                (Outer : ℕ) → List (CodedSorting.ScanProgram.Pass (Outer * (P * (q ^ x * S))))) x →
              List (CodedSorting.ScanProgram.Pass (Outer * (P * (q ^ x * S)))))
          x with
        | 0 => fun x => []
        | ρ.succ => fun x =>
          CodedSorting.BlockDigitMove.castPass ⋯ (CodedSorting.BlockDigitMove.digitPass Outer P q (q ^ ρ * S)) ::
            CodedSorting.BlockDigitMove.castProgram ⋯ (x.1 (Outer * q)))
        f)
    Outer
```

**继续展开**

- [CodedSorting.BlockDigitMove.castProgram](BlockDigitMove.definitions.md#def-a3f79c8b1137cbb3)
- [CodedSorting.BlockDigitMove.castPass](BlockDigitMove.definitions.md#def-834654c29111ab0e)
- [CodedSorting.BlockDigitMove.program._proof_2](BlockDigitMove.definitions.md#def-3b3a388edb9ca1fc)
- [CodedSorting.BlockDigitMove.program.match_1](BlockDigitMove.definitions.md#def-82a3236c0d237fd2)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.BlockDigitMove.digitPass](BlockDigitMove.definitions.md#def-33fd6bed08500715)
- [CodedSorting.BlockDigitMove.program._proof_1](BlockDigitMove.definitions.md#def-5c8b327894a883d9)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `Nat.brecOn`, `instMulNat`, `instOfNatNat`, `List.cons`, `Nat.below`, `List`, `instHAdd`, `Unit`, `PProd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Nat.succ`, `instHMul`, `List.nil`

<a id="def-5a42fe446735dbd5"></a>
## `CodedSorting.BlockDigitMove.invertPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockDigitMove.lean#L149)

**类型**

```lean
{V : ℕ} → CodedSorting.ScanProgram.Pass V → CodedSorting.ScanProgram.Pass V
```

**定义**

```lean
fun {V} x =>
  match x with
  | CodedSorting.ScanProgram.Pass.streams K e key hi =>
    CodedSorting.ScanProgram.Pass.streams K (Equiv.symm e) (fun y => key ((Equiv.symm e) y)) ⋯
  | CodedSorting.ScanProgram.Pass.reverse T L hL hV => CodedSorting.ScanProgram.Pass.reverse T L hL hV
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.streams](../Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.AffineStreams.inverse_increasing_streams](../../Circuit/Framework/AffineStreams.definitions.md#def-03a3a779aefd1efc)
- [CodedSorting.ScanProgram.Pass.reverse](../Programs/ScanProgramLift.definitions.md#def-b047d60fca52cebe)
- [CodedSorting.BlockDigitMove.invertPass.match_1](BlockDigitMove.definitions.md#def-9c01ee7d277c9dda)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `Equiv.symm`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-1c938335a9d18c4c"></a>
## `CodedSorting.BlockDigitMove.inverseProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](BlockDigitMove.lean#L155)

**类型**

```lean
{V : ℕ} → List (CodedSorting.ScanProgram.Pass V) → List (CodedSorting.ScanProgram.Pass V)
```

**定义**

```lean
fun {V} ps => List.map CodedSorting.BlockDigitMove.invertPass ps.reverse
```

**继续展开**

- [CodedSorting.BlockDigitMove.invertPass](BlockDigitMove.definitions.md#def-5a42fe446735dbd5)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List.map`, `List`, `Nat`, `List.reverse`

<a id="def-9c01ee7d277c9dda"></a>
## `CodedSorting.BlockDigitMove.invertPass.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](BlockDigitMove.lean)

**类型**

```lean
{V : ℕ} →
  (motive : CodedSorting.ScanProgram.Pass V → Sort u_1) →
    (x : CodedSorting.ScanProgram.Pass V) →
      ((K : ℕ) →
          (e : Equiv.Perm (Fin V)) →
            (key : Fin V → Fin K) →
              (hi : ∀ (x y : Fin V), x < y → key x = key y → e x < e y) →
                motive (CodedSorting.ScanProgram.Pass.streams K e key hi)) →
        ((T L : ℕ) → (hL : 0 < L) → (hV : T * L = V) → motive (CodedSorting.ScanProgram.Pass.reverse T L hL hV)) →
          motive x
```

**定义**

```lean
fun {V} motive x h_1 h_2 =>
  CodedSorting.ScanProgram.Pass.casesOn x (fun K e key increasing => h_1 K e key increasing) fun T L positive volume =>
    h_2 T L positive volume
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.streams](../Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.reverse](../Programs/ScanProgramLift.definitions.md#def-b047d60fca52cebe)
- [CodedSorting.ScanProgram.Pass.casesOn](../Programs/ScanProgramLift.definitions.md#def-15ff2a35b3786ae1)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-5c8b327894a883d9"></a>
## `CodedSorting.BlockDigitMove.program._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BlockDigitMove.lean)

**类型**

```lean
∀ (P q S Outer ρ : ℕ), Outer * (P * (q * (q ^ ρ * S))) = Outer * (P * (q ^ (ρ + 1) * S))
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-3b3a388edb9ca1fc"></a>
## `CodedSorting.BlockDigitMove.program._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](BlockDigitMove.lean)

**类型**

```lean
∀ (P q S Outer ρ : ℕ), Outer * q * (P * (q ^ ρ * S)) = Outer * (P * (q ^ (ρ + 1) * S))
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-82a3236c0d237fd2"></a>
## `CodedSorting.BlockDigitMove.program.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](BlockDigitMove.lean)

**类型**

```lean
(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((ρ : ℕ) → motive ρ.succ) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 => Nat.casesOn x (h_1 ()) fun n => h_2 n
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `instOfNatNat`, `Unit`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`
