# ScanProgramLift 的定义

[源码](ScanProgramLift.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-2e6b419ef8754e59"></a>
## `CodedSorting.ScanProgram.Pass`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](ScanProgramLift.lean#L16)

**类型**

```lean
ℕ → Type
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.streams](ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass.reverse](ScanProgramLift.definitions.md#def-b047d60fca52cebe)

**基础库名称**

`Nat`

<a id="def-15ff2a35b3786ae1"></a>
## `CodedSorting.ScanProgram.Pass.casesOn`

读取 `CodedSorting.ScanProgram.Pass` 的 `casesOn` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ScanProgramLift.lean#L16)

**类型**

```lean
{V : ℕ} →
  {motive : CodedSorting.ScanProgram.Pass V → Sort u} →
    (t : CodedSorting.ScanProgram.Pass V) →
      ((K : ℕ) →
          (e : Equiv.Perm (Fin V)) →
            (key : Fin V → Fin K) →
              (increasing : ∀ (x y : Fin V), x < y → key x = key y → e x < e y) →
                motive (CodedSorting.ScanProgram.Pass.streams K e key increasing)) →
        ((T L : ℕ) →
            (positive : 0 < L) →
              (volume : T * L = V) → motive (CodedSorting.ScanProgram.Pass.reverse T L positive volume)) →
          motive t
```

**定义**

```lean
fun {V} {motive} t streams reverse =>
  CodedSorting.ScanProgram.Pass.rec (fun K e key increasing => streams K e key increasing)
    (fun T L positive volume => reverse T L positive volume) t
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.rec](ScanProgramLift.definitions.md#def-13aa0adad0361d04)
- [CodedSorting.ScanProgram.Pass.streams](ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.reverse](ScanProgramLift.definitions.md#def-b047d60fca52cebe)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-13aa0adad0361d04"></a>
## `CodedSorting.ScanProgram.Pass.rec`

Lean 自动生成的递归函数：先判断值由哪种方式构成，再分别处理其中的数据；遇到同一类型的子项时，使用对子项递归计算的结果。

[源码位置](ScanProgramLift.lean#L16)

**类型**

```lean
{V : ℕ} →
  {motive : CodedSorting.ScanProgram.Pass V → Sort u} →
    ((K : ℕ) →
        (e : Equiv.Perm (Fin V)) →
          (key : Fin V → Fin K) →
            (increasing : ∀ (x y : Fin V), x < y → key x = key y → e x < e y) →
              motive (CodedSorting.ScanProgram.Pass.streams K e key increasing)) →
      ((T L : ℕ) →
          (positive : 0 < L) →
            (volume : T * L = V) → motive (CodedSorting.ScanProgram.Pass.reverse T L positive volume)) →
        (t : CodedSorting.ScanProgram.Pass V) → motive t
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.streams](ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.reverse](ScanProgramLift.definitions.md#def-b047d60fca52cebe)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-bd709324b13ade68"></a>
## `CodedSorting.ScanProgram.Pass.streams`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ScanProgramLift.lean#L17)

**类型**

```lean
{V : ℕ} →
  (K : ℕ) →
    (e : Equiv.Perm (Fin V)) →
      (key : Fin V → Fin K) → (∀ (x y : Fin V), x < y → key x = key y → e x < e y) → CodedSorting.ScanProgram.Pass V
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Equiv.instFunLike`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`, `DFunLike.coe`

<a id="def-b047d60fca52cebe"></a>
## `CodedSorting.ScanProgram.Pass.reverse`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](ScanProgramLift.lean#L19)

**类型**

```lean
{V : ℕ} → (T L : ℕ) → 0 < L → T * L = V → CodedSorting.ScanProgram.Pass V
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Eq`, `instHMul`

<a id="def-3add1298a3eb5e54"></a>
## `CodedSorting.ScanProgram.reversePerm`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgramLift.lean#L21)

**类型**

```lean
{V : ℕ} → (T L : ℕ) → T * L = V → Equiv.Perm (Fin V)
```

**定义**

```lean
fun {V} T L hV =>
  (finCongr hV).symm.trans (Equiv.trans (CodedSorting.BlockReflection.segmentReverseEquiv T L) (finCongr hV))
```

**继续展开**

- [CodedSorting.BlockReflection.segmentReverseEquiv](../../Interchange/Framework/Memory/LayoutMachine.definitions.md#def-5d59a52eabcd3361)

**基础库名称**

`HMul.hMul`, `Equiv.trans`, `finCongr`, `instMulNat`, `Equiv.Perm`, `Nat`, `Equiv.symm`, `Fin`, `Eq`, `instHMul`

<a id="def-2e82928d66382ba3"></a>
## `CodedSorting.ScanProgram.Pass.permutation`

读取 `CodedSorting.ScanProgram.Pass` 的 `permutation` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ScanProgramLift.lean#L37)

**类型**

```lean
{V : ℕ} → CodedSorting.ScanProgram.Pass V → Equiv.Perm (Fin V)
```

**定义**

```lean
fun {V} x =>
  match x with
  | CodedSorting.ScanProgram.Pass.streams K e key increasing => e
  | CodedSorting.ScanProgram.Pass.reverse T L positive hV => CodedSorting.ScanProgram.reversePerm T L hV
```

**继续展开**

- [CodedSorting.ScanProgram.reversePerm](ScanProgramLift.definitions.md#def-3add1298a3eb5e54)
- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.permutation.match_1](ScanProgramLift.definitions.md#def-ea941d91cbc702ec)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-e92eeeec1e2c268e"></a>
## `CodedSorting.ScanProgram.Pass.constant`

读取 `CodedSorting.ScanProgram.Pass` 的 `constant` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](ScanProgramLift.lean#L41)

**类型**

```lean
{V : ℕ} → CodedSorting.ScanProgram.Pass V → ℕ
```

**定义**

```lean
fun {V} x =>
  match x with
  | CodedSorting.ScanProgram.Pass.streams K e key increasing => 2 * K + 6
  | CodedSorting.ScanProgram.Pass.reverse T L positive volume => 5
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.permutation.match_1](ScanProgramLift.definitions.md#def-ea941d91cbc702ec)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instAddNat`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-e72f845372e79c59"></a>
## `CodedSorting.ScanProgram.totalConstant`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgramLift.lean#L110)

**类型**

```lean
{V : ℕ} → List (CodedSorting.ScanProgram.Pass V) → ℕ
```

**定义**

```lean
fun {V} ps => (List.map CodedSorting.ScanProgram.Pass.constant ps).sum
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.constant](ScanProgramLift.definitions.md#def-e92eeeec1e2c268e)
- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Nat.instMulZeroClass`, `List.map`, `List.sum`, `List`, `Nat`, `instAddNat`, `MulZeroClass.toZero`

<a id="def-155edcb120b335e1"></a>
## `CodedSorting.ScanProgram.destination`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgramLift.lean#L133)

**类型**

```lean
{V : ℕ} → List (CodedSorting.ScanProgram.Pass V) → Equiv.Perm (Fin V)
```

**定义**

```lean
fun {V} x =>
  List.brecOn x fun x f =>
    (match (motive := (x : List (CodedSorting.ScanProgram.Pass V)) → List.below x → Equiv.Perm (Fin V)) x with
      | [] => fun x => Equiv.refl (Fin V)
      | p :: ps => fun x => Equiv.trans p.permutation x.1)
      f
```

**继续展开**

- [CodedSorting.ScanProgram.destination.match_1](ScanProgramLift.definitions.md#def-34e5020522b847e0)
- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.permutation](ScanProgramLift.definitions.md#def-2e82928d66382ba3)

**基础库名称**

`List.brecOn`, `Equiv.trans`, `List.cons`, `List`, `Unit`, `PProd`, `Equiv.Perm`, `Nat`, `List.below`, `Fin`, `Equiv.refl`, `List.nil`

<a id="def-8c1fdfde71012a45"></a>
## `CodedSorting.ScanProgramLift.fieldReflections`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgramLift.lean#L175)

**类型**

```lean
{V : ℕ} → (P Q S : ℕ) → 0 < Q → 0 < S → P * (Q * S) = V → List (CodedSorting.ScanProgram.Pass V)
```

**定义**

```lean
fun {V} P Q S hQ hS hV =>
  [CodedSorting.ScanProgram.Pass.reverse P (Q * S) ⋯ hV, CodedSorting.ScanProgram.Pass.reverse (P * Q) S hS ⋯]
```

**继续展开**

- [CodedSorting.ScanProgramLift.fieldReflections._proof_1](ScanProgramLift.definitions.md#def-1ccdc6838f8302d7)
- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.reverse](ScanProgramLift.definitions.md#def-b047d60fca52cebe)

**基础库名称**

`HMul.hMul`, `Nat.mul_pos`, `instMulNat`, `instOfNatNat`, `List.cons`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Eq`, `instHMul`, `List.nil`

<a id="def-a5957be6c70c10e6"></a>
## `CodedSorting.ScanProgramLift.liftedVolume`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ScanProgramLift.lean#L194)

**类型**

```lean
∀ {V P S : ℕ} (T L : ℕ), T * L = V → P * T * (L * S) = P * (V * S)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`

<a id="def-cda9c7e596558f86"></a>
## `CodedSorting.ScanProgramLift.liftPass`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgramLift.lean#L209)

**类型**

```lean
{V : ℕ} → (P S : ℕ) → 0 < S → CodedSorting.ScanProgram.Pass V → List (CodedSorting.ScanProgram.Pass (P * (V * S)))
```

**定义**

```lean
fun {V} P S hS x =>
  match x with
  | CodedSorting.ScanProgram.Pass.streams K e key hi =>
    [CodedSorting.ScanProgram.Pass.streams K (CodedSorting.TriangularStreams.globalFieldEquiv fun x => e)
        (CodedSorting.TriangularStreams.globalKey fun x => key) ⋯]
  | CodedSorting.ScanProgram.Pass.reverse T L hL hV => CodedSorting.ScanProgramLift.fieldReflections (P * T) L S hL hS ⋯
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.streams](ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgramLift.liftedVolume](ScanProgramLift.definitions.md#def-a5957be6c70c10e6)
- [CodedSorting.ScanProgram.Pass.permutation.match_1](ScanProgramLift.definitions.md#def-ea941d91cbc702ec)
- [CodedSorting.ScanProgramLift.fieldReflections](ScanProgramLift.definitions.md#def-8c1fdfde71012a45)
- [CodedSorting.TriangularStreams.globalKey](../../Circuit/Framework/TriangularStreams.definitions.md#def-f272f59e3f07df97)
- [CodedSorting.ScanProgramLift.liftPass._proof_2](ScanProgramLift.definitions.md#def-ad10c99d3d6a3bcd)
- [CodedSorting.TriangularStreams.globalFieldEquiv](../../Circuit/Framework/TriangularStreams.definitions.md#def-512e9a6065bbe891)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `List.cons`, `List`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`, `List.nil`

<a id="def-08274d7795e99cb8"></a>
## `CodedSorting.ScanProgramLift.liftProgram`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgramLift.lean#L238)

**类型**

```lean
{V : ℕ} →
  (P S : ℕ) → 0 < S → List (CodedSorting.ScanProgram.Pass V) → List (CodedSorting.ScanProgram.Pass (P * (V * S)))
```

**定义**

```lean
fun {V} P S hS ps => List.flatMap (CodedSorting.ScanProgramLift.liftPass P S hS) ps
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgramLift.liftPass](ScanProgramLift.definitions.md#def-cda9c7e596558f86)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `List.flatMap`, `instHMul`

<a id="def-ea941d91cbc702ec"></a>
## `CodedSorting.ScanProgram.Pass.permutation.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ScanProgramLift.lean)

**类型**

```lean
{V : ℕ} →
  (motive : CodedSorting.ScanProgram.Pass V → Sort u_1) →
    (x : CodedSorting.ScanProgram.Pass V) →
      ((K : ℕ) →
          (e : Equiv.Perm (Fin V)) →
            (key : Fin V → Fin K) →
              (increasing : ∀ (x y : Fin V), x < y → key x = key y → e x < e y) →
                motive (CodedSorting.ScanProgram.Pass.streams K e key increasing)) →
        ((T L : ℕ) →
            (positive : 0 < L) → (hV : T * L = V) → motive (CodedSorting.ScanProgram.Pass.reverse T L positive hV)) →
          motive x
```

**定义**

```lean
fun {V} motive x h_1 h_2 =>
  CodedSorting.ScanProgram.Pass.casesOn x (fun K e key increasing => h_1 K e key increasing) fun T L positive volume =>
    h_2 T L positive volume
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.streams](ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.reverse](ScanProgramLift.definitions.md#def-b047d60fca52cebe)
- [CodedSorting.ScanProgram.Pass.casesOn](ScanProgramLift.definitions.md#def-15ff2a35b3786ae1)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-34e5020522b847e0"></a>
## `CodedSorting.ScanProgram.destination.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ScanProgramLift.lean)

**类型**

```lean
{V : ℕ} →
  (motive : List (CodedSorting.ScanProgram.Pass V) → Sort u_1) →
    (x : List (CodedSorting.ScanProgram.Pass V)) →
      (Unit → motive []) →
        ((p : CodedSorting.ScanProgram.Pass V) → (ps : List (CodedSorting.ScanProgram.Pass V)) → motive (p :: ps)) →
          motive x
```

**定义**

```lean
fun {V} motive x h_1 h_2 => List.casesOn x (h_1 ()) fun head tail => h_2 head tail
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `Nat`, `List.casesOn`, `List.nil`

<a id="def-1ccdc6838f8302d7"></a>
## `CodedSorting.ScanProgramLift.fieldReflections._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ScanProgramLift.lean)

**类型**

```lean
∀ {V : ℕ} (P Q S : ℕ), P * (Q * S) = V → P * Q * S = V
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`HMul.hMul`, `instMulNat`, `Nat`, `Eq`, `instHMul`

<a id="def-ad10c99d3d6a3bcd"></a>
## `CodedSorting.ScanProgramLift.liftPass._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](ScanProgramLift.lean)

**类型**

```lean
∀ {V : ℕ} (P S K : ℕ) (e : Equiv.Perm (Fin V)) (key : Fin V → Fin K),
  (∀ (x y : Fin V), x < y → key x = key y → e x < e y) →
    ∀ (x y : Fin (P * (V * S))),
      x < y →
        CodedSorting.TriangularStreams.globalKey (fun x => key) x =
            CodedSorting.TriangularStreams.globalKey (fun x => key) y →
          (CodedSorting.TriangularStreams.globalFieldEquiv fun x => e) x <
            (CodedSorting.TriangularStreams.globalFieldEquiv fun x => e) y
```

**继续展开**

- [CodedSorting.TriangularStreams.globalKey](../../Circuit/Framework/TriangularStreams.definitions.md#def-f272f59e3f07df97)
- [CodedSorting.TriangularStreams.globalFieldEquiv](../../Circuit/Framework/TriangularStreams.definitions.md#def-512e9a6065bbe891)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`
