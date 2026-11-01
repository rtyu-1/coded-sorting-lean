# ScanProgram 的定义

[源码](ScanProgram.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-a3f8f7609a0933eb"></a>
## `CodedSorting.CommonScanProgram.passCode`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgram.lean#L14)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V : ℕ} →
    Fin q.inventory.readers →
      CodedSorting.ScanProgram.Pass V → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q {V} reader p source target =>
  match p with
  | CodedSorting.ScanProgram.Pass.streams K e key increasing =>
    CodedSorting.CommonPermutationScan.program q reader e key source target
  | CodedSorting.ScanProgram.Pass.reverse T L positive volume =>
    CodedSorting.CommonReflection.code q reader T L source target
```

**继续展开**

- [CodedSorting.CommonScanProgram.passCode.match_1](ScanProgram.definitions.md#def-7c9bf9408a1e6dad)
- [CodedSorting.CommonPermutationScan.program](../../Interchange/Framework/Memory/Reflection.definitions.md#def-40c5a71a42c86359)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonReflection.code](../../Interchange/Framework/Memory/Reflection.definitions.md#def-4be803cd6e4d42f8)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `List`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`

<a id="def-9aed89b5c5f3201c"></a>
## `CodedSorting.CommonScanProgram.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgram.lean#L73)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  {V : ℕ} →
    Fin q.inventory.readers →
      List (CodedSorting.ScanProgram.Pass V) → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q {V} reader x x_1 x_2 =>
  List.brecOn (motive := fun x => ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x
    (fun x f x_3 x_4 =>
      (match (motive :=
          (x : List (CodedSorting.ScanProgram.Pass V)) →
            ℕ →
              ℕ →
                List.below (motive := fun x => ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)) x →
                  List (CodedSorting.CommonStaticSchedule.Instruction q))
          x, x_3, x_4 with
        | [], x, x_5 => fun x => []
        | p :: ps, source, target => fun x =>
          CodedSorting.CommonScanProgram.passCode q reader p source target ++ x.1 target source)
        f)
    x_1 x_2
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonScanProgram.code.match_1](ScanProgram.definitions.md#def-141c43ecfe0305fe)
- [CodedSorting.SortingResourceBudget.Inventory.readers](../../Sorting/Bounds/SortingResourceBudget.definitions.md#def-57a55c8de06b50b7)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Sorting/Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonScanProgram.passCode](ScanProgram.definitions.md#def-a3f8f7609a0933eb)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List.brecOn`, `List.cons`, `instHAppendOfAppend`, `List`, `PProd`, `Nat`, `List.below`, `List.instAppend`, `Fin`, `HAppend.hAppend`, `List.nil`

<a id="def-f5f05a8abbd2e902"></a>
## `CodedSorting.CommonScanProgram.finalBase`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](ScanProgram.lean#L78)

**类型**

```lean
{V : ℕ} → List (CodedSorting.ScanProgram.Pass V) → ℕ → ℕ → ℕ
```

**定义**

```lean
fun {V} x x_1 x_2 =>
  List.brecOn (motive := fun x => ℕ → ℕ → ℕ) x
    (fun x f x_3 x_4 =>
      (match (motive :=
          (x : List (CodedSorting.ScanProgram.Pass V)) → ℕ → ℕ → List.below (motive := fun x => ℕ → ℕ → ℕ) x → ℕ) x,
          x_3, x_4 with
        | [], x, x_5 => fun x_6 => x
        | p :: ps, source, target => fun x => x.1 target source)
        f)
    x_1 x_2
```

**继续展开**

- [CodedSorting.CommonScanProgram.code.match_1](ScanProgram.definitions.md#def-141c43ecfe0305fe)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List.brecOn`, `List.cons`, `List`, `PProd`, `Nat`, `List.below`, `List.nil`

<a id="def-141c43ecfe0305fe"></a>
## `CodedSorting.CommonScanProgram.code.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ScanProgram.lean)

**类型**

```lean
{V : ℕ} →
  (motive : List (CodedSorting.ScanProgram.Pass V) → ℕ → ℕ → Sort u_1) →
    (x : List (CodedSorting.ScanProgram.Pass V)) →
      (x_1 x_2 : ℕ) →
        ((x x_3 : ℕ) → motive [] x x_3) →
          ((p : CodedSorting.ScanProgram.Pass V) →
              (ps : List (CodedSorting.ScanProgram.Pass V)) → (source target : ℕ) → motive (p :: ps) source target) →
            motive x x_1 x_2
```

**定义**

```lean
fun {V} motive x x_1 x_2 h_1 h_2 => List.casesOn x (h_1 x_1 x_2) fun head tail => h_2 head tail x_1 x_2
```

**继续展开**

- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)

**基础库名称**

`List.cons`, `List`, `Nat`, `List.casesOn`, `List.nil`

<a id="def-7c9bf9408a1e6dad"></a>
## `CodedSorting.CommonScanProgram.passCode.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](ScanProgram.lean)

**类型**

```lean
{V : ℕ} →
  (motive : CodedSorting.ScanProgram.Pass V → Sort u_1) →
    (p : CodedSorting.ScanProgram.Pass V) →
      ((K : ℕ) →
          (e : Equiv.Perm (Fin V)) →
            (key : Fin V → Fin K) →
              (increasing : ∀ (x y : Fin V), x < y → key x = key y → e x < e y) →
                motive (CodedSorting.ScanProgram.Pass.streams K e key increasing)) →
        ((T L : ℕ) →
            (positive : 0 < L) →
              (volume : T * L = V) → motive (CodedSorting.ScanProgram.Pass.reverse T L positive volume)) →
          motive p
```

**定义**

```lean
fun {V} motive p h_1 h_2 =>
  CodedSorting.ScanProgram.Pass.casesOn p (fun K e key increasing => h_1 K e key increasing) fun T L positive volume =>
    h_2 T L positive volume
```

**继续展开**

- [CodedSorting.ScanProgram.Pass.streams](../Programs/ScanProgramLift.definitions.md#def-bd709324b13ade68)
- [CodedSorting.ScanProgram.Pass](../Programs/ScanProgramLift.definitions.md#def-2e6b419ef8754e59)
- [CodedSorting.ScanProgram.Pass.reverse](../Programs/ScanProgramLift.definitions.md#def-b047d60fca52cebe)
- [CodedSorting.ScanProgram.Pass.casesOn](../Programs/ScanProgramLift.definitions.md#def-15ff2a35b3786ae1)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `instMulNat`, `instOfNatNat`, `Equiv.Perm`, `Nat`, `LT.lt`, `instLTFin`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Eq`, `DFunLike.coe`, `instHMul`
