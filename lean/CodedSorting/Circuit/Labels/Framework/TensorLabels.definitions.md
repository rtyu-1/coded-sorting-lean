# TensorLabels 的定义

[源码](TensorLabels.lean) · [主定理导读](../../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-a5a55f5aababa4ea"></a>
## `CodedSorting.TensorLabels.tensor3`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLabels.lean#L106)

**类型**

```lean
{a : Type u_1} →
  {b : Type u_2} →
    {c : Type u_3} →
      {x : Type u_4} →
        {y : Type u_5} → {z : Type u_6} → Matrix a x ℚ → Matrix b y ℚ → Matrix c z ℚ → Matrix (a × b × c) (x × y × z) ℚ
```

**定义**

```lean
fun {a} {b} {c} {x} {y} {z} A B C =>
  Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) B C)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Rat.instMul`, `HMul.hMul`, `Matrix`, `Rat`, `Matrix.kroneckerMap`, `Prod`, `instHMul`

<a id="def-ef6f5b34a23a6f4c"></a>
## `CodedSorting.TensorLabels.H`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLabels.lean#L138)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun d => Fin d × Fin d × Fin d
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat`, `Prod`, `Fin`

<a id="def-43a4598c9218b5b2"></a>
## `CodedSorting.TensorLabels.Label`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLabels.lean#L139)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun d => Matrix (CodedSorting.TensorLabels.H d) (CodedSorting.TensorLabels.H d) ℚ
```

**继续展开**

- [CodedSorting.TensorLabels.H](TensorLabels.definitions.md#def-ef6f5b34a23a6f4c)

**基础库名称**

`Matrix`, `Rat`, `Nat`

<a id="def-3d1791b695e4d854"></a>
## `CodedSorting.TensorLabels.stageLabels`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](TensorLabels.lean#L777)

**类型**

```lean
{d : ℕ} →
  {G : Type u_1} →
    (G → Bool) →
      (G → CodedSorting.TensorLabels.Label d) →
        CodedSorting.TensorLabels.Label d → List G → List (CodedSorting.TensorLabels.Label d)
```

**定义**

```lean
fun {d} {G} active label P x =>
  List.brecOn (motive := fun x => CodedSorting.TensorLabels.Label d → List (CodedSorting.TensorLabels.Label d)) x
    (fun x f P =>
      (match (motive :=
          (x : List G) →
            List.below (motive := fun x => CodedSorting.TensorLabels.Label d → List (CodedSorting.TensorLabels.Label d))
                x →
              List (CodedSorting.TensorLabels.Label d))
          x with
        | [] => fun x => []
        | g :: gs => fun x =>
          let Q := if active g = true then label g else P;
          Q :: x.1 Q)
        f)
    P
```

**继续展开**

- [CodedSorting.TensorLabels.Label](TensorLabels.definitions.md#def-43a4598c9218b5b2)
- [CodedSorting.TensorLabels.stageLabels.match_1](TensorLabels.definitions.md#def-67599d93170d2842)

**基础库名称**

`List.brecOn`, `instDecidableEqBool`, `List.cons`, `Bool.true`, `List`, `Unit`, `PProd`, `Nat`, `Bool`, `List.below`, `Eq`, `List.nil`, `ite`

<a id="def-67599d93170d2842"></a>
## `CodedSorting.TensorLabels.stageLabels.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](TensorLabels.lean)

**类型**

```lean
{G : Type u_1} →
  (motive : List G → Sort u_2) →
    (x : List G) → (Unit → motive []) → ((g : G) → (gs : List G) → motive (g :: gs)) → motive x
```

**定义**

```lean
fun {G} motive x h_1 h_2 => List.casesOn x (h_1 ()) fun head tail => h_2 head tail
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `List.cons`, `List`, `Unit`, `List.casesOn`, `List.nil`
