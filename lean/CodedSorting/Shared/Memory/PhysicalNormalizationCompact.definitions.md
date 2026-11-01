# PhysicalNormalizationCompact 的定义

[源码](PhysicalNormalizationCompact.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-312dd55f8d0bedf4"></a>
## `CodedSorting.PhysicalNormalizationCompact.step`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationCompact.lean#L13)

**类型**

```lean
{R B b d w : ℕ} →
  CodedSorting.PhysicalNormalizationLayout.Program R B b d w →
    CodedSorting.PhysicalNormalizationLayout.State R B b d w →
      CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ
```

**定义**

```lean
fun {R B b d w} p s =>
  let j := CodedSorting.PhysicalNormalizationLayout.current s;
  if j < p.blocks then
    match ↑s.phase with
    | 0 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 1
          { buffer := s.disk (Sum.inl (CodedSorting.PhysicalNormalizationLayout.index p j)), scratch := s.scratch,
            counter := s.counter, phase := s.phase, disk := s.disk },
        1)
    | 1 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 2
          { buffer := s.buffer, scratch := fun i => s.buffer (Fin.castLE ⋯ i), counter := s.counter, phase := s.phase,
            disk := s.disk },
        0)
    | 2 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 3
          { buffer := s.disk (Sum.inr (CodedSorting.PhysicalNormalizationLayout.index p (j * b / B))),
            scratch := s.scratch, counter := s.counter, phase := s.phase, disk := s.disk },
        1)
    | 3 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 4
          { buffer := CodedSorting.LayoutConversion.patchBuffer B b (j * b) (j * b / B) s.scratch s.buffer,
            scratch := s.scratch, counter := s.counter, phase := s.phase, disk := s.disk },
        0)
    | 4 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 5
          { buffer := s.buffer, scratch := s.scratch, counter := s.counter, phase := s.phase,
            disk :=
              Function.update s.disk (Sum.inr (CodedSorting.PhysicalNormalizationLayout.index p (j * b / B)))
                s.buffer },
        1)
    | 5 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 6
          { buffer := s.disk (Sum.inr (CodedSorting.PhysicalNormalizationLayout.index p (j * b / B + 1))),
            scratch := s.scratch, counter := s.counter, phase := s.phase, disk := s.disk },
        1)
    | 6 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 7
          { buffer := CodedSorting.LayoutConversion.patchBuffer B b (j * b) (j * b / B + 1) s.scratch s.buffer,
            scratch := s.scratch, counter := s.counter, phase := s.phase, disk := s.disk },
        0)
    | 7 =>
      (CodedSorting.PhysicalNormalizationLayout.nextPhase p 0
          { buffer := s.buffer, scratch := s.scratch,
            counter := CodedSorting.PhysicalNormalizationLayout.counterCode d w (j + 1), phase := s.phase,
            disk :=
              Function.update s.disk (Sum.inr (CodedSorting.PhysicalNormalizationLayout.index p (j * b / B + 1)))
                s.buffer },
        1)
    | x => (s, 0)
  else (s, 0)
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State.buffer](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-c70ce37a8b88fc3e)
- [CodedSorting.PhysicalNormalizationLayout.Address](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-07aca1946acd437c)
- [CodedSorting.PhysicalNormalizationLayout.counterCode](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-92718a548009d747)
- [CodedSorting.PhysicalNormalizationLayout.current](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-8911b9716478d17d)
- [CodedSorting.PhysicalNormalizationLayout.State.counter](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-0f6743e028e821e8)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalNormalizationLayout.Program](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationCompact.step._proof_1](PhysicalNormalizationCompact.definitions.md#def-4bb6f41bf57af622)
- [CodedSorting.PhysicalNormalizationLayout.State.mk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-f8bfca1e966aa73b)
- [CodedSorting.PhysicalNormalizationLayout.nextPhase](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-f08ca752e1e41067)
- [CodedSorting.PhysicalNormalizationLayout.Program.block_ratio](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-5a467ed2df64d58d)
- [CodedSorting.PhysicalNormalizationLayout.Program.blocks](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-7de1abc85c13406f)
- [CodedSorting.PhysicalNormalizationLayout.index](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-acd374e79f7fc86a)
- [CodedSorting.PhysicalNormalizationCompact.step.match_1](PhysicalNormalizationCompact.definitions.md#def-ea0f0a44685b2579)
- [CodedSorting.PhysicalNormalizationLayout.State](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.PhysicalNormalizationLayout.State.disk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-48fddd883aa3f5eb)
- [CodedSorting.WordControl.Words](../Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)
- [CodedSorting.PhysicalNormalizationLayout.State.scratch](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-7a685606d02225f1)
- [CodedSorting.PhysicalNormalizationLayout.State.phase](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-d8014df3dd931356)
- [CodedSorting.LayoutConversion.patchBuffer](../../Interchange/Framework/Memory/LayoutMachine.definitions.md#def-caaf5ace3c9f2f31)

**基础库名称**

`instHDiv`, `Function.update`, `HMul.hMul`, `Fin.castLE`, `Nat.instMonoid`, `instDecidableEqFin`, `Monoid.toNatPow`, `Fin.instOfNat`, `HDiv.hDiv`, `Sum.instDecidableEq`, `Prod.mk`, `instMulNat`, `instOfNatNat`, `Sum.inl`, `Fin.val`, `instHAdd`, `Unit`, `HPow.hPow`, `HAdd.hAdd`, `Sum.inr`, `Nat`, `LT.lt`, `Nat.instDiv`, `Nat.decLt`, `instAddNat`, `instHPow`, `instLTNat`, `Prod`, `OfNat.ofNat`, `Fin`, `instHMul`, `ite`

<a id="def-37963a3a6483170d"></a>
## `CodedSorting.PhysicalNormalizationCompact.run`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationCompact.lean#L28)

**类型**

```lean
{R B b d w : ℕ} →
  CodedSorting.PhysicalNormalizationLayout.Program R B b d w →
    ℕ →
      CodedSorting.PhysicalNormalizationLayout.State R B b d w →
        CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ
```

**定义**

```lean
fun {R B b d w} p x x_1 =>
  Nat.brecOn (motive := fun x =>
    CodedSorting.PhysicalNormalizationLayout.State R B b d w →
      CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ)
    x
    (fun x f x_2 =>
      (match (motive :=
          (x : ℕ) →
            CodedSorting.PhysicalNormalizationLayout.State R B b d w →
              Nat.below (motive := fun x =>
                  CodedSorting.PhysicalNormalizationLayout.State R B b d w →
                    CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ)
                  x →
                CodedSorting.PhysicalNormalizationLayout.State R B b d w × ℕ)
          x, x_2 with
        | 0, s => fun x => (s, 0)
        | fuel.succ, s => fun x =>
          let first := CodedSorting.PhysicalNormalizationCompact.step p s;
          let rest := x.1 first.1;
          (rest.1, first.2 + rest.2))
        f)
    x_1
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationLayout.State](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)
- [CodedSorting.PhysicalNormalizationCompact.run.match_1](PhysicalNormalizationCompact.definitions.md#def-63a70ba26028a6de)
- [CodedSorting.PhysicalNormalizationCompact.step](PhysicalNormalizationCompact.definitions.md#def-312dd55f8d0bedf4)

**基础库名称**

`Nat.brecOn`, `Prod.mk`, `instOfNatNat`, `Prod.fst`, `Nat.below`, `instHAdd`, `PProd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `Prod`, `OfNat.ofNat`, `Nat.succ`, `Prod.snd`

<a id="def-2c2009d41f4dd5b2"></a>
## `CodedSorting.PhysicalNormalizationCompact.targetWord`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](PhysicalNormalizationCompact.lean#L101)

**类型**

```lean
{R B b d w : ℕ} →
  CodedSorting.PhysicalNormalizationLayout.Program R B b d w →
    CodedSorting.PhysicalNormalizationLayout.Disk R B w →
      CodedSorting.BlockReflection.Disk (CodedSorting.WordControl.Word w)
```

**定义**

```lean
fun {R B b d w} p disk y => disk (Sum.inr (CodedSorting.PhysicalNormalizationLayout.index p (y / B))) ⟨y % B, ⋯⟩
```

**继续展开**

- [CodedSorting.BlockReflection.Disk](../../Interchange/Framework/Memory/LayoutMachine.definitions.md#def-1f6cc5cd0ca85726)
- [CodedSorting.PhysicalNormalizationCompact.targetWord._proof_2](PhysicalNormalizationCompact.definitions.md#def-169965a11d3ad99a)
- [CodedSorting.WordControl.Word](../Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.PhysicalNormalizationLayout.Program](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)
- [CodedSorting.PhysicalNormalizationLayout.Disk](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-9e955a98938d0ed5)
- [CodedSorting.PhysicalNormalizationLayout.index](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-acd374e79f7fc86a)

**基础库名称**

`instHDiv`, `Fin.mk`, `HDiv.hDiv`, `Nat.instMod`, `instHMod`, `HMod.hMod`, `Sum.inr`, `Nat`, `Nat.instDiv`, `Fin`

<a id="def-63a70ba26028a6de"></a>
## `CodedSorting.PhysicalNormalizationCompact.run.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PhysicalNormalizationCompact.lean)

**类型**

```lean
{R B b d w : ℕ} →
  (motive : ℕ → CodedSorting.PhysicalNormalizationLayout.State R B b d w → Sort u_1) →
    (x : ℕ) →
      (x_1 : CodedSorting.PhysicalNormalizationLayout.State R B b d w) →
        ((s : CodedSorting.PhysicalNormalizationLayout.State R B b d w) → motive 0 s) →
          ((fuel : ℕ) → (s : CodedSorting.PhysicalNormalizationLayout.State R B b d w) → motive fuel.succ s) →
            motive x x_1
```

**定义**

```lean
fun {R B b d w} motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.State](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-678a62c95e8cebaa)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-4bb6f41bf57af622"></a>
## `CodedSorting.PhysicalNormalizationCompact.step._proof_1`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalNormalizationCompact.lean)

**类型**

```lean
NeZero (7 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-ea0f0a44685b2579"></a>
## `CodedSorting.PhysicalNormalizationCompact.step.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](PhysicalNormalizationCompact.lean)

**类型**

```lean
(motive : ℕ → Sort u_1) →
  (x : ℕ) →
    (Unit → motive 0) →
      (Unit → motive 1) →
        (Unit → motive 2) →
          (Unit → motive 3) →
            (Unit → motive 4) →
              (Unit → motive 5) → (Unit → motive 6) → (Unit → motive 7) → ((x : ℕ) → motive x) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9 =>
  if h_1_1 : x = 0 then ⋯ ▸ ⋯ ▸ h_1 ()
  else
    if h_2_1 : x = 1 then Eq.ndrec (motive := fun x => ¬x = 0 → motive x) (fun h_1 => ⋯ ▸ h_2 ()) ⋯ h_1_1
    else
      if h_3_1 : x = 2 then
        Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → motive x) (fun h_1 h_2 => ⋯ ▸ h_3 ()) ⋯ h_1_1 h_2_1
      else
        if h_4_1 : x = 3 then
          Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → motive x) (fun h_1 h_2 h_3 => ⋯ ▸ h_4 ()) ⋯ h_1_1
            h_2_1 h_3_1
        else
          if h_5_1 : x = 4 then
            Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → motive x)
              (fun h_1 h_2 h_3 h_4 => ⋯ ▸ h_5 ()) ⋯ h_1_1 h_2_1 h_3_1 h_4_1
          else
            if h_6_1 : x = 5 then
              Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → motive x)
                (fun h_1 h_2 h_3 h_4 h_5 => ⋯ ▸ h_6 ()) ⋯ h_1_1 h_2_1 h_3_1 h_4_1 h_5_1
            else
              if h_7_1 : x = 6 then
                Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → motive x)
                  (fun h_1 h_2 h_3 h_4 h_5 h_6 => ⋯ ▸ h_7 ()) ⋯ h_1_1 h_2_1 h_3_1 h_4_1 h_5_1 h_6_1
              else
                if h_8_1 : x = 7 then
                  Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → ¬x = 4 → ¬x = 5 → ¬x = 6 → motive x)
                    (fun h_1 h_2 h_3 h_4 h_5 h_6 h_7 => ⋯ ▸ h_8 ()) ⋯ h_1_1 h_2_1 h_3_1 h_4_1 h_5_1 h_6_1 h_7_1
                else h_9 x
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `instOfNatNat`, `dite`, `Unit`, `Nat`, `Eq.ndrec`, `instDecidableEqNat`, `OfNat.ofNat`, `Eq.symm`, `Eq`, `Not`

<a id="def-169965a11d3ad99a"></a>
## `CodedSorting.PhysicalNormalizationCompact.targetWord._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](PhysicalNormalizationCompact.lean)

**类型**

```lean
∀ {R B b d w : ℕ}, CodedSorting.PhysicalNormalizationLayout.Program R B b d w → ∀ (y : ℕ), y % B < B
```

**继续展开**

- [CodedSorting.PhysicalNormalizationLayout.Program](../../Interchange/Framework/Memory/PhysicalNormalizationLayout.definitions.md#def-ee21ebfead1ec0f6)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`, `LT.lt`, `instLTNat`
