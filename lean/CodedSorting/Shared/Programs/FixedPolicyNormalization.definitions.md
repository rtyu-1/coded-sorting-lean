# FixedPolicyNormalization 的定义

[源码](FixedPolicyNormalization.lean) · [主定理导读](../../Sorting/Theorem31/Definitions.zh-CN.md) · [基础概念](../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-6aba48f221a7029d"></a>
## `CodedSorting.FixedPolicyNormalization.Word`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FixedPolicyNormalization.lean#L302)

**类型**

```lean
ℕ → Type
```

**定义**

```lean
fun w => Fin (2 ^ w)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-2576571b58804cf6"></a>
## `CodedSorting.FixedPolicyNormalization.Program`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](FixedPolicyNormalization.lean#L304)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.Program.mk](FixedPolicyNormalization.definitions.md#def-8dc84ed3cbacb15d)

**基础库名称**

`Nat`

<a id="def-8dc84ed3cbacb15d"></a>
## `CodedSorting.FixedPolicyNormalization.Program.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](FixedPolicyNormalization.lean#L306)

**类型**

```lean
{L b D w : ℕ} →
  CodedSorting.ControlledNormalization.Policy L b D (CodedSorting.FixedPolicyNormalization.Word w) →
    CodedSorting.FixedPolicyNormalization.Program L b D w
```

**继续展开**

- [CodedSorting.ControlledNormalization.Policy](ControlledNormalization.definitions.md#def-311feb3c44e69784)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.FixedPolicyNormalization.Program](FixedPolicyNormalization.definitions.md#def-2576571b58804cf6)

**基础库名称**

`Nat`

<a id="def-4db99f43c099a6e8"></a>
## `CodedSorting.FixedPolicyNormalization.Program.policy`

读取 `CodedSorting.FixedPolicyNormalization.Program` 的 `policy` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FixedPolicyNormalization.lean#L307)

**类型**

```lean
{L b D w : ℕ} →
  CodedSorting.FixedPolicyNormalization.Program L b D w →
    CodedSorting.ControlledNormalization.Policy L b D (CodedSorting.FixedPolicyNormalization.Word w)
```

**定义**

```lean
fun L b D w self => self.1
```

**继续展开**

- [CodedSorting.ControlledNormalization.Policy](ControlledNormalization.definitions.md#def-311feb3c44e69784)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.FixedPolicyNormalization.Program](FixedPolicyNormalization.definitions.md#def-2576571b58804cf6)

**基础库名称**

`Nat`

<a id="def-649028e1590de6aa"></a>
## `CodedSorting.FixedPolicyNormalization.State`

下面列出这个类型或关系的所有构造方式。若它是一个结构，可以据此查看全部字段；若它是执行关系，可以据此查看允许哪些步骤。

[源码位置](FixedPolicyNormalization.lean#L309)

**类型**

```lean
ℕ → ℕ → ℕ → ℕ → Type
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.State.mk](FixedPolicyNormalization.definitions.md#def-ab55087183329d74)

**基础库名称**

`Nat`

<a id="def-ab55087183329d74"></a>
## `CodedSorting.FixedPolicyNormalization.State.mk`

按这个类型列出的参数构造一个值或一段执行证明。参数中的数据字段、条件和前后状态决定该构造方式的含义。

[源码位置](FixedPolicyNormalization.lean#L311)

**类型**

```lean
{L B D w : ℕ} →
  CodedSorting.Normalization.PhysicalState L B D (CodedSorting.FixedPolicyNormalization.Word w) →
    CodedSorting.FixedPolicyNormalization.Word w → CodedSorting.FixedPolicyNormalization.State L B D w
```

**继续展开**

- [CodedSorting.Normalization.PhysicalState](Normalization.definitions.md#def-fd728dbf7842361d)
- [CodedSorting.FixedPolicyNormalization.State](FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)

**基础库名称**

`Nat`

<a id="def-b353367b3b3b5fbc"></a>
## `CodedSorting.FixedPolicyNormalization.State.data`

读取 `CodedSorting.FixedPolicyNormalization.State` 的 `data` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FixedPolicyNormalization.lean#L312)

**类型**

```lean
{L B D w : ℕ} →
  CodedSorting.FixedPolicyNormalization.State L B D w →
    CodedSorting.Normalization.PhysicalState L B D (CodedSorting.FixedPolicyNormalization.Word w)
```

**定义**

```lean
fun L B D w self => self.1
```

**继续展开**

- [CodedSorting.Normalization.PhysicalState](Normalization.definitions.md#def-fd728dbf7842361d)
- [CodedSorting.FixedPolicyNormalization.State](FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)

**基础库名称**

`Nat`

<a id="def-8811097908191dac"></a>
## `CodedSorting.FixedPolicyNormalization.State.phase`

读取 `CodedSorting.FixedPolicyNormalization.State` 的 `phase` 字段。下面的函数说明怎样从结构中取出这个字段。

[源码位置](FixedPolicyNormalization.lean#L313)

**类型**

```lean
{L B D w : ℕ} → CodedSorting.FixedPolicyNormalization.State L B D w → CodedSorting.FixedPolicyNormalization.Word w
```

**定义**

```lean
fun L B D w self => self.2
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.State](FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)

**基础库名称**

`Nat`

<a id="def-2fd9efc790adbed0"></a>
## `CodedSorting.FixedPolicyNormalization.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FixedPolicyNormalization.lean#L315)

**类型**

```lean
{w : ℕ} → 4 ≤ 2 ^ w → Fin 4 → CodedSorting.FixedPolicyNormalization.Word w
```

**定义**

```lean
fun {w} hcap k => ⟨↑k, ⋯⟩
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.FixedPolicyNormalization.code._proof_4](FixedPolicyNormalization.definitions.md#def-c2775917ca1d3a92)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.mk`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-b638058d357e2528"></a>
## `CodedSorting.FixedPolicyNormalization.ready`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FixedPolicyNormalization.lean#L322)

**类型**

```lean
{L B D w : ℕ} →
  4 ≤ 2 ^ w →
    CodedSorting.Normalization.PhysicalState L B D (CodedSorting.FixedPolicyNormalization.Word w) →
      CodedSorting.FixedPolicyNormalization.State L B D w
```

**定义**

```lean
fun {L B D w} hcap s => { data := s, phase := CodedSorting.FixedPolicyNormalization.code hcap 0 }
```

**继续展开**

- [CodedSorting.Normalization.PhysicalState](Normalization.definitions.md#def-fd728dbf7842361d)
- [CodedSorting.FixedPolicyNormalization.State](FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.FixedPolicyNormalization.ready._proof_5](FixedPolicyNormalization.definitions.md#def-10332891bd2fd57b)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.FixedPolicyNormalization.code](FixedPolicyNormalization.definitions.md#def-2fd9efc790adbed0)
- [CodedSorting.FixedPolicyNormalization.State.mk](FixedPolicyNormalization.definitions.md#def-ab55087183329d74)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Fin.instOfNat`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-29dbd7b755660c52"></a>
## `CodedSorting.FixedPolicyNormalization.step`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FixedPolicyNormalization.lean#L325)

**类型**

```lean
{L b B D w : ℕ} →
  b ≤ B →
    4 ≤ 2 ^ w →
      CodedSorting.FixedPolicyNormalization.Word w →
        CodedSorting.FixedPolicyNormalization.Program L b D w →
          CodedSorting.FixedPolicyNormalization.State L B D w → CodedSorting.FixedPolicyNormalization.State L B D w × ℕ
```

**定义**

```lean
fun {L b B D w} hb hcap padding p s =>
  match ↑s.phase with
  | 0 =>
    match p.policy s.data.ram with
    | none => ({ data := s.data, phase := CodedSorting.FixedPolicyNormalization.code hcap 3 }, 0)
    | some i =>
      match i.operation with
      | CodedSorting.Normalization.Command.localOp f =>
        ({
            data :=
              let __src := s.data;
              { ram := i.resume (f s.data.ram), buffer := __src.buffer, disk := __src.disk },
            phase := CodedSorting.FixedPolicyNormalization.code hcap 3 },
          0)
      | CodedSorting.Normalization.Command.read address window =>
        ({
            data :=
              let __src := s.data;
              { ram := __src.ram, buffer := s.data.disk address, disk := __src.disk },
            phase := CodedSorting.FixedPolicyNormalization.code hcap 1 },
          1)
      | CodedSorting.Normalization.Command.write address window =>
        ({
            data :=
              let __src := s.data;
              { ram := __src.ram,
                buffer := CodedSorting.Normalization.pack padding (CodedSorting.Normalization.slice s.data.ram window),
                disk := __src.disk },
            phase := CodedSorting.FixedPolicyNormalization.code hcap 2 },
          0)
  | 1 =>
    match p.policy s.data.ram with
    | some i =>
      match i.operation with
      | CodedSorting.Normalization.Command.read address window =>
        (CodedSorting.FixedPolicyNormalization.ready hcap
            (let __src := s.data;
            {
              ram :=
                i.resume
                  (CodedSorting.Normalization.load s.data.ram window
                    (CodedSorting.Normalization.blockPrefix hb s.data.buffer)),
              buffer := __src.buffer, disk := __src.disk }),
          0)
      | x => (CodedSorting.FixedPolicyNormalization.ready hcap s.data, 0)
    | none => (CodedSorting.FixedPolicyNormalization.ready hcap s.data, 0)
  | 2 =>
    match p.policy s.data.ram with
    | some i =>
      match i.operation with
      | CodedSorting.Normalization.Command.write address window =>
        (CodedSorting.FixedPolicyNormalization.ready hcap
            (let __src := s.data;
            { ram := i.resume s.data.ram, buffer := __src.buffer,
              disk := Function.update s.data.disk address s.data.buffer }),
          1)
      | x => (CodedSorting.FixedPolicyNormalization.ready hcap s.data, 0)
    | none => (CodedSorting.FixedPolicyNormalization.ready hcap s.data, 0)
  | x => (CodedSorting.FixedPolicyNormalization.ready hcap s.data, 0)
```

**继续展开**

- [CodedSorting.ControlledNormalization.Instruction.resume](ControlledNormalization.definitions.md#def-f9b13fabe559e990)
- [CodedSorting.Normalization.load](Normalization.definitions.md#def-fcede4fc2d057680)
- [CodedSorting.Normalization.PhysicalState](Normalization.definitions.md#def-fd728dbf7842361d)
- [CodedSorting.ControlledNormalization.Instruction.operation](ControlledNormalization.definitions.md#def-3d5141c25fe6587d)
- [CodedSorting.Normalization.blockPrefix](Normalization.definitions.md#def-575e6dd1226e4cee)
- [CodedSorting.Normalization.PhysicalState.mk](Normalization.definitions.md#def-2b2feddbbfb01c5b)
- [CodedSorting.FixedPolicyNormalization.State](FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.Normalization.PhysicalState.disk](Normalization.definitions.md#def-df054804f555e188)
- [CodedSorting.FixedPolicyNormalization.ready._proof_5](FixedPolicyNormalization.definitions.md#def-10332891bd2fd57b)
- [CodedSorting.FixedPolicyNormalization.step.match_2](FixedPolicyNormalization.definitions.md#def-1bbe1a94460e7888)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.FixedPolicyNormalization.code](FixedPolicyNormalization.definitions.md#def-2fd9efc790adbed0)
- [CodedSorting.FixedPolicyNormalization.Program.policy](FixedPolicyNormalization.definitions.md#def-4db99f43c099a6e8)
- [CodedSorting.Normalization.slice](Normalization.definitions.md#def-97003b863ad4a44f)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.FixedPolicyNormalization.State.phase](FixedPolicyNormalization.definitions.md#def-8811097908191dac)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.FixedPolicyNormalization.State.mk](FixedPolicyNormalization.definitions.md#def-ab55087183329d74)
- [CodedSorting.FixedPolicyNormalization.step.match_4](FixedPolicyNormalization.definitions.md#def-065d85f0fbd8d0f8)
- [CodedSorting.FixedPolicyNormalization.ready](FixedPolicyNormalization.definitions.md#def-b638058d357e2528)
- [CodedSorting.FixedPolicyNormalization.State.data](FixedPolicyNormalization.definitions.md#def-b353367b3b3b5fbc)
- [CodedSorting.Normalization.pack](Normalization.definitions.md#def-97797717e5f5913c)
- [CodedSorting.Normalization.PhysicalState.buffer](Normalization.definitions.md#def-74cb96dbfc7116c1)
- [CodedSorting.Normalization.PhysicalState.ram](Normalization.definitions.md#def-401047fe136aec1d)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)
- [CodedSorting.FixedPolicyNormalization.step.match_5](FixedPolicyNormalization.definitions.md#def-bf60358649ca9894)
- [CodedSorting.ControlledNormalization.Instruction](ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)
- [CodedSorting.FixedPolicyNormalization.step.match_6](FixedPolicyNormalization.definitions.md#def-e7a04f1522d510c0)
- [CodedSorting.FixedPolicyNormalization.Program](FixedPolicyNormalization.definitions.md#def-2576571b58804cf6)
- [CodedSorting.FixedPolicyNormalization.step.match_1](FixedPolicyNormalization.definitions.md#def-6731d6efd62c3179)
- [CodedSorting.FixedPolicyNormalization.step.match_3](FixedPolicyNormalization.definitions.md#def-59d2c686f5764aea)

**基础库名称**

`Function.update`, `Nat.instMonoid`, `instDecidableEqFin`, `Monoid.toNatPow`, `Fin.instOfNat`, `Prod.mk`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `Unit`, `HPow.hPow`, `Nat`, `instHPow`, `Prod`, `OfNat.ofNat`, `Fin`, `Option`

<a id="def-5b674c82b533c4d0"></a>
## `CodedSorting.FixedPolicyNormalization.run`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](FixedPolicyNormalization.lean#L355)

**类型**

```lean
{L b B D w : ℕ} →
  b ≤ B →
    4 ≤ 2 ^ w →
      CodedSorting.FixedPolicyNormalization.Word w →
        CodedSorting.FixedPolicyNormalization.Program L b D w →
          ℕ →
            CodedSorting.FixedPolicyNormalization.State L B D w →
              CodedSorting.FixedPolicyNormalization.State L B D w × ℕ
```

**定义**

```lean
fun {L b B D w} hb hcap padding p x x_1 =>
  Nat.brecOn (motive := fun x =>
    CodedSorting.FixedPolicyNormalization.State L B D w → CodedSorting.FixedPolicyNormalization.State L B D w × ℕ) x
    (fun x f x_2 =>
      (match (motive :=
          (x : ℕ) →
            CodedSorting.FixedPolicyNormalization.State L B D w →
              Nat.below (motive := fun x =>
                  CodedSorting.FixedPolicyNormalization.State L B D w →
                    CodedSorting.FixedPolicyNormalization.State L B D w × ℕ)
                  x →
                CodedSorting.FixedPolicyNormalization.State L B D w × ℕ)
          x, x_2 with
        | 0, s => fun x => (s, 0)
        | fuel.succ, s => fun x =>
          let first := CodedSorting.FixedPolicyNormalization.step hb hcap padding p s;
          let rest := x.1 first.1;
          (rest.1, first.2 + rest.2))
        f)
    x_1
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.State](FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.FixedPolicyNormalization.run.match_1](FixedPolicyNormalization.definitions.md#def-03e5bbe2c05e3852)
- [CodedSorting.FixedPolicyNormalization.step](FixedPolicyNormalization.definitions.md#def-29dbd7b755660c52)
- [CodedSorting.FixedPolicyNormalization.Program](FixedPolicyNormalization.definitions.md#def-2576571b58804cf6)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `Nat.brecOn`, `Prod.mk`, `instOfNatNat`, `LE.le`, `instLENat`, `Prod.fst`, `Nat.below`, `instHAdd`, `PProd`, `HPow.hPow`, `HAdd.hAdd`, `Nat`, `instAddNat`, `instHPow`, `Prod`, `OfNat.ofNat`, `Nat.succ`, `Prod.snd`

<a id="def-c2775917ca1d3a92"></a>
## `CodedSorting.FixedPolicyNormalization.code._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
∀ {w : ℕ}, 4 ≤ 2 ^ w → ∀ (k : Fin 4), ↑k < 2 ^ w
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Preorder.toLT`, `Nat.instMonoid`, `Monoid.toNatPow`, `instOfNatNat`, `LE.le`, `instLENat`, `Fin.val`, `HPow.hPow`, `Nat.instPreorder`, `Nat`, `LT.lt`, `instHPow`, `OfNat.ofNat`, `Fin`

<a id="def-10332891bd2fd57b"></a>
## `CodedSorting.FixedPolicyNormalization.ready._proof_5`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
NeZero (3 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-03e5bbe2c05e3852"></a>
## `CodedSorting.FixedPolicyNormalization.run.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
{L B D w : ℕ} →
  (motive : ℕ → CodedSorting.FixedPolicyNormalization.State L B D w → Sort u_1) →
    (x : ℕ) →
      (x_1 : CodedSorting.FixedPolicyNormalization.State L B D w) →
        ((s : CodedSorting.FixedPolicyNormalization.State L B D w) → motive 0 s) →
          ((fuel : ℕ) → (s : CodedSorting.FixedPolicyNormalization.State L B D w) → motive fuel.succ s) → motive x x_1
```

**定义**

```lean
fun {L B D w} motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.State](FixedPolicyNormalization.definitions.md#def-649028e1590de6aa)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Nat.succ`, `Nat.casesOn`

<a id="def-6731d6efd62c3179"></a>
## `CodedSorting.FixedPolicyNormalization.step.match_1`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
{L b D w : ℕ} →
  (motive : CodedSorting.Normalization.Command L b D (CodedSorting.FixedPolicyNormalization.Word w) → Sort u_1) →
    (x : CodedSorting.Normalization.Command L b D (CodedSorting.FixedPolicyNormalization.Word w)) →
      ((f :
            CodedSorting.Normalization.Words L (CodedSorting.FixedPolicyNormalization.Word w) →
              CodedSorting.Normalization.Words L (CodedSorting.FixedPolicyNormalization.Word w)) →
          motive (CodedSorting.Normalization.Command.localOp f)) →
        ((address : Fin D) →
            (window : CodedSorting.Normalization.Window L b) →
              motive (CodedSorting.Normalization.Command.read address window)) →
          ((address : Fin D) →
              (window : CodedSorting.Normalization.Window L b) →
                motive (CodedSorting.Normalization.Command.write address window)) →
            motive x
```

**定义**

```lean
fun {L b D w} motive x h_1 h_2 h_3 =>
  CodedSorting.Normalization.Command.casesOn x (fun f => h_1 f) (fun address window => h_2 address window)
    fun address window => h_3 address window
```

**继续展开**

- [CodedSorting.Normalization.Command.write](Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.Normalization.Command.casesOn](Normalization.definitions.md#def-d5874f9d23d9c310)
- [CodedSorting.Normalization.Command.read](Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command.localOp](Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`, `Fin`

<a id="def-1bbe1a94460e7888"></a>
## `CodedSorting.FixedPolicyNormalization.step.match_2`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
{L b D w : ℕ} →
  (motive :
      Option (CodedSorting.ControlledNormalization.Instruction L b D (CodedSorting.FixedPolicyNormalization.Word w)) →
        Sort u_1) →
    (x :
        Option
          (CodedSorting.ControlledNormalization.Instruction L b D (CodedSorting.FixedPolicyNormalization.Word w))) →
      (Unit → motive none) →
        ((i : CodedSorting.ControlledNormalization.Instruction L b D (CodedSorting.FixedPolicyNormalization.Word w)) →
            motive (some i)) →
          motive x
```

**定义**

```lean
fun {L b D w} motive x h_1 h_2 => Option.casesOn x (h_1 ()) fun val => h_2 val
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.ControlledNormalization.Instruction](ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`Unit.unit`, `Option.casesOn`, `Option.some`, `Option.none`, `Unit`, `Nat`, `Option`

<a id="def-59d2c686f5764aea"></a>
## `CodedSorting.FixedPolicyNormalization.step.match_3`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
{L b D w : ℕ} →
  (motive : CodedSorting.Normalization.Command L b D (CodedSorting.FixedPolicyNormalization.Word w) → Sort u_1) →
    (x : CodedSorting.Normalization.Command L b D (CodedSorting.FixedPolicyNormalization.Word w)) →
      ((address : Fin D) →
          (window : CodedSorting.Normalization.Window L b) →
            motive (CodedSorting.Normalization.Command.read address window)) →
        ((x : CodedSorting.Normalization.Command L b D (CodedSorting.FixedPolicyNormalization.Word w)) → motive x) →
          motive x
```

**定义**

```lean
fun {L b D w} motive x h_1 h_2 =>
  CodedSorting.Normalization.Command.casesOn x (fun f => h_2 (CodedSorting.Normalization.Command.localOp f))
    (fun address window => h_1 address window) fun address window =>
    h_2 (CodedSorting.Normalization.Command.write address window)
```

**继续展开**

- [CodedSorting.Normalization.Command.write](Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.Normalization.Command.casesOn](Normalization.definitions.md#def-d5874f9d23d9c310)
- [CodedSorting.Normalization.Command.read](Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command.localOp](Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`, `Fin`

<a id="def-065d85f0fbd8d0f8"></a>
## `CodedSorting.FixedPolicyNormalization.step.match_4`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
{L b D w : ℕ} →
  (motive :
      Option (CodedSorting.ControlledNormalization.Instruction L b D (CodedSorting.FixedPolicyNormalization.Word w)) →
        Sort u_1) →
    (x :
        Option
          (CodedSorting.ControlledNormalization.Instruction L b D (CodedSorting.FixedPolicyNormalization.Word w))) →
      ((i : CodedSorting.ControlledNormalization.Instruction L b D (CodedSorting.FixedPolicyNormalization.Word w)) →
          motive (some i)) →
        (Unit → motive none) → motive x
```

**定义**

```lean
fun {L b D w} motive x h_1 h_2 => Option.casesOn x (h_2 ()) fun val => h_1 val
```

**继续展开**

- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.ControlledNormalization.Instruction](ControlledNormalization.definitions.md#def-2df5a4e499f7c5c7)

**基础库名称**

`Unit.unit`, `Option.casesOn`, `Option.some`, `Option.none`, `Unit`, `Nat`, `Option`

<a id="def-bf60358649ca9894"></a>
## `CodedSorting.FixedPolicyNormalization.step.match_5`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
{L b D w : ℕ} →
  (motive : CodedSorting.Normalization.Command L b D (CodedSorting.FixedPolicyNormalization.Word w) → Sort u_1) →
    (x : CodedSorting.Normalization.Command L b D (CodedSorting.FixedPolicyNormalization.Word w)) →
      ((address : Fin D) →
          (window : CodedSorting.Normalization.Window L b) →
            motive (CodedSorting.Normalization.Command.write address window)) →
        ((x : CodedSorting.Normalization.Command L b D (CodedSorting.FixedPolicyNormalization.Word w)) → motive x) →
          motive x
```

**定义**

```lean
fun {L b D w} motive x h_1 h_2 =>
  CodedSorting.Normalization.Command.casesOn x (fun f => h_2 (CodedSorting.Normalization.Command.localOp f))
    (fun address window => h_2 (CodedSorting.Normalization.Command.read address window)) fun address window =>
    h_1 address window
```

**继续展开**

- [CodedSorting.Normalization.Command.write](Normalization.definitions.md#def-de92fb94cadb9bcc)
- [CodedSorting.Normalization.Command.casesOn](Normalization.definitions.md#def-d5874f9d23d9c310)
- [CodedSorting.Normalization.Command.read](Normalization.definitions.md#def-54b8143801baed43)
- [CodedSorting.FixedPolicyNormalization.Word](FixedPolicyNormalization.definitions.md#def-6aba48f221a7029d)
- [CodedSorting.Normalization.Window](Normalization.definitions.md#def-532b4e9511b14109)
- [CodedSorting.Normalization.Words](Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.Normalization.Command.localOp](Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.Normalization.Command](Normalization.definitions.md#def-5d1402e119d2b0bd)

**基础库名称**

`Nat`, `Fin`

<a id="def-e7a04f1522d510c0"></a>
## `CodedSorting.FixedPolicyNormalization.step.match_6`

Lean 根据源码中的分情况处理自动生成这个函数。它检查输入属于哪种情形，再执行相应分支；原来的分支写法可从源码查看。

[源码位置](FixedPolicyNormalization.lean)

**类型**

```lean
(motive : ℕ → Sort u_1) →
  (x : ℕ) → (Unit → motive 0) → (Unit → motive 1) → (Unit → motive 2) → ((x : ℕ) → motive x) → motive x
```

**定义**

```lean
fun motive x h_1 h_2 h_3 h_4 =>
  if h_1_1 : x = 0 then ⋯ ▸ ⋯ ▸ h_1 ()
  else
    if h_2_1 : x = 1 then Eq.ndrec (motive := fun x => ¬x = 0 → motive x) (fun h_1 => ⋯ ▸ h_2 ()) ⋯ h_1_1
    else
      if h_3_1 : x = 2 then
        Eq.ndrec (motive := fun x => ¬x = 0 → ¬x = 1 → motive x) (fun h_1 h_2 => ⋯ ▸ h_3 ()) ⋯ h_1_1 h_2_1
      else h_4 x
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Unit.unit`, `instOfNatNat`, `dite`, `Unit`, `Nat`, `Eq.ndrec`, `instDecidableEqNat`, `OfNat.ofNat`, `Eq.symm`, `Eq`, `Not`
