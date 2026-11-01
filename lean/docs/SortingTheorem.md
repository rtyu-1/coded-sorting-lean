# The sorting theorem explained

[English](SortingTheorem.md) · [简体中文](SortingTheorem.zh-CN.md)

This page compares Theorem 3.1 in the paper with the Lean 4 source, explaining **how the code expresses its assumptions, conclusions, and external-memory model**.

The Lean 4 kernel checks the proofs from the concrete construction to the formal main theorem. This guide explains how to compare the theorem statement and related definitions with the paper. Starting with `theorem_3_1`, it covers parameter conditions, the proof by cases, disk input and output, execution steps, I/O accounting, memory and disk space, and the dependencies of complexity constants. Source excerpts appear alongside the explanations, with common syntax explained on first use and longer excerpts available to expand.

> **Theorem 3.1 of the paper (external-memory integer sorting).** Suppose $w=\Theta(\log N)$. For integer parameters satisfying $N\ge2$, $B>0$, and $2B\le M\le N$, there is a deterministic algorithm determined by the size parameters that sorts any $N$ disk-resident $w$-bit integers into nondecreasing order, preserving duplicates. It uses at most $M$ words of memory and polynomial disk space. The total number $Q$ of physical block transfers in the complete execution satisfies
>
> $$Q\le C\frac NB\left[1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^\varepsilon}\right],\qquad \varepsilon=\frac3{200000}=1.5\times10^{-5},$$
>
> where $C$ and the degree of the disk-space polynomial depend only on the fixed circuit construction and the word-width constants, independently of $N,M,B,w$ and the particular input.

### Verification roadmap

| Assumptions and conclusions in the paper | Corresponding definitions and explanation |
| --- | --- |
| **1. Parameter range and $w=\Theta(\log N)$** | **Section 1**: unsigned `Word`, the lower bound `Covers`, and the upper-bound inequality |
| **2. The program is fixed by the size parameters** | **Sections 2 and 3**: the program is determined before the input values are given; the fixed program and current state determine execution |
| **3. Input and output are stored compactly in disk blocks** | **Sections 2.1 and 3.1**: block number `i/B`, offset `i%B`, `InputFile`, and `File` |
| **4. Output is nondecreasing and preserves duplicates** | **Sections 2.1 and 3**: the disk output satisfies both `Perm` and `Pairwise` |
| **5. Every physical block transfer is counted** | **Sections 2.2 and 3.2**: `step` and `cost` charge `1` per whole-block read or write; compound steps add their costs |
| **6. Memory is at most $M$ words and disk space is polynomial** | **Sections 2.3 and 3.3**: `ResidentIndex` in the normal-memory case; the two buffers and `BoundedCode` in the small-memory case |
| **7. The complexity formula matches and its constants are independent of size** | **Section 4**: `factor`, `epsilon`, `coefficient`, and their parameters |

*Every Lean code block on this page is copied directly from the repository source. The check script verifies that each excerpt matches exactly.*

---

## 1. The top-level statement and its two cases

The main theorem appears in [Theorem.lean](../CodedSorting/Sorting/Theorem31/Theorem.lean). Its proof directly invokes `complete` from [Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean):

```lean
theorem theorem_3_1 (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    (∃ hM : GeneralWordNormalSorting.Mcut c κ≤M,
      NormalGuarantee c κ hκ N M B w hN hB hBM hMN hM hw hword) ∨
    (M<GeneralWordNormalSorting.Mcut c κ ∧
      SmallGuarantee c κ N M B w hB) :=
  GeneralWordSorting.complete
    c κ hκ N M B w hN hB hBM hMN hw hword
```

**Code structure.**

A Lean 4 theorem has the form `theorem name (parameters and assumptions) : conclusion := proof`. The declaration has three parts:

1. **Parameters and assumptions, before the outer colon `:`.**

   * **Numeric parameters:** `(c : ℕ)` and `(κ : ℝ)` are fixed constants for the word-width relation. `ℕ` denotes natural numbers and `ℝ` real numbers. `(N M B w : ℕ)` gives the number of input integers, memory capacity in words, words per block, and bits per word.
   * **Assumptions, named with `h`:** `(hBM : 2*B≤M)` requires a proof of $2B\le M$, named `hBM`. Similarly, `hκ`, `hN`, `hB`, `hMN`, `hw`, and `hword` express $\kappa\ge0$, $N\ge2$, $B>0$, $M\le N$, and the lower and upper word-width bounds.

2. **The conclusion, between the outer `:` and `:=`.**

   The logical “or” (`∨`) joins two cases, according to whether $M$ reaches the fixed threshold `Mcut c κ`. Spaces denote function application, so this means $\mathrm{Mcut}(c,\kappa)$.

   * **Left alternative, normal memory:** there is a proof `hM` of $\mathrm{Mcut}(c,\kappa)\le M$, under which the algorithm satisfies `NormalGuarantee ...`.
   * **Right alternative, small memory:** $M<\mathrm{Mcut}(c,\kappa)$ and (`∧`) the algorithm satisfies `SmallGuarantee ...`.

3. **The proof reference, after `:=`.**

   The declaration invokes the already proved theorem `GeneralWordSorting.complete`, passing the parameters and assumption proofs unchanged.

### 1.1 Preconditions and the word-width convention

**The machine-word type (`Word`).** A single $w$-bit integer is defined in [WordConvention.lean](../CodedSorting/Shared/Words/WordConvention.lean):

```lean
abbrev Word (w : ℕ) := Fin (2 ^ w)
```

Here `abbrev` defines a type abbreviation. The standard-library type `Fin n` contains $\{0,1,\ldots,n-1\}$, with each natural number paired with a proof that it is below $n$. Thus `Word w` represents unsigned $w$-bit integers $0,\ldots,2^w-1$.

**Word-width bounds (`Covers` and `hword`).** To express $w=\Theta(\log N)$, `hw` and `hword` constrain the lower and upper bounds. [WordConvention.lean](../CodedSorting/Shared/Words/WordConvention.lean) defines the lower-bound predicate:

```lean
def Covers (N w c : ℕ) : Prop := Nat.clog 2 N ≤ c*w
```

The return type `: Prop` means this is a proposition; `Nat.clog 2 N` is $\lceil\log_2N\rceil$. Thus:

* **The lower bound `hw`** requires $\lceil\log_2N\rceil\le cw$, so a constant number of words suffices for input indices and polynomial-size disk addresses.
* **The upper bound `hword`** requires `(w : ℝ) * Real.log 2 ≤ κ * Real.log (N : ℝ)`, or $w\ln2\le\kappa\ln N$. Here `(w : ℝ)` converts the natural number to a real number, and `Real.log` is the natural logarithm.

### 1.2 Combining the cases at the memory threshold (`complete`)

As in Section 8.4 of the paper, `complete` splits on the comparison between memory capacity $M$ and the fixed threshold `Mcut c κ`, combining the normal-memory and small-memory cases into the complete theorem:

<details>
<summary>Expand: the source of the proof combining the two cases, <code>complete</code></summary>

```lean
theorem complete (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    (∃ hM : GeneralWordNormalSorting.Mcut c κ≤M,
      NormalGuarantee c κ hκ N M B w hN hB hBM hMN hM hw hword) ∨
    (M<GeneralWordNormalSorting.Mcut c κ ∧ SmallGuarantee c κ N M B w hB) := by
  by_cases hM : GeneralWordNormalSorting.Mcut c κ≤M
  · exact Or.inl ⟨hM,normal_complete c κ hκ N M B w hN hB hBM hMN hM hw hword⟩
  · exact Or.inr ⟨by omega,
      small_complete c κ N M B w hN hB hBM hMN (by omega) hw hword⟩
```

</details>

**Proof steps.**

The keyword `by` introduces a tactic proof with three core steps:

1. **`by_cases hM : GeneralWordNormalSorting.Mcut c κ ≤ M`:** split according to whether $\mathrm{Mcut}(c,\kappa)\le M$ holds, with each branch introduced by `·`. In the first branch, `hM` proves the inequality; in the second, it proves $\neg(\mathrm{Mcut}(c,\kappa)\le M)$.
2. **When $\mathrm{Mcut}(c,\kappa)\le M$ holds:** `exact Or.inl ⟨hM, normal_complete ...⟩` establishes the left alternative. The brackets combine the threshold proof `hM` and the result of `normal_complete`, corresponding to Sections 6–8.2 and Appendix A.3.
3. **When $\mathrm{Mcut}(c,\kappa)\le M$ does not hold:** `exact Or.inr ⟨by omega, small_complete ...⟩` establishes the right alternative. The arithmetic tactic `omega` derives $M<\mathrm{Mcut}(c,\kappa)$ from the negated inequality, and `small_complete` supplies the small-memory result, corresponding to Lemma 8.3.

---

## 2. The normal-memory case `NormalGuarantee`

In [Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean), `NormalGuarantee` specifies the input, execution, and output properties of a complete sorting run:

<details>
<summary>Expand: the complete definition of <code>NormalGuarantee</code></summary>

```lean
def NormalGuarantee (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : GeneralWordNormalSorting.Mcut c κ≤M) (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) : Prop :=
  let q := GeneralWordNormalSorting.configuration c κ N M B w hN hB hBM hMN hM hw
  let p := GeneralWordNormalSorting.parameters c κ hκ N M B w hN hB hBM hMN hM hw hword
  ∀ (store : CommonLeafProgram.Store q)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word w)), xs.length=N → CommonIntegerPhysical.InputFile q disk xs →
    ∃ fuel,
      let prog := program q (CommonIntegerAllInputPhysical.algorithm q p)
      let s := CommonIntegerAllInputPhysical.start q p store disk
      let blocks := CommonIntegerPhysical.blocks q q.N
      let result := CommonNormalizationController.run prog (blocks+1+fuel+1+blocks+1) s
      (∀ i : Fin (CommonIntegerFile.output q xs).length,
        CommonNormalizationController.outputWord prog result.1 i.val=(CommonIntegerFile.output q xs).get i) ∧
      (CommonIntegerFile.output q xs).Perm xs ∧
      (CommonIntegerFile.output q xs).Pairwise (·≤·) ∧
      CommonNormalizationController.step prog result.1=(result.1,0) ∧
      Fintype.card (ResidentIndex q)≤M ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))≤
        N^(GeneralWordNormalSorting.exponent κ+2) ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))*B≤
        N^(GeneralWordNormalSorting.exponent κ+3) ∧
      (result.2 : ℝ)≤coefficient c κ*((N : ℝ)/B)*factor N M B
```

</details>

**Reading `NormalGuarantee` in four parts.**

1. **Configuration and algorithm parameters (`let q`, `let p`).** `let` introduces local names. The first two definitions assemble the size parameters and assumption proofs into the configuration `q` and algorithm parameters `p`.
2. **Every legal input (`∀` and `→`).** The statement quantifies over every initial working store `store`, disk `disk`, and input list `xs`. It requires the conclusion whenever `xs.length=N` and `InputFile q disk xs` hold. Each `→` means “if ... then ...”; the two successive arrows introduce the two assumptions.
3. **A program and a finite execution (`∃ fuel` and `run`).** There is a finite `fuel` such that `run prog (blocks+1+fuel+1+blocks+1) s` gives the required result. The configuration `q` and parameters `p` are determined before quantifying over the input, and `prog` uses only them, so the same program works for every input of that size. The state `s` incorporates `store` and `disk`. The `blocks` terms count $\lceil N/b\rceil$ logical blocks in each format conversion, and the three `1`s account for stage transitions. The returned pair `result` contains the final state as `result.1` and the accumulated physical I/O count as `result.2`.

4. **Eight conclusions joined by `∧`.** The first four describe the disk output, permutation, sortedness, and termination condition. The remaining four bound memory words, disk blocks, disk words, and total I/O.

`List (Word w)` is a list of words, `xs.length` its length, and `q.N` the configuration's `N` field. The following sections explain disk input and output, execution and accounting, and memory and disk space.

### 2.1 Check 1: disk-file layout and sorting correctness

**How the input is stored (`InputFile`).**

Let $R=N^E$, where $E=\mathtt{exponent}(\kappa)$ is a fixed exponent depending only on $\kappa$. The address type `Address R = Fin R ⊕ (Fin R ⊕ Fin R)` divides the disk into disjoint **input, working, and output regions**. Each region contains $R$ physical blocks, and each block contains $B$ words of $w$ bits (`Words B w`).

In [PhysicalHalted.lean](../CodedSorting/Sorting/Execution/Framework/PhysicalHalted.lean), `InputFile q disk xs` specifies that the length-$N$ input list `xs` is stored compactly in the input region (`.inl`): integer $i$ is at offset `i % q.B` in physical block `i / q.B`.

`⊕` is a disjoint union with left and right tags: `.inl` selects the left side and `.inr` the right. Thus `.inl a`, `.inr (.inl a)`, and `.inr (.inr a)` identify the three disk regions. The same block number in different regions denotes different addresses.

```lean
def inputWord (q : Configuration)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) (i : ℕ) : Word q.w :=
  if h : i/q.B<q.N^q.exponent then
    disk (.inl ⟨i/q.B,h⟩) ⟨i%q.B,Nat.mod_lt _ q.block_pos⟩
  else 0

def InputFile (q : Configuration)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word q.w)) : Prop := ∀ i : Fin xs.length,inputWord q disk i.val=xs.get i
```

`if h : condition then ... else ...` selects a result and names the evidence for the relevant branch `h`. Here `⟨i/q.B,h⟩` constructs a `Fin` index from a value and a proof that it is in range; `i.val` extracts the value. On natural numbers, `/` and `%` mean integer division and remainder. The `_` in `Nat.mod_lt _ ...` asks Lean to infer that argument from context.

The output observation function `outputWord` uses the same block number `y / B` and offset `y % B` to obtain a value from the final state's output region. It states the output condition; transfers performed during execution are charged by the transitions in Section 2.2. `Words count w` contains exactly `count` words of $w$ bits. Here `index p j` reduces a block number modulo the region size. For the first $N$ output positions, the block number is below $R$, so this reduction leaves it unchanged.

<details>
<summary>Expand: arrays <code>Words</code>, machine <code>State</code>, and <code>outputWord</code></summary>

Between data types, `A → B` means a function taking an `A` and returning a `B`. Thus `Fin count → Word w` represents a fixed-length array as a function from indices to elements. `structure ... where` lists fields and their types; inequality fields hold proofs of validity. Below, `fun y => ...` defines a function with input `y` and the expression on the right as its result.

[CodedSorting/Shared/Words/WordConvention.lean](../CodedSorting/Shared/Words/WordConvention.lean)

```lean
abbrev Words (count w : ℕ) := Fin count → Word w
```

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
abbrev Address (R : ℕ) := Fin R ⊕ (Fin R ⊕ Fin R)
abbrev Disk (R B w : ℕ) := Address R → Words B w

structure Program (L R B b d w : ℕ) where
  positive_region : 0 < R
  positive_block : 0 < B
  block_ratio : b ≤ B
  counter_capacity : R  <  (2^w)^d
  phase_capacity : 8 ≤ 2^w
  padding : Word w
  policy : ControlledNormalization.Policy L b R (Word w)

structure State (L R B b d w : ℕ) where
  ram : Words L w
  buffer : Words B w
  scratch : Words b w
  counter : Words d w
  inputCount : Words d w
  outputCount : Words d w
  phase : Word w
  stage : Word w
  disk : Disk R B w
```

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
def outputWord (p : Program L R B b d w) (s : State L R B b d w) :=
  PhysicalNormalizationCompact.targetWord (outputProgram p s) (compactView s.disk)
```

[CodedSorting/Shared/Memory/PhysicalNormalizationCompact.lean](../CodedSorting/Shared/Memory/PhysicalNormalizationCompact.lean)

```lean
def targetWord (p : Program R B b d w) (disk : Disk R B w) : BlockReflection.Disk (Word w) :=
  fun y => disk (.inr (index p (y/B))) ⟨y%B,Nat.mod_lt _ p.positive_block⟩
```

</details>

**Why the output conditions establish sorting correctness.**

`NormalGuarantee` gives four conjuncts concerning the output list `output q xs`:

| Code conclusion | Meaning |
| --- | --- |
| `outputWord ... = (output q xs).get i` | **Stored on disk**: the first $N$ positions of the final state's output region equal `output q xs`, word for word. |
| `(output q xs).Perm xs` | **All values and multiplicities preserved**: the output is a permutation of `xs`, with length $N$ and identical multiplicities. |
| `(output q xs).Pairwise (·≤·)` | **Nondecreasing order**: every earlier element is at most every later element. |
| `step prog result.1 = (result.1, 0)` | **Termination condition**: another step leaves the state unchanged and costs zero, so further iteration also leaves the output and accumulated cost unchanged. The controller’s stage 3 satisfies this condition. |

**Why the program is deterministic and independent of the input values.**

After the word-width constants are fixed, the configuration `q`, parameters `p`, and program `prog := program q (algorithm q p)` are constructed from $(N,M,B,w)$, independently of `xs`. The initial state `s := start q p store disk` receives the original `disk` unchanged. The quantifier `∀ store disk xs` covers every initial workspace and disk satisfying the input-file condition. The fixed policy receives only the current working memory `ram`. Together with the deterministic transitions in Section 2.2, this gives the same program for all legal inputs.

<details>
<summary>Expand: <code>configuration</code>, the <code>Command</code> type, and initialization with <code>start</code></summary>

When constructing a structure, `field := value` under `where` fills named fields; `⟨...⟩` fills them in declaration order. In proofs, `have` introduces a proved fact, `norm_num` checks numeric calculations, and `by decide` proves a decidable proposition by evaluation. These are proof steps checked by Lean.

[CodedSorting/Sorting/Theorem31/LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean)

```lean
def configuration (c : ℕ) (κ : ℝ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : Mcut c κ≤M) (hw : WordConvention.Covers N w c) : Configuration where
  inventory := inventory
  N := N
  M := M
  B := B
  w := w
  c := c
  exponent := exponent κ
  input_large := hN
  memory_input := hMN
  block_pos := hB
  block_memory := hBM
  exponent_pos := (by omega : 1≤17).trans
    (CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent_ge17 (wordFactor κ))
  word_convention := hw
  memory_large := hM
```

[CodedSorting/Shared/Programs/Normalization.lean](../CodedSorting/Shared/Programs/Normalization.lean)

`inductive Command` lists the allowed command forms; each line starting with `|` gives a constructor and its arguments. `Word : Type*` allows an arbitrary element type here rather than fixing a word width; the main theorem instantiates it with the word type defined above.

```lean
inductive Command (L b D : ℕ) (Word : Type*)
  | localOp (f : Words L Word → Words L Word)
  | read (address : Fin D) (window : Window L b)
  | write (address : Fin D) (window : Window L b)
```

[CodedSorting/Shared/Programs/ControlledNormalization.lean](../CodedSorting/Shared/Programs/ControlledNormalization.lean)

```lean
structure Instruction (L b D : ℕ) (Word : Type*) where
  operation : Command L b D Word
  resume : Words L Word → Words L Word

abbrev Policy (L b D : ℕ) (Word : Type*) :=
  Words L Word → Option (Instruction L b D Word)
```

`Option T` means an optional `T`: `some i` supplies the next instruction, while `none` means there is none. Later, names such as `.read` omit the constructor's type, which Lean infers from context.

[CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean)

```lean
abbrev SourcePolicy (q : Configuration) :=
  ControlledNormalization.Policy q.ramWords q.block (q.N^q.exponent) (Word q.w)
```

[CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean)

```lean
def program (q : Configuration) (policy : SourcePolicy q) :
    CommonNormalizationController.Program q.ramWords (q.N^q.exponent)
      q.B q.block q.digits q.w where
  positive_region := pow_pos (by have := q.input_large; omega) _
  positive_block := q.block_pos
  block_ratio := Normalization.logical_block_le_physical q.B _ q.block_pos
  counter_capacity := Nat.lt_of_succ_le
    (WordConvention.polynomial_capacity q.N q.w q.c q.exponent q.input_large q.word_convention)
  phase_capacity := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) q.word_width
    norm_num at h
    exact h
  padding := 0
  policy := policy
```

[CodedSorting/Sorting/Execution/AllInputPhysical.lean](../CodedSorting/Sorting/Execution/AllInputPhysical.lean)

```lean
def algorithm (q : Configuration) (p : Parameters q) : SourcePolicy q :=
  CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy q (core q p) q.N le_rfl

def start (q : Configuration) (p : Parameters q) (store : Store q)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  CommonIntegerPhysical.start q (algorithm q p)
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initStore q (core q p) q.N le_rfl store) q.N
    (CommonIntegerCapacity.blocks_lt q q.N le_rfl (by have:=CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent_ge17 (wordFactor p.kappa);have:=p.exponent;omega)) disk
```

[CodedSorting/Sorting/Execution/Framework/PhysicalHalted.lean](../CodedSorting/Sorting/Execution/Framework/PhysicalHalted.lean)

```lean
def start (q : Configuration) (policy : SourcePolicy q) (store : Store q)
    (n : ℕ) (hn : blocks q n<q.N^q.exponent)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  initialState q policy store ⟨blocks q n,by omega⟩ ⟨blocks q n,hn⟩ disk
```

[CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean)

```lean
def initialState (q : Configuration) (policy : SourcePolicy q)
    (s : SourceState q.inventory q.height q.block q.digits q.w)
    (nIn : Fin (q.N^q.exponent+1)) (nOut : Fin (q.N^q.exponent))
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  CommonNormalizationController.initial (program q policy) (pack s)
    (WordConvention.encode q.N q.w q.c q.exponent q.input_large q.word_convention nIn)
    (WordConvention.encode q.N q.w q.c q.exponent q.input_large q.word_convention nOut.castSucc)
    disk
```

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

`fun _ => p.padding` is a constant function: it ignores the index and puts `p.padding` at every position. Here `_` marks an unused function parameter.

```lean
def initial (p : Program L R B b d w) (ram : Words L w)
    (inputCount outputCount : Words d w) (disk : Disk R B w) : State L R B b d w :=
  ⟨ram,fun _=>p.padding,fun _=>p.padding,PhysicalNormalizationLayout.counterCode d w 0,
    inputCount,outputCount,code p 0,code p 0,disk⟩
```

</details>

### 2.2 Check 2: execution and physical I/O accounting

To check that `result.2` counts every physical block transfer, start with `run` in [NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean):

`State ... × ℕ` is a pair consisting of a state and a natural number; `(s,0)` is one such return value. The clauses `| 0,s => ...` and `| fuel+1,s => ...` handle zero and positive step counts, with each result after `=>`.

```lean
def run (p : Program L R B b d w) : ℕ → State L R B b d w → State L R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)
```

The existential `∃ fuel` supplies a sufficient finite execution length. `run` returns the final state `result.1` and accumulated cost `result.2`. Each call to `step` returns that step's physical I/O cost as `first.2`, which is added to the total. The final state of this same execution satisfies the sorting conditions, and its accumulated cost satisfies the complexity bound.

As in Appendix A.3 of the paper (constant-factor block simulation), the algorithm uses logical blocks of $b\le B$ words and a physical transfer buffer `buffer` of $B$ words. The execution has three stages, selected by `stage`:

1. **Stage 0: input conversion.** While the block counter is below `inputSize`, the controller runs `PhysicalNormalizationLayout.run ... 7`. These seven underlying steps read two adjacent input blocks, extract $b$ words, and write one logical block to the working region: two reads and one write, totaling **three I/Os per logical block**. After all $\lceil N/b\rceil$ blocks, the controller moves to stage 1 at zero I/O cost.

2. **Stage 1: sorting.** If the policy returns `none`, the controller moves to stage 2. Otherwise, `FixedPolicyNormalization.run ... 2` executes two underlying steps for an instruction. The command cases are:

   * `.localOp f` updates RAM using `i.resume (f s.data.ram)` and costs zero I/Os.
   * `.read address window` loads a whole physical block into `buffer` in phase 0, costing one I/O. Phase 1 copies its first $b$ words into the RAM window and applies `resume`, at zero I/O cost.
   * `.write address window` packs the RAM window into `buffer` in phase 0, at zero cost. Phase 2 writes the whole buffer to disk and applies `resume`, costing one I/O.

3. **Stage 2: output conversion.** `PhysicalNormalizationCompact.run ... 8` reads a logical working block, then reads, patches, and writes each of two adjacent output blocks. These eight underlying steps contain three reads and two writes, totaling **five I/Os per logical block**. After all output blocks, the controller moves to stage 3.
4. **Stage 3: termination.** The branch `| _ => (s, 0)` returns the same state with zero cost, so further iteration leaves the output and accumulated I/O unchanged.

The three `1`s in `blocks+1+fuel+1+blocks+1` are zero-cost stage transitions. Each outer input, sorting, or output step runs 7, 2, or 8 underlying steps, respectively, and sums their costs. Thus an outer step can contain several physical transfers, each counted individually.

<details>
<summary>Expand: the outer controller and cost propagation for the three stages</summary>

`{s with buffer := ..., phase := ...}` denotes a new state with the listed fields replaced and all other fields retained from `s`. `match ... with` selects one of the following `| ... => ...` branches by the current value; `_` in a pattern matches the remaining cases.

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
def code (p : Program L R B b d w) (k : Fin 8) : Word w :=
  ⟨k.val,lt_of_lt_of_le k.isLt p.phase_capacity⟩

def inputSize (s : State L R B b d w) : ℕ := min (decodeWords s.inputCount) R
def outputSize (s : State L R B b d w) : ℕ := min (decodeWords s.outputCount) (R-1)

def converter (p : Program L R B b d w) (n : ℕ) (hn : n ≤ R) :
    PhysicalNormalizationLayout.Program R B b d w :=
  ⟨n,hn,hn.trans_lt p.counter_capacity,p.positive_region,p.positive_block,
    p.block_ratio,p.phase_capacity,p.padding⟩

def inputProgram (p : Program L R B b d w) (s : State L R B b d w) :=
  converter p (inputSize s) (Nat.min_le_right _ _)
def outputProgram (p : Program L R B b d w) (s : State L R B b d w) :=
  converter p (outputSize s) ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))

def expandView (disk : Disk R B w) : PhysicalNormalizationLayout.Disk R B w
  | .inl a => disk (.inl a)
  | .inr a => disk (.inr (.inl a))
def compactView (disk : Disk R B w) : PhysicalNormalizationLayout.Disk R B w
  | .inl a => disk (.inr (.inl a))
  | .inr a => disk (.inr (.inr a))
def installExpand (old : Disk R B w) (new : PhysicalNormalizationLayout.Disk R B w) : Disk R B w
  | .inl a => new (.inl a)
  | .inr (.inl a) => new (.inr a)
  | .inr (.inr a) => old (.inr (.inr a))
def installCompact (old : Disk R B w) (new : PhysicalNormalizationLayout.Disk R B w) : Disk R B w
  | .inl a => old (.inl a)
  | .inr (.inl a) => new (.inl a)
  | .inr (.inr a) => new (.inr a)
def installCore (old : Disk R B w) (new : Normalization.Disk R B (Word w)) : Disk R B w
  | .inl a => old (.inl a)
  | .inr (.inl a) => new a
  | .inr (.inr a) => old (.inr (.inr a))

def expandState (s : State L R B b d w) : PhysicalNormalizationLayout.State R B b d w :=
  ⟨s.buffer,s.scratch,s.counter,s.phase,expandView s.disk⟩
def compactState (s : State L R B b d w) : PhysicalNormalizationLayout.State R B b d w :=
  ⟨s.buffer,s.scratch,s.counter,s.phase,compactView s.disk⟩
def coreState (s : State L R B b d w) : FixedPolicyNormalization.State L B R w :=
  ⟨⟨s.ram,s.buffer,fun a => s.disk (.inr (.inl a))⟩,s.phase⟩

def putExpand (s : State L R B b d w) (t : PhysicalNormalizationLayout.State R B b d w) :=
  {s with buffer:=t.buffer,scratch:=t.scratch,counter:=t.counter,phase:=t.phase, disk:=installExpand s.disk t.disk}
def putCompact (s : State L R B b d w) (t : PhysicalNormalizationLayout.State R B b d w) :=
  {s with buffer:=t.buffer,scratch:=t.scratch,counter:=t.counter,phase:=t.phase, disk:=installCompact s.disk t.disk}
def putCore (s : State L R B b d w) (t : FixedPolicyNormalization.State L B R w) :=
  {s with ram:=t.data.ram,buffer:=t.data.buffer,phase:=t.phase, disk:=installCore s.disk t.data.disk}
```

[CodedSorting/Shared/Memory/NormalizationController.lean](../CodedSorting/Shared/Memory/NormalizationController.lean)

```lean
def step (p : Program L R B b d w) (s : State L R B b d w) : State L R B b d w × ℕ :=
  match s.stage.val with
  | 0 =>
      if decodeWords s.counter  <  inputSize s then
        let e := PhysicalNormalizationLayout.run (inputProgram p s) 7 (expandState s)
        (putExpand s e.1,e.2)
      else ({s with stage:=code p 1,phase:=code p 0},0)
  | 1 =>
      if p.policy s.ram = none then
        ({s with stage:=code p 2,phase:=code p 0,counter:=PhysicalNormalizationLayout.counterCode d w 0, buffer:=fun _=>p.padding,scratch:=fun _=>p.padding},0)
      else
        let e := FixedPolicyNormalization.run p.block_ratio (by have := p.phase_capacity; omega) p.padding
          ⟨p.policy⟩ 2 (coreState s)
        (putCore s e.1,e.2)
  | 2 =>
      if decodeWords s.counter  <  outputSize s then
        let e := PhysicalNormalizationCompact.run (outputProgram p s) 8 (compactState s)
        (putCompact s e.1,e.2)
      else ({s with stage:=code p 3},0)
  | _ => (s,0)
```

</details>

<details>
<summary>Expand: the physical state and every execution case of the main algorithm</summary>

`Function.update disk address block` changes only the block at `address`, leaving every other address unchanged. Below it occurs in the disk-write branch, which charges one I/O. `/-- ... -/` is a source comment.

[CodedSorting/Shared/Programs/Normalization.lean](../CodedSorting/Shared/Programs/Normalization.lean)

```lean
structure PhysicalState (L B D : ℕ) (Word : Type*) where
  ram : Words L Word
  buffer : Words B Word
  disk : Disk D B Word
```

[CodedSorting/Shared/Programs/FixedPolicyNormalization.lean](../CodedSorting/Shared/Programs/FixedPolicyNormalization.lean)

```lean
structure Program (L b D w : ℕ) where
  policy : ControlledNormalization.Policy L b D (Word w)

/-- All data-dependent resident state: L payload/control words from the source
machine, B transfer words, and ONE additional phase word. -/
structure State (L B D w : ℕ) where
  data : PhysicalState L B D (Word w)
  phase : Word w
```

[CodedSorting/Shared/Programs/FixedPolicyNormalization.lean](../CodedSorting/Shared/Programs/FixedPolicyNormalization.lean)

```lean
def code (hcap : 4 ≤ 2^w) (k : Fin 4) : Word w :=
  ⟨k.val, lt_of_lt_of_le k.isLt hcap⟩
```

[CodedSorting/Shared/Programs/FixedPolicyNormalization.lean](../CodedSorting/Shared/Programs/FixedPolicyNormalization.lean)

```lean
def ready (hcap : 4 ≤ 2^w) (s : PhysicalState L B D (Word w)) : State L B D w :=
  ⟨s, code hcap 0⟩
```

[CodedSorting/Shared/Programs/FixedPolicyNormalization.lean](../CodedSorting/Shared/Programs/FixedPolicyNormalization.lean)

```lean
def step (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) (s : State L B D w) : State L B D w × ℕ :=
  match s.phase.val with
  | 0 => match p.policy s.data.ram with
    | none => (⟨s.data, code hcap 3⟩, 0)
    | some i => match i.operation with
      | .localOp f =>
          (⟨{s.data with ram := i.resume (f s.data.ram)}, code hcap 3⟩, 0)
      | .read address _ =>
          (⟨{s.data with buffer := s.data.disk address}, code hcap 1⟩, 1)
      | .write _ window =>
          (⟨{s.data with buffer := pack padding (slice s.data.ram window)},
            code hcap 2⟩, 0)
  | 1 => match p.policy s.data.ram with
    | some i => match i.operation with
      | .read _ window =>
          (ready hcap {s.data with ram := i.resume (load s.data.ram window (blockPrefix hb s.data.buffer))}, 0)
      | _ => (ready hcap s.data, 0)
    | none => (ready hcap s.data, 0)
  | 2 => match p.policy s.data.ram with
    | some i => match i.operation with
      | .write address _ =>
          (ready hcap {s.data with ram := i.resume s.data.ram, disk := Function.update s.data.disk address s.data.buffer}, 1)
      | _ => (ready hcap s.data, 0)
    | none => (ready hcap s.data, 0)
  | _ => (ready hcap s.data, 0)

def run (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w)
    (p : Program L b D w) : ℕ → State L B D w → State L B D w × ℕ
  | 0, s => (s, 0)
  | fuel+1, s =>
      let first := step hb hcap padding p s
      let rest := run hb hcap padding p fuel first.1
      (rest.1, first.2+rest.2)
```

</details>

<details>
<summary>Expand: memory windows and copying operations, <code>Window</code>, <code>load</code>, and <code>slice</code></summary>

[CodedSorting/Shared/Programs/Normalization.lean](../CodedSorting/Shared/Programs/Normalization.lean)

```lean
structure Window (L b : ℕ) where
  base : ℕ
  fits : base + b ≤ L

/-- Copy a block into the designated existing RAM window. -/
def load (ram : Words L Word) (w : Window L b) (block : Words b Word) :
    Words L Word := fun j =>
  if h : w.base ≤ j.val ∧ j.val < w.base + b then
    block ⟨j.val - w.base, by omega⟩
  else ram j

/-- Read the designated RAM window without allocating another RAM array. -/
def slice (ram : Words L Word) (w : Window L b) : Words b Word := fun j =>
  ram ⟨w.base + j.val, by have := w.fits; have := j.isLt; omega⟩

/-- Valid logical data is the blockPrefix of its own physical block. -/
def blockPrefix (h : b ≤ B) (block : Words B Word) : Words b Word :=
  fun j => block (Fin.castLE h j)

/-- Fill one physical transfer buffer; the unused suffix is irrelevant. -/
def pack (padding : Word) (block : Words b Word) : Words B Word := fun j =>
  if h : j.val < b then block ⟨j.val, h⟩ else padding
```

</details>

<details>
<summary>Expand: format-conversion counters and buffer operations</summary>

[CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean](../CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean)

```lean
structure Program (R B b d w : ℕ) where
  blocks : ℕ
  block_bound : blocks ≤ R
  counter_bound : blocks < (2^w)^d
  positive_region : 0<R
  positive_block : 0<B
  block_ratio : b≤B
  phase_capacity : 8≤2^w
  padding : Word w
```

[CodedSorting/Shared/Words/WordConvention.lean](../CodedSorting/Shared/Words/WordConvention.lean)

Braces around parameters, as in `{count w : ℕ}`, mean Lean usually infers them from the other arguments; this differs from the structure-update syntax `{s with ...}`. Below, `@[simp]` registers a proved equality as a simplification rule, and `simp [names, ...]` uses the listed definitions and simplification rules to prove the goal.

```lean
def decodeWords {count w : ℕ} (words : Words count w) : ℕ :=
  (finFunctionFinEquiv words).val
```

[CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean](../CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean)

```lean
def phaseCode (p : Program R B b d w) (k : Fin 8) : Word w :=
  ⟨k.val,lt_of_lt_of_le k.isLt p.phase_capacity⟩

def counterCode (d w j : ℕ) : Words d w :=
  finFunctionFinEquiv.symm ⟨j % (2^w)^d,Nat.mod_lt _ (by positivity)⟩

@[simp] theorem decode_counterCode (j : ℕ) :
    decodeWords (counterCode d w j) = j % (2^w)^d := by
  simp [counterCode,decodeWords]

/-- Addresses are evaluated from the counted counter. Live loop iterations
have j<R; the modular fallback merely makes the fixed program total. -/
def index (p : Program R B b d w) (j : ℕ) : Fin R :=
  ⟨j%R,Nat.mod_lt _ p.positive_region⟩

def current (s : State R B b d w) : ℕ := decodeWords s.counter

def nextPhase (p : Program R B b d w) (k : Fin 8) (s : State R B b d w) :=
  {s with phase := phaseCode p k}
```

[CodedSorting/Interchange/Framework/Memory/LayoutMachine.lean](../CodedSorting/Interchange/Framework/Memory/LayoutMachine.lean)

```lean
def extract (B b start block : ℕ) (hB : 0 < B)
    (buffer : Fin B → Value) (scratch : Fin b → Value) : Fin b → Value := fun i =>
  if (start+i.val) / B = block then
    buffer ⟨(start+i.val) % B, Nat.mod_lt _ hB⟩ else scratch i
```

[CodedSorting/Interchange/Framework/Memory/LayoutMachine.lean](../CodedSorting/Interchange/Framework/Memory/LayoutMachine.lean)

```lean
def patchBuffer (B b start block : ℕ) (scratch : Fin b → Value)
    (old : Fin B → Value) : Fin B → Value := fun i =>
  if h : start ≤ block*B+i.val ∧ block*B+i.val < start+b then
    scratch ⟨block*B+i.val-start, by omega⟩ else old i
```

</details>

<details>
<summary>Expand: physical transfers and costs of input and output conversion</summary>

[CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean](../CodedSorting/Interchange/Framework/Memory/PhysicalNormalizationLayout.lean)

```lean
def step (p : Program R B b d w) (s : State R B b d w) : State R B b d w × ℕ :=
  let j := current s
  if j < p.blocks then
    match s.phase.val with
    | 0 => (nextPhase p 1 {s with scratch := fun _ => p.padding},0)
    | 1 => (nextPhase p 2 {s with buffer := s.disk (.inl (index p (j*b/B)))},1)
    | 2 => (nextPhase p 3 {s with scratch := LayoutConversion.extract B b (j*b) (j*b/B) p.positive_block s.buffer s.scratch},0)
    | 3 => (nextPhase p 4 {s with buffer := s.disk (.inl (index p (j*b/B+1)))},1)
    | 4 => (nextPhase p 5 {s with scratch := LayoutConversion.extract B b (j*b) (j*b/B+1) p.positive_block s.buffer s.scratch},0)
    | 5 => (nextPhase p 6 {s with buffer := Normalization.pack p.padding s.scratch},0)
    | 6 => (nextPhase p 0 {s with counter := counterCode d w (j+1), disk := Function.update s.disk (.inr (index p j)) s.buffer},1)
    | _ => (s,0)
  else (s,0)

def run (p : Program R B b d w) : ℕ → State R B b d w → State R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)
```

[CodedSorting/Shared/Memory/PhysicalNormalizationCompact.lean](../CodedSorting/Shared/Memory/PhysicalNormalizationCompact.lean)

```lean
def step (p : Program R B b d w) (s : State R B b d w) : State R B b d w × ℕ :=
  let j := current s
  if j<p.blocks then
    match s.phase.val with
    | 0 => (nextPhase p 1 {s with buffer := s.disk (.inl (index p j))},1)
    | 1 => (nextPhase p 2 {s with scratch := fun i => s.buffer (i.castLE p.block_ratio)},0)
    | 2 => (nextPhase p 3 {s with buffer := s.disk (.inr (index p (j*b/B)))},1)
    | 3 => (nextPhase p 4 {s with buffer := LayoutConversion.patchBuffer B b (j*b) (j*b/B) s.scratch s.buffer},0)
    | 4 => (nextPhase p 5 {s with disk := Function.update s.disk (.inr (index p (j*b/B))) s.buffer},1)
    | 5 => (nextPhase p 6 {s with buffer := s.disk (.inr (index p (j*b/B+1)))},1)
    | 6 => (nextPhase p 7 {s with buffer := LayoutConversion.patchBuffer B b (j*b) (j*b/B+1) s.scratch s.buffer},0)
    | 7 => (nextPhase p 0 {s with counter := counterCode d w (j+1), disk := Function.update s.disk (.inr (index p (j*b/B+1))) s.buffer},1)
    | _ => (s,0)
  else (s,0)

def run (p : Program R B b d w) : ℕ → State R B b d w → State R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)
```

</details>

### 2.3 Check 3: at most $M$ memory words and polynomial disk space

**Accounting for the memory words (`Fintype.card (ResidentIndex q) ≤ M`).**

Apart from `disk`, all memory fields of `MachineState q`, together with a separately reserved complete disk-address port `port`, are indexed by the disjoint union `ResidentIndex q`. Since `Fin A ⊕ Fin B` has $A+B$ elements, `Fintype.card (ResidentIndex q)` counts all these memory positions:

| Memory field | Purpose | Words |
| --- | --- | --- |
| `ram` | Working memory, including data buffers and control variables for the current recursive call | $L=\mathtt{q.ramWords}$ |
| `buffer` | Physical block-transfer buffer (Appendix A.3) | $B$ |
| `scratch` | One logical block temporarily held during conversion | $\beta=\mathtt{q.block}$ |
| `counter`, `inputCount`, `outputCount` | Block counter and input/output block counts | $3d$, where $d=\mathtt{q.digits}$ |
| `phase`, `stage` | Inner phase and outer stage | $2$ |
| `port` | Separately reserved complete disk address | $d+1$ |
| **Total (`Fintype.card (ResidentIndex q)`)** | **Resident memory** | **$L+B+\beta+4d+3\le M$** |

<details>
<summary>Expand: <code>ResidentIndex</code> and its correspondence with state fields</summary>

[CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean](../CodedSorting/Sorting/Resources/Framework/NormalizationFrames.lean)

```lean
abbrev MachineState (q : Configuration) :=
  CommonNormalizationController.State q.ramWords (q.N^q.exponent) q.B q.block q.digits q.w

/-- These are the actual fields of MachineState, plus its separately
reserved address port. The source RAM is the injective pack above. -/
abbrev ResidentIndex (q : Configuration) :=
  (Fin q.ramWords ⊕ Fin q.B) ⊕
    ((Fin q.block ⊕ Fin q.digits) ⊕
      ((Fin q.digits ⊕ Fin q.digits) ⊕ (Fin 2 ⊕ Fin (q.digits+1))))

def resident (q : Configuration) (s : MachineState q) (port : Words (q.digits+1) q.w) :
    ResidentIndex q → Word q.w
  | .inl (.inl i) => s.ram i
  | .inl (.inr i) => s.buffer i
  | .inr (.inl (.inl i)) => s.scratch i
  | .inr (.inl (.inr i)) => s.counter i
  | .inr (.inr (.inl (.inl i))) => s.inputCount i
  | .inr (.inr (.inl (.inr i))) => s.outputCount i
  | .inr (.inr (.inr (.inl i))) => if i.val=0 then s.phase else s.stage
  | .inr (.inr (.inr (.inr i))) => port i
```

</details>

`ram` contains the current call's data and control variables. On entering a child call, the suspended parent state is written to disk. `fuel` is the mathematical iteration count used to describe a finite execution; counters and phase fields record the execution position in the actual state.

**Polynomial disk space.**

There are three disk regions. The total block count `Fintype.card (Address (q.N^q.exponent))` is $3N^E\le N^{E+2}$, and the total word count is $3N^EB\le N^{E+3}$. Since $E=\mathtt{exponent}(\kappa)$ depends only on the fixed word-width constant $\kappa$, disk space throughout the execution is bounded by a fixed polynomial in $N$.

---

## 3. The small-memory case `SmallGuarantee`

When $M<\mathrm{Mcut}(c,\kappa)$, physical memory is below a fixed threshold. The algorithm uses direct radix sorting when $w\ge\lceil\log_2N\rceil$ and counting sort when $w<\lceil\log_2N\rceil$, as in Section 8.3 (Lemma 8.3) of the paper. `SmallGuarantee` gives correctness and resource guarantees corresponding to the normal-memory case:

<details>
<summary>Expand: the complete definition of <code>SmallGuarantee</code></summary>

```lean
def SmallGuarantee (c : ℕ) (κ : ℝ) (N M B w : ℕ) (hB : 0<B) : Prop :=
  ∃ (code : List (TwoWordSmallMemorySorting.Stage B w)) (allocation : ℕ)
    (output : List (Word w) → List (Word w)),
    TwoWordSmallMemoryFootprint.BoundedCode allocation code ∧
    allocation*B≤smallSpaceBound c κ N ∧
    ∀ (s : TwoWordBlockLift.State B (Word w)) (xs : List (Word w)),
      xs.length=N → TwoWordBlockFormat.File hB s.disk xs →
      ∃t cost, TwoWordSmallMemorySorting.Executes hB code s t cost ∧
        TwoWordBlockFormat.File hB t.disk (output xs) ∧
        (output xs).Perm xs ∧ (output xs).Pairwise (fun x y=>x.val≤y.val) ∧
        Fintype.card (Fin B ⊕ Fin B)≤M ∧
        (cost : ℝ)≤coefficient c κ*((N : ℝ)/B)*factor N M B
```

</details>

**Reading `SmallGuarantee` in two parts.**

1. **Choose the program and disk allocation before the input (`∃ code allocation output`).** A list of program stages `code`, a block allocation `allocation`, and an output function `output` must satisfy `BoundedCode allocation code` and `allocation * B ≤ smallSpaceBound c κ N`. Since the existential quantifiers precede `∀ s xs`, the same program and allocation apply to every input of length $N$.
2. **Execute on every legal input (`∀ s xs` and `∃ t cost`).** For each initial state and compact input file, some final state `t` and I/O count `cost` satisfy all execution and output conditions. `Executes hB code s t cost` describes a completed finite run; `File hB t.disk (output xs)`, `Perm`, and `Pairwise` require the disk output to be a nondecreasing permutation of the input. The two buffers occupy $2B\le M$ words, and `cost` satisfies the same I/O bound as in the normal-memory case.

### 3.1 Check 1: two physical block buffers and compact disk files

In the small-memory model in [SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean), data memory consists of `left` and `right`, two physical buffers of $B$ words each. Their total size is `Fintype.card (Fin B ⊕ Fin B) = 2B ≤ M`. The predicate `File hB disk xs` requires offset `i % B` of disk block `i / B` to equal `xs.get i`, using the same compact layout as the normal-memory case.

The five basic commands have the following roles:

* `.readLeft a` and `.writeLeft a` transfer a whole block between fixed disk address `a` and the left buffer.
* `.readRight a` and `.writeRight a` compute an address from the current pair of buffers, then transfer a whole block to or from the right buffer.
* `.cpu f` computes and updates the two buffers from their current contents, without accessing disk.

<details>
<summary>Expand: compact <code>File</code>, the two-buffer <code>State</code>, and five basic commands</summary>

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def cell (hB : 0<B) (i : ℕ) : Fin B := ⟨i%B,Nat.mod_lt _ hB⟩
def wordAt (hB : 0<B) (disk : ℕ→Buffer B W) (i : ℕ) : W := disk (i/B) (cell hB i)
def File (hB : 0<B) (disk : ℕ→Buffer B W) (xs : List W) : Prop :=
  ∀ j : Fin xs.length,wordAt hB disk j.val=xs.get j
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
abbrev Buffer (B : ℕ) (W : Type*) := Fin B → W
structure State (B : ℕ) (W : Type*) where
  left : Buffer B W
  right : Buffer B W
  disk : ℕ → Buffer B W

inductive Command (B : ℕ) (W : Type*) where
  | readLeft (address : ℕ)
  | readRight (address : Buffer B W × Buffer B W → ℕ)
  | writeLeft (address : ℕ)
  | writeRight (address : Buffer B W × Buffer B W → ℕ)
  | cpu (f : Buffer B W × Buffer B W → Buffer B W × Buffer B W)

def step (cmd : Command B W) (s : State B W) : State B W :=
  match cmd with
  | .readLeft a => {s with left := s.disk a}
  | .readRight a => {s with right := s.disk (a (s.left,s.right))}
  | .writeLeft a => {s with disk := Function.update s.disk a s.left}
  | .writeRight a => {s with disk := Function.update s.disk (a (s.left,s.right)) s.right}
  | .cpu f => {s with left := (f (s.left,s.right)).1, right := (f (s.left,s.right)).2}
```

</details>

The inputs and outputs of `cpu` consist only of the two buffers. Data-dependent address functions also receive only these buffers. A fixed command and the current state therefore determine the next state uniquely. Section 3.3 states the storage convention for program control.

### 3.2 Check 2: small-memory execution and I/O accounting

[SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean) gives the cost of each of the five basic commands:

```lean
def cost : Command B W → ℕ
  | .cpu _ => 0
  | _ => 1
```

The in-memory buffer computation `.cpu f` costs zero I/Os. Each of the four physical transfer commands (`readLeft`, `readRight`, `writeLeft`, and `writeRight`) costs one I/O.

The outer program consists of sequential segments `straight`, block-compaction loops `loop`, and a sorting body `core`. Within `core`, each logical word occupies the first position of its own physical block, and `compile` translates the operations into the five whole-block commands above. The inductive relation `Executes` adds the costs of sequential commands, each read of a loop's stopping flag (`check`, costing one I/O), and each loop-body execution to obtain the total `cost`.

The rules separate sequential execution from loops. A sequential segment uses `execute` to run its command list and `transfers` to sum the command costs. Each loop iteration first reads its stopping flag with `check`, costing one I/O. The `stop` rule includes that final check. The `more` rule adds the check, the body cost, and the remaining iterations, giving `1 + transfers body + remaining cost`.

<details>
<summary>Expand: sequential execution and the outer <code>Executes</code> relation</summary>

`[]` is the empty list, and `cmd :: rest` is a list with first element `cmd` followed by `rest`. `inductive Executes ... : ... → Prop where` defines valid finite executions by rules: each rule lists its premises, then gives the resulting execution relation after the final colon. For example, `loop` requires both the loop and the remaining program to execute, yielding a combined execution with their costs added.

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def execute : List (Command B W) → State B W → State B W
  | [],s => s
  | cmd::rest,s => execute rest (step cmd s)
def transfers : List (Command B W) → ℕ
  | [] => 0
  | cmd::rest => cost cmd+transfers rest
```

[CodedSorting/Sorting/SmallMemory/SmallMemorySorting.lean](../CodedSorting/Sorting/SmallMemory/SmallMemorySorting.lean)

```lean
inductive Stage (B w : ℕ) where
  | straight (body : List (Command B (Word w)))
  | loop (p : TwoWordUniformBlockFormat.LoopProgram B (Word w))
  | core (base : ℕ) (body : List (TwoWordRadixPreparedBuild.Stage (Word w)))

inductive Executes {B w : ℕ} (hB : 0<B) :
    List (Stage B w) → State B (Word w) → State B (Word w) → ℕ → Prop where
  | done (s : State B (Word w)) : Executes hB [] s s 0
  | straight (body : List (Command B (Word w))) (rest : List (Stage B w))
      (s t : State B (Word w)) (cost : ℕ)
      (tail : Executes hB rest (TwoWordBlockLift.execute body s) t cost) :
      Executes hB (.straight body::rest) s t (TwoWordBlockLift.transfers body+cost)
  | loop (p : TwoWordUniformBlockFormat.LoopProgram B (Word w)) (rest : List (Stage B w))
      (s mid t : State B (Word w)) (ca cb : ℕ)
      (first : TwoWordUniformBlockFormat.Executes hB p s mid ca)
      (tail : Executes hB rest mid t cb) :
      Executes hB (.loop p::rest) s t (ca+cb)
  | core (base : ℕ) (body : List (TwoWordRadixPreparedBuild.Stage (Word w)))
      (rest : List (Stage B w)) (s mid t : State B (Word w)) (ca cb : ℕ)
      (first : TwoWordBlockLift.Executes hB base body s mid ca)
      (tail : Executes hB rest mid t cb) :
      Executes hB (.core base body::rest) s t (ca+cb)
```

</details>

<details>
<summary>Expand: stopping checks and costs of the block-compaction loop</summary>

[CodedSorting/Sorting/SmallMemory/Uniform/BlockCompress.lean](../CodedSorting/Sorting/SmallMemory/Uniform/BlockCompress.lean)

```lean
structure LoopProgram (B : ℕ) (W : Type*) where
  flagAddress : ℕ
  halt : W
  body : List (Command B W)

def check {W : Type*} (p : LoopProgram B W) (s : State B W) : State B W :=
  step (.readLeft p.flagAddress) s
def next {W : Type*} (p : LoopProgram B W) (s : State B W) : State B W :=
  execute p.body (check p s)
inductive Executes {W : Type*} (hB : 0<B) (p : LoopProgram B W) :
    State B W → State B W → ℕ → Prop where
  | stop (s : State B W) (h : (check p s).left ⟨0,hB⟩=p.halt) :
      Executes hB p s (check p s) 1
  | more (s t : State B W) (cost : ℕ)
      (h : (check p s).left ⟨0,hB⟩≠p.halt)
      (rest : Executes hB p (next p s) t cost) :
      Executes hB p s t (1+transfers p.body+cost)
```

</details>

<details>
<summary>Expand: instruction compilation and loop execution in the sorting <code>core</code></summary>

`code.map (compile hB base)` applies `compile hB base` to each instruction in `code`, preserving their order.

[CodedSorting/Sorting/SmallMemory/PhysicalAddresses.lean](../CodedSorting/Sorting/SmallMemory/PhysicalAddresses.lean)

```lean
inductive Command (W : Type*) where
  | readLeft (a : ℕ)
  | readRight (a : ℕ)
  | readRightAt (a : Resident W → ℕ)
  | writeLeft (a : ℕ)
  | writeRight (a : Resident W → ℕ)
  | localOp (f : Resident W → Resident W)
```

[CodedSorting/Sorting/SmallMemory/Uniform/Loop.lean](../CodedSorting/Sorting/SmallMemory/Uniform/Loop.lean)

```lean
structure Program (W : Type*) where
  pcAddress : ℕ
  halt : W
  body : List (Command W)
```

[CodedSorting/Sorting/SmallMemory/Radix/Initialize.lean](../CodedSorting/Sorting/SmallMemory/Radix/Initialize.lean)

```lean
inductive Stage (W : Type*) where
  | straight (code : List (TwoWordPhysicalAddresses.Command W))
  | loop (program : Physical.Program W)
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def compile (hB : 0<B) (base : ℕ) : TwoWordPhysicalAddresses.Command W → Command B W
  | .readLeft a => .readLeft (base+a)
  | .readRight a => .readRight (fun _ => base+a)
  | .readRightAt a => .readRight (fun r => base+a (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩))
  | .writeLeft a => .writeLeft (base+a)
  | .writeRight a => .writeRight (fun r => base+a (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩))
  | .localOp f => .cpu (fun r =>
      let v := f (r.1 ⟨0,hB⟩,r.2 ⟨0,hB⟩)
      (fun _ => v.1,fun _ => v.2))
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def check (base : ℕ) (p : Physical.Program W) (s : State B W) :=
  step (.readLeft (base+p.pcAddress)) s
def next (hB : 0<B) (base : ℕ) (p : Physical.Program W) (s : State B W) :=
  execute (p.body.map (compile hB base)) (check base p s)
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
inductive LoopExecutes (hB : 0<B) (base : ℕ) (p : Physical.Program W) :
    State B W → State B W → ℕ → Prop where
  | stop (s : State B W) (h : (check base p s).left ⟨0,hB⟩=p.halt) :
      LoopExecutes hB base p s (check base p s) 1
  | more (s t : State B W) (c : ℕ)
      (h : (check base p s).left ⟨0,hB⟩≠p.halt)
      (rest : LoopExecutes hB base p (next hB base p s) t c) :
      LoopExecutes hB base p s t (1+transfers (p.body.map (compile hB base))+c)
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
inductive Executes (hB : 0<B) (base : ℕ) :
    List (TwoWordRadixPreparedBuild.Stage W) → State B W → State B W → ℕ → Prop where
  | done (s : State B W) : Executes hB base [] s s 0
  | straight (code : List (TwoWordPhysicalAddresses.Command W))
      (rest : List (TwoWordRadixPreparedBuild.Stage W)) (s t : State B W) (c : ℕ)
      (tail : Executes hB base rest (execute (code.map (compile hB base)) s) t c) :
      Executes hB base (.straight code::rest) s t (transfers (code.map (compile hB base))+c)
  | loop (p : Physical.Program W) (rest : List (TwoWordRadixPreparedBuild.Stage W))
      (s mid t : State B W) (ca cb : ℕ) (first : LoopExecutes hB base p s mid ca)
      (tail : Executes hB base rest mid t cb) :
      Executes hB base (.loop p::rest) s t (ca+cb)
```

</details>

The inductive rules of `Executes` describe finite execution: a sequential segment consumes a finite instruction list, a loop consists of finitely many `more` steps followed by `stop`, and consecutive segments connect the preceding final state to the next initial state while adding their costs. Thus `∃ t cost, Executes ... s t cost` supplies both the state `t` after completing the program and its total I/O count `cost`.

### 3.3 Check 3: disk-space bounds and the control convention

**Disk address bounds (`BoundedCode allocation code`).**

Although the small-memory disk has type `ℕ → Buffer B W`, `BoundedCode allocation code` recursively checks all instructions, including every possible result of data-dependent addresses in `readRight` / `writeRight` and the loop-flag addresses. It requires **every physical block address read or written to be strictly below `allocation`**. The inequality `allocation * B ≤ smallSpaceBound c κ N` then bounds the total number of disk words by a fixed polynomial in $N$.

**Program control.**

As in Section 8.3 and Appendix D of the paper, program code is stored separately from data memory. Data memory consists of `left` and `right`, totaling $2B\le M$ words. When $w\ge\lceil\log_2N\rceil$, loop cursors and stopping flags are stored on disk and their reads and writes are included in the I/O count. When $w<\lceil\log_2N\rceil$, the controller maintains the position in a predetermined instruction sequence outside the $M$ data words.

<details>
<summary>Expand: <code>BoundedCode</code> address bounds and <code>smallSpaceBound</code></summary>

`∀ st ∈ code, ...` requires the condition for every stage in the list. `True` is the always-true proposition; here a memory-only command has no additional disk-address condition because it does not access disk.

[CodedSorting/Sorting/SmallMemory/PublicUnrolledBlockSort.lean](../CodedSorting/Sorting/SmallMemory/PublicUnrolledBlockSort.lean)

```lean
def BoundedStage (L : ℕ) : Stage B w → Prop
  | .straight body => TwoWordBlockFootprint.BoundedCode L body
  | .loop p => TwoWordUniformBlockFormat.BoundedProgram L p
  | .core base body => ∃ R, base+R≤L ∧ TwoWordRadixFootprint.BoundedCode R body

def BoundedCode (L : ℕ) (code : List (Stage B w)) : Prop := ∀st∈code,BoundedStage L st
```

[CodedSorting/Sorting/SmallMemory/Uniform/BlockCompress.lean](../CodedSorting/Sorting/SmallMemory/Uniform/BlockCompress.lean)

```lean
def BoundedProgram {W : Type*} (L : ℕ) (p : LoopProgram B W) : Prop :=
  p.flagAddress<L ∧ TwoWordBlockFootprint.BoundedCode L p.body
```

[CodedSorting/Sorting/SmallMemory/Radix/Sort.lean](../CodedSorting/Sorting/SmallMemory/Radix/Sort.lean)

```lean
def BoundedCommand (L : ℕ) : Command W → Prop
  | .readLeft a => a<L
  | .readRight a => a<L
  | .readRightAt a => ∀r,a r<L
  | .writeLeft a => a<L
  | .writeRight a => ∀r,a r<L
  | .localOp _ => True

def BoundedStage (L : ℕ) : Stage W → Prop
  | .straight cmds => ∀c∈cmds,BoundedCommand L c
  | .loop p => p.pcAddress<L ∧ ∀c∈p.body,BoundedCommand L c

def BoundedCode (L : ℕ) (code : List (Stage W)) := ∀s∈code,BoundedStage L s
```

[CodedSorting/Sorting/SmallMemory/SmallSort.lean](../CodedSorting/Sorting/SmallMemory/SmallSort.lean)

```lean
def BoundedCommand (L : ℕ) : Command B W → Prop
  | .readLeft a => a<L
  | .readRight a => ∀ r,a r<L
  | .writeLeft a => a<L
  | .writeRight a => ∀ r,a r<L
  | .cpu _ => True
def BoundedCode (L : ℕ) (code : List (Command B W)) :=
  ∀ cmd∈code,BoundedCommand L cmd
```

[CodedSorting/Sorting/Theorem31/Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean)

```lean
def smallSpaceBound (c : ℕ) (κ : ℝ) (N : ℕ) : ℕ :=
  (N+13+6*N^(2*SmallMemorySortingRate.wordFactor κ))*N+(2*c+16)*N^2
```

</details>

Writing $u=\max\{1,\lceil\kappa\rceil\}$, this space bound is $(N+13+6N^{2u})N+(2c+16)N^2$. Its coefficients and degree are fixed once $c,\kappa$ are fixed.

---

## 4. The common I/O bound and constant dependencies

Both `NormalGuarantee` and `SmallGuarantee` bound the accumulated physical I/O count $Q$ (`result.2` or `cost`) by the same expression:

$$Q\le\mathtt{coefficient}(c,\kappa)\cdot\frac NB\cdot\mathtt{factor}(N,M,B).$$

### 4.1 Checking the logarithmic factor `factor`

[Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean) and [LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean) specify `factor`:

`simp only [names, ...]` restricts simplification to the listed definitions and rules. Below, `ℚ` denotes rational numbers, so `3 / 200000` in `epsilon` is an exact fraction. In `factor`, `(M : ℝ)/B` is real division, not integer division.

```lean
theorem factor_eq (N M B : ℕ) : factor N M B=GeneralWordNormalSorting.factor N M B := by
  simp only [factor,SmallMemorySortingRate.paperFactor,GeneralWordNormalSorting.factor,
    CommonLocalBudgetRate.tau,sub_sub_cancel]
```

```lean
def factor (N M B : ℕ) : ℝ :=
  1+Real.log (N : ℝ)/
    (Real.log ((M : ℝ)/B)^(1-(CodedSorting.Construction.epsilon : ℝ))*
      Real.log (M : ℝ)^(CodedSorting.Construction.epsilon : ℝ))
```

The exponent constant $\varepsilon$ is defined as a rational number in [Exponent.lean](../CodedSorting/Circuit/Parameters/Exponent.lean):

```lean
def epsilon : ℚ := 3 / 200000
```

Thus $\varepsilon=1.5\times10^{-5}$. The exponents of $\ln(M/B)$ and $\ln M$ in the denominator sum to $(1-\varepsilon)+\varepsilon=1$. Consequently, changing `Real.log` from natural logarithms to the paper's base-two logarithms cancels the factor $\ln2$ between numerator and denominator. Hence `factor N M B` is exactly the bracketed term in Theorem 3.1:

$$1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^\varepsilon}.$$

### 4.2 Where the address-exchange recurrence enters

The exponent $1-\varepsilon$ comes from the address-field exchange recursion in Section 6 of the paper. In [ExchangeInterface.lean](../CodedSorting/Interchange/Bounds/ExchangeInterface.lean), `costBound` bounds the exchange cost at recursion depth $k$, data volume $V$ bits, block size $b$ bits, and in-memory stopping threshold `cutoff`. It satisfies the integer recurrence:

* If $k=0$ or $V\le\texttt{cutoff}$, then $Q(k,V)=20(\lfloor V/b\rfloor+1)$.
* If $V>\texttt{cutoff}$, then $Q(k+1,V)=a(\lfloor V/b\rfloor+1)+S\,Q(k,\lfloor V/W\rfloor)$, where $m=512$, $W=24432543$, and $S=12508242237$ are the fixed circuit parameters from Section 5, and $a$ is the fixed cost coefficient of the one-level implementation.

The theorem `exists_rate` in [Resources.lean](../CodedSorting/Interchange/Recursion/Resources.lean) gives an absolute constant $K$, chosen as `rateConstant` in the code, such that every $b,\texttt{cutoff},k,V$ with $b>0$ and $\texttt{cutoff}\ge Wb$ satisfies $Q(k,V)\le K(1+\frac Vb m^{k(1-\varepsilon)})$.

<details>
<summary>Expand: <code>exists_rate</code> and its quantifier order, <code>∃ K, ∀ b cutoff k V</code></summary>

[CodedSorting/Interchange/Recursion/Resources.lean](../CodedSorting/Interchange/Recursion/Resources.lean)

```lean
theorem exists_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b cutoff k V : Nat,
      0 < b → streamCount * b ≤ cutoff →
      (costBound coefficient b cutoff k V : ℝ) ≤
        K * (1 + (V : ℝ) / b *
          (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  exists_costBound_rate coefficient
```

</details>

### 4.3 Checking the independence of `coefficient`

The coefficient in the big-$O$ bound must apply uniformly to all legal size parameters. We check the parameters and definition of `coefficient`, together with the dependencies of its referenced constants:

```lean
def coefficient (c : ℕ) (κ : ℝ) : ℝ := max 1
  (max (GeneralWordNormalSorting.coefficient c κ)
    (max (5000*(SmallMemorySortingRate.wordFactor κ : ℝ)*GeneralWordNormalSorting.Mcut c κ)
      (305*((c : ℝ)+2)*GeneralWordNormalSorting.Mcut c κ)))
```

The complete parameter list of this `coefficient` contains only the word-width constants `(c : ℕ)` and `(κ : ℝ)`. It takes the maximum of $1$, the normal-memory coefficient, and the two small-memory coefficients. The excerpts below show that `Mcut c κ` and `GeneralWordNormalSorting.coefficient c κ` likewise depend only on the fixed construction and $c,\kappa$. The recurrence constant they use is selected uniformly by the preceding `∃ K, ∀ b cutoff k V` result, independently of $N,M,B,w$.

<details>
<summary>Expand: the memory threshold <code>Mcut</code>, disk <code>exponent</code>, and normal-memory coefficient</summary>

[CodedSorting/Sorting/Theorem31/LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean)

```lean
def inventory : SortingResourceBudget.Inventory where
  readers := 1
  writers := 0
  keys := 0
  pc := 0
  ratio := PhysicalLeafParameters.minimumRatio Construction.ExchangeSpecialization.radix 1
    Construction.streamCount
def exponent (κ : ℝ) : ℕ := CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent (wordFactor κ)
def digits (c : ℕ) (κ : ℝ) : ℕ := SortingResourceBudget.digits c (exponent κ)
def reserveSize (c : ℕ) (κ : ℝ) : ℕ :=
  SortingResourceBudget.reserve inventory c (digits c κ)
def Mcut (c : ℕ) (κ : ℝ) : ℕ := reserveSize c κ ^ 2
```

[CodedSorting/Sorting/Theorem31/LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean)

```lean
def coefficient (c : ℕ) (κ : ℝ) : ℝ :=
  (2*(reserveSize c κ : ℝ)^2)*
    (1+Real.log (2*(reserveSize c κ : ℝ))/Real.log 2)^2*
    (12*22194000000*
      GlobalSortingBound.rateConstant CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau*
      (κ*(1+Real.log (4*(digits c κ : ℝ))/Real.log 2)+2)+2*(16 : ℝ))
```

</details>

The quantifiers have the following order: first fix $c,\kappa$ and the corresponding complexity coefficient, memory threshold, and disk exponent; then take any legal $N,M,B,w$; determine the program from those size parameters; and finally obtain the same bound for every input of that size.

| Parameter category | Parameters | Dependencies | Source |
| --- | --- | --- | --- |
| **Circuit constants** | $m=512$, $W=24432543$, $S=12508242237$ | Fixed | [Counts.lean](../CodedSorting/Circuit/Parameters/Counts.lean) |
| **Exponent constants** | $\varepsilon=3/200000$, $\eta=33/338432$ | Fixed | [Exponent.lean](../CodedSorting/Circuit/Parameters/Exponent.lean) |
| **Implementation constants** | Prime `radix`, one-level cost $a$, `rateConstant` | Fixed | [Exchange.lean](../CodedSorting/Interchange/OneLevel/Exchange.lean), [Resources.lean](../CodedSorting/Interchange/Recursion/Resources.lean) |
| **Word-width constants** | $c,\kappa$ | Fixed in advance by the $w=\Theta(\log N)$ convention | [Model.md](Model.md) |
| **Top-level threshold and coefficients** | `Mcut c κ`, `coefficient c κ`, `exponent κ` | Depend only on $c,\kappa$; uniform in $N,M,B,w$ | [LargeMemory.lean](../CodedSorting/Sorting/Theorem31/LargeMemory.lean), [Proof.lean](../CodedSorting/Sorting/Theorem31/Proof.lean) |
| **Size and instance variables** | $N,M,B,w$ and subproblem dimensions $e,V,P,G,l,k$ | Vary with input size, machine configuration, or recursion depth | Explicit parameters in the corresponding statements and definitions |

---

## 5. Documentation checks and proof compilation

From the repository root, run the following to verify that every Lean excerpt on this page matches the repository source exactly:

```sh
python3 lean/scripts/check_release.py
```

After installing the repository's specified Lean toolchain, compile the complete proof and run the automated audit with the commands below. [Audit.lean](../Audit.lean) checks the type of `theorem_3_1` against its implementation theorem and lists its axiom dependencies. The verification script checks that those dependencies are among the three foundational logical principles `propext`, `Classical.choice`, and `Quot.sound`.

```sh
cd lean
lake exe cache get
python3 scripts/verify.py
```
