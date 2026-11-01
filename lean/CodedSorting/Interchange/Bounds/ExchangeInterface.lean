import CodedSorting.Interchange.Framework.Memory.ExchangeShapeProgram
import CodedSorting.Interchange.Framework.Recursion.ExchangeBudget
import CodedSorting.Interchange.Framework.Memory.ExchangeLeaf
import CodedSorting.Circuit.Parameters.Exponent

/-!
# Executable interface for the Construction equal-width recursion

`Constructors` is an uninstantiated implementation contract, not an Construction
algorithm.  Its fields return the existing finite-machine `Program`, so they
must provide real instructions, correctness on every machine state, a disk
frame, PC safety, I/O cost and instruction-length proofs.  `build` recursively
assembles those programs and `complete` proves properties of that SAME run.

The Construction child count, width multiplier and stream count occur in the indexed
tree itself.  The radix is a parameter: this file does not reuse the old
circuit's specialization prime as if it specialized the Construction matrices.

No Construction `Constructors` instance, canonical pruned family, improved sorting
theorem, or new global resource constants are claimed here.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.ExchangeInterface

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open scoped BigOperators

noncomputable section

/-- All dimensions and disk locations are public, independent of payloads. -/
structure Call where
  fieldWidth : ℕ
  prefixCount : ℕ
  gap : ℕ
  suffix : ℕ
  source : ℕ
  buffer : ℕ
  limit : ℕ

def volume (radix : ℕ) (c : Call) : ℕ :=
  CommonChunkLayout.Volume c.prefixCount (radix^c.fieldWidth) c.gap c.suffix

def permutation (radix : ℕ) (c : Call) : Equiv.Perm (Fin (volume radix c)) :=
  CommonChunkLayout.swap c.prefixCount (radix^c.fieldWidth) c.gap c.suffix

/-- This is the existing, fully specified actual-instruction program type. -/
abbrev Program (q : Configuration) (radix : ℕ) (c : Call) :=
  CommonFinitePermutation.Program q (volume radix c) c.source c.buffer c.limit
    (permutation radix c)

/-- At least one complete temporary copy fits inside the allocated interval.
The node constructor may require further space through the concrete child
calls and its own correctness/frame proof. -/
structure Allocation (q : Configuration) (radix : ℕ) (c : Call) : Prop where
  source_separate : c.source + count q (volume radix c) ≤ c.buffer
  temporary_fits : c.buffer + count q (volume radix c) ≤ c.limit
  limit_fits : c.limit ≤ q.N^q.exponent

theorem Allocation.source_fits {q : Configuration} {radix : ℕ} {c : Call}
    (a : Allocation q radix c) : c.source + count q (volume radix c) ≤ q.N^q.exponent := by
  have := a.source_separate
  have := a.temporary_fits
  have := a.limit_fits
  omega

/-- A node has exactly the new `rankBudget` selected equal-width child calls.
The volume identity accounts for all spectator coordinates.  Child source
and scratch intervals stay in the parent's disposable workspace. -/
structure Split (radix : ℕ) (parent : Call) where
  shortWidth : ℕ
  rows : ℕ
  short_positive : 0 < shortWidth
  parent_width : parent.fieldWidth = ambientDimension * shortWidth
  parent_prefix : parent.prefixCount = rows * streamCount
  child : Fin rankBudget → Call
  child_width : ∀ i, (child i).fieldWidth = shortWidth
  child_volume : ∀ i, streamCount * volume radix (child i) = volume radix parent
  child_source : ∀ i, parent.buffer ≤ (child i).source
  child_limit : ∀ i, (child i).limit ≤ parent.limit

theorem Split.child_volume_div {radix : ℕ} {parent : Call}
    (s : Split radix parent) (i : Fin rankBudget) :
    volume radix (s.child i) = volume radix parent / streamCount := by
  rw [←s.child_volume i]
  exact (Nat.mul_div_cancel_left _ (by decide : 0 < streamCount)).symm

theorem Split.child_field_smaller {radix : ℕ} {parent : Call}
    (s : Split radix parent) (i : Fin rankBudget) :
    (s.child i).fieldWidth < parent.fieldWidth := by
  rw [s.child_width i, s.parent_width, ambientDimension_eq]
  have := s.short_positive
  omega

theorem child_count : Fintype.card (Fin rankBudget) = rankBudget := Fintype.card_fin _

abbrev Children (q : Configuration) (radix : ℕ) {parent : Call}
    (s : Split radix parent) := (i : Fin rankBudget) → Program q radix (s.child i)

/-- The missing implementation obligations.  `node` must actually assemble
the supplied child instruction programs; no successful-execution oracle is
an argument.  Its returned `Program` contains all semantic/resource proofs.
`node_bound` relates that actual returned program to the sum of child charges.
There is deliberately no constructor instance in this module. -/
structure Constructors (q : Configuration) (radix : ℕ) where
  leafCharge : Call → ℕ
  localCharge : Call → ℕ
  leaf : (c : Call) → Allocation q radix c → Program q radix c
  leaf_bound : ∀ c a, (leaf c a).charge ≤ leafCharge c
  node : (c : Call) → Allocation q radix c → (s : Split radix c) →
    Children q radix s → Program q radix c
  node_bound : ∀ c a s children,
    (node c a s children).charge ≤ localCharge c + ∑ i, (children i).charge

/-- A finite public recursion plan.  Every leaf and node carries its actual
disk allocation, and every child is another tree, not a correctness premise. -/
inductive Tree (q : Configuration) (radix : ℕ) : Call → Type
  | leaf {c : Call} (allocation : Allocation q radix c) : Tree q radix c
  | node {c : Call} (allocation : Allocation q radix c) (split : Split radix c)
      (children : (i : Fin rankBudget) → Tree q radix (split.child i)) : Tree q radix c

def build {q : Configuration} {radix : ℕ} (kit : Constructors q radix) :
    {c : Call} → Tree q radix c → Program q radix c
  | c, .leaf a => kit.leaf c a
  | c, .node a s children => kit.node c a s (fun i => build kit (children i))

def budget {q : Configuration} {radix : ℕ} (kit : Constructors q radix) :
    {c : Call} → Tree q radix c → ℕ
  | c, .leaf _ => kit.leafCharge c
  | c, .node _ _ children => kit.localCharge c + ∑ i, budget kit (children i)

theorem build_charge_le {q : Configuration} {radix : ℕ} (kit : Constructors q radix) :
    ∀ {c : Call} (t : Tree q radix c), (build kit t).charge ≤ budget kit t
  | _, .leaf a => kit.leaf_bound _ a
  | _, .node a s children => by
      apply (kit.node_bound _ a s (fun i => build kit (children i))).trans
      exact Nat.add_le_add_left
        (Finset.sum_le_sum (fun i _ => build_charge_le kit (children i))) _

theorem build_cost_le {q : Configuration} {radix : ℕ} (kit : Constructors q radix)
    {c : Call} (t : Tree q radix c) :
    cost q (build kit t).instructions ≤ budget kit t :=
  (build kit t).cost_le.trans (build_charge_le kit t)

theorem build_length_le {q : Configuration} {radix : ℕ} (kit : Constructors q radix)
    {c : Call} (t : Tree q radix c) :
    (build kit t).instructions.length ≤ budget kit t :=
  (build kit t).length_le.trans (build_charge_le kit t)

/-- Literal code provenance at a recursive node: the output is the node
constructor applied to the recursively generated child programs. -/
theorem build_node_instructions {q : Configuration} {radix : ℕ}
    (kit : Constructors q radix) {c : Call} (a : Allocation q radix c)
    (s : Split radix c) (children : (i : Fin rankBudget) → Tree q radix (s.child i)) :
    (build kit (.node a s children)).instructions =
      (kit.node c a s (fun i => build kit (children i))).instructions := rfl

/-- Existing common-machine execution theorem, instantiated with the new
tree's actual program.  All five conclusions refer to one and the same run. -/
theorem complete {q : Configuration} {radix : ℕ} (kit : Constructors q radix)
    {c : Call} (t : Tree q radix c) (machine : Machine q)
    (hsize : budget kit t ≤ q.N^q.exponent) (hpc : pc q machine.ram = 0) :
    let p := build kit t
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length machine
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q machine.disk c.source (permutation radix c y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val < c.source ∨ c.source + count q (volume radix c) ≤ a.val) →
      (a.val < c.buffer ∨ c.limit ≤ a.val) → result.1.disk a = machine.disk a) ∧
    policy q p.instructions result.1.ram = none ∧ result.2 ≤ budget kit t ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  obtain ⟨hc,hf,hh,hcost,hm⟩ := CommonFinitePermutation.complete q (build kit t)
    machine ((build_charge_le kit t).trans hsize) hpc
  exact ⟨hc,hf,hh,hcost.trans (build_charge_le kit t),hm⟩

/-- The new pruned recurrence, with Construction's actual child count and splitting
factor.  The implementation coefficient is explicit; no old parameter is
silently substituted. -/
def costBound (coefficient b cutoff : ℕ) : ℕ → ℕ → ℕ
  | 0, V => 20 * (V / b + 1)
  | k+1, V => if V ≤ cutoff then 20 * (V / b + 1)
      else coefficient * (V / b + 1) +
        rankBudget * costBound coefficient b cutoff k (V / streamCount)

theorem costBound_stop (coefficient b cutoff k V : ℕ) (hV : V ≤ cutoff) :
    costBound coefficient b cutoff k V = 20 * (V / b + 1) := by
  cases k <;> simp only [costBound, if_pos hV]

/-- Numeric resident/buffered-leaf conditions.  These constrain the actual
machine bank and startup charge; they assert no successful execution. -/
def LeafFits (q : Configuration) (radix cutoff k : ℕ) (c : Call) : Prop :=
  if volume radix c ≤ cutoff then volume radix c ≤ CommonExchangeLeaf.bankBits q
  else k = 0 ∧
    (radix^c.fieldWidth)^2 * q.block ≤ CommonExchangeLeaf.bankWords q ∧
    (radix^c.fieldWidth)^2 * width q ≤ cutoff + width q

/-- Public resource and actual-charge conditions for a given finite tree.
Small leaves can stop at any depth; a buffered leaf is allowed at depth zero.
The charge conditions concern the same `Constructors` used by `build`. -/
def Fits {q : Configuration} {radix : ℕ} (kit : Constructors q radix)
    (coefficient cutoff : ℕ) : {c : Call} → Tree q radix c → ℕ → Prop
  | c, .leaf _, k => LeafFits q radix cutoff k c ∧
      kit.leafCharge c ≤ 20 * (volume radix c / width q + 1)
  | _, .node _ _ _, 0 => False
  | c, .node _ _ children, k+1 => cutoff < volume radix c ∧
      kit.localCharge c ≤ coefficient * (volume radix c / width q + 1) ∧
      ∀ i, Fits kit coefficient cutoff (children i) k

/-- Link the numerical recurrence to the budget of the actual assembled
instruction tree.  In particular the sum is over precisely `rankBudget`
children, each on a file of the proved parent-volume/streamCount size. -/
theorem budget_le_costBound {q : Configuration} {radix : ℕ}
    (kit : Constructors q radix) (coefficient cutoff : ℕ) :
    ∀ {c : Call} (t : Tree q radix c) (k : ℕ), Fits kit coefficient cutoff t k →
      budget kit t ≤ costBound coefficient (width q) cutoff k (volume radix c)
  | c, .leaf _, k, hf => by
      obtain ⟨hfit,hcharge⟩ := hf
      by_cases hsmall : volume radix c ≤ cutoff
      · rw [costBound_stop _ _ _ _ _ hsmall]
        exact hcharge
      · have hk : k = 0 := (by
          simpa only [LeafFits, if_neg hsmall] using hfit :
            k = 0 ∧ (radix^c.fieldWidth)^2 * q.block ≤ CommonExchangeLeaf.bankWords q ∧
              (radix^c.fieldWidth)^2 * width q ≤ cutoff + width q).1
        subst k
        exact hcharge
  | _, .node _ _ _, 0, hf => False.elim hf
  | c, .node _ s children, k+1, hf => by
      obtain ⟨hlarge,hlocal,hchildren⟩ := hf
      have hsum : (∑ i, budget kit (children i)) ≤
          rankBudget * costBound coefficient (width q) cutoff k
            (volume radix c / streamCount) := by
        calc
          (∑ i, budget kit (children i)) ≤
              ∑ _i : Fin rankBudget, costBound coefficient (width q) cutoff k
                (volume radix c / streamCount) := by
            apply Finset.sum_le_sum
            intro i _
            have h := budget_le_costBound kit coefficient cutoff (children i) k (hchildren i)
            rw [s.child_volume_div i] at h
            exact h
          _ = _ := by simp
      rw [costBound, if_neg (Nat.not_le.mpr hlarge)]
      exact Nat.add_le_add hlocal hsum

/-- Given the implementation, recursion tree, and workspace conditions, the constructed program runs on the common finite machine and satisfies the recurrence bound. The conclusion includes its output, termination, disk behavior, and memory use. 


-/
theorem pruned_complete {q : Configuration} {radix : ℕ}
    (kit : Constructors q radix) (coefficient cutoff : ℕ)
    {c : Call} (t : Tree q radix c) (k : ℕ) (hf : Fits kit coefficient cutoff t k)
    (machine : Machine q)
    (hsize : costBound coefficient (width q) cutoff k (volume radix c) ≤ q.N^q.exponent)
    (hpc : pc q machine.ram = 0) :
    let p := build kit t
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length machine
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q machine.disk c.source (permutation radix c y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val < c.source ∨ c.source + count q (volume radix c) ≤ a.val) →
      (a.val < c.buffer ∨ c.limit ≤ a.val) → result.1.disk a = machine.disk a) ∧
    policy q p.instructions result.1.ram = none ∧
    result.2 ≤ costBound coefficient (width q) cutoff k (volume radix c) ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  have hb := budget_le_costBound kit coefficient cutoff t k hf
  obtain ⟨hc,hframe,hh,hcost,hm⟩ := complete kit t machine (hb.trans hsize) hpc
  exact ⟨hc,hframe,hh,hcost.trans hb,hm⟩

/-- The numerical exponent belongs to Construction, independently of the old module's
parameters.  An actual node instance and analytic tree budget remain needed
before this inequality becomes a sorting bound. -/
theorem exponent_gap : (rankBudget : ℝ) / (streamCount : ℝ) <
    (ambientDimension : ℝ) ^ (1 - (Construction.epsilon : ℝ)) := Construction.strict_exponent_gap

def multiplier : ℝ := (rankBudget : ℝ) / (streamCount : ℝ)

/-- A scalar envelope used only after the actual-program/recurrence bridge.
The additional 40 handles resident stops at every remaining depth. -/
def envelope (coefficient : ℕ) : ℕ → ℝ
  | 0 => 40
  | k+1 => multiplier * envelope coefficient k + 2 * coefficient + 40

theorem multiplier_nonneg : 0 ≤ multiplier := by
  unfold multiplier
  positivity

theorem envelope_ge_forty (coefficient k : ℕ) : 40 ≤ envelope coefficient k := by
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
      have hp := mul_nonneg multiplier_nonneg (by linarith : 0 ≤ envelope coefficient k)
      have hc : (0 : ℝ) ≤ coefficient := Nat.cast_nonneg _
      dsimp only [envelope]
      linarith

theorem scan_scaled (coefficient b V : ℕ) (hV : b ≤ V) :
    (coefficient : ℝ) * ((V / b : ℕ) + 1) * (b : ℝ) ≤ 2 * coefficient * V := by
  have hd := Nat.div_mul_le_self V b
  have hs : (V / b + 1) * b ≤ 2 * V := by nlinarith
  have hc := Nat.mul_le_mul_left coefficient hs
  have h : coefficient * (V / b + 1) * b ≤ 2 * coefficient * V := by nlinarith
  exact_mod_cast h

/-- Above one block, every large node has children above one block, so
startup costs are absorbed without doubling the rank multiplier S/W. -/
theorem costBound_large_scaled (coefficient b cutoff k V : ℕ)
    (hcut : streamCount * b ≤ cutoff) (hV : b ≤ V) :
    (costBound coefficient b cutoff k V : ℝ) * b ≤ envelope coefficient k * V := by
  induction k generalizing V with
  | zero =>
      have h := scan_scaled 20 b V hV
      norm_num [costBound, envelope] at h ⊢
      exact h
  | succ k ih =>
      by_cases hsmall : V ≤ cutoff
      · have h := scan_scaled 20 b V hV
        have he := mul_le_mul_of_nonneg_right (envelope_ge_forty coefficient (k+1))
          (Nat.cast_nonneg V : (0 : ℝ) ≤ V)
        rw [costBound, if_pos hsmall]
        push_cast
        norm_num at h
        exact h.trans he
      · have hlarge : cutoff < V := Nat.lt_of_not_ge hsmall
        have hchild : b ≤ V / streamCount :=
          Recurrence.child_at_least_one_block V streamCount b
            (by decide) (hcut.trans hlarge.le)
        have hi := ih (V / streamCount) hchild
        have hs := scan_scaled coefficient b V hV
        have he : 0 ≤ envelope coefficient k :=
          (by norm_num : (0 : ℝ) ≤ 40).trans (envelope_ge_forty coefficient k)
        have hdiv : ((V / streamCount : ℕ) : ℝ) ≤ (V : ℝ) / streamCount := Nat.cast_div_le
        have hd := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdiv he) (Nat.cast_nonneg rankBudget : (0 : ℝ) ≤ rankBudget)
        have hid : (rankBudget : ℝ) * (envelope coefficient k * ((V : ℝ) / streamCount)) =
            multiplier * envelope coefficient k * V := by unfold multiplier; ring
        rw [hid] at hd
        have hc := mul_le_mul_of_nonneg_left hi
          (Nat.cast_nonneg rankBudget : (0 : ℝ) ≤ rankBudget)
        have hv0 : (0 : ℝ) ≤ V := Nat.cast_nonneg _
        rw [costBound, if_neg hsmall]
        push_cast
        dsimp only [envelope]
        nlinarith

/-- A coefficient uniform in b, cutoff, depth and volume, with Construction's target
epsilon.  The proof uses the generic recurrence lemma, never its old-parameter
specialization.  `pruned_improved_complete` applies it to actual instructions. -/
theorem exists_costBound_rate (coefficient : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b cutoff k V : ℕ,
      0 < b → streamCount * b ≤ cutoff →
      (costBound coefficient b cutoff k V : ℝ) ≤
        K * (1 + (V : ℝ) / b *
          (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) := by
  let R : ℝ := (ambientDimension : ℝ) ^ (1 - (Construction.epsilon : ℝ))
  have hm : (1 : ℝ) ≤ ambientDimension := by norm_num [ambientDimension_eq]
  have he : (Construction.epsilon : ℝ) < 1 := by exact_mod_cast Construction.epsilon_lt_one
  have hR : 1 ≤ R := Real.one_le_rpow hm (by linarith)
  obtain ⟨K,hK,hbound⟩ := Recurrence.exists_power_bound (envelope coefficient)
    multiplier (2 * coefficient + 40) 40 R multiplier_nonneg (by positivity)
    (by norm_num) hR exponent_gap (le_refl 40)
    (fun k => by dsimp only [envelope]; linarith)
  have hforty : 40 ≤ K := by simpa only [envelope, pow_zero, mul_one] using hbound 0
  refine ⟨K,hK,?_⟩
  intro b cutoff k V hb hcut
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hpow : R^k = (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ))) := by
    dsimp only [R]
    rw [mul_comm (k : ℝ), Real.rpow_mul_natCast (by positivity)]
  by_cases hV : b ≤ V
  · have hc := costBound_large_scaled coefficient b cutoff k V hcut hV
    have ha := mul_le_mul_of_nonneg_right (hbound k) (Nat.cast_nonneg V : (0 : ℝ) ≤ V)
    have hx : (costBound coefficient b cutoff k V : ℝ) ≤ K * ((V : ℝ) / b * R^k) := by
      apply (mul_le_mul_right hbr).mp
      have hid : K * ((V : ℝ) / b * R^k) * b = K * R^k * V := by
        field_simp [ne_of_gt hbr]
        ring
      rw [hid]
      exact hc.trans ha
    calc
      _ ≤ K * ((V : ℝ) / b * R^k) := hx
      _ ≤ K * (1 + (V : ℝ) / b * R^k) := by nlinarith
      _ = _ := by rw [hpow]
  · have hless : V < b := Nat.lt_of_not_ge hV
    have hW : 1 ≤ streamCount := by decide
    have hbW : b ≤ streamCount * b := by
      simpa only [one_mul] using Nat.mul_le_mul_right b hW
    have hbcut : b ≤ cutoff := hbW.trans hcut
    have hsmall : V ≤ cutoff := hless.le.trans hbcut
    rw [costBound_stop _ _ _ _ _ hsmall, Nat.div_eq_of_lt hless]
    simp only [Nat.zero_add, Nat.mul_one, Nat.cast_ofNat]
    have hx : (0 : ℝ) ≤ (V : ℝ) / b *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ))) := by positivity
    nlinarith

/-- Conditional executable equal-width endpoint with the new epsilon.
The same generated instructions supply correctness, frame, halt, RAM and the
improved real I/O bound.  No Construction `Constructors` instance is asserted. -/
theorem pruned_improved_complete {q : Configuration} {radix : ℕ}
    (kit : Constructors q radix) (coefficient : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ cutoff (c : Call) (t : Tree q radix c) (k : ℕ),
      Fits kit coefficient cutoff t k → streamCount * width q ≤ cutoff →
      ∀ machine : Machine q,
      costBound coefficient (width q) cutoff k (volume radix c) ≤ q.N^q.exponent →
      pc q machine.ram = 0 →
      let p := build kit t
      let result := ControlledNormalization.runLogical (policy q p.instructions)
        p.instructions.length machine
      (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
        readBit q machine.disk c.source (permutation radix c y).val) ∧
      (∀ a : Fin (q.N^q.exponent),
        (a.val < c.source ∨ c.source + count q (volume radix c) ≤ a.val) →
        (a.val < c.buffer ∨ c.limit ≤ a.val) → result.1.disk a = machine.disk a) ∧
      policy q p.instructions result.1.ram = none ∧
      (result.2 : ℝ) ≤ K * (1 + (volume radix c : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) ∧
      Fintype.card (ResidentIndex q) ≤ q.M := by
  obtain ⟨K,hK,hbound⟩ := exists_costBound_rate coefficient
  refine ⟨K,hK,?_⟩
  intro cutoff c t k hf hcut machine hsize hpc
  obtain ⟨hc,hframe,hh,hcost,hm⟩ :=
    pruned_complete kit coefficient cutoff t k hf machine hsize hpc
  exact ⟨hc,hframe,hh,(Nat.cast_le.mpr hcost).trans
    (hbound (width q) cutoff k (volume radix c) (width_pos q) hcut),hm⟩

def scalarCall (f P G S source buffer limit : ℕ) : Call :=
  ⟨f,P,G,S,source,buffer,limit⟩

/-- Existing scalar leaf programs can enter the numeric interface with no
new pass, provided the radix agrees.  The original instructions, charge and
all machine-resource certificates are retained. -/
def fromScalar {q : Configuration} {f P G S source buffer limit : ℕ}
    (p : CommonRecursiveExchange.Program q f P G S source buffer limit) :
    Program q RecursiveExchange.radix (scalarCall f P G S source buffer limit) where
  instructions := p.instructions
  charge := p.charge
  correct := fun machine => CommonChunkLayout.scalar_correct_numeric f P G S
    (readBit q machine.disk source)
    (readBit q (executeRaw q p.instructions machine).1.disk source) (p.correct machine)
  frame := p.frame
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

theorem fromScalar_instructions {q : Configuration} {f P G S source buffer limit : ℕ}
    (p : CommonRecursiveExchange.Program q f P G S source buffer limit) :
    (fromScalar p).instructions = p.instructions := rfl

theorem fromScalar_charge {q : Configuration} {f P G S source buffer limit : ℕ}
    (p : CommonRecursiveExchange.Program q f P G S source buffer limit) :
    (fromScalar p).charge = p.charge := rfl

/-- Exact compatibility with the old scalar exchange contract when the
chosen radix is that contract's radix.  This is a codec bridge only: it does
not assert that the old prime is valid for the new Construction matrix family. -/
def toScalar {q : Configuration} {f P G S source buffer limit : ℕ}
    (p : Program q RecursiveExchange.radix (scalarCall f P G S source buffer limit)) :
    CommonRecursiveExchange.Program q f P G S source buffer limit where
  instructions := p.instructions
  charge := p.charge
  correct := by
    intro machine a
    have h := p.correct machine (PhysicalFieldPacking.scalarLayout f P G S a)
    change readBit q (executeRaw q p.instructions machine).1.disk source
        (PhysicalFieldPacking.scalarLayout f P G S a).val =
      readBit q machine.disk source
        ((CommonRecursiveBase.permutation f P G S).symm
          (PhysicalFieldPacking.scalarLayout f P G S a)).val at h
    rw [CommonRecursiveBase.permutation_inverse_encoded] at h
    exact h
  frame := p.frame
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

theorem toScalar_instructions {q : Configuration} {f P G S source buffer limit : ℕ}
    (p : Program q RecursiveExchange.radix (scalarCall f P G S source buffer limit)) :
    (toScalar p).instructions = p.instructions := rfl

theorem toScalar_charge {q : Configuration} {f P G S source buffer limit : ℕ}
    (p : Program q RecursiveExchange.radix (scalarCall f P G S source buffer limit)) :
    (toScalar p).charge = p.charge := rfl

/-- A new tree can inhabit the existing scalar execution endpoint without
changing any instruction or charge.  The radix restriction is explicit. -/
theorem scalar_complete {q : Configuration} (kit : Constructors q RecursiveExchange.radix)
    {f P G S source buffer limit : ℕ}
    (t : Tree q RecursiveExchange.radix (scalarCall f P G S source buffer limit))
    (machine : Machine q) (hsize : budget kit t ≤ q.N^q.exponent)
    (hpc : pc q machine.ram = 0) :
    let p := toScalar (build kit t)
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length machine
    (∀ a : CommonRecursiveExchange.ScalarAddress f P G S,
      readBit q result.1.disk source (PhysicalFieldPacking.scalarLayout f P G S a).val =
      readBit q machine.disk source
        (PhysicalFieldPacking.scalarLayout f P G S (Address.exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val < source ∨ source + count q (PhysicalFieldPacking.ScalarVolume f P G S) ≤ a.val) →
      (a.val < buffer ∨ limit ≤ a.val) → result.1.disk a = machine.disk a) ∧
    policy q p.instructions result.1.ram = none ∧ result.2 ≤ budget kit t ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  obtain ⟨hc,hf,hh,hcost,hm⟩ := CommonRecursiveExchange.complete q f P G S source buffer limit
    (toScalar (build kit t)) machine ((build_charge_le kit t).trans hsize) hpc
  exact ⟨hc,hf,hh,hcost.trans (build_charge_le kit t),hm⟩

end
end CodedSorting.Construction.ExchangeInterface

#print axioms CodedSorting.Construction.ExchangeInterface.build_charge_le
#print axioms CodedSorting.Construction.ExchangeInterface.pruned_complete
#print axioms CodedSorting.Construction.ExchangeInterface.toScalar
#print axioms CodedSorting.Construction.ExchangeInterface.scalar_complete
#print axioms CodedSorting.Construction.ExchangeInterface.pruned_improved_complete
