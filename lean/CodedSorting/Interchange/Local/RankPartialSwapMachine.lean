import CodedSorting.Interchange.Framework.Memory.ExchangeShapeProgram
import CodedSorting.Interchange.Local.ExchangeFramePermutation

section PartialSwapMachine
/-!
# Actual-machine programs for the partial-swap scan components

The scan compiler below emits `Instruction q`, and its returned existing
`CommonFinitePermutation.Program` includes correctness, frame, PC safety,
I/O cost and code length. Padding returns every scan list to its source.
Recursive children are actual machine programs and are inserted once each;
they are not replaced by hypothetical scan executions.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.PartialSwapMachine

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs ScanProgram
open CommonLeafProgram (Machine)
open MatrixFactorization ScanProgramLift CommonAddressLayout
open PartialSwapScan PartialSwapExecution RankPartialSwapExecution

noncomputable section

/-- Numeric interval conditions for the actual two-buffer scan compiler. -/
structure ScanAllocation (q : Configuration) (V source buffer limit : ℕ) : Prop where
  source_separate : source + count q V ≤ buffer
  buffer_fits : buffer + count q V ≤ limit
  limit_fits : limit ≤ q.N^q.exponent

theorem ScanAllocation.source_fits {q : Configuration} {V source buffer limit : ℕ}
    (a : ScanAllocation q V source buffer limit) : source + count q V ≤ q.N^q.exponent := by
  have := a.source_separate
  have := a.buffer_fits
  have := a.limit_fits
  omega

/-- Compile the supplied concrete scans, including any required identity copy.
The declared charge pays for every generated instruction. -/
def scans (q : Configuration) {V source buffer limit : ℕ}
    (reader : Fin q.inventory.readers) (ps : List (Pass V))
    (a : ScanAllocation q V source buffer limit) :
    CommonFinitePermutation.Program q V source buffer limit (destination ps).symm where
  instructions := CommonRankEdgeScan.code q reader ps source buffer
  charge := 3 * (totalConstant ps + 8) * count q V
  correct := fun s y => CommonRankEdgeScan.raw_correct q reader ps source buffer s
    a.source_fits (a.buffer_fits.trans a.limit_fits) (Or.inl a.source_separate) y
  frame := by
    intro s x hs hb
    apply CommonRankEdgeScan.raw_outside q reader ps source buffer s
      a.source_fits (a.buffer_fits.trans a.limit_fits) (Or.inl a.source_separate) x hs
    rcases hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (a.buffer_fits.trans hb)
  safe := CommonRankEdgeScan.safe q reader ps source buffer
  cost_le := CommonRankEdgeScan.cost_le q reader ps source buffer
  length_le := CommonRankEdgeScan.length_le q reader ps source buffer

theorem scans_instructions (q : Configuration) {V source buffer limit : ℕ}
    (reader : Fin q.inventory.readers) (ps : List (Pass V))
    (a : ScanAllocation q V source buffer limit) :
    (scans q reader ps a).instructions = CommonRankEdgeScan.code q reader ps source buffer := rfl

/-- The two scan lists surround the literal instructions of the child program.
There is one child insertion, and its charge occurs with coefficient one. -/
def surround (q : Configuration) {V source buffer limit : ℕ}
    (reader : Fin q.inventory.readers) (before after : List (Pass V))
    (a : ScanAllocation q V source buffer limit) {π : Equiv.Perm (Fin V)}
    (child : CommonFinitePermutation.Program q V source buffer limit π) :
    CommonFinitePermutation.Program q V source buffer limit
      ((destination after).symm.trans (π.trans (destination before).symm)) :=
  ((scans q reader before a).append child).append (scans q reader after a)

theorem surround_instructions (q : Configuration) {V source buffer limit : ℕ}
    (reader : Fin q.inventory.readers) (before after : List (Pass V))
    (a : ScanAllocation q V source buffer limit) {π : Equiv.Perm (Fin V)}
    (child : CommonFinitePermutation.Program q V source buffer limit π) :
    (surround q reader before after a child).instructions =
      CommonRankEdgeScan.code q reader before source buffer ++ child.instructions ++
        CommonRankEdgeScan.code q reader after source buffer := rfl

theorem surround_charge (q : Configuration) {V source buffer limit : ℕ}
    (reader : Fin q.inventory.readers) (before after : List (Pass V))
    (a : ScanAllocation q V source buffer limit) {π : Equiv.Perm (Fin V)}
    (child : CommonFinitePermutation.Program q V source buffer limit π) :
    (surround q reader before after a child).charge =
      3 * (totalConstant before + totalConstant after + 16) * count q V + child.charge := by
  change 3 * (totalConstant before + 8) * count q V + child.charge +
    3 * (totalConstant after + 8) * count q V = _
  ring

section Lower
variable {K : Type*} [Fintype K] {m : ℕ}
local instance doubledDecEq : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq
variable {A : K → Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) ℚ}
variable (F : SpecializedFamily A) (f : ℕ) (k : K)
variable (hLower : TriangularConjugacy.LowerTriangular (A k)) (hUnit : IsUnit (A k))
variable (Pref G S : ℕ) (hG : 0 < G) (hS : 0 < S)
local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

/-- A concrete lower-matrix component from the new shared specialization,
compiled to the common finite machine. -/
def lower (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (a : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit) :=
  scans q reader (lowerProgram F f k hLower hUnit Pref G S hG hS) a

theorem lower_charge_le (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (a : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit) :
    (lower F f k hLower hUnit Pref G S hG hS q reader a).charge ≤
      3 * (lowerConstant (A := A) k + 8) * count q (Volume (Fin m) Pref (F.prime^f) G S) := by
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right (lowerProgram_constant F f k hLower hUnit Pref G S hG hS) 8

/-- Actual source-to-destination semantics. The program specification itself
uses the inverse permutation because its reads are output-to-input. -/
theorem lower_forward (a : Addr (Fin m) Pref (F.prime^f) G S) :
    destination (lowerProgram F f k hLower hUnit Pref G S hG hS) (longLayout a) =
      longLayout (matrixAddress (fullFinMatrix F f k) a) :=
  lowerProgram_encoded F f k hLower hUnit Pref G S hG hS a

end Lower
end
end CodedSorting.Construction.PartialSwapMachine

#print axioms CodedSorting.Construction.PartialSwapMachine.scans
#print axioms CodedSorting.Construction.PartialSwapMachine.surround
#print axioms CodedSorting.Construction.PartialSwapMachine.lower
end PartialSwapMachine

section RankPartialSwapMachine
/-!
# Actual-machine assembly for the rank-many partial swaps

This is the actual instruction compiler for one arbitrary-rank partial swap.
Its endpoint proves the shared-specialization address action, disk frame,
program-counter safety, I/O charge and instruction-list length. This module
is a component of the one-level network, not the complete network assembly.

The call plan contains ordinary lower-factor scans around each supplied
actual machine child. Its generated code retains every child instruction.
No assumption that a recursive child is itself a list of scans is needed.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.RankPartialSwapMachine

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs ScanProgram
open CommonLeafProgram (Machine)
open MatrixFactorization ScanProgramLift CommonAddressLayout
open PartialSwapScan PartialSwapExecution RankPartialSwapExecution ProjectionRankDecomposition
open PartialSwapMachine
open scoped BigOperators

noncomputable section

section Plan
variable {J : Type*} {V source buffer limit : ℕ} {q : Configuration}

/-- Retarget a specification while preserving the code and charge literally. -/
def relabel {π ρ : Equiv.Perm (Fin V)}
    (p : CommonFinitePermutation.Program q V source buffer limit π) (h : π = ρ) :
    CommonFinitePermutation.Program q V source buffer limit ρ where
  instructions := p.instructions
  charge := p.charge
  correct := by simpa only [← h] using p.correct
  frame := p.frame
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

/-- Forward address action; machine child specifications are output-to-input. -/
def callForward (child : J → Equiv.Perm (Fin V)) (b : CallBlock J V) :
    Equiv.Perm (Fin V) :=
  (destination b.before).trans ((child b.childIndex).symm.trans (destination b.after))

def callProgram (reader : Fin q.inventory.readers)
    (a : ScanAllocation q V source buffer limit)
    {child : J → Equiv.Perm (Fin V)}
    (children : (i : J) → CommonFinitePermutation.Program q V source buffer limit (child i))
    (b : CallBlock J V) :
    CommonFinitePermutation.Program q V source buffer limit (callForward child b).symm :=
  relabel (surround q reader b.before b.after a (children b.childIndex)) (by
    apply Equiv.ext
    intro x
    rfl)

def planForward (child : J → Equiv.Perm (Fin V)) : List (CallBlock J V) → Equiv.Perm (Fin V)
  | [] => Equiv.refl _
  | b :: bs => (callForward child b).trans (planForward child bs)

def compilePlan (reader : Fin q.inventory.readers)
    (a : ScanAllocation q V source buffer limit)
    {child : J → Equiv.Perm (Fin V)}
    (children : (i : J) → CommonFinitePermutation.Program q V source buffer limit (child i)) :
    (bs : List (CallBlock J V)) →
      CommonFinitePermutation.Program q V source buffer limit (planForward child bs).symm
  | [] => CommonFinitePermutation.Program.identity q V source buffer limit
  | b :: bs => relabel ((callProgram reader a children b).append
      (compilePlan reader a children bs)) (by
        apply Equiv.ext
        intro x
        rfl)

theorem compilePlan_instructions (reader : Fin q.inventory.readers)
    (a : ScanAllocation q V source buffer limit)
    {child : J → Equiv.Perm (Fin V)}
    (children : (i : J) → CommonFinitePermutation.Program q V source buffer limit (child i))
    (bs : List (CallBlock J V)) :
    (compilePlan reader a children bs).instructions =
      (bs.map (fun b => CommonRankEdgeScan.code q reader b.before source buffer ++
        (children b.childIndex).instructions ++
          CommonRankEdgeScan.code q reader b.after source buffer)).flatten := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change (callProgram reader a children b).instructions ++
        (compilePlan reader a children bs).instructions = _
      rw [ih]
      rfl

theorem compilePlan_charge (reader : Fin q.inventory.readers)
    (a : ScanAllocation q V source buffer limit)
    {child : J → Equiv.Perm (Fin V)}
    (children : (i : J) → CommonFinitePermutation.Program q V source buffer limit (child i))
    (bs : List (CallBlock J V)) :
    (compilePlan reader a children bs).charge =
      (bs.map (fun b => 3 * (totalConstant b.before + totalConstant b.after + 16) *
        count q V + (children b.childIndex).charge)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change (surround q reader b.before b.after a (children b.childIndex)).charge +
        (compilePlan reader a children bs).charge = _
      rw [surround_charge, ih]
      rfl

end Plan

section Encoding
variable {J K : Type*} {m Q Pref G S : ℕ} [NeZero Q]
local instance doubledDecEqEncoding : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq

/-- Exact same coordinate string, viewed as a numeric permutation. -/
def selected (s t : Fin m) : Equiv.Perm (Fin (Volume (Fin m) Pref Q G S)) :=
  longLayout.symm.trans ((SingleCoordinate.shortExchange s t).trans longLayout)

omit [NeZero Q] in
theorem selected_symm_apply (s t : Fin m) (a : Addr (Fin m) Pref Q G S) :
    (selected (Pref := Pref) (Q := Q) (G := G) (S := S) s t).symm (longLayout a) =
      longLayout (SingleCoordinate.shortExchange s t a) := by
  change longLayout ((SingleCoordinate.shortExchange s t).symm
    (longLayout.symm (longLayout a))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem planForward_encoded
    (child : K → Equiv.Perm (Fin (Volume (Fin m) Pref Q G S)))
    (bs : J → CallBlock K (Volume (Fin m) Pref Q G S))
    (M : J → Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) (Fin Q))
    (hbs : ∀ i (a : Addr (Fin m) Pref Q G S),
      callForward child (bs i) (longLayout a) = longLayout (matrixAddress (M i) a))
    (l : List J) (a : Addr (Fin m) Pref Q G S) :
    planForward child (l.map bs) (longLayout a) =
      longLayout (matrixAddress ((l.reverse.map M).prod) a) := by
  induction l generalizing a with
  | nil =>
      simp only [List.map_nil,planForward,Equiv.refl_apply,List.reverse_nil,List.prod_nil,
        matrixAddress_one]
  | cons i l ih =>
      rw [List.map_cons,planForward,Equiv.trans_apply,hbs,ih]
      simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
        List.prod_append,List.prod_cons,List.prod_nil,mul_one,matrixAddress_mul]

end Encoding

section Rank
variable {m : ℕ}
local instance doubledDecEqRank : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq
variable {P : Matrix (Fin m) (Fin m) ℚ} (d : RankDecomposition P)
variable (F : SpecializedFamily (family d)) (f : ℕ)
local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩
variable (Pref G S : ℕ) (hG : 0 < G) (hS : 0 < S)

abbrev childPermutation (i : Fin P.rank) :
    Equiv.Perm (Fin (Volume (Fin m) Pref (F.prime^f) G S)) :=
  selected (supports d i).first (supports d i).last

/-- The full forward action of the visible rank-many machine call plan. -/
def forward : Equiv.Perm (Fin (Volume (Fin m) Pref (F.prime^f) G S)) :=
  planForward (childPermutation d F f Pref G S) (plan d F f Pref G S hG hS)

/-- Actual machine children, one for every orthogonal rank-one factor. -/
def program (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (a : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit)
    (children : (i : Fin P.rank) → CommonFinitePermutation.Program q
      (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit
      (childPermutation d F f Pref G S i)) :
    CommonFinitePermutation.Program q (Volume (Fin m) Pref (F.prime^f) G S)
      source buffer limit (forward d F f Pref G S hG hS).symm :=
  compilePlan reader a children (plan d F f Pref G S hG hS)

/-- The actual instruction list contains the supplied child code exactly in
its indexed call slot, between the concrete inverse and forward factor scans. -/
theorem program_instructions (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (a : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit)
    (children : (i : Fin P.rank) → CommonFinitePermutation.Program q
      (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit
      (childPermutation d F f Pref G S i)) :
    (program d F f Pref G S hG hS q reader a children).instructions =
      ((plan d F f Pref G S hG hS).map (fun b =>
        CommonRankEdgeScan.code q reader b.before source buffer ++
          (children b.childIndex).instructions ++
            CommonRankEdgeScan.code q reader b.after source buffer)).flatten :=
  compilePlan_instructions reader a children _

theorem componentForward_encoded (i : Fin P.rank)
    (a : Addr (Fin m) Pref (F.prime^f) G S) :
    callForward (childPermutation d F f Pref G S)
      (componentPlan d F f Pref G S hG hS i) (longLayout a) =
      longLayout (matrixAddress (fullFinMatrix F f (some (i,(false,false)))) a) := by
  let h := lineFamily_properties (d.vectors i) (supports d i).first (supports d i).last
    (supports d i).first_nonzero (supports d i).last_nonzero
    (supports d i).before_zero (supports d i).after_zero
  change destination (lowerProgram (componentFamily d F i) f (false,true)
      h.1 h.2.1 Pref G S hG hS)
    ((childPermutation d F f Pref G S i).symm
      (destination (lowerProgram (componentFamily d F i) f (true,true)
        h.2.2.1 h.2.2.2.1 Pref G S hG hS) (longLayout a))) = _
  rw [lowerProgram_encoded,selected_symm_apply,lowerProgram_encoded]
  change _ = longLayout (matrixAddress
    (fullFinMatrix (componentFamily d F i) f (false,false)) a)
  rw [fullFinMatrix_factorization (componentFamily d F i) f (false,false)
      (false,true) (true,false) (true,true) h.2.2.2.2,
    matrixAddress_mul,matrixAddress_mul,
    fullFinMatrix_swap (componentFamily d F i) f (true,false)
      (supports d i).first (supports d i).last rfl,
    matrixAddress_swap]

/-- The actual program's forward permutation is the jointly specialized
full D_P, including all spectator coordinates. -/
theorem forward_encoded (a : Addr (Fin m) Pref (F.prime^f) G S) :
    forward d F f Pref G S hG hS (longLayout a) =
      longLayout (matrixAddress (fullFinMatrix F f none) a) := by
  rw [forward,plan,planForward_encoded
    (childPermutation d F f Pref G S) (componentPlan d F f Pref G S hG hS)
    (fun i => fullFinMatrix F f (some (i,(false,false))))
    (fun i => componentForward_encoded d F f Pref G S hG hS i),
    finite_reverse_product]

/-- The single shared specialization preserves the exact involution
identity of the target projection, for every power of its good prime. -/
theorem target_square :
    fullFinMatrix F f none * fullFinMatrix F f none = 1 :=
  finite_target_square d F f

theorem forward_involutive : Function.Involutive (forward d F f Pref G S hG hS) := by
  intro x
  obtain ⟨a, rfl⟩ := longLayout.surjective x
  rw [forward_encoded, forward_encoded, ← matrixAddress_mul,
    target_square, matrixAddress_one]

/-- Machine reads use output-to-input maps; the actual partial swap is its
own inverse, so its matrix formula also describes those reads directly. -/
theorem forward_symm :
    (forward d F f Pref G S hG hS).symm = forward d F f Pref G S hG hS := by
  apply Equiv.ext
  intro x
  apply (forward d F f Pref G S hG hS).injective
  rw [Equiv.apply_symm_apply, forward_involutive]

theorem program_correct_encoded (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (alloc : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit)
    (children : (i : Fin P.rank) → CommonFinitePermutation.Program q
      (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit
      (childPermutation d F f Pref G S i))
    (s : Machine q) (a : Addr (Fin m) Pref (F.prime^f) G S) :
    readBit q (executeRaw q (program d F f Pref G S hG hS q reader alloc children).instructions
      s).1.disk source (longLayout a).val =
        readBit q s.disk source (longLayout (matrixAddress (fullFinMatrix F f none) a)).val := by
  rw [(program d F f Pref G S hG hS q reader alloc children).correct,
    forward_symm, forward_encoded]

theorem component_scan_constant_le (i : Fin P.rank) :
    totalConstant (componentPlan d F f Pref G S hG hS i).before +
      totalConstant (componentPlan d F f Pref G S hG hS i).after ≤
        componentConstant d i := by
  let h := lineFamily_properties (d.vectors i) (supports d i).first (supports d i).last
    (supports d i).first_nonzero (supports d i).last_nonzero
    (supports d i).before_zero (supports d i).after_zero
  exact Nat.add_le_add
    (lowerProgram_constant (componentFamily d F i) f (true,true)
      h.2.2.1 h.2.2.2.1 Pref G S hG hS)
    (lowerProgram_constant (componentFamily d F i) f (false,true)
      h.1 h.2.1 Pref G S hG hS)

/-- The common machine pays for both padded scan segments and for exactly
one copy of each actual recursive child's charge. -/
theorem program_charge_le (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (a : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit)
    (children : (i : Fin P.rank) → CommonFinitePermutation.Program q
      (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit
      (childPermutation d F f Pref G S i)) :
    (program d F f Pref G S hG hS q reader a children).charge ≤
      3 * (fixedConstant d + 16 * P.rank) * count q (Volume (Fin m) Pref (F.prime^f) G S) +
        ∑ i, (children i).charge := by
  rw [program,compilePlan_charge]
  simp only [plan,List.map_map,Function.comp_def]
  rw [← Fin.sum_univ_def]
  calc
    _ ≤ ∑ i : Fin P.rank,
        (3 * (componentConstant d i + 16) * count q (Volume (Fin m) Pref (F.prime^f) G S) +
          (children i).charge) := by
      apply Finset.sum_le_sum
      intro i _
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_right (component_scan_constant_le d F f Pref G S hG hS i) 16
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,
        fixedConstant,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
      ring

/-- The visible instruction cost has the same bound as the declared charge;
the sum counts each indexed child's charge once. -/
theorem program_cost_le (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (a : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit)
    (children : (i : Fin P.rank) → CommonFinitePermutation.Program q
      (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit
      (childPermutation d F f Pref G S i)) :
    cost q (program d F f Pref G S hG hS q reader a children).instructions ≤
      3 * (fixedConstant d + 16 * P.rank) * count q (Volume (Fin m) Pref (F.prime^f) G S) +
        ∑ i, (children i).charge :=
  (program d F f Pref G S hG hS q reader a children).cost_le.trans
    (program_charge_le d F f Pref G S hG hS q reader a children)

/-- The same budget also bounds the literal generated instruction-list
length, so the common program-counter execution theorem applies. -/
theorem program_length_le (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (a : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit)
    (children : (i : Fin P.rank) → CommonFinitePermutation.Program q
      (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit
      (childPermutation d F f Pref G S i)) :
    (program d F f Pref G S hG hS q reader a children).instructions.length ≤
      3 * (fixedConstant d + 16 * P.rank) * count q (Volume (Fin m) Pref (F.prime^f) G S) +
        ∑ i, (children i).charge :=
  (program d F f Pref G S hG hS q reader a children).length_le.trans
    (program_charge_le d F f Pref G S hG hS q reader a children)

/-- A machine-level execution endpoint for the actual rank program, with its
own frame, halt, code length and RAM bound inherited from Program. -/
theorem program_complete (q : Configuration) {source buffer limit : ℕ}
    (reader : Fin q.inventory.readers)
    (a : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit)
    (children : (i : Fin P.rank) → CommonFinitePermutation.Program q
      (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit
      (childPermutation d F f Pref G S i))
    (s : Machine q)
    (hsize : 3 * (fixedConstant d + 16 * P.rank) *
      count q (Volume (Fin m) Pref (F.prime^f) G S) + ∑ i, (children i).charge ≤ q.N^q.exponent)
    (hpc : pc q s.ram = 0) :
    let p := program d F f Pref G S hG hS q reader a children
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ y : Fin (Volume (Fin m) Pref (F.prime^f) G S),
      readBit q result.1.disk source y.val =
        readBit q s.disk source ((forward d F f Pref G S hG hS).symm y).val) ∧
    (∀ x : Fin (q.N^q.exponent),
      (x.val < source ∨ source + count q (Volume (Fin m) Pref (F.prime^f) G S) ≤ x.val) →
      (x.val < buffer ∨ limit ≤ x.val) → result.1.disk x = s.disk x) ∧
    policy q p.instructions result.1.ram = none ∧
    result.2 ≤ 3 * (fixedConstant d + 16 * P.rank) *
      count q (Volume (Fin m) Pref (F.prime^f) G S) + ∑ i, (children i).charge ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  have hc := program_charge_le d F f Pref G S hG hS q reader a children
  obtain ⟨hcorrect,hframe,hhalt,hcost,hram⟩ := CommonFinitePermutation.complete q
    (program d F f Pref G S hG hS q reader a children) s (hc.trans hsize) hpc
  exact ⟨hcorrect,hframe,hhalt,hcost.trans hc,hram⟩

end Rank
end
end CodedSorting.Construction.RankPartialSwapMachine

#print axioms CodedSorting.Construction.RankPartialSwapMachine.program
#print axioms CodedSorting.Construction.RankPartialSwapMachine.program_instructions
#print axioms CodedSorting.Construction.RankPartialSwapMachine.forward_encoded
#print axioms CodedSorting.Construction.RankPartialSwapMachine.forward_symm
#print axioms CodedSorting.Construction.RankPartialSwapMachine.program_correct_encoded
#print axioms CodedSorting.Construction.RankPartialSwapMachine.program_charge_le
#print axioms CodedSorting.Construction.RankPartialSwapMachine.program_cost_le
#print axioms CodedSorting.Construction.RankPartialSwapMachine.program_length_le
#print axioms CodedSorting.Construction.RankPartialSwapMachine.program_complete
end RankPartialSwapMachine
