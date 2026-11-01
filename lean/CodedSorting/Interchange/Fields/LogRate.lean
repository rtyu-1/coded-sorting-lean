import CodedSorting.Interchange.Recursion.Resources

section Calls
/-! Numerical width decomposition for the actual Construction specialization.
The generic radix schedule is instantiated with Construction's dimension and stream
count, and every field count uses the single Construction specialization prime.
Zero-width remainders and zero prefixes are retained. This module constructs
no replacement exchange operation: actual programs are assembled separately. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CodedSorting.Construction.ArbitraryCalls

open ArbitrarySchedule ArbitraryShapes ExchangeSpecialization

noncomputable section

attribute [local irreducible] ExchangeSpecialization.uniform TensorFrameNetwork.program

structure Call where
  baseWidth : Nat
  depth : Nat
  deriving DecidableEq

def Call.width (c : Call) : Nat := c.baseWidth * ambientDimension^c.depth

theorem Call.width_pos (c : Call) (h : 0 < c.baseWidth) : 0 < c.width :=
  Nat.mul_pos h (pow_pos (by rw [ambientDimension_eq]; decide) _)

theorem Call.width_zero (k : Nat) : (Call.mk 0 k).width = 0 := by
  simp only [Call.width, Nat.zero_mul]

/-- Each emitted scale is one recursive call, followed by one remainder. -/
def calls (base k e : Nat) : List Call :=
  (scales ambientDimension k (e/base)).map (fun j => ⟨base,j⟩) ++ [⟨e%base,0⟩]

def baseCalls (base e : Nat) : List Call :=
  List.replicate (e/base) ⟨base,0⟩ ++ [⟨e%base,0⟩]

/-- The ordered product of all chunk cardinalities. -/
def fieldCount : List Call → Nat
  | [] => 1
  | c::cs => radix^c.width * fieldCount cs

theorem fieldCount_pos (cs : List Call) : 0 < fieldCount cs := by
  induction cs with
  | nil => exact Nat.zero_lt_one
  | cons c cs ih => exact Nat.mul_pos (pow_pos radix_prime.pos _) ih

theorem fieldCount_width (cs : List Call) :
    fieldCount cs = radix ^ (cs.map Call.width).sum := by
  induction cs with
  | nil => simp only [fieldCount, List.map_nil, List.sum_nil, pow_zero]
  | cons c cs ih =>
    simp only [fieldCount, List.map_cons, List.sum_cons, pow_add, ih]

theorem calls_width (base k e : Nat) : ((calls base k e).map Call.width).sum = e := by
  simpa only [calls, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Call.width, pow_zero, Nat.mul_one, Function.comp_apply] using
      widths_sum ambientDimension base k e

theorem baseCalls_width (base e : Nat) :
    ((baseCalls base e).map Call.width).sum = e := by
  simp only [baseCalls, List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Call.width, pow_zero, Nat.mul_one, smul_eq_mul, Nat.add_zero]
  simpa only [Nat.mul_comm] using Nat.div_add_mod e base

theorem calls_fieldCount (base k e : Nat) : fieldCount (calls base k e) = radix^e := by
  rw [fieldCount_width, calls_width]

theorem base_fields (base e : Nat) : fieldCount (baseCalls base e) = radix^e := by
  rw [fieldCount_width, baseCalls_width]

theorem baseCalls_length (base e : Nat) : (baseCalls base e).length = e/base+1 := by
  simp only [baseCalls, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]

theorem calls_length (base k e : Nat) :
    (calls base k e).length = (scales ambientDimension k (e/base)).length+1 := by
  simp only [calls, List.length_append, List.length_map, List.length_cons, List.length_nil]

theorem calls_depth_mem (base k e : Nat) (c : Call) (hc : c ∈ calls base k e) :
    c.depth ≤ k := by
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
    exact scales_depth _ _ _ _ hj
  · have he : c = ⟨e%base,0⟩ := by simpa using h
    rw [he]
    exact Nat.zero_le k

theorem calls_depth (base k e : Nat) (i : Fin (calls base k e).length) :
    ((calls base k e).get i).depth ≤ k :=
  calls_depth_mem base k e _ (List.get_mem _ _)

theorem calls_base (base k e : Nat) (hb : 0 < base) :
    ∀ c ∈ calls base k e, c.baseWidth ≤ base := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
    exact Nat.le_refl base
  · have he : c = ⟨e%base,0⟩ := by simpa using h
    rw [he]
    exact (Nat.mod_lt e hb).le

theorem baseCalls_base (base e : Nat) (hb : 0 < base) :
    ∀ c ∈ baseCalls base e, c.baseWidth ≤ base := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · rw [(List.mem_replicate.mp h).2]
  · have he : c = ⟨e%base,0⟩ := by simpa using h
    rw [he]
    exact (Nat.mod_lt e hb).le

theorem baseCalls_depth_mem (base e : Nat) (c : Call) (hc : c ∈ baseCalls base e) :
    c.depth = 0 := by
  rcases List.mem_append.mp hc with h | h
  · rw [(List.mem_replicate.mp h).2]
  · have he : c = ⟨e%base,0⟩ := by simpa using h
    rw [he]

theorem baseCalls_depth (base e : Nat) (i : Fin (baseCalls base e).length) :
    ((baseCalls base e).get i).depth = 0 :=
  baseCalls_depth_mem base e _ (List.get_mem _ _)

theorem baseCalls_fit (P base e : Nat) :
    ∀ c ∈ baseCalls base e, streamCount^c.depth ∣ P := by
  intro c hc
  rw [baseCalls_depth_mem base e c hc, pow_zero]
  exact one_dvd P

def paddedRows (P k : Nat) : Nat := paddedCount P (streamCount^(k+1))

theorem original_rows_le_padded (P k : Nat) : P ≤ paddedRows P k :=
  paddedCount_ge _ _ (pow_pos (by rw [streamCount_eq]; decide) _)

theorem paddedRows_multiple (P k : Nat) : streamCount^(k+1) ∣ paddedRows P k :=
  paddedCount_multiple _ _

theorem automatic_calls_fit (P base k e : Nat) (i : Fin (calls base k e).length) :
    streamCount^((calls base k e).get i).depth ∣ paddedRows P k :=
  dvd_trans (pow_dvd_pow streamCount ((calls_depth base k e i).trans (Nat.le_succ k)))
    (paddedRows_multiple P k)

theorem calls_fit (P base k e : Nat) :
    ∀ c ∈ calls base k e, streamCount^c.depth ∣ paddedRows P k := by
  intro c hc
  exact dvd_trans (pow_dvd_pow streamCount
    ((calls_depth_mem base k e c hc).trans (Nat.le_succ k))) (paddedRows_multiple P k)

theorem paddedRows_zero (k : Nat) : paddedRows 0 k = 0 := by
  have hW : 0 < streamCount^(k+1) := pow_pos (by rw [streamCount_eq]; decide) _
  simp only [paddedRows, paddedCount, Nat.zero_add,
    Nat.div_eq_of_lt (Nat.sub_lt hW Nat.zero_lt_one), Nat.mul_zero]

def highRows (P ρ : Nat) : Nat := P*((radix^ρ)*(radix^ρ))

theorem highRows_zero (ρ : Nat) : highRows 0 ρ = 0 := Nat.zero_mul _

theorem highRows_enough (P k : Nat) (hP : 0 < P) :
    streamCount^(k+1) ≤ highRows P (borrowedWidth radix streamCount k) := by
  have h := borrowed_rows_enough radix streamCount k radix_prime.one_lt
  have hpow : radix^(2*borrowedWidth radix streamCount k) =
      radix^borrowedWidth radix streamCount k * radix^borrowedWidth radix streamCount k := by
    rw [two_mul, pow_add]
  rw [hpow] at h
  exact h.trans (Nat.le_mul_of_pos_left _ hP)

/-- A nonempty borrowed prefix gains less than a factor of two. -/
theorem generated_padding_bound (P k : Nat) (hP : 0 < P) :
    paddedRows (highRows P (borrowedWidth radix streamCount k)) k <
      2*highRows P (borrowedWidth radix streamCount k) :=
  paddedCount_lt_twice _ _ (pow_pos (by rw [streamCount_eq]; decide) _)
    (highRows_enough P k hP)

/-- The non-strict bound includes an empty original prefix. -/
theorem generated_padding_le_twice (P k : Nat) :
    paddedRows (highRows P (borrowedWidth radix streamCount k)) k ≤
      2*highRows P (borrowedWidth radix streamCount k) := by
  by_cases hP : P = 0
  · subst P
    rw [highRows_zero, paddedRows_zero, Nat.mul_zero]
  · exact (generated_padding_bound P k (Nat.pos_of_ne_zero hP)).le

/-- Borrowed high digits together with all emitted low chunks recover the
original field cardinality exactly. -/
theorem borrowed_fields (base e k ρ : Nat) (hρ : ρ ≤ e) :
    radix^ρ * fieldCount (calls base k (e-ρ)) = radix^e := by
  rw [calls_fieldCount, ← pow_add, Nat.add_sub_of_le hρ]

end
end CodedSorting.Construction.ArbitraryCalls
end Calls

section Cost
/-! Arithmetic sum of the new Construction recurrence over the emitted width chunks.
The actual instruction composition supplies its charge inequality separately;
no implementation or correctness assumption occurs in this numerical module. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.ArbitraryCost

open ArbitrarySchedule ExchangeSpecialization ArbitraryCalls
open ExchangeInterface (costBound)

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs MachineNetworkActualEdges.localCoefficient

local notation "coefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)

/-- One scan envelope in the existing physical block width. -/
def scan (B V : Nat) : ℝ := 1+(V : ℝ)/B

theorem scan_nonneg (B V : Nat) : 0 ≤ scan B V := by unfold scan; positivity

theorem nat_scan_le (B V : Nat) : ((V/B+1 : Nat) : ℝ) ≤ scan B V := by
  have hd : ((V/B : Nat) : ℝ) ≤ (V : ℝ)/B := Nat.cast_div_le
  simp only [Nat.cast_add, Nat.cast_one, scan]
  linarith

theorem scan_double (B V V' : Nat) (hv : V' ≤ 2*V) : scan B V' ≤ 2*scan B V := by
  have hr : (V' : ℝ) ≤ 2*V := by exact_mod_cast hv
  have hd := div_le_div_of_nonneg_right hr (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  unfold scan
  rw [mul_div_assoc] at hd
  linarith

def tau : ℝ := 1-(Construction.epsilon : ℝ)
def ratio : ℝ := (ambientDimension : ℝ)^tau

theorem tau_pos : 0 < tau := by
  have he : (Construction.epsilon : ℝ) < 1 := by exact_mod_cast Construction.epsilon_lt_one
  unfold tau
  linarith

theorem ratio_gt_one : 1 < ratio := by
  apply Real.one_lt_rpow
  · norm_num [ambientDimension_eq]
  · exact tau_pos

theorem ratio_power (k : Nat) :
    (ambientDimension : ℝ)^((k : ℝ)*(1-(Construction.epsilon : ℝ))) = ratio^k := by
  rw [mul_comm, Real.rpow_mul_natCast (by positivity)]
  rfl

def weight (cs : List Call) : ℝ := (cs.map fun c => ratio^c.depth).sum

def totalBound (cutoff b : Nat) (cs : List Call) (V : Nat) : Nat :=
  (cs.map fun c => costBound coefficient b cutoff c.depth V).sum

@[simp] theorem totalBound_nil (cutoff b V : Nat) : totalBound cutoff b [] V = 0 := rfl

@[simp] theorem totalBound_cons (cutoff b V : Nat) (c : Call) (cs : List Call) :
    totalBound cutoff b (c::cs) V =
      costBound coefficient b cutoff c.depth V + totalBound cutoff b cs V := rfl

/-- Every chunk is charged through the actual Construction scalar recurrence. -/
theorem totalBound_improved (cutoff b V : Nat) (hb : 0 < b)
    (hcut : streamCount*b ≤ cutoff) (cs : List Call) :
    (totalBound cutoff b cs V : ℝ) ≤
      RecursiveCostRate.rateConstant * scan b V * weight cs := by
  induction cs with
  | nil => simp [totalBound, weight]
  | cons c cs ih =>
      have hcost := RecursiveCostRate.costBound_le_rate b cutoff c.depth V hb hcut
      rw [ratio_power] at hcost
      have hp : (1 : ℝ) ≤ ratio^c.depth := one_le_pow₀ ratio_gt_one.le
      have hstep : (costBound coefficient b cutoff c.depth V : ℝ) ≤
          RecursiveCostRate.rateConstant * scan b V * ratio^c.depth := by
        have hh := mul_le_mul_of_nonneg_left
          (show 1+(V : ℝ)/b*ratio^c.depth ≤ scan b V*ratio^c.depth by
            unfold scan
            nlinarith) RecursiveCostRate.rateConstant_nonneg
        simpa only [mul_assoc] using hcost.trans hh
      simp only [totalBound, List.map_cons, List.sum_cons, Nat.cast_add, weight] at ih ⊢
      nlinarith

theorem geometric_one (k : Nat) : 1 ≤ geometric ratio k :=
  (show (1 : ℝ) ≤ (k+1 : Nat) by exact_mod_cast (by omega : 1 ≤ k+1)).trans
    (depth_le_geometric ratio ratio_gt_one.le k)

theorem calls_weight (base k e : Nat) :
    weight (calls base k e) = scaleWeight ratio (scales ambientDimension k (e/base))+1 := by
  simp only [weight, calls, List.map_append, List.sum_append, List.map_map,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Function.comp_apply, pow_zero, add_zero, scaleWeight]
  rfl

theorem calls_weight_bound (base k e : Nat) (he : e/base < ambientDimension^(k+1)) :
    weight (calls base k e) ≤ ambientDimension * geometric ratio k := by
  rw [calls_weight]
  have hm : 1 < ambientDimension := by rw [ambientDimension_eq]; omega
  have hs := scaleWeight_bound ambientDimension k (e/base) hm he ratio
    (by have := ratio_gt_one; linarith)
  have hg := geometric_one k
  have hcast : ((ambientDimension-1 : Nat) : ℝ) = ambientDimension-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast] at hs
  nlinarith

theorem calls_totalBound (cutoff b V base k e : Nat) (hb : 0 < b)
    (hcut : streamCount*b ≤ cutoff) (he : e/base < ambientDimension^(k+1)) :
    (totalBound cutoff b (calls base k e) V : ℝ) ≤
      RecursiveCostRate.rateConstant * scan b V * ambientDimension * geometric ratio k := by
  have hC : 0 ≤ RecursiveCostRate.rateConstant * scan b V :=
    mul_nonneg RecursiveCostRate.rateConstant_nonneg (scan_nonneg b V)
  have hs := mul_le_mul_of_nonneg_left (calls_weight_bound base k e he) hC
  exact (totalBound_improved cutoff b V hb hcut _).trans
    (by simpa only [mul_assoc] using hs)

def borrowing : ℝ := borrowConstant radix streamCount

theorem borrowing_nonneg : 0 ≤ borrowing := Nat.cast_nonneg _

theorem rho_bound (k : Nat) :
    (borrowedWidth radix streamCount k : ℝ) ≤ borrowing * geometric ratio k := by
  have h := mul_le_mul_of_nonneg_left (depth_le_geometric ratio ratio_gt_one.le k)
    borrowing_nonneg
  simpa [borrowedWidth, borrowing] using h

theorem base_totalBound (cutoff b V base e : Nat) :
    totalBound cutoff b (baseCalls base e) V = (e/base+1)*(20*(V/b+1)) := by
  simp [totalBound, baseCalls, costBound, List.sum_replicate, smul_eq_mul]
  ring

theorem fallback_bound (cutoff b V base e k : Nat)
    (he : e ≤ borrowedWidth radix streamCount k) :
    (totalBound cutoff b (baseCalls base e) V : ℝ) ≤
      (20*(borrowing+1))*scan b V*geometric ratio k := by
  have hdiv : e/base ≤ borrowedWidth radix streamCount k := (Nat.div_le_self _ _).trans he
  have hr : ((e/base : Nat) : ℝ) ≤ borrowedWidth radix streamCount k := by exact_mod_cast hdiv
  have hρ := rho_bound k
  have hg := geometric_one k
  have hn : ((e/base+1 : Nat) : ℝ) ≤ (borrowing+1)*geometric ratio k := by
    push_cast
    nlinarith
  have hm := mul_le_mul hn (nat_scan_le b V)
    (by positivity : (0 : ℝ) ≤ (V/b+1 : Nat))
    (by have := borrowing_nonneg; have := geometric_nonneg ratio (by have := ratio_gt_one; linarith) k
        positivity)
  rw [base_totalBound]
  push_cast at hm ⊢
  nlinarith only [hm]

end
end CodedSorting.Construction.ArbitraryCost
end Cost

section CostRate
/-! Uniform arithmetic envelope for arbitrary-width actual Construction chunk code.
Padding and borrowing are charged by explicit numerical coefficients;
the execution module must supply its actual instruction-cost inequality.
No execution or correctness assumption appears in these arithmetic results.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.ArbitraryCostRate
open ArbitrarySchedule BinaryPadding
open ExchangeSpecialization ArbitraryCalls ArbitraryCost
noncomputable section

/-- The actual Construction row rounding enlarges a borrowed file by less than two. -/
theorem padded_volume (P k L G S : Nat) (hP : 0 < P) :
    Volume (paddedRows
      (P*((radix^(borrowedWidth radix streamCount k))*(radix^(borrowedWidth radix streamCount k)))) k)
      L G S ≤ 2*Volume P (radix^(borrowedWidth radix streamCount k)*L) G S := by
  have hp := (ArbitraryCalls.generated_padding_bound P k hP).le
  change paddedRows
    (P*((radix^(borrowedWidth radix streamCount k))*(radix^(borrowedWidth radix streamCount k)))) k ≤
    2*(P*((radix^(borrowedWidth radix streamCount k))*(radix^(borrowedWidth radix streamCount k)))) at hp
  have hm := Nat.mul_le_mul_right ((L*G)*(L*S)) hp
  unfold Volume
  nlinarith only [hm]


def overheadBound (cutoff b : ℕ) (cs : List ArbitraryCalls.Call)
    (V V' ρ A D F : ℕ) : ℕ :=
  ArbitraryCost.totalBound cutoff b cs V'+A*(V/b+1)+D*(V'/b+1)+F*ρ*(V/b+1)

def borrowCoefficient (A D F : ℕ) : ℝ :=
  2*RecursiveCostRate.rateConstant*ambientDimension+A+2*D+F*borrowing

theorem borrowCoefficient_nonneg (A D F : ℕ) : 0≤borrowCoefficient A D F := by
  unfold borrowCoefficient
  have := RecursiveCostRate.rateConstant_nonneg
  have := borrowing_nonneg
  positivity

/-- Any fixed number of scans of the original and padded files, together
with linearly many borrowing scans, retains the geometric chunk bound. -/
theorem overhead_bound (cutoff b V V' base k e A D F : ℕ) (hb : 0<b)
    (hcut : streamCount*b≤cutoff) (he : e/base<ambientDimension^(k+1)) (hv : V'≤2*V) :
    (overheadBound cutoff b (ArbitraryCalls.calls base k e) V V'
        (borrowedWidth radix streamCount k) A D F : ℝ)≤
      borrowCoefficient A D F*scan b V*geometric ratio k := by
  have hs := scan_double b V V' hv
  have hg := geometric_one k
  have hg0 : 0≤geometric ratio k := by linarith
  have hsc := scan_nonneg b V
  have hchunk := ArbitraryCost.calls_totalBound cutoff b V' base k e hb hcut he
  change (ArbitraryCost.totalBound cutoff b (ArbitraryCalls.calls base k e) V' : ℝ)≤
    RecursiveCostRate.rateConstant*scan b V'*ambientDimension*geometric ratio k at hchunk
  have hchunk' : (ArbitraryCost.totalBound cutoff b (ArbitraryCalls.calls base k e) V' : ℝ)≤
      (2*RecursiveCostRate.rateConstant*ambientDimension)*scan b V*geometric ratio k := by
    have hm := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (mul_nonneg RecursiveCostRate.rateConstant_nonneg
        (Nat.cast_nonneg ambientDimension)) hg0)
    nlinarith only [hchunk,hm]
  have hvscan := nat_scan_le b V
  have hv'scan := (nat_scan_le b V').trans hs
  have hA : ((A*(V/b+1) : ℕ) : ℝ)≤A*scan b V*geometric ratio k := by
    have h1 := mul_le_mul_of_nonneg_left hvscan (Nat.cast_nonneg A : (0 : ℝ)≤A)
    have h2 := mul_le_mul_of_nonneg_left hg (mul_nonneg (Nat.cast_nonneg A) hsc)
    push_cast at h1 ⊢
    nlinarith only [h1,h2]
  have hD : ((D*(V'/b+1) : ℕ) : ℝ)≤(2*D)*scan b V*geometric ratio k := by
    have h1 := mul_le_mul_of_nonneg_left hv'scan (Nat.cast_nonneg D : (0 : ℝ)≤D)
    have h2 := mul_le_mul_of_nonneg_left hg
      (by positivity : (0 : ℝ)≤(2*D)*scan b V)
    push_cast at h1 ⊢
    nlinarith only [h1,h2]
  have hprod := mul_le_mul (rho_bound k) hvscan
    (by positivity : (0 : ℝ)≤(V/b+1 : ℕ)) (mul_nonneg borrowing_nonneg hg0)
  have hF : ((F*borrowedWidth radix streamCount k*(V/b+1) : ℕ) : ℝ)≤
      (F*borrowing)*scan b V*geometric ratio k := by
    have hm := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg F : (0 : ℝ)≤F)
    push_cast at hm ⊢
    nlinarith only [hm]
  unfold overheadBound borrowCoefficient
  push_cast at hA hD hF ⊢
  nlinarith only [hchunk',hA,hD,hF]

/-- The coefficients used by the actual wrapper: two borrowing programs,
and insertion/erasure with their charged reads, writes, and startup costs. -/
theorem assembled_overhead_le (q : CommonSortingNormalization.Configuration)
    (cutoff V V' ρ : ℕ) (cs : List ArbitraryCalls.Call) :
    ArbitraryCost.totalBound cutoff (CommonPermutationPairs.width q) cs V'+
      2*((3*ρ*(2*radix+6)+6)*CommonPermutationPairs.count q V)+
      (12*CommonPermutationPairs.count q V+27*CommonPermutationPairs.count q V')≤
    overheadBound cutoff (CommonPermutationPairs.width q) cs V V' ρ 24 27 (6*(2*radix+6)) := by
  have hV := CommonResidentBase.count_le_floor q V
  have hV' := CommonResidentBase.count_le_floor q V'
  change CommonPermutationPairs.count q V ≤ V / CommonPermutationPairs.width q + 1 at hV
  change CommonPermutationPairs.count q V' ≤ V' / CommonPermutationPairs.width q + 1 at hV'
  have h1 := Nat.mul_le_mul_left (24+6*(2*radix+6)*ρ) hV
  have h2 := Nat.mul_le_mul_left 27 hV'
  unfold overheadBound
  nlinarith only [h1,h2]

def borrowedBound (cutoff b : ℕ) (cs : List ArbitraryCalls.Call)
    (P ρ P' G S A D F : ℕ) : ℕ :=
  overheadBound cutoff b cs (Volume P (radix^ρ*fieldCount cs) G S)
    (Volume P' (fieldCount cs) G S) ρ A D F

theorem borrowed_bound (cutoff b P base k e G S A D F : ℕ) (hb : 0<b) (hP : 0<P)
    (hcut : streamCount*b≤cutoff) (he : e/base<ambientDimension^(k+1)) :
    let ρ := borrowedWidth radix streamCount k
    let cs := ArbitraryCalls.calls base k e
    let V := Volume P (radix^ρ*fieldCount cs) G S
    let P' := ArbitraryCalls.paddedRows (P*((radix^ρ)*(radix^ρ))) k
    (borrowedBound cutoff b cs P ρ P' G S A D F : ℝ)≤
      borrowCoefficient A D F*scan b V*geometric ratio k := by
  dsimp only [borrowedBound]
  apply overhead_bound cutoff b _ _ base k e A D F hb hcut he
  exact padded_volume P k _ G S hP

def bound (base cutoff b P e G S A D F : ℕ) : ℕ :=
  let k := depth ambientDimension base e
  let ρ := borrowedWidth radix streamCount k
  if ρ<e then
    let cs := ArbitraryCalls.calls base k (e-ρ)
    borrowedBound cutoff b cs P ρ
      (ArbitraryCalls.paddedRows (P*((radix^ρ)*(radix^ρ))) k) G S A D F
  else ArbitraryCost.totalBound cutoff b (ArbitraryCalls.baseCalls base e)
    (Volume P (radix^e) G S)

def coefficient (A D F : ℕ) : ℝ := borrowCoefficient A D F+20*(borrowing+1)

theorem coefficient_nonneg (A D F : ℕ) : 0≤coefficient A D F := by
  unfold coefficient
  have := borrowCoefficient_nonneg A D F
  have := borrowing_nonneg
  positivity

theorem bound_geometric (base cutoff b P e G S A D F : ℕ) (hb : 0<b) (hP : 0<P)
    (hcut : streamCount*b≤cutoff) :
    (bound base cutoff b P e G S A D F : ℝ)≤
      coefficient A D F*scan b (Volume P (radix^e) G S)*
        geometric ratio (depth ambientDimension base e) := by
  let k := depth ambientDimension base e
  let ρ := borrowedWidth radix streamCount k
  let V := Volume P (radix^e) G S
  have hg0 : 0≤geometric ratio k := by have := geometric_one k; linarith
  by_cases hborrow : ρ<e
  · let cs := ArbitraryCalls.calls base k (e-ρ)
    have hquot : (e-ρ)/base<ambientDimension^(k+1) :=
      (Nat.div_le_div_right (Nat.sub_le e ρ)).trans_lt
        (quotient_depth_bound ambientDimension base e (by rw [ambientDimension_eq]; omega))
    have hv : Volume P (radix^ρ*fieldCount cs) G S=V := by
      rw [fieldCount_width,ArbitraryCalls.calls_width]
      have hp : radix^ρ*radix^(e-ρ)=radix^e := by rw [← pow_add]; congr 1; omega
      rw [hp]
    have hh := borrowed_bound cutoff b P base k (e-ρ) G S A D F hb hP hcut hquot
    change (borrowedBound cutoff b cs P ρ
      (ArbitraryCalls.paddedRows (P*((radix^ρ)*(radix^ρ))) k) G S A D F : ℝ)≤
        borrowCoefficient A D F*scan b (Volume P (radix^ρ*fieldCount cs) G S)*
          geometric ratio k at hh
    rw [hv] at hh
    have hc : borrowCoefficient A D F≤coefficient A D F := by
      unfold coefficient
      have := borrowing_nonneg
      linarith
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (scan_nonneg b V)) hg0
    have hh' := hh.trans hm
    simpa only [bound,show borrowedWidth radix streamCount (depth ambientDimension base e)<e
      from hborrow,↓reduceIte] using hh'
  · have he : e≤ρ := by omega
    have hh := ArbitraryCost.fallback_bound cutoff b V base e k he
    have hc : 20*(borrowing+1)≤coefficient A D F := by
      unfold coefficient
      exact le_add_of_nonneg_left (borrowCoefficient_nonneg A D F)
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (scan_nonneg b V)) hg0
    have hh' := hh.trans hm
    simpa only [bound,show ¬borrowedWidth radix streamCount (depth ambientDimension base e)<e
      from hborrow,↓reduceIte] using hh'

def finalConstant (A D F : ℕ) : ℝ := coefficient A D F*(ratio/(ratio-1))

theorem finalConstant_nonneg (A D F : ℕ) : 0≤finalConstant A D F := by
  unfold finalConstant
  apply mul_nonneg (coefficient_nonneg A D F)
  have := ratio_gt_one
  apply div_nonneg <;> linarith

theorem bound_improved (base cutoff b P e G S A D F : ℕ) (hb : 0<b)
    (hbase : 0<base) (hP : 0<P) (hcut : streamCount*b≤cutoff) :
    (bound base cutoff b P e G S A D F : ℝ)≤
      finalConstant A D F*scan b (Volume P (radix^e) G S)*
        (1+((e : ℝ)/base)^(1-(Construction.epsilon : ℝ))) := by
  let V := Volume P (radix^e) G S
  let k := depth ambientDimension base e
  have hgeo := mul_le_mul_of_nonneg_left (geometric_power_bound ratio ratio_gt_one k)
    (mul_nonneg (coefficient_nonneg A D F) (scan_nonneg b V))
  have hfirst := (bound_geometric base cutoff b P e G S A D F hb hP hcut).trans hgeo
  have htau : 0≤1-(Construction.epsilon : ℝ) := by
    have h : (Construction.epsilon : ℝ)<1 := by exact_mod_cast Construction.epsilon_lt_one
    linarith
  have hwidth := depth_power_width_bound ambientDimension base e hbase
    (1-(Construction.epsilon : ℝ)) htau
  change ratio^k≤_ at hwidth
  have hsecond := mul_le_mul_of_nonneg_left hwidth
    (mul_nonneg (finalConstant_nonneg A D F) (scan_nonneg b V))
  unfold finalConstant at hfirst hsecond ⊢
  dsimp only [V,k] at hfirst hsecond
  nlinarith only [hfirst,hsecond]

end
end CodedSorting.Construction.ArbitraryCostRate
end CostRate

section LogRate
/-! Logarithmic width factors for the new Construction base choice.
These are arithmetic transformations of an established charge bound, not
assumptions that an arbitrary exchange or sorting program exists. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.ArbitraryLogRate

open CommonSortingNormalization ExchangeSpecialization RecursiveParameters
open PhysicalLeafParameters

noncomputable section

/-- Depends only on the Construction dimension and its one common prime. -/
def baseLogConstant : ℝ :=
  (8*(ambientDimension : ℝ)+2)*Real.log (radix : ℝ)

theorem baseLogConstant_nonneg : 0 ≤ baseLogConstant := by
  have hq : (1 : ℝ) ≤ radix := by exact_mod_cast radix_prime.one_lt.le
  unfold baseLogConstant
  exact mul_nonneg (by positivity) (Real.log_nonneg hq)

theorem quotient_lt_succ (H B : Nat) (hB : 0 < B) :
    (H : ℝ)/B < (H/B : Nat)+1 := by
  apply (div_lt_iff₀ (show (0 : ℝ) < B by exact_mod_cast hB)).2
  have hh : H < (H/B+1)*B := by
    have := Nat.mod_lt H hB
    have := Nat.div_add_mod H B
    nlinarith
  exact_mod_cast hh

theorem ratio_pos (q : Configuration) (hnormal : Normalized q) : 0 < ratio q := by
  have hp : 0 < radix^8 := pow_pos radix_prime.pos _
  have hn : max (radix^8) streamCount ≤ ratio q := by
    simpa only [Normalized, minimumRatio_eq] using hnormal
  exact hp.trans_le ((Nat.le_max_left _ _).trans hn)

/-- The floor and power-of-512 rounding alter only a fixed coefficient. -/
theorem log_bank_le_base (q : Configuration) (hnormal : Normalized q) :
    Real.log ((CommonExchangeLeaf.bankWords q : ℝ)/q.block) ≤
      baseLogConstant * chosenBase q := by
  have hb := chosenBase_pos q hnormal
  have hr := ratio_pos q hnormal
  have hH : 0 < CommonExchangeLeaf.bankWords q := Nat.pos_of_div_pos hr
  have hB := CommonLeafProgram.block_positive q
  have hq : (1 : ℝ) < radix := by exact_mod_cast radix_prime.one_lt
  have hp := Nat.lt_pow_succ_log_self radix_prime.one_lt (ratio q)
  have hpn : ratio q+1 ≤ radix^(Nat.log radix (ratio q)+1) := hp
  have hpr : ((ratio q : Nat) : ℝ)+1 ≤
      (radix : ℝ)^(Nat.log radix (ratio q)+1) := by exact_mod_cast hpn
  have hquot := (quotient_lt_succ (CommonExchangeLeaf.bankWords q) q.block hB).trans_le hpr
  have hlog := Real.log_le_log
    (show 0 < (CommonExchangeLeaf.bankWords q : ℝ)/q.block by positivity) hquot.le
  rw [Real.log_pow] at hlog
  have he := (chosenBase_log_sandwich q hnormal).2
  have he' : (Nat.log radix (ratio q) : ℝ)+1 ≤
      (8*(ambientDimension : ℝ)+2)*chosenBase q := by
    have heR : (Nat.log radix (ratio q) : ℝ) <
        8*(ambientDimension : ℝ)*chosenBase q := by exact_mod_cast he
    have hbR : (1 : ℝ) ≤ chosenBase q := by exact_mod_cast hb
    nlinarith
  have hm := mul_le_mul_of_nonneg_right he' (Real.log_nonneg hq.le)
  push_cast at hlog
  unfold baseLogConstant
  nlinarith only [hlog, hm]

/-- Positivity of the logarithmic denominator follows from normalization. -/
theorem normalized_log_one (H B : Nat) (hB : 0 < B)
    (hnormal : minimumRatio radix 1 streamCount ≤ H/B) :
    1 ≤ Real.log ((H : ℝ)/B) := by
  have hp : radix^8 ≤ H/B := by
    rw [minimumRatio_eq] at hnormal
    exact (Nat.le_max_left _ _).trans hnormal
  have hfour : 4 ≤ H/B := by
    have h2 := Nat.pow_le_pow_left radix_prime.one_lt 8
    norm_num at h2
    omega
  have hcast : (4 : ℝ) ≤ (H/B : Nat) := by exact_mod_cast hfour
  have hquot : (4 : ℝ) ≤ (H : ℝ)/B := hcast.trans Nat.cast_div_le
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hquot
  have hlogfour : Real.log 4 = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^(2 : Nat) by norm_num, Real.log_pow]
    norm_num
  rw [hlogfour] at hl
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh
  linarith

theorem normalized_memory (H B : Nat) (hB : 0 < B)
    (hnormal : minimumRatio radix 1 streamCount ≤ H/B) :
    2 ≤ H ∧ B ≤ H := by
  have hp : radix^8 ≤ H/B := by
    rw [minimumRatio_eq] at hnormal
    exact (Nat.le_max_left _ _).trans hnormal
  have htwo : 2 ≤ H/B := by
    have h2 := Nat.pow_le_pow_left radix_prime.one_lt 8
    norm_num at h2
    omega
  have hd := Nat.div_mul_le_self H B
  constructor <;> nlinarith

/-- A reusable algebraic conversion from base width to any positive log
scale already bounded by a fixed multiple of that base. -/
theorem factor_of_scale (t base : Nat) (L C : ℝ) (hb : 0 < base)
    (hL : 0 < L) (hC : 0 ≤ C) (hscale : L ≤ C*base) :
    1+((t : ℝ)/base)^(1-(Construction.epsilon : ℝ)) ≤
      (1+C^(1-(Construction.epsilon : ℝ))) *
        (1+((t : ℝ)/L)^(1-(Construction.epsilon : ℝ))) := by
  have hbR : (0 : ℝ) < base := by exact_mod_cast hb
  have ht : 0 ≤ 1-(Construction.epsilon : ℝ) := ArbitraryCost.tau_pos.le
  have hd : (t : ℝ)/base ≤ C*((t : ℝ)/L) := by
    apply (div_le_iff₀ hbR).2
    rw [show C*((t : ℝ)/L)*base = (C*t*base)/L by ring]
    apply (le_div_iff₀ hL).2
    have hm := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
    nlinarith only [hm]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (t : ℝ)/base) hd ht
  rw [Real.mul_rpow hC (by positivity)] at hp
  have hx : 0 ≤ ((t : ℝ)/L)^(1-(Construction.epsilon : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hc : 0 ≤ C^(1-(Construction.epsilon : ℝ)) := Real.rpow_nonneg hC _
  nlinarith only [hp, hx, hc]

theorem factor_bank (q : Configuration) (t : Nat) (hnormal : Normalized q) :
    1+((t : ℝ)/chosenBase q)^(1-(Construction.epsilon : ℝ)) ≤
      (1+baseLogConstant^(1-(Construction.epsilon : ℝ))) *
        (1+((t : ℝ)/Real.log ((CommonExchangeLeaf.bankWords q : ℝ)/q.block))^
          (1-(Construction.epsilon : ℝ))) :=
  factor_of_scale t (chosenBase q) _ _ (chosenBase_pos q hnormal)
    (lt_of_lt_of_le (by norm_num) (normalized_log_one _ _
      (CommonLeafProgram.block_positive q) hnormal))
    baseLogConstant_nonneg (log_bank_le_base q hnormal)

theorem height_le_bank (q : Configuration) : q.height ≤ CommonExchangeLeaf.bankWords q := by
  unfold CommonExchangeLeaf.bankWords
  omega

theorem normal_of_height (q : Configuration)
    (hnormal : minimumRatio radix 1 streamCount ≤ q.height/q.block) : Normalized q :=
  hnormal.trans (Nat.div_le_div_right (height_le_bank q))

theorem normal_height_of_inventory (q : Configuration)
    (hthreshold : minimumRatio radix 1 streamCount ≤ q.inventory.ratio) :
    minimumRatio radix 1 streamCount ≤ q.height/q.block := by
  apply (Nat.le_div_iff_mul_le (CommonLeafProgram.block_positive q)).2
  exact (Nat.mul_le_mul_right q.block hthreshold).trans (normalized_ratio q)

/-- The selected leaf bank also supplies the smaller sorting-height scale. -/
theorem factor_height (q : Configuration) (t : Nat)
    (hnormal : minimumRatio radix 1 streamCount ≤ q.height/q.block) :
    1+((t : ℝ)/chosenBase q)^(1-(Construction.epsilon : ℝ)) ≤
      (1+baseLogConstant^(1-(Construction.epsilon : ℝ))) *
        (1+((t : ℝ)/Real.log ((q.height : ℝ)/q.block))^(1-(Construction.epsilon : ℝ))) := by
  have hB := CommonLeafProgram.block_positive q
  have hBR : (0 : ℝ) < q.block := by exact_mod_cast hB
  have hH := (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B
    q.memory_large (by have := q.block_memory; omega)).1
  have hHR : (0 : ℝ) < q.height := by exact_mod_cast hH
  have hlog : Real.log ((q.height : ℝ)/q.block) ≤
      Real.log ((CommonExchangeLeaf.bankWords q : ℝ)/q.block) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by exact_mod_cast height_le_bank q) hBR.le
  exact factor_of_scale t (chosenBase q) _ _
    (chosenBase_pos q (normal_of_height q hnormal))
    (lt_of_lt_of_le (by norm_num) (normalized_log_one q.height q.block hB hnormal))
    baseLogConstant_nonneg
    (hlog.trans (log_bank_le_base q (normal_of_height q hnormal)))

/-- One fixed coefficient for the logarithmic envelope. -/
def logConstant (A D F : Nat) : ℝ :=
  ArbitraryCostRate.finalConstant A D F *
    (1+baseLogConstant^(1-(Construction.epsilon : ℝ)))

theorem logConstant_nonneg (A D F : Nat) : 0 ≤ logConstant A D F := by
  unfold logConstant
  exact mul_nonneg (ArbitraryCostRate.finalConstant_nonneg A D F)
    (by have := baseLogConstant_nonneg; positivity)

/-- The exact scalar bound used by the actual arbitrary-width wrapper
has the required height/block logarithm, with all borrowing costs retained. -/
theorem bound_log_height (q : Configuration) (P e G S A D F : Nat) (hP : 0 < P)
    (hnormal : minimumRatio radix 1 streamCount ≤ q.height/q.block) :
    (ArbitraryCostRate.bound (chosenBase q) (cutoff q) (CommonPermutationPairs.width q)
      P e G S A D F : ℝ) ≤
      logConstant A D F *
        ArbitraryCost.scan (CommonPermutationPairs.width q)
          (BinaryPadding.Volume P (radix^e) G S) *
        (1+((e : ℝ)/Real.log ((q.height : ℝ)/q.block))^(1-(Construction.epsilon : ℝ))) := by
  have hb := normal_of_height q hnormal
  have hc := ArbitraryCostRate.bound_improved (chosenBase q) (cutoff q)
    (CommonPermutationPairs.width q) P e G S A D F
    (CommonPermutationPairs.width_pos q) (chosenBase_pos q hb) hP (cutoff_child q hb)
  have hf := factor_height q e hnormal
  have hm := mul_le_mul_of_nonneg_left hf
    (mul_nonneg (ArbitraryCostRate.finalConstant_nonneg A D F)
      (ArbitraryCost.scan_nonneg (CommonPermutationPairs.width q)
        (BinaryPadding.Volume P (radix^e) G S)))
  exact hc.trans (by simpa only [logConstant, mul_assoc, mul_left_comm, mul_comm] using hm)

end
end CodedSorting.Construction.ArbitraryLogRate
end LogRate
