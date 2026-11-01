import CodedSorting.Shared.Words.WordConvention
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

section SmallMemorySortingRate
/-! Numerical bounds for the complete constant-round, two-word LSD
fallback. These lemmas do not posit a sorting execution: they bound the
explicit budget of the real multi-pass program, including its copy-back.
The lower word-address convention remains a separate public assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.SmallMemorySortingRate
noncomputable section

/-- Fixed solely by the upper word-size convention, not the input size. -/
def wordFactor (κ : ℝ) : ℕ := max 1 ⌈κ⌉₊

theorem wordFactor_one (κ : ℝ) : 1≤wordFactor κ := Nat.le_max_left _ _

theorem word_upper (N w : ℕ) (κ : ℝ) (hN : 1≤N)
    (hw : (w:ℝ)*Real.log 2≤κ*Real.log (N:ℝ)) :
    w≤wordFactor κ*Nat.clog 2 N := by
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hpow : (N:ℝ)≤(2:ℝ)^(Nat.clog 2 N) := by
    exact_mod_cast Nat.le_pow_clog (by omega : 1<2) N
  have hp := Real.log_le_log hNpos hpow
  rw [Real.log_pow] at hp
  have hc : κ≤(wordFactor κ:ℝ) :=
    (Nat.le_ceil κ).trans (Nat.cast_le.mpr (Nat.le_max_right _ _))
  have hk := mul_le_mul_of_nonneg_right hc hlog
  have hl := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (wordFactor κ): (0:ℝ)≤wordFactor κ)
  have htwo : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h : (w:ℝ)≤(wordFactor κ:ℝ)*(Nat.clog 2 N:ℝ) := by
    nlinarith only [hw,hk,hl,htwo]
  exact_mod_cast h

/-- A full pass includes 1527N+376N+93 transfers and 2N copy-back
transfers. The public word convention requires at most 2c such passes. -/
def budget (c N : ℕ) : ℕ := (2*c)*(1905*N+93)

theorem budget_linear (c N : ℕ) (hN : 1≤N) : budget c N≤4000*c*N := by
  have hb : 1905*N+93≤2000*N := by omega
  have h := Nat.mul_le_mul_left (2*c) hb
  unfold budget
  nlinarith only [h]

/-- The first branch of the refined sorting bound is exactly the
linear-in-record-count fallback, for every positive physical block size. -/
theorem individual_branch (c N B : ℕ) (hN : 1≤N) (hB : 0<B) :
    (budget c N:ℝ)≤(4000*c:ℝ)*((N:ℝ)/B)*B := by
  have h := budget_linear c N hN
  have hb : (B:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  rw [mul_assoc,div_mul_cancel₀ _ hb]
  exact_mod_cast h

/-- Any scan multiplier at least one absorbs O(N) when B has a fixed
upper bound. This is the only use of the small-memory cutoff. -/
theorem bounded_block_absorb (c N B M₀ : ℕ) (F : ℝ)
    (hN : 1≤N) (hB : 0<B) (hBM : B≤M₀) (hF : 1≤F) :
    (budget c N:ℝ)≤(4000*c*M₀:ℝ)*((N:ℝ)/B)*F := by
  have hb := individual_branch c N B hN hB
  have hm : (B:ℝ)≤M₀ := by exact_mod_cast hBM
  have hbase : (0:ℝ)≤(4000*c:ℝ)*((N:ℝ)/B) := by positivity
  have he := mul_le_mul_of_nonneg_left hm hbase
  have hf := mul_le_mul_of_nonneg_left hF
    (show (0:ℝ)≤(4000*c:ℝ)*((N:ℝ)/B)*M₀ by positivity)
  nlinarith only [hb,he,hf]

def paperFactor (N M B : ℕ) (τ ε : ℝ) : ℝ :=
  1+Real.log (N:ℝ)/(Real.log ((M:ℝ)/B)^τ*Real.log (M:ℝ)^ε)

theorem paperFactor_one (N M B : ℕ) (τ ε : ℝ)
    (hN : 1≤N) (hB : 0<B) (hMB : 2*B≤M) : 1≤paperFactor N M B τ ε := by
  have hb : (0:ℝ)<B := by exact_mod_cast hB
  have hm : (1:ℝ)<M := by exact_mod_cast (show 1<M by omega)
  have hr : (1:ℝ)<(M:ℝ)/B := by
    apply (lt_div_iff₀ hb).2
    simpa only [one_mul] using (show (B:ℝ)<M by exact_mod_cast (show B<M by omega))
  have hlog := Real.log_nonneg (show (1:ℝ)≤N by exact_mod_cast hN)
  have ha := Real.log_pos hr
  have hh := Real.log_pos hm
  unfold paperFactor
  exact le_add_of_nonneg_right (by positivity)

/-- Covers every 2B≤M<M₀ with one coefficient depending only on the
fixed cutoff M₀ and the fixed word convention c. -/
theorem bounded_memory (c N M B M₀ : ℕ) (τ ε : ℝ)
    (hN : 1≤N) (hB : 0<B) (hMB : 2*B≤M) (hM : M<M₀) :
    (budget c N:ℝ)≤(4000*c*M₀:ℝ)*((N:ℝ)/B)*paperFactor N M B τ ε :=
  bounded_block_absorb c N B M₀ _ hN hB (by omega)
    (paperFactor_one N M B τ ε hN hB hMB)

/-- The multiplier in the paper's refined Section 7.4 bound. -/
def refinedFactor (N M B : ℕ) (τ ε : ℝ) : ℝ :=
  let p:=Real.log ((N:ℝ)/M)
  let a:=Real.log ((M:ℝ)/B)
  let h:=Real.log (M:ℝ)
  1+p/(a^τ*(a+min p h)^ε)

theorem refinedFactor_one (N M B : ℕ) (τ ε : ℝ)
    (hB : 0<B) (hMB : 2*B≤M) (hNM : M≤N) : 1≤refinedFactor N M B τ ε := by
  have hb : (0:ℝ)<B := by exact_mod_cast hB
  have hm : (1:ℝ)<M := by exact_mod_cast (show 1<M by omega)
  have hr : (1:ℝ)<(M:ℝ)/B := by
    apply (lt_div_iff₀ hb).2
    simpa only [one_mul] using (show (B:ℝ)<M by exact_mod_cast (show B<M by omega))
  have hn : (1:ℝ)≤(N:ℝ)/M := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<M)).2
    simpa only [one_mul] using (show (M:ℝ)≤N by exact_mod_cast hNM)
  have hp:=Real.log_nonneg hn
  have ha:=Real.log_pos hr
  have hh:=Real.log_pos hm
  unfold refinedFactor
  exact le_add_of_nonneg_right (by positivity)

/-- The same actual fallback budget also covers the refined minimum
throughout the fixed small-memory range; no additional algorithm is assumed. -/
theorem bounded_memory_refined (c N M B M₀ : ℕ) (τ ε : ℝ)
    (hB : 0<B) (hMB : 2*B≤M) (hNM : M≤N) (hM : M<M₀) :
    (budget c N:ℝ)≤(4000*c*M₀:ℝ)*((N:ℝ)/B)*
      min (B:ℝ) (refinedFactor N M B τ ε) := by
  apply bounded_block_absorb c N B M₀ _ (by omega) hB (by omega)
  exact le_min (by exact_mod_cast hB) (refinedFactor_one N M B τ ε hB hMB hNM)

end
end CodedSorting.SmallMemorySortingRate
end SmallMemorySortingRate

section SmallMemoryPhysicalRate
/-! The small-memory numerical endpoint includes the two real compact
layout scans: 2N input transfers and 3N output transfers. -/
set_option autoImplicit false
namespace CodedSorting.SmallMemoryPhysicalRate
open SmallMemorySortingRate
noncomputable section

def budget (c N : ℕ) : ℕ := SmallMemorySortingRate.budget c N+5*N

theorem format_le_double (c N : ℕ) (hc : 1≤c) :
    budget c N≤2*SmallMemorySortingRate.budget c N := by
  have hn:=Nat.mul_le_mul_right N hc
  unfold budget SmallMemorySortingRate.budget
  nlinarith only [hn]

theorem budget_linear (c N : ℕ) (hc : 1≤c) (hN : 1≤N) : budget c N≤8000*c*N := by
  have h:=format_le_double c N hc
  have hr:=SmallMemorySortingRate.budget_linear c N hN
  nlinarith only [h,hr]

theorem bounded_block_absorb (c N B M₀ : ℕ) (F : ℝ)
    (hc : 1≤c) (hN : 1≤N) (hB : 0<B) (hBM : B≤M₀) (hF : 1≤F) :
    (budget c N:ℝ)≤(8000*c*M₀:ℝ)*((N:ℝ)/B)*F := by
  have h : (budget c N:ℝ)≤2*(SmallMemorySortingRate.budget c N:ℝ) := by
    exact_mod_cast format_le_double c N hc
  have hr:=SmallMemorySortingRate.bounded_block_absorb c N B M₀ F hN hB hBM hF
  nlinarith only [h,hr]

theorem bounded_memory (c N M B M₀ : ℕ) (τ ε : ℝ)
    (hc : 1≤c) (hN : 1≤N) (hB : 0<B) (hMB : 2*B≤M) (hM : M<M₀) :
    (budget c N:ℝ)≤(8000*c*M₀:ℝ)*((N:ℝ)/B)*paperFactor N M B τ ε :=
  bounded_block_absorb c N B M₀ _ hc hN hB (by omega)
    (paperFactor_one N M B τ ε hN hB hMB)

theorem bounded_memory_refined (c N M B M₀ : ℕ) (τ ε : ℝ)
    (hc : 1≤c) (hB : 0<B) (hMB : 2*B≤M) (hNM : M≤N) (hM : M<M₀) :
    (budget c N:ℝ)≤(8000*c*M₀:ℝ)*((N:ℝ)/B)*
      min (B:ℝ) (refinedFactor N M B τ ε) := by
  apply bounded_block_absorb c N B M₀ _ hc (by omega) hB (by omega)
  exact le_min (by exact_mod_cast hB) (refinedFactor_one N M B τ ε hB hMB hNM)

/-- Generic absorption for any proved cost of the actual execution. The
coefficient may include a uniform controller and format conversion. -/
theorem linear_absorb (cost N B M₀ : ℕ) (A F : ℝ)
    (hA : 0≤A) (hcost : (cost:ℝ)≤A*N) (hB : 0<B)
    (hBM : B≤M₀) (hF : 1≤F) :
    (cost:ℝ)≤(A*M₀)*((N:ℝ)/B)*F := by
  have hb : (B:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have he : A*(N:ℝ)=A*((N:ℝ)/B)*B := by rw [mul_assoc,div_mul_cancel₀ _ hb]
  rw [he] at hcost
  have hm : (B:ℝ)≤M₀ := by exact_mod_cast hBM
  have hbase : 0≤A*((N:ℝ)/B) := mul_nonneg hA (by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm hbase
  have hf := mul_le_mul_of_nonneg_left hF
    (show 0≤A*((N:ℝ)/B)*M₀ by positivity)
  nlinarith only [hcost,hm',hf]

/-- Includes 2c real passes, each charged AN+D, and both format scans. -/
def affineBudget (A D c N : ℕ) : ℕ := (2*c)*(A*N+D)+5*N

theorem affine_linear (A D c N : ℕ) (hc : 1≤c) (hN : 1≤N) :
    affineBudget A D c N≤(2*(A+D)+5)*c*N := by
  have hd:=Nat.mul_le_mul_left D hN
  have hn:=Nat.mul_le_mul_right N hc
  have hp:=Nat.mul_le_mul_left (2*c) (show A*N+D≤(A+D)*N by nlinarith only [hd])
  unfold affineBudget
  nlinarith only [hn,hp]

theorem linear_memory (cost N M B M₀ : ℕ) (A τ ε : ℝ)
    (hA : 0≤A) (hcost : (cost:ℝ)≤A*N) (hN : 1≤N)
    (hB : 0<B) (hMB : 2*B≤M) (hM : M<M₀) :
    (cost:ℝ)≤(A*M₀)*((N:ℝ)/B)*paperFactor N M B τ ε :=
  linear_absorb cost N B M₀ A _ hA hcost hB (by omega)
    (paperFactor_one N M B τ ε hN hB hMB)

theorem linear_refined (cost N M B M₀ : ℕ) (A τ ε : ℝ)
    (hA : 0≤A) (hcost : (cost:ℝ)≤A*N)
    (hB : 0<B) (hMB : 2*B≤M) (hNM : M≤N) (hM : M<M₀) :
    (cost:ℝ)≤(A*M₀)*((N:ℝ)/B)*min (B:ℝ) (refinedFactor N M B τ ε) := by
  apply linear_absorb cost N B M₀ A _ hA hcost hB (by omega)
  exact le_min (by exact_mod_cast hB) (refinedFactor_one N M B τ ε hB hMB hNM)

end
end CodedSorting.SmallMemoryPhysicalRate
end SmallMemoryPhysicalRate
