import CodedSorting.Sorting.Radix.Program.Power
import CodedSorting.Sorting.Bounds.GlobalSortingBound

/-! Numerical transfer for the actual one-time normalization. The usable
memory H=M/C and logical block b=max(1,B/C²) have the paper's logarithmic
rate up to a constant depending only on the fixed reserve. Scan allowances
can include both raw-record conversions and the physical layout boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.Construction.Sorting.CommonMSDPhysicalRate
open CommonSortingNormalization CodedSorting.Construction.Sorting.CommonLocalBudgetRate
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension 

def reserve (q : Configuration) : ℕ := SortingResourceBudget.reserve q.inventory q.c q.digits
def logFactor (q : Configuration) : ℝ := 1+Real.log (2*(reserve q:ℝ))/Real.log 2
def logicalFactor (q : Configuration) (n : ℕ) : ℝ :=
  1+Real.log (n:ℝ)/(Real.log ((q.height:ℝ)/q.block)^tau*Real.log (q.height:ℝ)^(1-tau))
def paperFactor (q : Configuration) (n : ℕ) : ℝ :=
  1+Real.log (n:ℝ)/(Real.log ((q.M:ℝ)/q.B)^tau*Real.log (q.M:ℝ)^(1-tau))
def coefficient (q : Configuration) (A : ℝ) (scans : ℕ) : ℝ :=
  (2*(reserve q:ℝ)^2)*logFactor q^2*(A+2*(scans:ℝ))

theorem reserve_positive (q : Configuration) : 0<reserve q :=
  SortingResourceBudget.reserve_pos _ _ _

theorem reserve_large (q : Configuration) : 16≤reserve q :=
  (SortingResourceBudget.reserve_bounds _ _ _).2.2.2.2.2

theorem block_le_physical (q : Configuration) : q.block≤q.B :=
  Normalization.logical_block_le_physical _ _ q.block_pos

theorem reserve_blocks (q : Configuration) : reserve q*q.block≤q.height := by
  let C := reserve q
  have hC : 0<C := reserve_positive q
  change C*max 1 (q.B/C^2)≤q.M/C
  apply (Nat.le_div_iff_mul_le hC).2
  by_cases hb : 1≤q.B/C^2
  · rw [max_eq_right hb]
    have hd := Nat.div_mul_le_self q.B (C^2)
    have hBM : q.B≤q.M := by have:=q.block_memory;omega
    nlinarith only [hd,hBM]
  · rw [max_eq_left (by omega)]
    simpa only [Nat.mul_one,pow_two] using q.memory_large

theorem memory_scaled (q : Configuration) : q.M≤2*reserve q*q.height := by
  have hC := reserve_positive q
  have hH := CommonMSDRadixLogBounds.height_two q
  have hdiv := Nat.lt_mul_div_succ q.M hC
  change q.M<reserve q*(q.height+1) at hdiv
  nlinarith

theorem logical_ratio_two (q : Configuration) : (2:ℝ)≤(q.height:ℝ)/q.block := by
  have hbR : (0:ℝ)<q.block := by exact_mod_cast CommonLeafProgram.block_positive q
  apply (le_div_iff₀ hbR).2
  have h := reserve_blocks q
  have hC := reserve_large q
  have hm := Nat.mul_le_mul_right q.block (show 2≤reserve q by omega)
  exact_mod_cast (show 2*q.block≤q.height by omega)

theorem physical_ratio_two (q : Configuration) : (2:ℝ)≤(q.M:ℝ)/q.B := by
  have hbR : (0:ℝ)<q.B := by exact_mod_cast q.block_pos
  apply (le_div_iff₀ hbR).2
  exact_mod_cast q.block_memory

theorem logFactor_one (q : Configuration) : 1≤logFactor q := by
  have hC : (1:ℝ)≤2*(reserve q:ℝ) := by exact_mod_cast (show 1≤2*reserve q by have:=reserve_positive q;omega)
  have hlog := Real.log_nonneg hC
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  unfold logFactor
  exact le_add_of_nonneg_right (div_nonneg hlog h2.le)

theorem log_memory (q : Configuration) :
    Real.log (q.M:ℝ)≤logFactor q*Real.log (q.height:ℝ) := by
  have hM : (0:ℝ)<q.M := by
    exact_mod_cast (show 0<q.M by have:=q.block_pos;have:=q.block_memory;omega)
  apply NormalizationLogs.log_scale_bound hM
    (by exact_mod_cast CommonMSDRadixLogBounds.height_two q)
    (show (1:ℝ)≤2*(reserve q:ℝ) by exact_mod_cast (show 1≤2*reserve q by have:=reserve_positive q;omega))
  exact_mod_cast memory_scaled q

theorem log_ratio (q : Configuration) :
    Real.log ((q.M:ℝ)/q.B)≤logFactor q*Real.log ((q.height:ℝ)/q.block) := by
  have hB : (0:ℝ)<q.B := by exact_mod_cast q.block_pos
  have hb : (0:ℝ)<q.block := by exact_mod_cast CommonLeafProgram.block_positive q
  have hM : (0:ℝ)<q.M := by
    exact_mod_cast (show 0<q.M by have:=q.block_pos;have:=q.block_memory;omega)
  have hmem : (q.M:ℝ)≤2*(reserve q:ℝ)*q.height := by exact_mod_cast memory_scaled q
  have hbB : (q.block:ℝ)≤q.B := by exact_mod_cast block_le_physical q
  apply NormalizationLogs.log_scale_bound (div_pos hM hB) (logical_ratio_two q)
    (show (1:ℝ)≤2*(reserve q:ℝ) by exact_mod_cast (show 1≤2*reserve q by have:=reserve_positive q;omega))
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hB hb).2
  exact (mul_le_mul_of_nonneg_left hbB hM.le).trans
    (mul_le_mul_of_nonneg_right hmem hB.le)

theorem power_scaled (x y F t : ℝ) (hx : 0≤x) (hy : 0≤y)
    (hF : 1≤F) (hxy : x≤F*y) (ht : 0≤t) (ht1 : t≤1) : x^t≤F*y^t := by
  have h := Real.rpow_le_rpow hx hxy ht
  rw [Real.mul_rpow (by linarith) hy] at h
  exact h.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hF ht1)
    (Real.rpow_nonneg hy _))

theorem tau_le_one : tau≤1 := by
  have he : (0:ℝ)<CodedSorting.Construction.epsilon := by exact_mod_cast CodedSorting.Construction.epsilon_pos
  unfold tau
  linarith

theorem denominator_transfer (q : Configuration) :
    Real.log ((q.M:ℝ)/q.B)^tau*Real.log (q.M:ℝ)^(1-tau)≤
      logFactor q^2*(Real.log ((q.height:ℝ)/q.block)^tau*Real.log (q.height:ℝ)^(1-tau)) := by
  have hm : 0≤Real.log (q.M:ℝ) := Real.log_nonneg
    (by exact_mod_cast (show 1≤q.M by have:=q.block_pos;have:=q.block_memory;omega))
  have hh : 0≤Real.log (q.height:ℝ) := Real.log_nonneg
    (by exact_mod_cast (show 1≤q.height by have:=CommonMSDRadixLogBounds.height_two q;omega))
  have hmr : 0≤Real.log ((q.M:ℝ)/q.B) := Real.log_nonneg (by linarith [physical_ratio_two q])
  have hhr : 0≤Real.log ((q.height:ℝ)/q.block) := Real.log_nonneg (by linarith [logical_ratio_two q])
  have h1 := power_scaled _ _ (logFactor q) tau hmr hhr (logFactor_one q) (log_ratio q) tau_nonneg tau_le_one
  have h2 := power_scaled _ _ (logFactor q) (1-tau) hm hh (logFactor_one q) (log_memory q)
    (by linarith [tau_le_one]) (by linarith [tau_nonneg])
  have hp := mul_le_mul h1 h2 (Real.rpow_nonneg hm _)
    (mul_nonneg (by linarith [logFactor_one q]) (Real.rpow_nonneg hhr _))
  nlinarith only [hp]

theorem paperFactor_one (q : Configuration) (n : ℕ) (hn : 1≤n) : 1≤paperFactor q n := by
  have hz : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hmr : 0<Real.log ((q.M:ℝ)/q.B) := Real.log_pos (by linarith [physical_ratio_two q])
  have hm : 0<Real.log (q.M:ℝ) := Real.log_pos
    (by exact_mod_cast (show 1<q.M by have:=q.block_pos;have:=q.block_memory;omega))
  unfold paperFactor
  exact le_add_of_nonneg_right (by positivity)

theorem factor_transfer (q : Configuration) (n : ℕ) (hn : 1≤n) :
    logicalFactor q n≤logFactor q^2*paperFactor q n := by
  let D := Real.log ((q.M:ℝ)/q.B)^tau*Real.log (q.M:ℝ)^(1-tau)
  let d := Real.log ((q.height:ℝ)/q.block)^tau*Real.log (q.height:ℝ)^(1-tau)
  have hmr : 0<Real.log ((q.M:ℝ)/q.B) := Real.log_pos (by linarith [physical_ratio_two q])
  have hhr : 0<Real.log ((q.height:ℝ)/q.block) := Real.log_pos (by linarith [logical_ratio_two q])
  have hm : 0<Real.log (q.M:ℝ) := Real.log_pos
    (by exact_mod_cast (show 1<q.M by have:=q.block_pos;have:=q.block_memory;omega))
  have hh : 0<Real.log (q.height:ℝ) := Real.log_pos
    (by exact_mod_cast CommonMSDRadixLogBounds.height_two q)
  have hD : 0<D := by dsimp [D];positivity
  have hd : 0<d := by dsimp [d];positivity
  have hz : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hDd : D≤logFactor q^2*d := denominator_transfer q
  have hdiv : Real.log (n:ℝ)/d≤logFactor q^2*(Real.log (n:ℝ)/D) := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hd hD).2
    have hm := mul_le_mul_of_nonneg_left hDd hz
    nlinarith only [hm]
  have hF : 1≤logFactor q^2 := by nlinarith [logFactor_one q]
  change 1+Real.log (n:ℝ)/d≤logFactor q^2*(1+Real.log (n:ℝ)/D)
  nlinarith only [hdiv,hF]

theorem scan_transfer (q : Configuration) (n : ℕ) :
    (n:ℝ)/q.block≤(2*(reserve q:ℝ)^2)*((n:ℝ)/q.B) := by
  have h := MainSortingParametersNormalized.normalized_scan q.M q.B (reserve q^2) n q.block_pos
    (pow_pos (reserve_positive q) _)
  simpa only [Nat.cast_pow] using h

theorem rounded_scan (q : Configuration) (n : ℕ) (hn : q.B≤n) :
    (PhysicalStreamCursor.blockCount q.block n:ℝ)≤2*((n:ℝ)/q.block) := by
  have hb := CommonLeafProgram.block_positive q
  have hbR : (0:ℝ)<q.block := by exact_mod_cast hb
  have hbn := (block_le_physical q).trans hn
  have h := LocalSortingCost.blockCount_capacity q.block hb n
  change PhysicalStreamCursor.blockCount q.block n*q.block≤n+q.block at h
  have hR : (PhysicalStreamCursor.blockCount q.block n:ℝ)*(q.block:ℝ)≤(n:ℝ)+q.block := by exact_mod_cast h
  have hnR : (q.block:ℝ)≤n := by exact_mod_cast hbn
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hbR).2
  nlinarith only [hR,hnR]

/-- Apply this to the exact normalization equality together with the
already proved raw-record scan bounds. All constants are explicit. -/
theorem with_scans (q : Configuration) (n logical physical scans : ℕ) (A : ℝ)
    (hn : q.B≤n) (hA : 0≤A)
    (hlogical : (logical:ℝ)≤A*((n:ℝ)/q.block)*logicalFactor q n)
    (hphysical : physical≤logical+scans*PhysicalStreamCursor.blockCount q.block n) :
    (physical:ℝ)≤coefficient q A scans*((n:ℝ)/q.B)*paperFactor q n := by
  have hn1 : 1≤n := by have:=q.block_pos;omega
  have hf := factor_transfer q n hn1
  have hp := paperFactor_one q n hn1
  have hF : 1≤logFactor q^2 := by nlinarith [logFactor_one q]
  have hb := scan_transfer q n
  have hs := rounded_scan q n hn
  have hx0 : (0:ℝ)≤(n:ℝ)/q.block := by positivity
  have hy0 : (0:ℝ)≤(n:ℝ)/q.B := by positivity
  have hbase : 0≤(2*(reserve q:ℝ)^2)*((n:ℝ)/q.B) := by positivity
  have hlog := hlogical.trans (mul_le_mul_of_nonneg_left hf (mul_nonneg hA hx0))
  have hm := mul_le_mul_of_nonneg_left hb (show 0≤A*logFactor q^2*paperFactor q n by positivity)
  have hscan := mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
    (Nat.cast_nonneg scans: (0:ℝ)≤scans)
  have hphys : (physical:ℝ)≤(logical:ℝ)+(scans:ℝ)*(PhysicalStreamCursor.blockCount q.block n:ℝ) := by
    exact_mod_cast hphysical
  have hsup : 1≤logFactor q^2*paperFactor q n := by nlinarith only [hF,hp]
  have hmore := mul_le_mul_of_nonneg_left hsup
    (show 0≤2*(scans:ℝ)*((2*(reserve q:ℝ)^2)*((n:ℝ)/q.B)) by positivity)
  unfold coefficient
  nlinarith only [hlog,hm,hscan,hphys,hmore]

end
end CodedSorting.Construction.Sorting.CommonMSDPhysicalRate
