import CodedSorting.Sorting.Radix.Partition.Cost
import CodedSorting.Sorting.Radix.Program.Framework.Cost

section TreeCost
/-! Summation of the actual local, partition, directory, and stack
budgets over the MSD recursion. Per-child startup costs are absorbed
at their parent using radix*block<=height^2; no leaf-count oracle is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalTreeCost
open CommonSortingNormalization CommonMSDParameters CodedSorting.Construction.Sorting.CommonMSDSemanticCost
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension 

def budget (q : Configuration) : ℕ→List (KeyRecordWords.Record q.w)→ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDSemanticCost.budget CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
    (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q)
    (fun n=>CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q n+CommonMSDGlobalControlCost.controlCharge q n)

theorem node_scaled (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (n : ℕ) (hn : q.height^2<n) :
    (CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q n+CommonMSDGlobalControlCost.controlCharge q n)*q.block≤
      (4*localRate q+297)*n := by
  have hn' := CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget_scaled q n hn.le hnormal
  have hc := CommonMSDGlobalControlCost.controlCharge_words_le q n hn
  nlinarith only [hn',hc]

/-- Exact tree-level ledger, including one startup allowance per child. -/
theorem budget_scaled (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) :
    budget q fuel xs*q.block≤
      ((5*localRate q+333)*fuel+(localRate q+36))*xs.length+(localRate q+36)*q.block := by
  have h := budget_depth_bound CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.block q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q)
    (CodedSorting.Construction.Sorting.CommonLocalRecursion.block_le_height q) (radix_le_height q) CommonWordMSD.localSort
    (CommonMSDSemantics.record_local_correct q.w) (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q)
    (fun n=>CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q n+CommonMSDGlobalControlCost.controlCharge q n)
    (localRate q+36) (4*localRate q+297)
    (CodedSorting.Construction.Sorting.CommonMSDNodeRate.local_scaled q hnormal) (node_scaled q hnormal) fuel xs
  have he : 4*localRate q+297+(localRate q+36)=5*localRate q+333 := by ring
  simpa only [budget,he] using h

theorem localRate_large (q : Configuration) : 333≤localRate q := by
  unfold localRate
  omega

/-- A scan-sized input absorbs the sole root startup term. -/
theorem absorb (q : Configuration) (charge fuel n : ℕ) (hn : q.block≤n)
    (hc : charge*q.block≤((5*localRate q+333)*fuel+(localRate q+36))*n+
      (localRate q+36)*q.block) :
    charge*q.block≤6*localRate q*(fuel+1)*n := by
  have hl := localRate_large q
  have hroot := Nat.mul_le_mul_left (localRate q+36) hn
  have hco : (5*localRate q+333)*fuel+(localRate q+36)+(localRate q+36)≤
      6*localRate q*(fuel+1) := by nlinarith
  have hm := Nat.mul_le_mul_right n hco
  nlinarith only [hc,hroot,hm]

theorem budget_scan_scaled (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) (hn : q.block≤xs.length) :
    budget q fuel xs*q.block≤6*localRate q*(fuel+1)*xs.length :=
  absorb q (budget q fuel xs) fuel xs.length hn (budget_scaled q hnormal fuel xs)

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalTreeCost
end TreeCost

section Power
/-! The actual-radix integer ledger implies the improved logarithmic
sorting expression. The numeric conversion is separate so the same
physical run can supply its already proved charge without a cost oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalPower
open CommonSortingNormalization CodedSorting.Construction.Sorting.CommonMSDSemanticCost CodedSorting.Construction.Sorting.CommonLocalBudgetRate
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension 

def coefficient (q : Configuration) (κ : ℝ) : ℝ :=
  12*22194000000*GlobalSortingBound.rateConstant K tau*(κ*CommonMSDRadixLogBounds.factor q+2)

theorem rate_constant_nonneg : 0≤GlobalSortingBound.rateConstant K tau := by
  have hk:=K_nonneg
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  unfold GlobalSortingBound.rateConstant
  positivity

theorem local_power (q : Configuration)
    (ha : 1≤Real.log ((q.height : ℝ)/q.block)) :
    (CodedSorting.Construction.Sorting.CommonMSDSemanticCost.localRate q : ℝ)≤
      22194000000*GlobalSortingBound.rateConstant K tau*
        (1+(Real.log (q.height : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by
  have h := GlobalSortingBound.localRate_power_bound q.height (CommonMSDRadixLogBounds.height_two q)
    K (Real.log ((q.height : ℝ)/q.block)) tau K_nonneg ha tau_nonneg
  unfold CodedSorting.Construction.Sorting.CommonMSDSemanticCost.localRate
  push_cast
  nlinarith only [h]

/-- No algorithmic premise is hidden here: hc is the explicit integer
ledger supplied by the actual complete run. The descriptor-width factor
is part of the displayed constant, independent of the input payload. -/
theorem sorting_power (q : Configuration) (charge n : ℕ) (κ : ℝ)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (hκ : 0≤κ) (hn : q.height≤n)
    (hword : (q.w : ℝ)*Real.log 2≤κ*Real.log (n : ℝ))
    (hc : charge*q.block≤6*CodedSorting.Construction.Sorting.CommonMSDSemanticCost.localRate q*(CommonMSDRadixCost.depth q+1)*n) :
    (charge : ℝ)≤coefficient q κ*((n : ℝ)/q.block)*
      (1+Real.log (n : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
        Real.log (q.height : ℝ)^(1-tau))) := by
  have hb := CommonLeafProgram.block_positive q
  have hbR : (0:ℝ)<q.block := by exact_mod_cast hb
  have hH : (0:ℝ)<q.height := by
    exact_mod_cast (show 0<q.height by have:=CommonMSDRadixLogBounds.height_two q;omega)
  have hh : 0<Real.log (q.height : ℝ) :=
    Real.log_pos (by exact_mod_cast CommonMSDRadixLogBounds.height_two q)
  have ha := CodedSorting.Construction.ArbitraryLogRate.normalized_log_one q.height q.block hb hnormal
  have ha0 : 0<Real.log ((q.height : ℝ)/q.block) := by linarith
  have hlogB : 0≤Real.log (q.block : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤q.block by omega))
  have hah : Real.log ((q.height : ℝ)/q.block)≤Real.log (q.height : ℝ) := by
    rw [Real.log_div hH.ne' hbR.ne']
    linarith
  have hlogN : Real.log (q.height : ℝ)≤Real.log (n : ℝ) :=
    Real.log_le_log hH (by exact_mod_cast hn)
  have hD : 0≤CommonMSDRadixLogBounds.factor q := by
    linarith [CommonMSDRadixLogBounds.factor_one q]
  have hd := CommonMSDRadixLogBounds.depth_bound q κ (Real.log (n : ℝ)) hword
  have hl := local_power q ha
  have hC : 0≤22194000000*GlobalSortingBound.rateConstant K tau :=
    mul_nonneg (by norm_num) rate_constant_nonneg
  have hratio : 0≤(Real.log (q.height : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau :=
    Real.rpow_nonneg (div_nonneg hh.le ha0.le) _
  have hp := mul_le_mul hl hd
    (show (0:ℝ)≤(CommonMSDRadixCost.depth q : ℝ)+1 by positivity)
    (mul_nonneg hC (by linarith))
  have hcancel := GlobalSortingBound.depth_times_rate
    (Real.log (q.height : ℝ)) (Real.log ((q.height : ℝ)/q.block)) (Real.log (n : ℝ))
    tau (κ*CommonMSDRadixLogBounds.factor q) hh ha0 hah hlogN tau_nonneg (mul_nonneg hκ hD)
  have hproduct : (CodedSorting.Construction.Sorting.CommonMSDSemanticCost.localRate q : ℝ)*
      ((CommonMSDRadixCost.depth q : ℝ)+1)≤
      22194000000*GlobalSortingBound.rateConstant K tau*
        (2*(κ*CommonMSDRadixLogBounds.factor q+2)*
          (Real.log (n : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
            Real.log (q.height : ℝ)^(1-tau)))) := by
    calc
      _ ≤ _ := hp
      _ = (22194000000*GlobalSortingBound.rateConstant K tau)*
          ((1+(Real.log (q.height : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau)*
            (2+(κ*CommonMSDRadixLogBounds.factor q)*Real.log (n : ℝ)/Real.log (q.height : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcancel hC
  have hcR : (charge : ℝ)*(q.block : ℝ)≤6*(CodedSorting.Construction.Sorting.CommonMSDSemanticCost.localRate q : ℝ)*
      ((CommonMSDRadixCost.depth q : ℝ)+1)*(n : ℝ) := by exact_mod_cast hc
  have hscaled := mul_le_mul_of_nonneg_left hproduct (show (0:ℝ)≤6*(n : ℝ) by positivity)
  have hcb : (charge : ℝ)*(q.block : ℝ)≤coefficient q κ*(n : ℝ)*
      (Real.log (n : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
        Real.log (q.height : ℝ)^(1-tau))) := by
    unfold coefficient
    nlinarith only [hcR,hscaled]
  apply (le_div_iff₀ hbR).2 at hcb
  have hnonnegative : 0≤coefficient q κ*((n : ℝ)/q.block) := by
    unfold coefficient
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) rate_constant_nonneg)
        (by have:=mul_nonneg hκ hD;linarith)) (by positivity)
  calc
    _ ≤ _ := hcb
    _ = (coefficient q κ*((n : ℝ)/q.block))*
        (Real.log (n : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
          Real.log (q.height : ℝ)^(1-tau))) := by ring
    _ ≤ _ := by rw [mul_add,mul_one];linarith

/-- The tree budget is concrete: local sorts, row preparation, gather,
all child directory scans, and both stack transfers are included. -/
theorem budget_power (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (xs : List (KeyRecordWords.Record q.w)) (κ : ℝ) (hκ : 0≤κ) (hn : q.height≤xs.length)
    (hword : (q.w : ℝ)*Real.log 2≤κ*Real.log (xs.length : ℝ)) :
    (CodedSorting.Construction.Sorting.CommonMSDGlobalTreeCost.budget q (CommonMSDRadixCost.depth q) xs : ℝ)≤
      coefficient q κ*((xs.length : ℝ)/q.block)*
        (1+Real.log (xs.length : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
          Real.log (q.height : ℝ)^(1-tau))) :=
  sorting_power q _ xs.length κ hnormal hκ hn hword
    (CodedSorting.Construction.Sorting.CommonMSDGlobalTreeCost.budget_scan_scaled q hnormal _ xs
      ((CodedSorting.Construction.Sorting.CommonLocalRecursion.block_le_height q).trans hn))

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalPower
end Power
