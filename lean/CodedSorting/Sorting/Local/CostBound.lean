import CodedSorting.Sorting.Local.Program
import CodedSorting.Sorting.Resources.Swaps

/-! The actual finite-machine local budget has the improved sorting rate.
The exchange rate is supplied by the concrete common-machine exchanges,
and all resident groups, padding passes, and slab scans remain in budget. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.Construction.Sorting.CommonLocalBudgetRate
open CommonSortingNormalization CommonRecordProgram CodedSorting.Construction.Sorting.CommonLocalBudget
open CodedSorting.Construction.Sorting.CommonLocalBudgetTrace CommonLocalAdmissible CommonGroupedLeafCost
open LocalSortingCost LocalShape RecursiveColumnsort CodedSorting.Construction.ExchangeSpecialization
open GlobalSortingBound CodedSorting.Construction.ArbitraryLogRate
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension 

def tau : ℝ := 1-(CodedSorting.Construction.epsilon : ℝ)
def K : ℝ := CodedSorting.Construction.Sorting.CommonSortingExchangeRate.rateConstant 3
def boundConstant : ℝ := 22194000000*(GlobalSortingBound.rateConstant K tau+1)

theorem tau_nonneg : 0≤tau := by
  have he : (CodedSorting.Construction.epsilon : ℝ)<1 := by exact_mod_cast CodedSorting.Construction.epsilon_lt_one
  unfold tau
  linarith

theorem K_nonneg : 0≤K := CodedSorting.Construction.Sorting.CommonSortingExchangeRate.rateConstant_nonneg 3

theorem constant_large : 25≤boundConstant := by
  have hk := K_nonneg
  have hp : 0≤(1/Real.log 2+3)^tau := by
    apply Real.rpow_nonneg
    have : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hm := mul_nonneg hk (show 0≤1+(1/Real.log 2+3)^tau by linarith)
  unfold boundConstant GlobalSortingBound.rateConstant
  linarith

/-- Integer bound obtained by comparing the same local budget to its actual
recursive sorting trace.  The factor 822 covers all new machine overhead. -/
theorem integer_bound (q : Configuration) (n : ℕ) (hn : 0<n) (hsize : n≤q.height^2)
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 CodedSorting.Construction.streamCount≤q.height/q.block) :
    budget q 3 n*q.block≤22194000000*
      (localRate q.height K (Real.log ((q.height : ℝ)/q.block)) tau+2)*(n+q.block) := by
  have hb := CommonLeafProgram.block_positive q
  have hh := CodedSorting.Construction.ArbitraryLogRate.normalized_memory q.height q.block hb hnormal
  have hH : 0<q.height := by omega
  have ha := CodedSorting.Construction.ArbitraryLogRate.normalized_log_one q.height q.block hb hnormal
  let f : Fin n→KeyRecordWords.Record q.w := fun _=>⊥
  let t := (localRun q.height hH 3 n f).trace
  have hf : LocalTrace.Fits q.height 3 n t := localRun_trace_fits q.height hH 3 n f
  have hbudget := budget_trace q 3 n hn (three q.height n hH hsize) t hf
  have hwide := RecordWidthTraceCost.traceCost_bound q.block 3 q.height 3 n
    hb (by omega) (exchangeCost q) t hf
  have hx : ActualShapeSortingBound.ActualShapeRate q.block q.height K
      (Real.log ((q.height : ℝ)/q.block)) tau (exchangeCost q) :=
    CodedSorting.Construction.Sorting.CommonSortingExchangeRate.actual_shape_rate q 3 (by omega) hnormal
  have hcontract := ActualShapeSortingBound.local_exchange_contract q.block q.height K
    (Real.log ((q.height : ℝ)/q.block)) tau K_nonneg (by linarith) tau_nonneg (exchangeCost q) hx
  have htrace := (LocalSortingCost.local_trace_bound q.block q.height
    (localRate q.height K (Real.log ((q.height : ℝ)/q.block)) tau)
    hb hH hh.2 (exchangeCost q) hcontract n t hsize hf).1
  have hb' := Nat.mul_le_mul_right q.block hbudget
  have hw' := Nat.mul_le_mul_right q.block hwide
  change budget q 3 n*q.block≤(256+6*3)*
    RecordWidthTraceCost.traceCost q.block 3 (exchangeCost q) t*q.block at hb'
  nlinarith only [hb',hw',htrace]

/-- A single fixed constant bounds the complete local machine charge for
every positive input at most H squared.  In the recursive branch log H is
at most log n; the resident branch is already a constant number of scans. -/
theorem improved_bound (q : Configuration) (n : ℕ) (hn : 0<n) (hsize : n≤q.height^2)
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 CodedSorting.Construction.streamCount≤q.height/q.block) :
    (budget q 3 n : ℝ)≤boundConstant*(1+(n : ℝ)/q.block)*
      (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by
  have hb := CommonLeafProgram.block_positive q
  have hBR : (0 : ℝ)<q.block := by exact_mod_cast hb
  have hh := CodedSorting.Construction.ArbitraryLogRate.normalized_memory q.height q.block hb hnormal
  have hHR : (0 : ℝ)<q.height := by exact_mod_cast (show 0<q.height by omega)
  have ha := CodedSorting.Construction.ArbitraryLogRate.normalized_log_one q.height q.block hb hnormal
  have ha0 : 0<Real.log ((q.height : ℝ)/q.block) := by linarith
  have hlogn : 0≤Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hpow : 0≤(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau :=
    Real.rpow_nonneg (div_nonneg hlogn ha0.le) _
  have hc := constant_large
  have hscaled : (budget q 3 n : ℝ)*q.block≤
      boundConstant*((n : ℝ)+q.block)*
        (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by
    by_cases hs : n≤512*q.height
    · have hscan := blockCount_capacity q.block hb (3*n)
      rw [←recordBlocks_eq] at hscan
      have hbudget : budget q 3 n*q.block≤25*(n+q.block) := by
        rw [budget_small q 3 n hs]
        nlinarith only [hscan]
      have hbudgetR : (budget q 3 n : ℝ)*q.block≤25*((n : ℝ)+q.block) := by
        exact_mod_cast hbudget
      have hcoeff : (25 : ℝ)≤boundConstant*
          (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by
        nlinarith only [hc,hpow,mul_nonneg (show 0≤boundConstant by linarith) hpow]
      have hm := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0≤(n : ℝ)+q.block)
      nlinarith only [hbudgetR,hm]
    · have hi := integer_bound q n hn hsize hnormal
      have hiR : (budget q 3 n : ℝ)*q.block≤22194000000*
          ((localRate q.height K (Real.log ((q.height : ℝ)/q.block)) tau : ℝ)+2)*
            ((n : ℝ)+q.block) := by exact_mod_cast hi
      have hrate := GlobalSortingBound.localRate_power_bound q.height hh.1 K
        (Real.log ((q.height : ℝ)/q.block)) tau K_nonneg ha tau_nonneg
      have hlog : Real.log (q.height : ℝ)≤Real.log (n : ℝ) := by
        apply Real.log_le_log hHR
        exact_mod_cast (show q.height≤n by omega)
      have hpowH := Real.rpow_le_rpow
        (div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤q.height by omega))) ha0.le)
        (div_le_div_of_nonneg_right hlog ha0.le) tau_nonneg
      have hG : 0≤GlobalSortingBound.rateConstant K tau := by
        unfold GlobalSortingBound.rateConstant
        have := K_nonneg
        have : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        positivity
      have hm := mul_le_mul_of_nonneg_left (add_le_add_left hpowH 1) hG
      have hrate' := hrate.trans hm
      have hscaledRate := mul_le_mul_of_nonneg_right hrate'
        (by positivity : 0≤22194000000*((n : ℝ)+q.block))
      have hextra : 0≤22194000000*((n : ℝ)+q.block)*
          (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by positivity
      unfold boundConstant
      nlinarith only [hiR,hscaledRate,hextra]
  apply (le_div_iff₀ hBR).mpr at hscaled
  have he : (boundConstant*((n : ℝ)+q.block)*
      (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau))/q.block=
        boundConstant*(1+(n : ℝ)/q.block)*
          (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by
    calc
      _=boundConstant*(((n : ℝ)+q.block)/q.block)*
          (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by ring
      _=_ := by rw [add_div,div_self (ne_of_gt hBR)]; ring
  exact he ▸ hscaled

end
end CodedSorting.Construction.Sorting.CommonLocalBudgetRate
