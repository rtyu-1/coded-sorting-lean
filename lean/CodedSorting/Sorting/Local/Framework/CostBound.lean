import CodedSorting.Sorting.Resources.Framework.SemanticSwaps
import CodedSorting.Shared.Memory.GroupedLeafBatch
import CodedSorting.Shared.Words.RecordWidthTraceCost

section Admissible
/-! A numerical legality predicate for the actual finite-depth local
sorter.  It contains only leaf-size obligations, and is discharged for
every input of at most H squared records before the machine is built. -/
set_option autoImplicit false
namespace CodedSorting.CommonLocalAdmissible
open LocalShape LocalSortingCost

def Admissible (H : ℕ) : ℕ→ℕ→Prop
  | 0,n => n≤512*H
  | fuel+1,n => if n≤512*H then True else Admissible H fuel (columnLength n)

theorem of_small (H fuel n : ℕ) (hn : n≤512*H) : Admissible H fuel n := by
  cases fuel with
  | zero => exact hn
  | succ fuel => simp only [Admissible,if_pos hn]

theorem zero {H n : ℕ} (h : Admissible H 0 n) : n≤512*H := h

theorem child {H fuel n : ℕ} (h : Admissible H (fuel+1) n) (hn : 512*H<n) :
    Admissible H fuel (columnLength n) := by
  simpa only [Admissible,if_neg (show ¬n≤512*H by omega)] using h

theorem of_iter (H fuel n : ℕ) (hn : iterColumn fuel n≤512*H) :
    Admissible H fuel n := by
  induction fuel generalizing n with
  | zero => exact hn
  | succ fuel ih =>
    by_cases hsmall : n≤512*H
    · exact of_small H (fuel+1) n hsmall
    · simpa only [Admissible,if_neg hsmall] using ih (columnLength n) hn

/-- The real rounded child sizes fit after three levels.  No leaf-size
premise remains beyond the public usable-memory and local-input bounds. -/
theorem three (H n : ℕ) (hH : 0<H) (hn : n≤H^2) : Admissible H 3 n := by
  apply of_iter
  have h := LocalShape.three_levels_fit n H hH hn
  change columnLength (columnLength (columnLength n))≤512*H
  omega

end CodedSorting.CommonLocalAdmissible
end Admissible

section Cost
/-! Public bounds for the actual finite-machine local sorter. Grouping
short columns avoids paying one rounded disk block for every column. -/
set_option autoImplicit false
namespace CodedSorting.CommonLocalBudget
open CommonSortingNormalization CommonRecordProgram PhysicalLocalSortNode
noncomputable section

def batchBound (q : Configuration) (child c r : ℕ) : ℕ :=
  if r≤512*q.height then 256*(recordBlocks q (c*r)+1)
  else c*(child+12*recordBlocks q r)

def budget (q : Configuration) : ℕ → ℕ → ℕ
  | 0,n => 8*recordBlocks q n+1
  | fuel+1,n =>
    if n≤512*q.height then 8*recordBlocks q n+1
    else
      let s := LocalShape.sizeChoice n
      let r := rows s
      3*batchBound q (budget q fuel r) s r+
        batchBound q (budget q fuel r) (s+1) r+
        6*CommonSortingSwaps.exchangeCost q (LocalShape.sizeExponent n) 3+
        3*(2*recordBlocks q (s*r)+recordBlocks q ((s+1)*r)+recordBlocks q n)

def batchBudget (q : Configuration) (fuel c r : ℕ) : ℕ :=
  batchBound q (budget q fuel r) c r

theorem budget_small (q : Configuration) (fuel n : ℕ) (hn : n≤512*q.height) :
    budget q fuel n=8*recordBlocks q n+1 := by
  cases fuel <;> simp [budget,hn]

end
end CodedSorting.CommonLocalBudget
end Cost

section ExecutionCost
/-! Comparison of the actual machine's public local budget with the trace
of the mathematical sorter it implements.  Group startup and slab scans
are absorbed here, rather than omitted from the instruction budget. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonLocalBudgetTrace
open CommonSortingNormalization CommonRecordProgram CommonLocalBudget
open CommonLocalAdmissible LocalShape RecursiveColumnsort LocalSortingCost
open CommonGroupedLeafCost
noncomputable section

def exchangeCost (q : Configuration) : InterchangeCost :=
  fun t _ => CommonSortingSwaps.exchangeCost q t 3

def trace (q : Configuration) (t : CallTree) : ℕ :=
  RecordWidthTraceCost.traceCost q.block 3 (exchangeCost q) t

def batchTrace (q : Configuration) (ts : List CallTree) : ℕ :=
  RecordWidthTraceCost.batchCharge q.block 3
    (RecordWidthTraceCost.summarize q.block 3 (exchangeCost q) ts)

theorem recordBlocks_pos (q : Configuration) {n : ℕ} (hn : 0<n) : 0<recordBlocks q n := by
  rw [recordBlocks_eq]
  have h := WordControl.frame_fits (3*n) q.block (CommonLeafProgram.block_positive q)
  change 3*n≤blockCount q.block (3*n)*q.block at h
  nlinarith only [h,hn]

theorem trace_leaf (q : Configuration) (n : ℕ) : trace q (.leaf n)=2*recordBlocks q n := by
  simp only [trace,RecordWidthTraceCost.traceCost,RecordWidthTraceCost.leafCharge,
    leafScan,recordBlocks_eq]

theorem trace_ge_scan (q : Configuration) {fuel n : ℕ} {t : CallTree}
    (hf : LocalTrace.Fits q.height fuel n t) : 2*recordBlocks q n≤trace q t := by
  cases hf with
  | leaf => rw [trace_leaf]
  | node =>
    simp only [trace,RecordWidthTraceCost.traceCost,RecordWidthTraceCost.scanCharge,recordBlocks_eq]
    omega

private theorem sum_uniform (ts : List CallTree) (f : CallTree→ℕ) (c A : ℕ)
    (h : ∀t∈ts,c≤A*f t) : ts.length*c≤A*(ts.map f).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have hh := h t (by simp)
    have ht := ih (fun a ha=>h a (by simp [ha]))
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    nlinarith only [hh,ht]

theorem batch_bound (q : Configuration) (fuel c r child A : ℕ) (hr : 0<r) (hc : 0<c)
    (hA : 256≤A) (ha : Admissible q.height fuel r)
    (ts : List CallTree) (hlen : ts.length=c)
    (hf : ∀t∈ts,LocalTrace.Fits q.height fuel r t)
    (hb : ∀t∈ts,child≤A*trace q t) :
    batchBound q child c r≤(A+6)*batchTrace q ts := by
  have hv : (ts.map CallTree.inputSize).sum=c*r := by
    have he : ts.map CallTree.inputSize=ts.map (fun _=>r) := by
      apply List.map_congr_left
      intro t ht
      exact fits_inputSize (hf t ht)
    rw [he]
    simp [hlen]
  by_cases hs : r≤512*q.height
  · have hall : ts.all CallTree.isLeaf=true := by
      apply List.all_eq_true.mpr
      intro t ht
      rw [(hf t ht).leaf_of_small hs]
      rfl
    have hpos := recordBlocks_pos q (Nat.mul_pos hc hr)
    simp only [batchBound,if_pos hs,batchTrace,RecordWidthTraceCost.summarize_spec,
      RecordWidthTraceCost.batchCharge,hall,hv,↓reduceIte,
      RecordWidthTraceCost.leafCharge,leafScan,←recordBlocks_eq]
    nlinarith only [hpos,hA]
  · have hfu : fuel≠0 := by
      intro he
      subst fuel
      exact hs ha
    have hnot : ts.all CallTree.isLeaf≠true := by
      intro hall
      have hne : ts≠[] := by intro he; simp only [he,List.length_nil] at hlen; omega
      obtain ⟨t,ht⟩ := List.exists_mem_of_ne_nil ts hne
      have htleaf := List.all_eq_true.mp hall t ht
      have hfit := hf t ht
      cases hfit with
      | leaf _ _ hh => exact hh.elim hfu hs
      | node => simp [CallTree.isLeaf] at htleaf
    have hb' := sum_uniform ts (trace q) child A hb
    rw [hlen] at hb'
    have hl := sum_uniform ts (trace q) (2*recordBlocks q r) 1
      (fun t ht=>by simpa only [one_mul] using trace_ge_scan q (hf t ht))
    rw [hlen] at hl
    simp only [batchBound,if_neg hs,batchTrace,RecordWidthTraceCost.summarize_spec,
      RecordWidthTraceCost.batchCharge,hnot,↓reduceIte]
    change c*(child+12*recordBlocks q r)≤(A+6)*(ts.map (trace q)).sum
    nlinarith only [hb',hl]

theorem budget_trace (q : Configuration) (fuel n : ℕ) (hn : 0<n)
    (ha : Admissible q.height fuel n) (t : CallTree)
    (hf : LocalTrace.Fits q.height fuel n t) :
    budget q fuel n≤(256+6*fuel)*trace q t := by
  induction fuel generalizing n t with
  | zero =>
    rw [hf.leaf_of_zero,trace_leaf]
    have hpos := recordBlocks_pos q hn
    simp only [budget,Nat.mul_zero,Nat.add_zero]
    omega
  | succ fuel ih =>
    cases hf with
    | leaf _ _ hh =>
      have hs : n≤512*q.height := hh.resolve_left (by omega)
      rw [budget_small q (fuel+1) n hs,trace_leaf]
      have hpos := recordBlocks_pos q hn
      have hmul : 256*(2*recordBlocks q n)≤(256+6*(fuel+1))*(2*recordBlocks q n) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    | @node _ n first second third fourth hlarge hfirst hsecond hthird hfourth hf1 hf2 hf3 hf4 =>
      have hrow : PhysicalLocalSortNode.rows (sizeChoice n)=columnLength n := by
        unfold PhysicalLocalSortNode.rows columnLength
        ring
      have hr : 0<columnLength n := by unfold columnLength sizeChoice; positivity
      have hs : 0<sizeChoice n := by unfold sizeChoice; positivity
      have hc := CommonLocalAdmissible.child ha hlarge
      have h1 := batch_bound q fuel (sizeChoice n) (columnLength n)
        (budget q fuel (columnLength n)) (256+6*fuel) hr hs (by omega) hc first hfirst hf1
        (fun t ht=>ih _ hr hc t (hf1 t ht))
      have h2 := batch_bound q fuel (sizeChoice n) (columnLength n)
        (budget q fuel (columnLength n)) (256+6*fuel) hr hs (by omega) hc second hsecond hf2
        (fun t ht=>ih _ hr hc t (hf2 t ht))
      have h3 := batch_bound q fuel (sizeChoice n) (columnLength n)
        (budget q fuel (columnLength n)) (256+6*fuel) hr hs (by omega) hc third hthird hf3
        (fun t ht=>ih _ hr hc t (hf3 t ht))
      have h4 := batch_bound q fuel (sizeChoice n+1) (columnLength n)
        (budget q fuel (columnLength n)) (256+6*fuel) hr (by omega) (by omega) hc fourth hfourth hf4
        (fun t ht=>ih _ hr hc t (hf4 t ht))
      have hvol : sizeChoice n*columnLength n=sizeChoice n^4 := by unfold columnLength; ring
      have hshift : (sizeChoice n+1)*columnLength n=sizeChoice n^4+sizeChoice n^3 := by
        unfold columnLength
        ring
      have hfac : 2≤256+6*(fuel+1) := by omega
      have he := Nat.mul_le_mul_left
        (6*CommonSortingSwaps.exchangeCost q (sizeExponent n) 3) (show 1≤256+6*(fuel+1) by omega)
      have hscan : 3*(2*recordBlocks q (sizeChoice n^4)+
          recordBlocks q (sizeChoice n^4+sizeChoice n^3)+recordBlocks q n)≤
          (256+6*(fuel+1))*RecordWidthTraceCost.scanCharge q.block 3 n (sizeChoice n) := by
        simp only [recordBlocks_eq,RecordWidthTraceCost.scanCharge]
        nlinarith only [hfac]
      simp only [budget,if_neg (show ¬n≤512*q.height by omega),hrow,hvol,hshift]
      change _≤(256+6*(fuel+1))*(6*CommonSortingSwaps.exchangeCost q (sizeExponent n) 3+
        RecordWidthTraceCost.scanCharge q.block 3 n (sizeChoice n)+
        batchTrace q first+batchTrace q second+batchTrace q third+batchTrace q fourth)
      nlinarith only [h1,h2,h3,h4,he,hscan]

theorem actual_trace (q : Configuration) (hH : 0<q.height) (fuel n : ℕ) (hn : 0<n)
    (ha : Admissible q.height fuel n)
    {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α] (f : Fin n→α) :
    budget q fuel n≤(256+6*fuel)*
      RecordWidthTraceCost.traceCost q.block 3 (exchangeCost q)
        (localRun q.height hH fuel n f).trace :=
  budget_trace q fuel n hn ha _ (localRun_trace_fits q.height hH fuel n f)

end
end CodedSorting.CommonLocalBudgetTrace
end ExecutionCost

section CostBound
/-! The actual finite-machine local budget has the improved sorting rate.
The exchange rate is supplied by the concrete common-machine exchanges,
and all resident groups, padding passes, and slab scans remain in budget. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonLocalBudgetRate
open CommonSortingNormalization CommonRecordProgram CommonLocalBudget
open CommonLocalBudgetTrace CommonLocalAdmissible CommonGroupedLeafCost
open LocalSortingCost LocalShape RecursiveColumnsort RecursiveExchange
open GlobalSortingBound MainSortingParameters
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m radix

def tau : ℝ := 1-(Parameters.epsilon : ℝ)
def K : ℝ := CommonSortingExchangeRate.rateConstant 3
def boundConstant : ℝ := 22194000000*(GlobalSortingBound.rateConstant K tau+1)

theorem tau_nonneg : 0≤tau := by
  have he : (Parameters.epsilon : ℝ)<1 := by exact_mod_cast Parameters.epsilon_lt_one
  unfold tau
  linarith

theorem K_nonneg : 0≤K := CommonSortingExchangeRate.rateConstant_nonneg 3

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
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.height/q.block) :
    budget q 3 n*q.block≤22194000000*
      (localRate q.height K (Real.log ((q.height : ℝ)/q.block)) tau+2)*(n+q.block) := by
  have hb := CommonLeafProgram.block_positive q
  have hh := MainSortingParameters.normalized_memory 1 q.height q.block hb hnormal
  have hH : 0<q.height := by omega
  have ha := MainSortingParameters.normalized_log_one 1 q.height q.block hb hnormal
  let f : Fin n→KeyRecordWords.Record q.w := fun _=>⊥
  let t := (localRun q.height hH 3 n f).trace
  have hf : LocalTrace.Fits q.height 3 n t := localRun_trace_fits q.height hH 3 n f
  have hbudget := budget_trace q 3 n hn (three q.height n hH hsize) t hf
  have hwide := RecordWidthTraceCost.traceCost_bound q.block 3 q.height 3 n
    hb (by omega) (exchangeCost q) t hf
  have hx : ActualShapeSortingBound.ActualShapeRate q.block q.height K
      (Real.log ((q.height : ℝ)/q.block)) tau (exchangeCost q) :=
    CommonSortingExchangeRate.actual_shape_rate q 3 (by omega) hnormal
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
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.height/q.block) :
    (budget q 3 n : ℝ)≤boundConstant*(1+(n : ℝ)/q.block)*
      (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by
  have hb := CommonLeafProgram.block_positive q
  have hBR : (0 : ℝ)<q.block := by exact_mod_cast hb
  have hh := MainSortingParameters.normalized_memory 1 q.height q.block hb hnormal
  have hHR : (0 : ℝ)<q.height := by exact_mod_cast (show 0<q.height by omega)
  have ha := MainSortingParameters.normalized_log_one 1 q.height q.block hb hnormal
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
end CodedSorting.CommonLocalBudgetRate
end CostBound
