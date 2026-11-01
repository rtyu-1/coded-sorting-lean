import CodedSorting.Sorting.Resources.Swaps
import CodedSorting.Sorting.Local.Framework.Program

section Cost
/-! Public bounds for the actual finite-machine local sorter. Grouping
short columns avoids paying one rounded disk block for every column. -/
set_option autoImplicit false
namespace CodedSorting.Construction.Sorting.CommonLocalBudget
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
        6*CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q (LocalShape.sizeExponent n) 3+
        3*(2*recordBlocks q (s*r)+recordBlocks q ((s+1)*r)+recordBlocks q n)

def batchBudget (q : Configuration) (fuel c r : ℕ) : ℕ :=
  batchBound q (budget q fuel r) c r

theorem budget_small (q : Configuration) (fuel n : ℕ) (hn : n≤512*q.height) :
    budget q fuel n=8*recordBlocks q n+1 := by
  cases fuel <;> simp [budget,hn]

end
end CodedSorting.Construction.Sorting.CommonLocalBudget
end Cost

section ExecutionCost
/-! Comparison of the actual machine's public local budget with the trace
of the mathematical sorter it implements.  Group startup and slab scans
are absorbed here, rather than omitted from the instruction budget. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.Construction.Sorting.CommonLocalBudgetTrace
open CommonSortingNormalization CommonRecordProgram CodedSorting.Construction.Sorting.CommonLocalBudget
open CommonLocalAdmissible LocalShape RecursiveColumnsort LocalSortingCost
open CommonGroupedLeafCost
noncomputable section

def exchangeCost (q : Configuration) : InterchangeCost :=
  fun t _ => CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q t 3

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
        (6*CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q (sizeExponent n) 3) (show 1≤256+6*(fuel+1) by omega)
      have hscan : 3*(2*recordBlocks q (sizeChoice n^4)+
          recordBlocks q (sizeChoice n^4+sizeChoice n^3)+recordBlocks q n)≤
          (256+6*(fuel+1))*RecordWidthTraceCost.scanCharge q.block 3 n (sizeChoice n) := by
        simp only [recordBlocks_eq,RecordWidthTraceCost.scanCharge]
        nlinarith only [hfac]
      simp only [budget,if_neg (show ¬n≤512*q.height by omega),hrow,hvol,hshift]
      change _≤(256+6*(fuel+1))*(6*CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q (sizeExponent n) 3+
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
end CodedSorting.Construction.Sorting.CommonLocalBudgetTrace
end ExecutionCost

section RecursiveProgram
/-! The actual finite-depth local sorter. Every recursive child is built
here, all children share one allocated workspace, and all leaf batches
are implemented by grouped resident computations. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
namespace CodedSorting.Construction.Sorting.CommonLocalRecursion
open CommonSortingNormalization CommonRecordProgram CodedSorting.Construction.RecursiveParameters
open CommonLocalNode CommonLocalSemantic RecursiveColumnsort CommonLocalAdmissible
noncomputable section

/-- Only publicly bounded word descriptors are required by the margin scans. -/
def Descriptors (q : Configuration) : ℕ→ℕ→Prop
  | 0,_ => True
  | fuel+1,n => if n≤512*q.height then True else
      3*large n<(2^q.w)^q.digits ∧ Descriptors q fuel (rowCount n)

def batchSpace (q : Configuration) (c r childSpace : ℕ) : ℕ :=
  if r≤512*q.height then CommonGroupedLeafBatch.space q c r else
    c*recordBlocks q r+childSpace

def space (q : Configuration) (hnormal : Normalized q) : ℕ→ℕ→ℕ
  | 0,n => recordBlocks q n
  | fuel+1,n => if n≤512*q.height then recordBlocks q n else
      max 1 (recordBlocks q (small n))+max 1 (recordBlocks q (large n))+
        max (batchSpace q (side n) (rowCount n) (space q hnormal fuel (rowCount n)))
          (max (batchSpace q (side n+1) (rowCount n) (space q hnormal fuel (rowCount n)))
            (CodedSorting.Construction.Sorting.CommonSortingSwaps.space q (LocalShape.sizeExponent n) 3 (by omega) hnormal))

theorem height_pos (q : Configuration) : 0<q.height :=
  (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B
    q.memory_large (by have:=q.block_memory; omega)).1

theorem block_le_height (q : Configuration) : q.block≤q.height :=
  (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B
    q.memory_large (by have:=q.block_memory; omega)).2.1

def operation (q : Configuration) (fuel : ℕ) : Operation (KeyRecordWords.Record q.w) :=
  returned (localRun q.height (height_pos q) fuel)

theorem small_output (q : Configuration) (fuel n : ℕ) (hn : n≤512*q.height)
    (f : Records q n) : operation q fuel n f=Columnsort.sortColumn f := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [operation,returned,localRun,if_pos hn]

theorem small_batch (q : Configuration) (fuel c r : ℕ) (hr : r≤512*q.height) :
    CommonGroupedLeafBatch.sortColumns (q:=q) c r=batch (operation q fuel) c r := by
  funext f i
  obtain ⟨⟨j,k⟩,rfl⟩ := finProdFinEquiv.surjective i
  simp only [CommonGroupedLeafBatch.sortColumns,CommonSlabBatch.batchOutput,
    PhysicalLocalSortPadding.flattenColumns,Equiv.symm_apply_apply,batch_at,small_output q fuel r hr]

theorem blocks_positive (q : Configuration) (n : ℕ) (hn : 0<n) :
    0<recordBlocks q n := by
  have h := LayoutConversion.blockCount_covers (3*n) q.block (CommonLeafProgram.block_positive q)
  change 3*n≤PhysicalStreamCursor.blockCount q.block (3*n)*q.block at h
  rw [←CommonRecordEncoding.recordBlocks_eq_words] at h
  by_contra hz
  have he : recordBlocks q n=0 := by omega
  rw [he,Nat.zero_mul] at h
  omega


end
end CodedSorting.Construction.Sorting.CommonLocalRecursion
namespace CodedSorting.Construction.Sorting
open CommonSortingNormalization
noncomputable def concreteLocalExchange (q : Configuration) : LocalSorter.Exchange q where
  condition := CodedSorting.Construction.RecursiveParameters.Normalized q
  cost t := CodedSorting.Construction.Sorting.CommonSortingSwaps.exchangeCost q t 3
  space t hnormal := CodedSorting.Construction.Sorting.CommonSortingSwaps.space q t 3 (by omega) hnormal
  forward := CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forwardProgram q
  backward := CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backwardProgram q
  forward_bound := CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.forward_charge_le q
  backward_bound := CodedSorting.Construction.Sorting.CommonSortingSemanticSwaps.backward_charge_le q
end CodedSorting.Construction.Sorting
namespace CodedSorting.Construction.Sorting.CommonLocalRecursion
noncomputable section
abbrev batchBuild := LocalSorter.batchBuild
def build := LocalSorter.build concreteLocalExchange
end
end CodedSorting.Construction.Sorting.CommonLocalRecursion
end RecursiveProgram

section Program
namespace CodedSorting.Construction.Sorting.CommonLocalMachine
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CodedSorting.Construction.Sorting.CommonLocalRecursion CommonLocalAdmissible CodedSorting.Construction.RecursiveParameters
open CommonLeafProgram (Machine)
noncomputable section
abbrev operation_eq_sortColumn := LocalSorter.Machine.operation_eq_sortColumn
abbrev program := LocalSorter.Machine.program concreteLocalExchange
abbrev program_charge_le := LocalSorter.Machine.program_charge_le concreteLocalExchange
abbrev complete := LocalSorter.Machine.complete concreteLocalExchange
def localProgram := LocalSorter.Machine.localProgram concreteLocalExchange
theorem local_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal 3 n≤limit) (hl : limit≤q.N^q.exponent) :
    (localProgram q reader hnormal n hn he source buffer limit hs hw hl).charge≤
      CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 n :=
  LocalSorter.Machine.local_charge_le concreteLocalExchange q reader hnormal n hn he source buffer limit hs hw hl
theorem local_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal 3 n≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 n≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := localProgram q reader hnormal n hn he source buffer limit hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    Encoded q result.1.disk source (Columnsort.sortColumn f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    result.2≤CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 n ∧
    Fintype.card (ResidentIndex q)≤q.M :=
  LocalSorter.Machine.local_complete concreteLocalExchange q reader hnormal n hn he source buffer limit hs hw hl s f hf hsize hpc
end
end CodedSorting.Construction.Sorting.CommonLocalMachine
end Program
