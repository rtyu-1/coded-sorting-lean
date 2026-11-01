import CodedSorting.Sorting.Local.Framework.PhysicalLocalSortNode
import CodedSorting.Sorting.Local.Framework.LocalSortingCost
import CodedSorting.Shared.Records.RecordOperations

/-! Record-level semantics of the local Columnsort node.  The stages below
consume the actual preceding record array.  They do not assert that a
child implementation exists, and they introduce no additional sorting
operation between the four child batches. -/
set_option autoImplicit false

namespace CodedSorting.CommonLocalSemantic
open RecursiveColumnsort PhysicalLocalSortNode PhysicalLocalSortPadding
open PhysicalLocalSortLayout PhysicalLocalSortInverse
open PhysicalLocalSortTranspose

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

abbrev Operation (α : Type*) := ∀ n : ℕ, (Fin n → α) → Fin n → α

/-- A view of the same consecutive records, without data movement. -/
def columns (c r : ℕ) (f : Fin (c*r) → α) : Fin c → Fin r → α :=
  fun j i => f (finProdFinEquiv (j,i))

@[simp] theorem flatten_columns (c r : ℕ) (f : Fin (c*r) → α) :
    flattenColumns c r (columns c r f)=f := by
  funext i
  exact congrArg f (Equiv.apply_symm_apply finProdFinEquiv i)

@[simp] theorem columns_flatten (c r : ℕ) (f : Fin c → Fin r → α) :
    columns c r (flattenColumns c r f)=f := by
  funext j i
  simp only [columns,flattenColumns,Equiv.symm_apply_apply]

/-- Invoke the child operation once on each consecutive column. -/
def batch (op : Operation α) (c r : ℕ) (f : Fin (c*r) → α) : Fin (c*r) → α :=
  flattenColumns c r (fun j => op r (columns c r f j))

@[simp] theorem batch_at (op : Operation α) (c r : ℕ) (f : Fin (c*r) → α)
    (j : Fin c) (i : Fin r) :
    batch op c r f (finProdFinEquiv (j,i))=op r (columns c r f j) i := by
  simp only [batch,flattenColumns,Equiv.symm_apply_apply]

def forward (s : ℕ) (f : Fin (s*rows s) → α) : Fin (s*(s*(s^2*1))) → α :=
  flattenColumns s (s*(s^2*1)) (secondInput (s^2) s (columns s (rows s) f))

def backward (s : ℕ) (f : Fin (s*(s*(s^2*1))) → α) : Fin (s*rows s) → α :=
  flattenColumns s (rows s) (thirdColumns s (columns s (s*(s^2*1)) f))

theorem forward_fields (s : ℕ) (f : Fin (s*rows s) → α) (x : ColumnsortExchange.Fields s) :
    forward s f (finCongr (show s^4=s*(s*(s^2*1)) by ring) (ColumnsortExchange.encode s x))=
      f (finCongr (show s^4=s*rows s by unfold rows; ring)
        (ColumnsortExchange.encode s ((ColumnsortExchange.forward s).symm x))) := by
  dsimp only [rows] at f ⊢
  rw [← secondColumn_address]
  simp only [forward,flattenColumns,Equiv.symm_apply_apply]
  unfold secondRow
  rw [ColumnsortExchange.secondInput_source]
  rw [← firstColumn_address s ((ColumnsortExchange.forward s).symm x)]
  unfold columns
  apply congrArg f
  apply congrArg finProdFinEquiv
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change (x.2.2.2.val+s*x.2.2.1.val)*s+x.1.val=
      x.1.val+s*(x.2.2.2.val+s*x.2.2.1.val)
    ring

theorem backward_fields (s : ℕ) (f : Fin (s*(s*(s^2*1))) → α)
    (x : ColumnsortExchange.Fields s) :
    backward s f (finCongr (show s^4=s*rows s by unfold rows; ring)
      (ColumnsortExchange.encode s x))=
      f (finCongr (show s^4=s*(s*(s^2*1)) by ring)
        (ColumnsortExchange.encode s (ColumnsortExchange.forward s x))) := by
  dsimp only [rows] at f ⊢
  rw [← firstColumn_address s x]
  simp only [backward,flattenColumns,Equiv.symm_apply_apply,thirdColumns]
  have ht := afterTwoTape_at (s^2) s (columns s (s*(s^2*1)) f) (prefixThree s x) x.2.2.2
  have hi : (0 : ℤ)+(x.1 : ℤ)*((s^2*s*1 : ℕ) : ℤ)+(firstRow s x : ℤ)=
      ((finProdFinEquiv (prefixThree s x,finProdFinEquiv (x.2.2.2,(0 : Fin 1)))) :
        Fin (s*s^2*(s*1))) := by
    change (0 : ℤ)+(x.1 : ℤ)*(s^2*s*1)+
      ((x.2.2.2.val+s*(x.2.2.1.val+s*x.2.1.val) : ℕ) : ℤ)=
      (((0+1*x.2.2.2.val)+(s*1)*((x.2.2.1.val+s*x.2.1.val)+s^2*x.1.val) : ℕ) : ℤ)
    push_cast
    ring
  unfold gridInput
  simp only [Equiv.symm_apply_apply,rows]
  rw [hi,ht,← secondColumn_address s (ColumnsortExchange.forward s x)]
  unfold columns
  apply congrArg f
  apply congrArg finProdFinEquiv
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change (x.2.2.1.val+s*x.2.1.val)+s^2*x.1.val=
      (x.2.2.1.val+s*x.2.1.val)+(s^2*1)*x.1.val
    ring

theorem forward_index (s : ℕ) (f : Fin (s*rows s) → α) (i : Fin (s^4)) :
    forward s f (finCongr (show s^4=s*(s*(s^2*1)) by ring) i)=
      f (finCongr (show s^4=s*rows s by unfold rows; ring)
        ((ColumnsortExchange.transpose s).symm i)) := by
  have ht := forward_fields s f ((ColumnsortExchange.encode s).symm i)
  simpa only [Equiv.apply_symm_apply,ColumnsortExchange.transpose,Equiv.symm_trans_apply,
    Equiv.trans_apply,Equiv.symm_symm] using ht

theorem backward_index (s : ℕ) (f : Fin (s*(s*(s^2*1))) → α) (i : Fin (s^4)) :
    backward s f (finCongr (show s^4=s*rows s by unfold rows; ring) i)=
      f (finCongr (show s^4=s*(s*(s^2*1)) by ring) (ColumnsortExchange.transpose s i)) := by
  have ht := backward_fields s f ((ColumnsortExchange.encode s).symm i)
  simpa only [Equiv.apply_symm_apply,ColumnsortExchange.transpose,Equiv.trans_apply] using ht

/-- Insert half a column of bottom and top sentinels on the two sides. -/
def shift (s r h : ℕ) (f : Fin (s*r) → α) : Fin ((s+1)*r) → α :=
  flattenColumns (s+1) r (fourthInput s r h (columns s r f))

/-- Retain the middle after the final child batch. -/
def unshift (s r h : ℕ) (f : Fin ((s+1)*r) → α) : Fin (s*r) → α :=
  unshiftedRecords s r h (columns (s+1) r f)

theorem shift_list (s r h : ℕ) (hr : r=2*h) (f : Fin (s*r) → α) :
    List.ofFn (shift s r h f)=
      List.replicate h (⊥ : α)++List.ofFn f++List.replicate h (⊤ : α) := by
  unfold shift
  rw [fourth_flatten,shifted_records s r h hr,flatten_columns]

theorem shift_at (s r h : ℕ) (f : Fin (s*r) → α) (i : Fin ((s+1)*r)) :
    shift s r h f i=if hl : i.val<h then ⊥ else
      if hu : i.val<h+s*r then f ⟨i.val-h,by omega⟩ else ⊤ := by
  unfold shift
  rw [fourth_flatten]
  change gridTape s r 0 (columns s r f) (-(h : ℤ)+(i : ℤ))=_
  split_ifs with hl hu
  · exact (gridTape_bounds s r 0 (columns s r f)).1 _ (by omega)
  · let j : Fin (s*r) := ⟨i.val-h,by omega⟩
    have he : -(h : ℤ)+(i : ℤ)=0+(j : ℤ) := by dsimp [j]; omega
    rw [he,gridTape_at_fin]
    exact congrArg f (Equiv.apply_symm_apply finProdFinEquiv j)
  · exact (gridTape_bounds s r 0 (columns s r f)).2 _ (by omega)

theorem unshift_at (s r h : ℕ) (hr : r=2*h) (f : Fin ((s+1)*r) → α)
    (i : Fin (s*r)) :
    unshift s r h f i=f ⟨h+i.val,by
      have hi := i.isLt
      have hh : h≤r := by omega
      nlinarith⟩ := by
  unfold unshift
  rw [unshifted_at s r h hr,flatten_columns]
  apply congrArg f
  apply Fin.ext
  simp only [Fin.coe_cast,Fin.coe_castAdd,Fin.coe_natAdd]

theorem rows_eq_columnLength (n : ℕ) : rows (LocalShape.sizeChoice n)=LocalShape.columnLength n := by
  unfold rows LocalShape.columnLength
  ring

theorem second_rows_eq_columnLength (n : ℕ) :
    LocalShape.sizeChoice n*(LocalShape.sizeChoice n^2*1)=LocalShape.columnLength n := by
  unfold LocalShape.columnLength
  ring

theorem padded_size (n : ℕ) : n≤LocalShape.sizeChoice n*rows (LocalShape.sizeChoice n) := by
  have h := LocalShape.padding_ge n
  convert h using 1 <;> unfold rows <;> ring

/-- The complete node in serialized record order: padding, four child
batches, the two transposes and the half-column shift, then both trims. -/
def pipeline (op : Operation α) (n : ℕ) (f : Fin n → α) : Fin n → α :=
  let s := LocalShape.sizeChoice n
  let r := rows s
  let h := LocalShape.columnLength n/2
  let padded := pad (N:=s*r) f
  let first := batch op s r padded
  let second := batch op s (s*(s^2*1)) (forward s first)
  let third := batch op s r (backward s second)
  let fourth := batch op (s+1) r (shift s r h third)
  trim (padded_size n) (unshift s r h fourth)

abbrev returned (sorter : Sorter α) : Operation α := fun n f => (sorter n f).output

/-- The machine-facing stage sequence is precisely the pre-existing node
algorithm, rather than a second independently specified sorting function. -/
theorem pipeline_nodeRun (sorter : Sorter α) (n : ℕ) (f : Fin n → α) :
    pipeline (returned sorter) n f=(nodeRun sorter n f).output := by
  simp only [pipeline,batch,forward,backward,shift,unshift,columns_flatten]
  rfl

/-- Correct child calls are the sole semantic hypothesis for this node. -/
theorem pipeline_correct (sorter : Sorter α)
    (hc : ∀ n (f : Fin n → α), Correct f (sorter n f).output)
    (n H : ℕ) (hH : 0<H) (hn : 512*H<n) (f : Fin n → α) :
    Correct f (pipeline (returned sorter) n f) := by
  rw [pipeline_nodeRun]
  exact nodeRun_correct sorter hc n H hH hn f

/-- All actual leaves of the existing three-level recursion respect the
same resident cutoff. This includes fuel-zero leaves. -/
theorem local_three_level_leaves (H : ℕ) (hH : 0<H) (n : ℕ) (hn : n≤H^2)
    (f : Fin n → α) :
    LocalSortingCost.leavesFit H (localRun H hH 3 n f).trace :=
  LocalSortingCost.three_level_leaves_fit hH hn (localRun_trace_fits H hH 3 n f)

end CodedSorting.CommonLocalSemantic
