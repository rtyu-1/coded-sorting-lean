import CodedSorting.Shared.Memory.IntervalAdapter
import CodedSorting.Sorting.Local.Framework.Program

section Local
/-! Actual local sorting of a packed, possibly block-unaligned MSD bucket.
The program extracts the records, runs the constructed three-level local
sorter, and reinserts the result while preserving neighboring records. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
namespace CodedSorting.CommonMSDIntervalLocal
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonRecordInterval (EncodedAt)
open CommonLocalRecursion CommonPrunedParameters
open CommonLeafProgram (Machine)
open CommonMarginTransform (wordAt)
noncomputable section
attribute [local irreducible] CommonLocalMachine.localProgram
  ControlledNormalization.runLogical

def space (q : Configuration) (hnormal : Normalized q) (n : ℕ) : ℕ :=
  recordBlocks q n+2+CommonLocalRecursion.space q hnormal 3 n

def charge (q : Configuration) (n : ℕ) : ℕ :=
  CommonLocalBudget.budget q 3 n+12*(recordBlocks q n+1)

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (base O buffer limit : ℕ)
    (hs : base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)+2≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent) :
    CommonRecordInterval.Program q n base O buffer limit Columnsort.sortColumn := by
  let work := buffer+recordBlocks q n+2
  have hlocal : work+CommonLocalRecursion.space q hnormal 3 n≤limit := by
    simpa only [work,space,Nat.add_assoc] using hw
  let p := CommonLocalMachine.localProgram q reader hnormal n hn he buffer work limit
    (by dsimp [work];omega) hlocal hl
  have hf : CommonIntervalAdapter.Fits q n base O buffer work limit :=
    ⟨hs,le_rfl,by omega,hl⟩
  let adapted := CommonIntervalAdapter.program q reader p hf
  have hcharge : adapted.charge≤charge q n := by
    have hx := CommonIntervalAdapter.charge_le q n O p.charge
    have hp := CommonLocalMachine.local_charge_le q reader hnormal n hn he buffer work limit
      (by dsimp [work];omega) hlocal hl
    exact hx.trans (Nat.add_le_add_right hp _)
  exact {adapted with
    charge := charge q n
    cost_le := adapted.cost_le.trans hcharge
    length_le := adapted.length_le.trans hcharge}

@[simp] theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (base O buffer limit : ℕ)
    (hs : base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)+2≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent) :
    (program q reader hnormal n hn he base O buffer limit hs hw hl).charge=charge q n := rfl

/-- The output is an actual sorted permutation of the interval. Correctness,
boundary preservation, halt and the transfer bound refer to the same run. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (base O buffer limit : ℕ)
    (hs : base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)+2≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q n) (hf : EncodedAt q s.disk base O f)
    (hsize : charge q n≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader hnormal n hn he base O buffer limit hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    EncodedAt q result.1.disk base O (Columnsort.sortColumn f) ∧
    Monotone (Columnsort.sortColumn f) ∧
    (List.ofFn (Columnsort.sortColumn f)).Perm (List.ofFn f) ∧
    (∀ j,base+j/q.block<q.N^q.exponent → (j<3*O ∨ 3*O+3*n≤j) →
      (base+j/q.block<buffer ∨ limit≤base+j/q.block) →
      wordAt q result.1.disk base j=wordAt q s.disk base j) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<base+3*O/q.block ∨ base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧ result.2≤charge q n ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  let p := program q reader hnormal n hn he base O buffer limit hs hw hl
  obtain ⟨hc,hwf,hdf,hh,hcost,hram⟩ := CommonRecordInterval.complete q p s f hf hsize hpc
  exact ⟨hc,Columnsort.sortColumn_monotone f,Columnsort.sortColumn_perm f,hwf,hdf,hh,hcost,hram⟩

end
end CodedSorting.CommonMSDIntervalLocal
end Local

section LocalRate
/-! Transporting a local sorter to an unaligned bucket changes only the
constant in its improved I/O bound. Both copies are included in the charge. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.CommonMSDIntervalLocalRate
open CommonSortingNormalization CommonRecordProgram CommonMSDIntervalLocal
open RecursiveExchange
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m radix

def boundConstant : ℝ := CommonLocalBudgetRate.boundConstant+36

theorem transport_scaled (q : Configuration) (n : ℕ) :
    (12*(recordBlocks q n+1))*q.block≤36*(n+q.block) := by
  have h := LocalSortingCost.blockCount_capacity q.block
    (CommonLeafProgram.block_positive q) (3*n)
  change PhysicalStreamCursor.blockCount q.block (3*n)*q.block≤3*n+q.block at h
  rw [←CommonRecordEncoding.recordBlocks_eq_words] at h
  nlinarith

theorem transport_bound (q : Configuration) (n : ℕ) :
    ((12*(recordBlocks q n+1) : ℕ) : ℝ)≤36*(1+(n : ℝ)/q.block) := by
  have hb : (0 : ℝ)<q.block := by exact_mod_cast CommonLeafProgram.block_positive q
  have h : ((12*(recordBlocks q n+1) : ℕ) : ℝ)*(q.block : ℝ)≤36*((n : ℝ)+q.block) := by
    exact_mod_cast transport_scaled q n
  have he : 36*(1+(n : ℝ)/q.block)*(q.block : ℝ)=36*((n : ℝ)+q.block) := by
    field_simp
    ring
  apply (mul_le_mul_iff_of_pos_right hb).mp
  rw [he]
  exact h

theorem improved_bound (q : Configuration) (n : ℕ) (hn : 0<n) (hlocal : n≤q.height^2)
    (hnormal : PhysicalLeafParameters.minimumRatio radix 1 Parameters.W≤q.height/q.block) :
    (charge q n : ℝ)≤boundConstant*(1+(n : ℝ)/q.block)*
      (1+(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^CommonLocalBudgetRate.tau) := by
  have hc := CommonLocalBudgetRate.improved_bound q n hn hlocal hnormal
  have hx := transport_bound q n
  have hb := CommonLeafProgram.block_positive q
  have hlog := MainSortingParameters.normalized_log_one 1 q.height q.block hb hnormal
  have hlogn : 0≤Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hp : 0≤(Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^CommonLocalBudgetRate.tau :=
    Real.rpow_nonneg (div_nonneg hlogn (by linarith)) _
  have ha : 0≤36*(1+(n : ℝ)/q.block) := by positivity
  have he := mul_le_mul_of_nonneg_left (show 1≤1+
      (Real.log (n : ℝ)/Real.log ((q.height : ℝ)/q.block))^CommonLocalBudgetRate.tau by linarith) ha
  simp only [mul_one] at he
  unfold charge
  push_cast
  push_cast at hx
  unfold boundConstant
  nlinarith only [hc,hx,he]

end
end CodedSorting.CommonMSDIntervalLocalRate
end LocalRate
