import CodedSorting.Sorting.Local.CostBound
import CodedSorting.Sorting.Radix.Framework.Chunks

section Chunks
/-! Sort every public H²-sized chunk on the common finite machine.
The final partial chunk receives top padding; real margin scans add and
remove this padding. Every slab invokes the verified local program. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
namespace CodedSorting.Construction.Sorting.CommonMSDChunks
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonSlabBatch CodedSorting.Construction.RecursiveParameters
open CommonLeafProgram (Machine)
noncomputable section
attribute [local irreducible] CodedSorting.Construction.Sorting.CommonLocalRecursion.build
  ControlledNormalization.runLogical

def chunkSize (q : Configuration) : ℕ := q.height^2
def chunkCount (q : Configuration) (n : ℕ) : ℕ :=
  PhysicalStreamCursor.blockCount (chunkSize q) n
def paddedSize (q : Configuration) (n : ℕ) : ℕ := chunkCount q n*chunkSize q

theorem chunk_positive (q : Configuration) : 0<chunkSize q :=
  Nat.pow_pos (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q)

theorem padded_covers (q : Configuration) (n : ℕ) : n≤paddedSize q n :=
  LayoutConversion.blockCount_covers n (chunkSize q) (chunk_positive q)

def operation (q : Configuration) (n : ℕ) : Records q n→Records q n :=
  CommonRecordTopPrefix.operation (padded_covers q n)
    (batchOutput (C:=chunkCount q n) (r:=chunkSize q) Columnsort.sortColumn)

def space (q : Configuration) (hnormal : Normalized q) (n : ℕ) : ℕ :=
  max 1 (recordBlocks q (paddedSize q n))+
    chunkCount q n*recordBlocks q (chunkSize q)+
    CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 (chunkSize q)

def charge (q : Configuration) (n : ℕ) : ℕ :=
  3*recordBlocks q (paddedSize q n)+
    chunkCount q n*(CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (chunkSize q)+12*recordBlocks q (chunkSize q))+
    3*recordBlocks q n

def batchProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (C : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+recordBlocks q (C*chunkSize q)≤buffer)
    (hw : buffer+C*recordBlocks q (chunkSize q)+
      CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 (chunkSize q)≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (C*chunkSize q) source buffer limit (batchOutput Columnsort.sortColumn) := by
  let R := chunkSize q
  let work := buffer+C*recordBlocks q R
  have hwork : work+CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 R≤limit := hw
  have hpos : 0<recordBlocks q R :=
    CodedSorting.Construction.Sorting.CommonLocalRecursion.blocks_positive q R (chunk_positive q)
  let kids : Children q C R buffer work limit Columnsort.sortColumn := fun c =>
    CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram q reader hnormal R le_rfl he
      (recordBase q R buffer c.val) work limit
      (by
        rw [max_eq_right hpos]
        have h := base_end q (C:=C) (n:=R*3) (buffer:=buffer) c
        simpa only [←record_blocks,work] using h)
      hwork hl
  exact CommonSlabBatch.program reader kids hs
    (by dsimp only [work]; rw [record_blocks]) (by omega) hl

theorem batchProgram_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (C : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+recordBlocks q (C*chunkSize q)≤buffer)
    (hw : buffer+C*recordBlocks q (chunkSize q)+
      CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 (chunkSize q)≤limit)
    (hl : limit≤q.N^q.exponent) :
    (batchProgram q reader hnormal C he source buffer limit hs hw hl).charge≤
      C*(CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (chunkSize q)+12*recordBlocks q (chunkSize q)) := by
  unfold batchProgram
  simp only [CommonSlabBatch.program]
  have hsum : ∀ (p : Children q C (chunkSize q) buffer
      (buffer+C*recordBlocks q (chunkSize q)) limit Columnsort.sortColumn),
      (∀ c,(p c).charge≤CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (chunkSize q)) →
      childrenCharge p (List.finRange C)≤C*CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (chunkSize q) := by
    intro p hp
    unfold childrenCharge
    calc
      _ ≤ ((List.finRange C).map (fun _=>CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (chunkSize q))).sum := by
        apply List.sum_le_sum
        intro i hi
        exact hp i
      _ = C*CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (chunkSize q) := by simp
  refine (Nat.add_le_add_right (hsum _ ?_) _).trans ?_
  · intro c
    exact CodedSorting.Construction.Sorting.CommonLocalMachine.local_charge_le q reader hnormal
      (chunkSize q) le_rfl he _ _ _ _ hw hl
  · rw [←record_blocks]
    exact le_of_eq (by ring)

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*paddedSize q n<(2^q.w)^q.digits) :
    Program q n source buffer limit (operation q n) := by
  let slabs := buffer+max 1 (recordBlocks q (paddedSize q n))
  have hslabs : slabs+chunkCount q n*recordBlocks q (chunkSize q)+
      CodedSorting.Construction.Sorting.CommonLocalRecursion.space q hnormal 3 (chunkSize q)≤limit := by
    simpa only [slabs,space,Nat.add_assoc] using hw
  let inner := batchProgram q reader hnormal (chunkCount q n) he buffer slabs limit
    (by
      change buffer+recordBlocks q (paddedSize q n)≤buffer+max 1 (recordBlocks q (paddedSize q n))
      omega) hslabs hl
  exact CommonRecordTopPrefix.program q reader (padded_covers q n) inner hs
    le_rfl (by omega) hl hshape

theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*paddedSize q n<(2^q.w)^q.digits) :
    (program q reader hnormal n he source buffer limit hs hw hl hshape).charge≤charge q n := by
  unfold program
  rw [CommonRecordTopPrefix.program_charge]
  have h := batchProgram_charge_le q reader hnormal (chunkCount q n) he buffer
    (buffer+max 1 (recordBlocks q (paddedSize q n))) limit (by
      change buffer+recordBlocks q (paddedSize q n)≤buffer+max 1 (recordBlocks q (paddedSize q n))
      omega)
    (by simpa only [space,Nat.add_assoc] using hw) hl
  unfold charge
  exact Nat.add_le_add_right (Nat.add_le_add_left h _) _

/-- Correct chunk output, preservation, termination and charged transfers
describe the same actual machine run. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*paddedSize q n<(2^q.w)^q.digits)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : charge q n≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader hnormal n he source buffer limit hs hw hl hshape
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    Encoded q result.1.disk source (operation q n f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧ result.2≤charge q n ∧
    Fintype.card (ResidentIndex q)≤q.M :=
  by
    let p := program q reader hnormal n he source buffer limit hs hw hl hshape
    have hc : p.charge≤charge q n :=
      program_charge_le q reader hnormal n he source buffer limit hs hw hl hshape
    obtain ⟨hout,hframe,hhalt,hcost,hram⟩ :=
      CommonRecordProgram.complete q p s f hf (hc.trans hsize) hpc
    exact ⟨hout,hframe,hhalt,hcost.trans hc,hram⟩

end
end CodedSorting.Construction.Sorting.CommonMSDChunks
end Chunks

section ChunkCost
/-! Scan overhead and the final short chunk preserve the proved local
sorting rate. This bounds the charge of the actual common-machine program. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace CodedSorting.Construction.Sorting.CommonMSDChunks
open CommonSortingNormalization CommonRecordProgram
open CommonGroupedLeafCost CodedSorting.Construction.Sorting.CommonLocalBudgetRate
noncomputable section

theorem padded_size_le (q : Configuration) (n : ℕ) :
    paddedSize q n≤n+chunkSize q := by
  exact LocalSortingCost.blockCount_capacity (chunkSize q) (chunk_positive q) n

theorem block_le_chunk (q : Configuration) : q.block≤chunkSize q := by
  have hh := CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q
  have hb := CodedSorting.Construction.Sorting.CommonLocalRecursion.block_le_height q
  dsimp only [chunkSize]
  nlinarith

theorem charge_bound_of_local (q : Configuration) (n L : ℕ)
    (hn : chunkSize q≤n)
    (hlocal : CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (chunkSize q)*q.block≤L*(chunkSize q+q.block)) :
    charge q n*q.block≤(4*L+129)*n := by
  let C := chunkCount q n
  let R := chunkSize q
  let M := paddedSize q n
  have hpad : C*R≤2*n := by
    have h := padded_size_le q n
    change C*R≤n+R at h
    omega
  have hBR : q.block≤R := block_le_chunk q
  have hBn : q.block≤n := hBR.trans hn
  have hc : recordBlocks q R*q.block≤3*R+q.block := by
    rw [recordBlocks_eq]
    exact LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) _
  have hchunk : C*recordBlocks q R*q.block≤8*n := by
    have h := Nat.mul_le_mul_left C hc
    have h' := Nat.mul_le_mul_left C hBR
    nlinarith only [h,h',hpad]
  have hpm : recordBlocks q M*q.block≤7*n := by
    have h := LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) (3*M)
    rw [←recordBlocks_eq] at h
    change recordBlocks q M*q.block≤3*(C*R)+q.block at h
    omega
  have hin : recordBlocks q n*q.block≤4*n := by
    have h := LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) (3*n)
    rw [←recordBlocks_eq] at h
    omega
  have hkids : C*CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 R*q.block≤4*L*n := by
    have h := Nat.mul_le_mul_left C hlocal
    have h' := Nat.mul_le_mul_left C hBR
    have h'' := Nat.mul_le_mul_left L (show C*(R+q.block)≤4*n by nlinarith only [h',hpad])
    change C*(CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 R*q.block)≤C*(L*(R+q.block)) at h
    nlinarith only [h,h'']
  change (3*recordBlocks q M+C*(CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 R+12*recordBlocks q R)+
    3*recordBlocks q n)*q.block≤_
  nlinarith only [hpm,hchunk,hin,hkids]

/-- Uniform actual preparation charge per record at an MSD node larger
than the local threshold. -/
theorem integer_charge_bound (q : Configuration) (n : ℕ)
    (hn : chunkSize q≤n)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block) :
    charge q n*q.block≤
      (4*(22194000000*(GlobalSortingBound.localRate q.height K
        (Real.log ((q.height : ℝ)/q.block)) tau+2))+129)*n := by
  apply charge_bound_of_local q n _ hn
  exact CodedSorting.Construction.Sorting.CommonLocalBudgetRate.integer_bound q (chunkSize q) (chunk_positive q) le_rfl hnormal

end
end CodedSorting.Construction.Sorting.CommonMSDChunks
end ChunkCost

section SemanticCost
/-! Cost composition for recursive sorting by successive groups of key digits. The local-sort and preparation costs come from the common-machine programs; the gather cost is an explicit parameter of the composition theorem. 


-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.Construction.Sorting.CommonMSDSemanticCost
open CommonMSDSemantics ExternalMSD BucketMachine
variable {α : Type*}

/-- This accounting follows the very child lists of `CommonMSDSemantics.sort`.
`nodeCharge` covers preparation and gathering at each nonterminal node. -/
def budget (key : α → ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α → List α) (localCharge nodeCharge : ℕ → ℕ) :
    ℕ → List α → ℕ
  | 0,_ => 0
  | fuel+1,xs =>
      if xs.length≤H^2 then localCharge xs.length
      else nodeCharge xs.length+
        ((List.finRange base).map fun k =>
          budget key base hb H hH localSort localCharge nodeCharge fuel
            (child (CommonMSDSemantics.digit key base hb fuel)
              (CommonMSDSemantics.prepare H hH localSort xs) k)).sum

private theorem sum_affine_bound {β : Type*} (items : List β)
    (f size : β → ℕ) (B C D : ℕ)
    (h : ∀ x∈items,f x*B≤C*size x+D) :
    (items.map f).sum*B≤C*(items.map size).sum+D*items.length := by
  induction items with
  | nil => simp
  | cons x rest ih =>
    have hx := h x (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- One startup allowance per child is absorbed by `base*B≤H²<n`.
No scan bound is inserted for the overall recursion. -/
theorem budget_depth_bound (key : α → ℕ) (base : ℕ) (hb : 0<base)
    (B H : ℕ) (hH : 0<H) (hBH : B≤H) (hbase : base≤H)
    (localSort : List α → List α) (hc : LocalCorrect key localSort)
    (localCharge nodeCharge : ℕ → ℕ) (L A : ℕ)
    (hl : ∀ n,n≤H^2 → localCharge n*B≤L*(n+B))
    (ha : ∀ n,H^2<n → nodeCharge n*B≤A*n)
    (fuel : ℕ) (xs : List α) :
    budget key base hb H hH localSort localCharge nodeCharge fuel xs*B≤
      ((A+L)*fuel+L)*xs.length+L*B := by
  induction fuel generalizing xs with
  | zero => simp [budget]
  | succ fuel ih =>
    rw [budget]
    split
    · rename_i hsmall
      have hh := hl xs.length hsmall
      have hm := Nat.mul_le_mul_right xs.length
        (show L≤(A+L)*(fuel+1)+L by omega)
      nlinarith only [hh,hm]
    · rename_i hlarge
      have hnode := ha xs.length (by omega)
      have hKB : base*B≤xs.length := by
        have hmul := Nat.mul_le_mul hbase hBH
        nlinarith only [hmul,show H^2<xs.length by omega]
      have hchildren := sum_affine_bound (List.finRange base)
        (fun k => budget key base hb H hH localSort localCharge nodeCharge fuel
          (child (CommonMSDSemantics.digit key base hb fuel)
            (CommonMSDSemantics.prepare H hH localSort xs) k))
        (fun k => (child (CommonMSDSemantics.digit key base hb fuel)
          (CommonMSDSemantics.prepare H hH localSort xs) k).length)
        B ((A+L)*fuel+L) (L*B) (fun k _ => ih _)
      rw [children_volume,(CommonMSDSemantics.prepare_perm key H hH localSort hc xs).length_eq,
        List.length_finRange] at hchildren
      have hstart := Nat.mul_le_mul_left L hKB
      nlinarith only [hnode,hchildren,hstart]

open CommonSortingNormalization
noncomputable section

/-- Exactly the integer local rate established for the actual Round-14
machine, with its three-word records and all movement overhead. -/
def localRate (q : Configuration) : ℕ :=
  22194000000*(GlobalSortingBound.localRate q.height CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K
    (Real.log ((q.height : ℝ)/q.block)) CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau+2)

theorem actual_local_charge (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (n : ℕ) (hn : n≤q.height^2) :
    CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 n*q.block≤localRate q*(n+q.block) := by
  by_cases hz : n=0
  · subst n
    rw [CodedSorting.Construction.Sorting.CommonLocalBudget.budget_small q 3 0 (Nat.zero_le _)]
    have he : CommonRecordProgram.recordBlocks q 0=0 := by
      rw [CommonRecordEncoding.recordBlocks_eq_words]
      simp [PhysicalStreamCursor.blockCount,CommonLeafProgram.block_positive q]
    rw [he]
    have hL : 1≤localRate q := by unfold localRate; omega
    simpa using Nat.mul_le_mul_right q.block hL
  · exact CodedSorting.Construction.Sorting.CommonLocalBudgetRate.integer_bound q n (by omega) hn hnormal

/-- Actual chunk preparation plus a separately verified gather charge has
one linear nonterminal budget. The gather implementation is not assumed here. -/
theorem actual_node_charge (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (gatherCharge : ℕ → ℕ) (G : ℕ)
    (hg : ∀ n,q.height^2<n → gatherCharge n*q.block≤G*n)
    (n : ℕ) (hn : q.height^2<n) :
    (CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n+gatherCharge n)*q.block≤(4*localRate q+129+G)*n := by
  have hprep := CodedSorting.Construction.Sorting.CommonMSDChunks.integer_charge_bound q n (by exact Nat.le_of_lt hn) hnormal
  have hgat := hg n hn
  change CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n*q.block≤(4*localRate q+129)*n at hprep
  nlinarith only [hprep,hgat]

/-- This is a bound for the semantic recursion using the actual local and
preparation budgets. Connecting the remaining gather/controller execution
is still required before interpreting it as a complete machine theorem. -/
theorem actual_budget_depth (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (gatherCharge : ℕ → ℕ) (G : ℕ)
    (hg : ∀ n,q.height^2<n → gatherCharge n*q.block≤G*n)
    (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) :
    budget CommonWordMSD.key q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q)
      q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
      (CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3) (fun n => CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n+gatherCharge n)
      fuel xs*q.block≤
      ((5*localRate q+129+G)*fuel+localRate q)*xs.length+localRate q*q.block := by
  have h := budget_depth_bound CommonWordMSD.key q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q)
    q.block q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q)
    (CodedSorting.Construction.Sorting.CommonLocalRecursion.block_le_height q) le_rfl CommonWordMSD.localSort
    (record_local_correct q.w) (CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3)
    (fun n => CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n+gatherCharge n)
    (localRate q) (4*localRate q+129+G)
    (actual_local_charge q hnormal) (actual_node_charge q hnormal gatherCharge G hg) fuel xs
  have he : 4*localRate q+129+G+localRate q=5*localRate q+129+G := by ring
  simpa only [he] using h

end
end CodedSorting.Construction.Sorting.CommonMSDSemanticCost
end SemanticCost
