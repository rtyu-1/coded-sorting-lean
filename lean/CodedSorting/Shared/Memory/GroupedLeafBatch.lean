import CodedSorting.Shared.Memory.Leaf.Grouping
import CodedSorting.Interchange.Framework.Memory.SlabBatch
import CodedSorting.Interchange.Framework.Resident.RecordProgram

section GroupedLeafCost
/-! The complete scan charge of the concrete grouped leaf, including
padding, resident groups, slab split/join, and prefix restoration. -/
set_option autoImplicit false
namespace CodedSorting.CommonGroupedLeafCost
open CommonSortingNormalization CommonRecordProgram CommonLeafGrouping

theorem recordBlocks_eq (q : Configuration) (n : ℕ) :
    recordBlocks q n=LocalSortingCost.blockCount q.block (3*n) := by
  rw [CommonSlabBatch.record_blocks]
  simp only [CommonSlabBatch.stride,PhysicalStreamCursor.blockCount,
    LocalSortingCost.blockCount,Nat.mul_comm n 3]

theorem grouped_bound (q : Configuration) (c r : ℕ) (hBH : q.block≤q.height)
    (hr : r≤512*q.height) (hlarge : 512*q.height<c*r) :
    let cap := 512*q.height
    let g := groupRecords cap r
    let ng := groups cap r c
    let pad := paddedRecords cap r c
    12*recordBlocks q (c*r)+3*recordBlocks q pad+
      ng*(8*recordBlocks q g+1)+12*(ng*recordBlocks q g)≤
        256*(recordBlocks q (c*r)+1) := by
  dsimp only
  simp only [recordBlocks_eq]
  have h := grouped_charge_le (CommonLeafProgram.block_positive q)
    (rows_pos hlarge) hr (by omega : 2*q.block≤512*q.height) hlarge.le 20 3 12
  nlinarith only [h]

end CodedSorting.CommonGroupedLeafCost
end GroupedLeafCost

section GroupedLeafSemantic
/-! Grouping resident columns does not mix records belonging to different
columns.  Padding may contain arbitrary records: it lies entirely in extra
columns and cannot affect the original prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonGroupedLeafSemantic
open CommonSortingNormalization CommonRecordProgram CommonSlabBatch
open CommonLocalSemantic PhysicalLocalSortPadding
noncomputable section

theorem batch_at {q : Configuration} {C r : ℕ}
    (F : Records q r→Records q r) (f : Records q (C*r)) (c : Fin C) (j : Fin r) :
    batchOutput F f (finProdFinEquiv (c,j))=F (columns C r f c) j := by
  simp only [batchOutput,flattenColumns,Equiv.symm_apply_apply]

theorem grouped_index {C ng gc r : ℕ} (hc : C≤ng*gc) (hp : C*r≤ng*(gc*r))
    (c : Fin C) (j : Fin r) :
    Fin.castLE hp (finProdFinEquiv (c,j))=
      finProdFinEquiv ((finProdFinEquiv.symm (Fin.castLE hc c)).1,
        finProdFinEquiv ((finProdFinEquiv.symm (Fin.castLE hc c)).2,j)) := by
  apply Fin.ext
  have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply (Fin.castLE hc c))
  simp only [finProdFinEquiv_apply_val,Fin.coe_castLE] at h ⊢
  nlinarith only [h]

/-- Any independent per-column transformation can be executed by first
grouping columns into equal resident batches.  The theorem refers to the
original, unpadded prefix and needs no property of the added columns. -/
theorem prefix_nested_batch {q : Configuration} {C ng gc r : ℕ}
    (hc : C≤ng*gc) (hp : C*r≤ng*(gc*r))
    (F : Records q r→Records q r) (f : Records q (C*r))
    (g : Records q (ng*(gc*r))) (hprefix : ∀ i,g (Fin.castLE hp i)=f i) :
    ∀ i,batchOutput (batchOutput (C:=gc) F) g (Fin.castLE hp i)=batchOutput F f i := by
  intro i
  obtain ⟨⟨c,j⟩,rfl⟩ := finProdFinEquiv.surjective i
  rw [grouped_index hc hp,batch_at,batch_at,batch_at]
  congr 1
  funext k
  change g (finProdFinEquiv ((finProdFinEquiv.symm (Fin.castLE hc c)).1,
    finProdFinEquiv ((finProdFinEquiv.symm (Fin.castLE hc c)).2,k)))=
      f (finProdFinEquiv (c,k))
  rw [←grouped_index hc hp]
  exact hprefix _

end
end CodedSorting.CommonGroupedLeafSemantic
end GroupedLeafSemantic

section GroupedLeafBatch
/-! An implemented batch of resident Columnsort leaves.  Short columns
share a resident group, so block rounding is paid per group rather than
per column.  A final partial group is explicitly padded and copied back. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace CodedSorting.CommonGroupedLeafBatch
open CommonSortingNormalization CommonRecordProgram CommonSlabBatch
open CommonLeafGrouping
noncomputable section

def gc (q : Configuration) (r : ℕ) := CommonLeafGrouping.columns (512*q.height) r
def ng (q : Configuration) (c r : ℕ) := groups (512*q.height) r c
def groupSize (q : Configuration) (r : ℕ) := gc q r*r
def paddedSize (q : Configuration) (c r : ℕ) := ng q c r*groupSize q r

def space (q : Configuration) (c r : ℕ) : ℕ :=
  if c*r≤512*q.height then recordBlocks q (c*r) else
    recordBlocks q (paddedSize q c r)+ng q c r*recordBlocks q (groupSize q r)+
      recordBlocks q (groupSize q r)

def sortColumns {q : Configuration} (c r : ℕ) : Records q (c*r)→Records q (c*r) :=
  batchOutput (C:=c) Columnsort.sortColumn

def largeProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (c r source buffer limit : ℕ) (hr : r≤512*q.height) (hlarge : 512*q.height<c*r)
    (hs : source+recordBlocks q (c*r)≤buffer)
    (hw : buffer+recordBlocks q (paddedSize q c r)+ng q c r*recordBlocks q (groupSize q r)+
      recordBlocks q (groupSize q r)≤limit) (hl : limit≤q.N^q.exponent) :
    Program q (c*r) source buffer limit (sortColumns c r) := by
  let G := groupSize q r
  let K := ng q c r
  let M := paddedSize q c r
  let slabs := buffer+recordBlocks q M
  let work := slabs+K*recordBlocks q G
  have hG : G≤512*q.height := group_fits _ _
  have hpos : 0<r := CommonLeafGrouping.rows_pos hlarge
  have hp : c*r≤M := padded_covers hpos hr
  have hc : c≤K*gc q r := groups_cover hpos hr
  have hwork : work+recordBlocks q G≤limit := by
    dsimp only [work,slabs,G,K,M]
    exact hw
  let kids : Children q K G slabs work limit (sortColumns (gc q r) r) := fun a=>
    CommonResidentRecordProgram.program q reader G hG (sortColumns (gc q r) r)
      (recordBase q G slabs a.val) work limit
      (by
        have he := base_end q (C:=K) (n:=G*3) (buffer:=slabs) a
        simpa only [record_blocks,work] using he)
      hwork hl
  let inner : Program q M buffer slabs limit
      (batchOutput (C:=K) (sortColumns (gc q r) r)) :=
    CommonSlabBatch.program reader kids le_rfl (by dsimp only [work]; rw [record_blocks])
      (by omega) hl
  let padded := CommonRecordPrefix.program reader hp inner hs le_rfl (by omega) hl
  apply padded.changeFunction
  funext f i
  exact CommonGroupedLeafSemantic.prefix_nested_batch hc hp Columnsort.sortColumn f
    (CommonRecordPrefix.extendBottom f) (CommonRecordPrefix.extend_prefix hp f) i

theorem largeProgram_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (c r source buffer limit : ℕ) (hr : r≤512*q.height) (hlarge : 512*q.height<c*r)
    (hs : source+recordBlocks q (c*r)≤buffer)
    (hw : buffer+recordBlocks q (paddedSize q c r)+ng q c r*recordBlocks q (groupSize q r)+
      recordBlocks q (groupSize q r)≤limit) (hl : limit≤q.N^q.exponent) :
    (largeProgram q reader c r source buffer limit hr hlarge hs hw hl).charge=
      12*recordBlocks q (c*r)+3*recordBlocks q (paddedSize q c r)+
        ng q c r*(8*recordBlocks q (groupSize q r)+1)+
        12*(ng q c r*recordBlocks q (groupSize q r)) := by
  simp only [largeProgram,CommonRecordReindex.changeFunction_charge,CommonRecordPrefix.program,
    CommonSlabBatch.program,childrenCharge,CommonResidentRecordProgram.program,
    CommonResidentRecordProgram.charge]
  simp only [List.map_const',List.length_finRange,List.sum_replicate,smul_eq_mul,
    ←record_blocks]
  omega

/-- The public batch has a uniform scan charge.  The two branches both
contain only concrete resident programs and charged disk instructions. -/
private def construction (q : Configuration) (reader : Fin q.inventory.readers)
    (c r source buffer limit : ℕ) (hr : r≤512*q.height) (hBH : q.block≤q.height)
    (hs : source+recordBlocks q (c*r)≤buffer)
    (hw : buffer+space q c r≤limit) (hl : limit≤q.N^q.exponent) :
    {p : Program q (c*r) source buffer limit (sortColumns c r) //
      p.charge≤256*(recordBlocks q (c*r)+1)} := by
  by_cases hn : c*r≤512*q.height
  · let p := CommonResidentRecordProgram.program q reader (c*r) hn (sortColumns c r)
      source buffer limit hs (by simpa only [space,if_pos hn] using hw) hl
    have hc : p.charge≤256*(recordBlocks q (c*r)+1) := by
      dsimp only [p,CommonResidentRecordProgram.program,CommonResidentRecordProgram.charge]
      omega
    exact ⟨p,hc⟩
  · have hg : 512*q.height<c*r := by omega
    have hwork : buffer+recordBlocks q (paddedSize q c r)+ng q c r*recordBlocks q (groupSize q r)+
        recordBlocks q (groupSize q r)≤limit := by
      simpa only [space,if_neg hn,Nat.add_assoc] using hw
    let p := largeProgram q reader c r source buffer limit hr hg hs hwork hl
    have hc : p.charge≤256*(recordBlocks q (c*r)+1) := by
      dsimp only [p]
      rw [largeProgram_charge]
      exact CommonGroupedLeafCost.grouped_bound q c r hBH hr hg
    exact ⟨p,hc⟩

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (c r source buffer limit : ℕ) (hr : r≤512*q.height) (hBH : q.block≤q.height)
    (hs : source+recordBlocks q (c*r)≤buffer)
    (hw : buffer+space q c r≤limit) (hl : limit≤q.N^q.exponent) :
    Program q (c*r) source buffer limit (sortColumns c r) :=
  let p := construction q reader c r source buffer limit hr hBH hs hw hl
  { instructions:=p.1.instructions
    charge:=256*(recordBlocks q (c*r)+1)
    correct:=p.1.correct
    frame:=p.1.frame
    safe:=p.1.safe
    cost_le:=p.1.cost_le.trans p.2
    length_le:=p.1.length_le.trans p.2 }

theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (c r source buffer limit : ℕ) (hr : r≤512*q.height) (hBH : q.block≤q.height)
    (hs : source+recordBlocks q (c*r)≤buffer)
    (hw : buffer+space q c r≤limit) (hl : limit≤q.N^q.exponent) :
    (program q reader c r source buffer limit hr hBH hs hw hl).charge=
      256*(recordBlocks q (c*r)+1) := rfl

theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (c r source buffer limit : ℕ) (hr : r≤512*q.height) (hBH : q.block≤q.height)
    (hs : source+recordBlocks q (c*r)≤buffer)
    (hw : buffer+space q c r≤limit) (hl : limit≤q.N^q.exponent) :
    (program q reader c r source buffer limit hr hBH hs hw hl).charge≤
      256*(recordBlocks q (c*r)+1) := by
  rw [program_charge]

end
end CodedSorting.CommonGroupedLeafBatch
end GroupedLeafBatch
