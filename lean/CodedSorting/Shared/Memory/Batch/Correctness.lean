import CodedSorting.Shared.Memory.Batch.Program

section Write
/-! Actual finite-disk execution of the shared-buffer batch writer. Logical
writer lists occur only in the refinement assertions; the running state
contains the existing counted descriptors and one resident stream buffer. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonLeafBatchWrite
open WordControl CommonSortingNormalization
open CommonLeafProgram (Slots Store Disk)
open CommonLeafBatchProgram BucketMachine
namespace S
export CommonSortingNormalizationStreams (output cells writeStep writeStep_refines writeStep_flush
  writer_decode pushLocal encodeWriter finishStep finishStep_empty finishStep_partial)
end S

/-- The completed logical blocks are the actual blocks of the finite disk. -/
def DiskRep (q : Configuration) (base : ℕ) (blocks : List (List (Word q.w))) (disk : Disk q) : Prop :=
  ∀ (i : ℕ) (hi : i<blocks.length),
    extendDisk q disk (base+i)=S.cells q.block blocks[i]

theorem extend_restrict_write (q : Configuration) (disk : Disk q)
    (a : ℕ) (block : Words q.block q.w) (ha : a<q.N^q.exponent) :
    extendDisk q (restrictDisk q (writeBlock (extendDisk q disk) a block))=
      writeBlock (extendDisk q disk) a block := by
  funext i
  by_cases hi : i<q.N^q.exponent
  · simp [extendDisk,restrictDisk,hi]
  · have hne : i≠a := by omega
    simp [extendDisk,restrictDisk,writeBlock,hi,hne]

theorem push_blocks_mono {α : Type*} (B : ℕ) (writer : Writer α) (a : α) :
    writer.blocks.length≤(writer.push B a).blocks.length := by
  simp only [Writer.push]
  split <;> simp

theorem append_blocks_mono {α : Type*} (B : ℕ) (xs : List α) (writer : Writer α) :
    writer.blocks.length≤(BatchMemorySort.appendRecords B xs writer).blocks.length := by
  induction xs generalizing writer with
  | nil => exact le_rfl
  | cons a rest ih => exact (push_blocks_mono B writer a).trans (ih _)

/-- One actual writer call updates its finite disk representation and
preserves every address outside the newly completed block interval. -/
theorem writeStep_disk (q : Configuration) (base : ℕ) (writer : Writer (Word q.w))
    (a : Word q.w) (disk : Disk q) (hv : writer.Valid q.block)
    (hb : base<(2^q.w)^q.digits) (hc : writer.blocks.length<(2^q.w)^q.digits)
    (hfit : base+(writer.push q.block a).blocks.length≤q.N^q.exponent)
    (hd : DiskRep q base writer.blocks disk) :
    let out := S.writeStep (extendDisk q disk) (S.output q.block q.digits q.w base writer) a
    DiskRep q base (writer.push q.block a).blocks (restrictDisk q out.2.1) ∧
    (∀ j : Fin (q.N^q.exponent),
      j.val<base+writer.blocks.length ∨ base+(writer.push q.block a).blocks.length≤j.val →
      restrictDisk q out.2.1 j=disk j) := by
  have hB := (stream_block_capacity q).le
  by_cases hfull : (writer.pending++[a]).length=q.block
  · rw [S.writeStep_flush q.block q.digits q.w base writer a (extendDisk q disk) hv hB hb hc hfull]
    have hpush : (writer.push q.block a).blocks=writer.blocks++[writer.pending++[a]] := by
      simp [Writer.push,hfull]
    rw [hpush] at hfit ⊢
    have ha : base+writer.blocks.length<q.N^q.exponent := by
      simp only [List.length_append,List.length_singleton] at hfit
      omega
    constructor
    · intro i hi
      rw [extend_restrict_write q disk _ _ ha]
      by_cases hi' : i<writer.blocks.length
      · rw [List.getElem_append_left hi']
        have hne : base+i≠base+writer.blocks.length := by omega
        simpa only [writeBlock,if_neg hne] using hd i hi'
      · have he : i=writer.blocks.length := by
          simp only [List.length_append,List.length_singleton] at hi
          omega
        subst i
        simp [writeBlock]
    · intro j hj
      have hne : j.val≠base+writer.blocks.length := by
        simp only [List.length_append,List.length_singleton] at hj
        omega
      simp [restrictDisk,writeBlock,hne,extendDisk,j.isLt]
  · have he : (S.writeStep (extendDisk q disk)
        (S.output q.block q.digits q.w base writer) a).2.1=extendDisk q disk := by
      unfold CommonSortingNormalizationStreams.writeStep CommonSortingNormalizationStreams.output
        CommonSortingNormalizationStreams.pushLocal
      rw [S.writer_decode q.block q.digits q.w writer hv hB hc]
      simp only [hfull,if_false]
    have hp : (writer.push q.block a).blocks=writer.blocks := by simp only [Writer.push,if_neg hfull]
    dsimp only
    rw [he,restrict_extend,hp]
    exact ⟨hd,fun _ _ => rfl⟩

/-- Payload and all reader/frame state remain the very same resident values. -/
structure Preserved (q : Configuration) (before after : Store q) : Prop where
  leaf : after.leaf=before.leaf
  readers : after.readers=before.readers
  directories : after.directories=before.directories
  shapes : after.shapes=before.shapes
  top : after.top=before.top
  pcs : after.pcs=before.pcs

 theorem Preserved.refl (q : Configuration) (s : Store q) : Preserved q s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
 theorem Preserved.trans {q : Configuration} {s t u : Store q}
    (hs : Preserved q s t) (ht : Preserved q t u) : Preserved q s u :=
  ⟨ht.leaf.trans hs.leaf,ht.readers.trans hs.readers,ht.directories.trans hs.directories,
    ht.shapes.trans hs.shapes,ht.top.trans hs.top,ht.pcs.trans hs.pcs⟩

def payload (q : Configuration) (s : Store q) (n : ℕ) : List (Word q.w) :=
  List.ofFn (fun i : Fin n => ResidentLeafBank.getWord s.leaf (position q s+i.val))

theorem payload_succ (q : Configuration) (s : Store q) (n : ℕ) :
    payload q s (n+1)=ResidentLeafBank.getWord s.leaf (position q s)::
      List.ofFn (fun i : Fin n => ResidentLeafBank.getWord s.leaf (position q s+(i.val+1))) := by
  simp [payload,List.ofFn_succ]

/-- A single call derives its output word only from the current leaf bank. -/
theorem writeOne_correct (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (base : ℕ) (writer : Writer (Word q.w))
    (hw : s.writers z.writer=S.output q.block q.digits q.w base writer)
    (hv : writer.Valid q.block) (hb : base<(2^q.w)^q.digits)
    (hc : writer.blocks.length<(2^q.w)^q.digits)
    (hp : position q s+1<(2^q.w)^q.digits)
    (hfit : base+(writer.push q.block (ResidentLeafBank.getWord s.leaf (position q s))).blocks.length≤q.N^q.exponent)
    (hd : DiskRep q base writer.blocks disk) :
    let next := writer.push q.block (ResidentLeafBank.getWord s.leaf (position q s))
    let out := writeOne q z disk s
    Preserved q s out.1 ∧ position q out.1=position q s+1 ∧
      out.1.writers z.writer=S.output q.block q.digits q.w base next ∧
      DiskRep q base next.blocks out.2.1 ∧
      out.2.2+writer.blocks.length=next.blocks.length ∧
      (∀ j : Fin (q.N^q.exponent),
        j.val<base+writer.blocks.length ∨ base+next.blocks.length≤j.val → out.2.1 j=disk j) := by
  have hs := S.writeStep_refines q.block q.digits q.w base writer
    (ResidentLeafBank.getWord s.leaf (position q s)) (extendDisk q disk) hv
    (stream_block_capacity q).le hb hc
  have hdis := writeStep_disk q base writer (ResidentLeafBank.getWord s.leaf (position q s))
    disk hv hb hc hfit hd
  dsimp only
  refine ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,?_,?_,?_,?_,?_⟩
  · exact position_setPosition q _ _ hp
  · simp only [writeOne,setPosition,Function.update_self,hw]
    exact hs.1
  · simpa only [writeOne,hw] using hdis.1
  · simp only [writeOne,hw,hs.2.1]
    exact Nat.sub_add_cancel (push_blocks_mono q.block writer _)
  · simpa only [writeOne,hw] using hdis.2

/-- The entire word loop runs on one actual finite disk. The pending writer
buffer persists, and the returned cost is the number of blocks really flushed. -/
theorem writeN_correct (q : Configuration) (z : Slots q) (k : ℕ)
    (s : Store q) (disk : Disk q) (base : ℕ) (writer : Writer (Word q.w))
    (hw : s.writers z.writer=S.output q.block q.digits q.w base writer)
    (hv : writer.Valid q.block) (hb : base<(2^q.w)^q.digits)
    (hp : position q s+k<(2^q.w)^q.digits)
    (hc : (BatchMemorySort.appendRecords q.block (payload q s k) writer).blocks.length<(2^q.w)^q.digits)
    (hfit : base+(BatchMemorySort.appendRecords q.block (payload q s k) writer).blocks.length≤q.N^q.exponent)
    (hd : DiskRep q base writer.blocks disk) :
    let final := BatchMemorySort.appendRecords q.block (payload q s k) writer
    let out := writeN q z k s disk
    Preserved q s out.1 ∧ position q out.1=position q s+k ∧
      out.1.writers z.writer=S.output q.block q.digits q.w base final ∧
      DiskRep q base final.blocks out.2.1 ∧
      out.2.2+writer.blocks.length=final.blocks.length ∧
      (∀ j : Fin (q.N^q.exponent),
        j.val<base+writer.blocks.length ∨ base+final.blocks.length≤j.val → out.2.1 j=disk j) := by
  induction k generalizing s disk writer with
  | zero =>
      simpa [writeN,payload,BatchMemorySort.appendRecords] using
        (show Preserved q s s ∧ position q s=position q s ∧
          s.writers z.writer=S.output q.block q.digits q.w base writer ∧
          DiskRep q base writer.blocks disk ∧ writer.blocks.length=writer.blocks.length ∧
          (∀ j : Fin (q.N^q.exponent),
            j.val<base+writer.blocks.length ∨ base+writer.blocks.length≤j.val → disk j=disk j)
          from ⟨Preserved.refl q s,rfl,hw,hd,rfl,fun _ _ => rfl⟩)
  | succ k ih =>
      let one := writeOne q z disk s
      let next := writer.push q.block (ResidentLeafBank.getWord s.leaf (position q s))
      let final := BatchMemorySort.appendRecords q.block (payload q s (k+1)) writer
      have hp1 : position q s+1<(2^q.w)^q.digits := by omega
      have hpos : position q one.1=position q s+1 := position_setPosition q _ _ hp1
      have hleaf : one.1.leaf=s.leaf := rfl
      have htail : payload q one.1 k=
          List.ofFn (fun i : Fin k => ResidentLeafBank.getWord s.leaf (position q s+(i.val+1))) := by
        unfold payload
        rw [hpos,hleaf]
        congr 1
        funext i
        congr 1
        omega
      have he : final=BatchMemorySort.appendRecords q.block (payload q one.1 k) next := by
        dsimp only [final]
        rw [payload_succ,htail]
        rfl
      have hmono : next.blocks.length≤final.blocks.length := by
        rw [he]
        exact append_blocks_mono q.block _ next
      have hmono0 : writer.blocks.length≤next.blocks.length := push_blocks_mono q.block writer _
      obtain ⟨hpres,hpnext,hwnext,hdnext,hcostnext,houtside⟩ := writeOne_correct q z s disk base writer
        hw hv hb (by change final.blocks.length<_ at hc; omega) hp1
        (by change base+final.blocks.length≤_ at hfit; exact (Nat.add_le_add_left hmono base).trans hfit) hd
      have hp' : position q one.1+k<(2^q.w)^q.digits := by rw [hpos]; omega
      have hc' : (BatchMemorySort.appendRecords q.block (payload q one.1 k) next).blocks.length<(2^q.w)^q.digits := by
        rw [←he]
        exact hc
      have hf' : base+(BatchMemorySort.appendRecords q.block (payload q one.1 k) next).blocks.length≤q.N^q.exponent := by
        rw [←he]
        exact hfit
      obtain ⟨hrpres,hrpos,hrwriter,hrdisk,hrcost,hroutside⟩ :=
        ih one.1 one.2.1 next hwnext (Writer.push_valid q.block writer _ hv) hp' hc' hf' hdnext
      rw [←he] at hrwriter hrdisk hrcost hroutside
      change Preserved q s (writeN q z k one.1 one.2.1).1 ∧
        position q (writeN q z k one.1 one.2.1).1=position q s+(k+1) ∧
        (writeN q z k one.1 one.2.1).1.writers z.writer=S.output q.block q.digits q.w base final ∧
        DiskRep q base final.blocks (writeN q z k one.1 one.2.1).2.1 ∧
        (one.2.2+(writeN q z k one.1 one.2.1).2.2)+writer.blocks.length=final.blocks.length ∧ _
      refine ⟨hpres.trans hrpres,?_,hrwriter,hrdisk,?_,?_⟩
      · rw [hrpos,hpos]
        omega
      · change one.2.2+writer.blocks.length=next.blocks.length at hcostnext
        omega
      · intro j hj
        change j.val<base+writer.blocks.length ∨ base+final.blocks.length≤j.val at hj
        change (writeN q z k one.1 one.2.1).2.1 j=disk j
        have hn : j.val<base+next.blocks.length ∨ base+final.blocks.length≤j.val := by omega
        rw [hroutside j hn]
        apply houtside j
        change j.val<base+writer.blocks.length ∨ base+next.blocks.length≤j.val
        omega

/-- Finalization emits the one pending partial block, if any, on the same
finite disk and charges precisely that physical write. -/
theorem finish_correct (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (base : ℕ) (writer : Writer (Word q.w))
    (hw : s.writers z.writer=S.output q.block q.digits q.w base writer)
    (hv : writer.Valid q.block) (hb : base<(2^q.w)^q.digits)
    (hc : writer.blocks.length<(2^q.w)^q.digits)
    (hfit : base+writer.finish.length≤q.N^q.exponent)
    (hd : DiskRep q base writer.blocks disk) :
    let out := finish q z s disk
    DiskRep q base writer.finish out.1 ∧
      out.2+writer.blocks.length=writer.finish.length ∧
      (∀ j : Fin (q.N^q.exponent),
        j.val<base+writer.blocks.length ∨ base+writer.finish.length≤j.val → out.1 j=disk j) := by
  have hB := (stream_block_capacity q).le
  by_cases hempty : writer.pending=[]
  · have hs := S.finishStep_empty q.block q.digits q.w base writer (extendDisk q disk) hv hB hc hempty
    simp only [finish,hw,hs,restrict_extend]
    simpa [Writer.finish,hempty] using
      (show DiskRep q base writer.blocks disk ∧ writer.blocks.length=writer.blocks.length ∧
        (∀ j : Fin (q.N^q.exponent),
          j.val<base+writer.blocks.length ∨ base+writer.blocks.length≤j.val → disk j=disk j)
        from ⟨hd,rfl,fun _ _ => rfl⟩)
  · have hs := S.finishStep_partial q.block q.digits q.w base writer (extendDisk q disk) hv hB hb hc hempty
    have hf : writer.finish=writer.blocks++[writer.pending] := by
      simp [Writer.finish,hempty]
    have ha : base+writer.blocks.length<q.N^q.exponent := by
      rw [hf] at hfit
      simp only [List.length_append,List.length_singleton] at hfit
      omega
    simp only [finish,hw,hs,hf]
    refine ⟨?_,by simp; omega,?_⟩
    · intro i hi
      rw [extend_restrict_write q disk _ _ ha]
      by_cases hi' : i<writer.blocks.length
      · rw [List.getElem_append_left hi']
        have hne : base+i≠base+writer.blocks.length := by omega
        simpa only [writeBlock,if_neg hne] using hd i hi'
      · have he : i=writer.blocks.length := by
          simp only [List.length_append,List.length_singleton] at hi
          omega
        subst i
        simp [writeBlock]
    · intro j hj
      have hne : j.val≠base+writer.blocks.length := by
        simp only [List.length_append,List.length_singleton] at hj
        omega
      simp [restrictDisk,writeBlock,hne,extendDisk,j.isLt]

end CodedSorting.CommonLeafBatchWrite
end Write

section CPU
/-! The resident CPU receives exactly the words installed by the shared
reader.  These assertions expose the complete encoded sorted output. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonLeafBatchCPU
open WordControl CommonLeafBatchProgram ResidentLeafSort ResidentLeafBank KeyRecordWords

variable {cap d w n : ℕ}

@[simp] theorem count_loadWords (offset : ℕ) (xs : List (Word w)) (ram : RAM cap d w) :
    count (loadWords offset xs ram)=count ram := by
  induction xs generalizing offset ram with
  | nil => rfl
  | cons a xs ih => rw [loadWords,ih,count_putBlock]

theorem raw_loadWords_before (offset : ℕ) (xs : List (Word w)) (ram : RAM cap d w)
    (i : Fin (cap*3)) (hi : i.val<offset) : raw (loadWords offset xs ram) i=raw ram i := by
  induction xs generalizing offset ram with
  | nil => rfl
  | cons a xs ih =>
      rw [loadWords,ih (offset+1) _ (by omega)]
      exact raw_putBlock_outside offset 1 _ ram i (Or.inl hi)

theorem raw_loadWords_at (offset : ℕ) (xs : List (Word w)) (ram : RAM cap d w)
    (i : Fin (cap*3)) (hlo : offset ≤ i.val) (hhi : i.val<offset+xs.length) :
    raw (loadWords offset xs ram) i=xs[i.val-offset]'(by omega) := by
  induction xs generalizing offset ram with
  | nil => simp only [List.length_nil] at hhi; omega
  | cons a xs ih =>
      rw [loadWords]
      by_cases he : i.val=offset
      · rw [raw_loadWords_before (offset+1) xs _ i (by omega)]
        rw [raw_putBlock_inside offset 1 _ ram i hlo (by omega) (by decide)]
        simp [he]
      · have hlo' : offset+1 ≤ i.val := by omega
        have hhi' : i.val<offset+1+xs.length := by simp only [List.length_cons] at hhi; omega
        rw [ih (offset+1) _ hlo' hhi']
        have hd : i.val-offset=(i.val-(offset+1))+1 := by omega
        simp only [hd,List.getElem_cons_succ]

theorem words_ofFn_numeric (hw : 2≤w) (records : Fin n → Record w) :
    words w hw (List.ofFn records)=List.ofFn (fun i : Fin (n*3) =>
      encode w hw (records (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2) := by
  rw [List.ofFn_mul]
  unfold words
  rw [List.flatMap,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*3+j.val,by have := i.isLt; have := j.isLt; omega⟩ : Fin (n*3))=
      finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*3+j.val=j.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

theorem raw_loadWords_records (hw : 2≤w) (ram : RAM cap d w)
    (hn : count ram=n) (records : Fin n → Record w) (i : Fin n) (j : Fin 3) :
    raw (loadWords 0 (words w hw (List.ofFn records)) ram)
      (finProdFinEquiv (⟨i.val,by have := count_le ram; have := i.isLt; omega⟩,j))=
        encode w hw (records i) j := by
  have hi := i.isLt
  have hj := j.isLt
  have hval : (finProdFinEquiv
      ((⟨i.val,by have := count_le ram; omega⟩ : Fin cap),j)).val = i.val*3+j.val := by
    change j.val+3*i.val=i.val*3+j.val
    omega
  rw [raw_loadWords_at 0 _ ram _ (by omega) (by
    rw [hval,words_length,List.length_ofFn]
    omega)]
  simp only [Nat.sub_zero]
  simp only [words_ofFn_numeric, List.getElem_ofFn]
  have he : (⟨(finProdFinEquiv
      ((⟨i.val,by have := count_le ram; omega⟩ : Fin cap),j)).val,
      by rw [hval]; omega⟩ : Fin (n*3))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    rfl
  rw [he,Equiv.symm_apply_apply]

theorem cpu_loadWords_records (hw : 2≤w) (ram : RAM cap d w)
    (hn : count ram=n) (records : Fin n → Record w) :
    List.ofFn (fun i : Fin (3*n) => getWord
      (cpu hw (loadWords 0 (words w hw (List.ofFn records)) ram)) i.val)=
        words w hw (List.ofFn (Columnsort.sortColumn records)) := by
  let loaded := loadWords 0 (words w hw (List.ofFn records)) ram
  have hc : count loaded=n := (count_loadWords _ _ _).trans hn
  have hexact := cpu_exact_of_raw hw loaded hc records
    (raw_loadWords_records hw ram hn records)
  rw [words_ofFn_numeric hw (Columnsort.sortColumn records)]
  apply List.ext_getElem
  · simp [Nat.mul_comm]
  · intro k hk hk'
    simp only [List.length_ofFn] at hk
    simp only [List.getElem_ofFn]
    let i : Fin n := (finProdFinEquiv.symm (⟨k,by omega⟩ : Fin (n*3))).1
    let j : Fin 3 := (finProdFinEquiv.symm (⟨k,by omega⟩ : Fin (n*3))).2
    have hindex : (finProdFinEquiv
        ((⟨i.val,by have := count_le loaded; have := i.isLt; omega⟩ : Fin cap),j)).val=k := by
      have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply
        (⟨k,by omega⟩ : Fin (n*3)))
      exact h
    have hout := hexact i j
    have hget := getWord_at (cpu hw loaded)
      (finProdFinEquiv ((⟨i.val,by have := count_le loaded; have := i.isLt; omega⟩ : Fin cap),j))
    rw [hindex] at hget
    exact hget.trans hout

open CommonSortingNormalization CommonLeafProgram in
theorem compute_loaded_payload (q : Configuration) (n : ℕ) (s loaded : Store q)
    (records : Fin n → Record q.w) (hn : count s.leaf=n)
    (hload : loaded.leaf=loadWords 0
      (words q.w (by have := q.word_width; omega) (List.ofFn records)) s.leaf) :
    CommonLeafBatchWrite.payload q (compute q loaded) (3*n)=
      words q.w (by have := q.word_width; omega) (List.ofFn (Columnsort.sortColumn records)) := by
  unfold CommonLeafBatchWrite.payload
  have hz : position q (compute q loaded)=0 := by
    apply position_setPosition
    positivity
  rw [hz]
  simp only [Nat.zero_add]
  change List.ofFn (fun i : Fin (3*n) => getWord (cpu _ loaded.leaf) i.val)=_
  rw [hload]
  exact cpu_loadWords_records _ s.leaf hn records

end CodedSorting.CommonLeafBatchCPU
end CPU

section Correctness
/-! Whole shared-buffer batches on the finite common disk. The proof-only
reader and writer views follow the actual resident descriptors across all
column boundaries. Input and output occupy ordered disjoint regions. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonLeafBatchCorrectness
open WordControl CommonSortingNormalization CommonLeafBatchProgram
open CommonLeafProgram (Slots Store Disk)
open BucketMachine BucketReader
open CommonLeafBatchRead CommonLeafBatchWrite
namespace S
export CommonSortingNormalizationStreams (input output)
end S

def columnWords (q : Configuration) {n : ℕ}
    (records : Fin n → KeyRecordWords.Record q.w) : List (Word q.w) :=
  KeyRecordWords.words q.w (by have:=q.word_width; omega) (List.ofFn records)

@[simp] theorem columnWords_length (q : Configuration) {n : ℕ}
    (records : Fin n → KeyRecordWords.Record q.w) : (columnWords q records).length=3*n := by
  simp [columnWords,KeyRecordWords.words_length]

def outputWords (q : Configuration) {n : ℕ}
    (cols : List (Fin n → KeyRecordWords.Record q.w)) : List (Word q.w) :=
  (cols.map (fun f => columnWords q (Columnsort.sortColumn f))).flatten

theorem outputWords_cons (q : Configuration) {n : ℕ}
    (f : Fin n → KeyRecordWords.Record q.w) (fs : List (Fin n → KeyRecordWords.Record q.w)) :
    outputWords q (f::fs)=columnWords q (Columnsort.sortColumn f)++outputWords q fs := rfl

theorem appendRecords_append {α : Type*} (B : ℕ) (xs ys : List α) (writer : Writer α) :
    BatchMemorySort.appendRecords B (xs++ys) writer=
      BatchMemorySort.appendRecords B ys (BatchMemorySort.appendRecords B xs writer) := by
  simp only [BatchMemorySort.appendRecords,List.foldl_append]

/-- The controller fields which survive a complete column, including its
RAM computation. Leaf payload itself is replaced with the last output. -/
def Frames (q : Configuration) (s t : Store q) : Prop :=
  t.directories=s.directories ∧ t.shapes=s.shapes ∧ t.top=s.top ∧ t.pcs=s.pcs

theorem columns_correct (q : Configuration) (z : Slots q) (n : ℕ)
    (cols : List (Fin n → KeyRecordWords.Record q.w))
    (source target total : ℕ) (reader : Reader (Word q.w)) (writer : Writer (Word q.w))
    (s : Store q) (disk : Disk q)
    (hn : ResidentLeafSort.count s.leaf=n)
    (hr : reader.Valid q.block) (hview : ReaderView q disk source total reader)
    (hrs : s.readers z.reader=S.input q.block q.digits q.w source total reader)
    (hcontents : reader.contents=(cols.map (columnWords q)).flatten)
    (hw : writer.Valid q.block)
    (hws : s.writers z.writer=S.output q.block q.digits q.w target writer)
    (hd : DiskRep q target writer.blocks disk)
    (hsource : source<(2^q.w)^q.digits) (htotal : total<(2^q.w)^q.digits)
    (hcursor : reader.reads<(2^q.w)^q.digits) (htarget : target<(2^q.w)^q.digits)
    (hposition : 3*n<(2^q.w)^q.digits)
    (hsep : source+PhysicalStreamCursor.blockCount q.block total≤target)
    (hcap : (BatchMemorySort.appendRecords q.block (outputWords q cols) writer).blocks.length<(2^q.w)^q.digits)
    (hfit : target+(BatchMemorySort.appendRecords q.block (outputWords q cols) writer).blocks.length≤q.N^q.exponent) :
    let finalWriter := BatchMemorySort.appendRecords q.block (outputWords q cols) writer
    ∃ finalReader finalStore finalDisk cost,
      columns q z cols.length s disk=some (finalStore,finalDisk,cost) ∧
      finalReader.Valid q.block ∧ ReaderView q finalDisk source total finalReader ∧
      finalReader.contents=[] ∧ finalReader.reads<(2^q.w)^q.digits ∧
      finalStore.readers z.reader=S.input q.block q.digits q.w source total finalReader ∧
      finalStore.writers z.writer=S.output q.block q.digits q.w target finalWriter ∧
      DiskRep q target finalWriter.blocks finalDisk ∧
      ResidentLeafSort.count finalStore.leaf=n ∧ Frames q s finalStore ∧
      cost+reader.reads+writer.blocks.length=finalReader.reads+finalWriter.blocks.length ∧
      finalReader.reads+finalReader.disk.length=reader.reads+reader.disk.length ∧
      (∀ a : Fin (q.N^q.exponent),
        a.val<target+writer.blocks.length ∨ target+finalWriter.blocks.length≤a.val →
          finalDisk a=disk a) := by
  induction cols generalizing reader writer s disk with
  | nil =>
      refine ⟨reader,s,disk,0,rfl,hr,hview,?_,hcursor,hrs,hws,hd,hn,
        ⟨rfl,rfl,rfl,rfl⟩,?_,rfl,fun _ _ => rfl⟩
      · simpa using hcontents
      · simp only [outputWords,List.map_nil,List.flatten_nil,BatchMemorySort.appendRecords,
          List.foldl_nil,Nat.zero_add]
  | cons f fs ih =>
      let words := columnWords q f
      let outs := columnWords q (Columnsort.sortColumn f)
      let start := setPosition q 0 s
      have hzero : position q start=0 := position_setPosition q 0 s (by positivity)
      have hfront : reader.contents=words++(fs.map (columnWords q)).flatten := hcontents
      obtain ⟨nextReader,loaded,readCost,hread,hvalid,hreadview,hrest,hreadcap,
        hreadslot,hreadcost,hreadpos,hload,hwriters,hdirs,hshapes,htop,hpcs,hconserve⟩ :=
        readN_correct q z disk source total words (fs.map (columnWords q)).flatten reader start
          hr hview hrs hfront (stream_block_capacity q).le hsource htotal hcursor
          (by rw [hzero]; simpa only [Nat.zero_add,words,columnWords_length] using hposition)
      rw [hzero] at hload
      let sorted := compute q loaded
      have hsortedCount : ResidentLeafSort.count sorted.leaf=n := by
        change ResidentLeafSort.count (ResidentLeafSort.cpu _ loaded.leaf)=n
        rw [ResidentLeafSort.count_cpu,hload]
        exact (CommonLeafBatchCPU.count_loadWords 0 words s.leaf).trans hn
      have hsortedPayload : payload q sorted (3*n)=outs := by
        exact CommonLeafBatchCPU.compute_loaded_payload q n s loaded f hn hload
      let nextWriter := BatchMemorySort.appendRecords q.block outs writer
      let finalWriter := BatchMemorySort.appendRecords q.block (outputWords q (f::fs)) writer
      have hfinal : finalWriter=BatchMemorySort.appendRecords q.block (outputWords q fs) nextWriter := by
        dsimp only [finalWriter,nextWriter,outs]
        rw [outputWords_cons,appendRecords_append]
      have hmono : nextWriter.blocks.length≤finalWriter.blocks.length := by
        rw [hfinal]
        exact append_blocks_mono q.block _ nextWriter
      have hwriteSlot : sorted.writers z.writer=S.output q.block q.digits q.w target writer := by
        change loaded.writers z.writer=_
        rw [hwriters]
        exact hws
      have hsortedPosition : position q sorted=0 := position_setPosition q 0 _ (by positivity)
      have hwrite := writeN_correct q z (3*n) sorted disk target writer hwriteSlot hw htarget
        (by rw [hsortedPosition]; simpa only [Nat.zero_add] using hposition)
        (by rw [hsortedPayload]; exact lt_of_le_of_lt hmono hcap)
        (by rw [hsortedPayload]; exact (Nat.add_le_add_left hmono target).trans hfit) hd
      rw [hsortedPayload] at hwrite
      obtain ⟨hpres,hwritepos,hwriteslot,hwritedisk,hwritecost,houtside⟩ := hwrite
      let written := writeN q z (3*n) sorted disk
      have hnextValid : nextWriter.Valid q.block := BatchMemorySort.appendRecords_valid _ _ _ hw
      have hnextReadSlot : written.1.readers z.reader=S.input q.block q.digits q.w source total nextReader := by
        rw [hpres.readers]
        exact hreadslot
      have hnextView : ReaderView q written.2.1 source total nextReader :=
        readerView_preserved q disk written.2.1 source total target nextReader hreadview hsep
          (by omega) (fun a ha => houtside a (Or.inl (by omega)))
      have hnextCount : ResidentLeafSort.count written.1.leaf=n := by
        rw [hpres.leaf]
        exact hsortedCount
      obtain ⟨finalReader,finalStore,finalDisk,restCost,hrun,hrv,hrview,hrcontents,hrcap,
        hrslot,hwslot,hdd,hcount,hframes,hcost,hcons,ho⟩ :=
        ih nextReader nextWriter written.1 written.2.1 hnextCount hvalid hnextView hnextReadSlot
          hrest hnextValid hwriteslot hwritedisk hreadcap
          (by rw [←hfinal]; exact hcap) (by rw [←hfinal]; exact hfit)
      rw [←hfinal] at hwslot hdd hcost ho
      refine ⟨finalReader,finalStore,finalDisk,readCost+written.2.2+restCost,?_,hrv,hrview,
        hrcontents,hrcap,hrslot,hwslot,hdd,hcount,?_,?_,hcons.trans hconserve,?_⟩
      · rw [List.length_cons,columns,hn]
        have he : readN q z disk (3*n) start=some (loaded,readCost) := by
          simpa only [words,columnWords_length] using hread
        dsimp only [written,sorted] at hrun
        simp only [start,he,bind,Option.bind,pure,Prod.fst,Prod.snd,hrun]
        rfl
      · rcases hframes with ⟨hd',hs',ht',hp'⟩
        exact ⟨hd'.trans (hpres.directories.trans hdirs),
          hs'.trans (hpres.shapes.trans hshapes),ht'.trans (hpres.top.trans htop),
          hp'.trans (hpres.pcs.trans hpcs)⟩
      · change written.2.2+writer.blocks.length=nextWriter.blocks.length at hwritecost
        change readCost+written.2.2+restCost+reader.reads+writer.blocks.length=
          finalReader.reads+finalWriter.blocks.length
        omega
      · intro a ha
        change a.val<target+writer.blocks.length ∨ target+finalWriter.blocks.length≤a.val at ha
        have hm0 : writer.blocks.length≤nextWriter.blocks.length := append_blocks_mono q.block outs writer
        have ha' : a.val<target+nextWriter.blocks.length ∨ target+finalWriter.blocks.length≤a.val := by omega
        rw [ho a ha']
        apply houtside a
        change a.val<target+writer.blocks.length ∨ target+nextWriter.blocks.length≤a.val
        omega

end CodedSorting.CommonLeafBatchCorrectness
end Correctness
