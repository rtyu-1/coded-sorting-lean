import CodedSorting.Shared.Memory.Batch.Correctness

section Endpoint
/-! Initialized whole-batch execution on one finite common disk. The exact
cost is two scans of the packed batch volume. Input and output blocks are
shared across column boundaries, including columns shorter than a block. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonLeafBatchEndpoint
open WordControl CommonSortingNormalization CommonLeafBatchProgram
open CommonLeafProgram (Slots Store Disk)
open BucketMachine BucketReader CommonLeafBatchRead CommonLeafBatchWrite
open CommonLeafBatchCorrectness CommonLeafBatchInit

@[simp] theorem inputWords_length (q : Configuration) {n : ℕ}
    (cols : List (Fin n → KeyRecordWords.Record q.w)) :
    ((cols.map (columnWords q)).flatten).length=3*cols.length*n := by
  induction cols with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons,List.flatten_cons,List.length_append,columnWords_length,
      List.length_cons,ih]
    ring

@[simp] theorem outputWords_length (q : Configuration) {n : ℕ}
    (cols : List (Fin n → KeyRecordWords.Record q.w)) :
    (CommonLeafBatchCorrectness.outputWords q cols).length=3*cols.length*n := by
  induction cols with
  | nil => simp [CommonLeafBatchCorrectness.outputWords]
  | cons f fs ih =>
    rw [outputWords_cons,List.length_append,columnWords_length,ih,List.length_cons]
    ring

theorem blocks_le_finish {α : Type*} (writer : Writer α) :
    writer.blocks.length≤writer.finish.length := by
  unfold Writer.finish
  split_ifs <;> simp

/-- Finishing the single shared writer gives one packed batch, not a list
of separately rounded per-column files. -/
theorem packed_output (q : Configuration) {n : ℕ}
    (cols : List (Fin n → KeyRecordWords.Record q.w)) :
    let writer := BatchMemorySort.appendRecords q.block
      (CommonLeafBatchCorrectness.outputWords q cols) Writer.empty
    writer.Valid q.block ∧
    writer.finish=BucketMachine.pack q.block (CommonLeafProgram.block_positive q)
      (CommonLeafBatchCorrectness.outputWords q cols) ∧
    writer.finish.length=PhysicalStreamCursor.blockCount q.block (3*cols.length*n) := by
  let writer := BatchMemorySort.appendRecords q.block
    (CommonLeafBatchCorrectness.outputWords q cols) Writer.empty
  have hv : writer.Valid q.block := BatchMemorySort.appendRecords_valid _ _ _
    (Writer.empty_valid _ (CommonLeafProgram.block_positive q))
  have hc : writer.contents=CommonLeafBatchCorrectness.outputWords q cols := by
    change (BatchMemorySort.appendRecords q.block
      (CommonLeafBatchCorrectness.outputWords q cols) Writer.empty).contents=_
    rw [BatchMemorySort.appendRecords_contents]
    rfl
  have hf : writer.finish=BucketMachine.pack q.block (CommonLeafProgram.block_positive q)
      (CommonLeafBatchCorrectness.outputWords q cols) := by
    rw [DiskStreamPass.writer_finish_eq_pack q.block (CommonLeafProgram.block_positive q) writer hv,hc]
  refine ⟨hv,hf,?_⟩
  rw [hf,pack_count,outputWords_length]
  rfl

/-- The input relation reads the existing common disk through its counted
source descriptor. Initialization supplies only addresses and counts. -/
theorem batch_initialized_positive (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (hn : 0<n.val)
    (cols : List (Fin n.val → KeyRecordWords.Record q.w))
    (total : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (htotal : total.val=3*cols.length*n.val)
    (hinput : (PhysicalStreamCursor.suffix (extendDisk q disk) source.val total.val 0).flatten=
      (cols.map (columnWords q)).flatten)
    (hsep : source.val+PhysicalStreamCursor.blockCount q.block total.val≤target.val)
    (hfit : target.val+PhysicalStreamCursor.blockCount q.block total.val≤q.N^q.exponent) :
    ∃ finalStore finalDisk,
      batch q z (initialStore q z n total source target s) disk=
        some (finalStore,finalDisk,2*PhysicalStreamCursor.blockCount q.block (3*cols.length*n.val)) ∧
      DiskRep q target.val
        (BucketMachine.pack q.block (CommonLeafProgram.block_positive q)
          (CommonLeafBatchCorrectness.outputWords q cols)) finalDisk ∧
      ResidentLeafSort.count finalStore.leaf=n.val ∧ Frames q s finalStore ∧
      (∀ a : Fin (q.N^q.exponent), a.val<target.val ∨
        target.val+PhysicalStreamCursor.blockCount q.block total.val≤a.val → finalDisk a=disk a) ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  let initial := initialStore q z n total source target s
  let reader : Reader (Word q.w) :=
    Reader.fromDisk (PhysicalStreamCursor.suffix (extendDisk q disk) source.val total.val 0)
  let writer := BatchMemorySort.appendRecords q.block
    (CommonLeafBatchCorrectness.outputWords q cols) Writer.empty
  have hB := CommonLeafProgram.block_positive q
  have hvalid : reader.Valid q.block :=
    PhysicalStreamCursor.readerView_valid (extendDisk q disk) source.val total.val 0 [] hB
      (by simpa using hB)
  have hview : ReaderView q disk source.val total.val reader := rfl
  have hcontents : reader.contents=(cols.map (columnWords q)).flatten := by
    simpa only [reader,Reader.fromDisk,Reader.contents,List.nil_append] using hinput
  obtain ⟨hwvalid,hwpack,hwlength⟩ := packed_output q cols
  change writer.Valid q.block at hwvalid
  change writer.finish=_ at hwpack
  change writer.finish.length=_ at hwlength
  rw [←htotal] at hwlength
  have hwblocks := blocks_le_finish writer
  have hsourcecap := descriptor_capacity q source.val source.isLt.le
  have htargetcap := descriptor_capacity q target.val target.isLt.le
  have htotalcap := descriptor_capacity q total.val (by have:=total.isLt; omega)
  have hwritecap : writer.blocks.length<(2^q.w)^q.digits :=
    descriptor_capacity q _ (by omega)
  have hwritefit : target.val+writer.blocks.length≤q.N^q.exponent := by omega
  have hnil : DiskRep q target.val (Writer.empty : Writer (Word q.w)).blocks disk := by
    intro i hi
    simp only [Writer.empty,List.length_nil] at hi
    omega
  obtain ⟨finalReader,finalStore,partialDisk,cost,hcolumns,hrv,hrview,hrcontents,hrcap,
    hrslot,hwslot,hdisk,hcount,hframes,hcost,hconserve,houtside⟩ :=
    columns_correct q z n.val cols source.val target.val total.val reader Writer.empty initial disk
      (count_initial q z n total source target s) hvalid hview
      (reader_initial q z n total source target s _) hcontents (Writer.empty_valid _ hB)
      (writer_initial q z n total source target s) hnil hsourcecap htotalcap
      (by dsimp [reader,Reader.fromDisk]; positivity) htargetcap
      (leaf_words_capacity_of_le q n.val (by have:=n.isLt; omega)) hsep hwritecap hwritefit
  change finalStore.writers z.writer=CommonSortingNormalizationStreams.output
    q.block q.digits q.w target.val writer at hwslot
  change DiskRep q target.val writer.blocks partialDisk at hdisk
  change cost+reader.reads+(Writer.empty : Writer (Word q.w)).blocks.length=
    finalReader.reads+writer.blocks.length at hcost
  have hfinished := finish_correct q z finalStore partialDisk target.val writer hwslot hwvalid
    htargetcap hwritecap (by rw [hwlength]; exact hfit) hdisk
  obtain ⟨hfinaldisk,hfinishcost,hfinaloutside⟩ := hfinished
  have hempty : finalReader.disk=[] := Reader.empty_contents_disk q.block finalReader hrv hrcontents
  have hreads : finalReader.reads=PhysicalStreamCursor.blockCount q.block total.val := by
    simpa only [hempty,List.length_nil,Nat.add_zero,reader,Reader.fromDisk,suffix_length,
      Nat.sub_zero,Nat.zero_add] using hconserve
  have hcostexact : cost+(finish q z finalStore partialDisk).2=
      2*PhysicalStreamCursor.blockCount q.block total.val := by
    simp only [reader,Reader.fromDisk,Writer.empty,List.length_nil,Nat.add_zero] at hcost
    omega
  have hcontrol : total.val/(3*n.val)=cols.length := by
    rw [htotal,show 3*cols.length*n.val=cols.length*(3*n.val) by ring]
    exact Nat.mul_div_cancel _ (by omega)
  have heof : Stream.readStep (extendDisk q partialDisk) (finalStore.readers z.reader)=(none,0) := by
    rw [hrslot]
    exact eof_refines q partialDisk source.val total.val finalReader hrv hrview hrcontents
      (stream_block_capacity q).le htotalcap hrcap
  refine ⟨finalStore,(finish q z finalStore partialDisk).1,?_,?_,hcount,?_,?_,resident_memory q⟩
  · simp only [batch,initial,total_initial,count_initial,hcontrol,hcolumns,Option.bind_some]
    simp only [bind,Option.bind,pure,Prod.fst,Prod.snd,heof,Nat.add_zero]
    rw [hcostexact,htotal]
  · rw [←hwpack]
    exact hfinaldisk
  · exact ⟨hframes.1,hframes.2.1,hframes.2.2.1,hframes.2.2.2⟩
  · intro a ha
    rw [hfinaloutside a (by omega)]
    exact houtside a (by simpa only [Writer.empty,List.length_nil,Nat.add_zero] using
      (show a.val<target.val ∨ target.val+writer.blocks.length≤a.val by omega))

/-- A zero counted volume performs no transfer and leaves the finite disk
unchanged, regardless of the current positive or zero leaf length. -/
theorem batch_empty (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (total : Fin (q.N^q.exponent+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q)
    (htotal : total.val=0) :
    batch q z (initialStore q z n total source target s) disk=
      some (initialStore q z n total source target s,disk,0) := by
  let initial := initialStore q z n total source target s
  have hB := CommonLeafProgram.block_positive q
  have hz : 0<(2^q.w)^q.digits := by positivity
  have heof : Stream.readStep (extendDisk q disk) (initial.readers z.reader)=(none,0) := by
    rw [reader_initial q z n total source target s [],htotal]
    exact CommonSortingNormalizationStreams.readStep_eof q.block q.digits q.w source.val 0 0
      (extendDisk q disk) hB (stream_block_capacity q).le hz hz (by omega)
  have hs := CommonSortingNormalizationStreams.finishStep_empty q.block q.digits q.w target.val
    (Writer.empty : Writer (Word q.w)) (extendDisk q disk) (Writer.empty_valid q.block hB)
    (stream_block_capacity q).le (by simpa only [Writer.empty,List.length_nil] using hz) rfl
  have hfinish : finish q z initial disk=(disk,0) := by
    simp only [finish,initial,writer_initial,hs,restrict_extend]
  simp only [batch,initial,total_initial,htotal,Nat.zero_div,columns,
    bind,Option.bind,pure,Prod.fst,Prod.snd]
  change (match (Stream.readStep (extendDisk q disk) (initial.readers z.reader)).1 with
    | some _ => none
    | none => some (initial,(finish q z initial disk).1,
      0+(Stream.readStep (extendDisk q disk) (initial.readers z.reader)).2+
        (finish q z initial disk).2))=some (initial,disk,0)
  rw [heof,hfinish]
  rfl

/-- Complete initialized shared-buffer execution, including zero-length
columns. The number of columns is read from the resident counted header,
and the exact cost rounds only the total batch volume. -/
theorem batch_initialized (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1))
    (cols : List (Fin n.val → KeyRecordWords.Record q.w))
    (total : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (htotal : total.val=3*cols.length*n.val)
    (hinput : (PhysicalStreamCursor.suffix (extendDisk q disk) source.val total.val 0).flatten=
      (cols.map (columnWords q)).flatten)
    (hsep : source.val+PhysicalStreamCursor.blockCount q.block total.val≤target.val)
    (hfit : target.val+PhysicalStreamCursor.blockCount q.block total.val≤q.N^q.exponent) :
    ∃ finalStore finalDisk,
      batch q z (initialStore q z n total source target s) disk=
        some (finalStore,finalDisk,2*PhysicalStreamCursor.blockCount q.block (3*cols.length*n.val)) ∧
      DiskRep q target.val
        (BucketMachine.pack q.block (CommonLeafProgram.block_positive q)
          (CommonLeafBatchCorrectness.outputWords q cols)) finalDisk ∧
      ResidentLeafSort.count finalStore.leaf=n.val ∧ Frames q s finalStore ∧
      (∀ a : Fin (q.N^q.exponent), a.val<target.val ∨
        target.val+PhysicalStreamCursor.blockCount q.block total.val≤a.val → finalDisk a=disk a) ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  by_cases hn : 0<n.val
  · exact batch_initialized_positive q z n hn cols total source target s disk htotal hinput hsep hfit
  · have hnzero : n.val=0 := by omega
    have hvolume : 3*cols.length*n.val=0 := Nat.mul_eq_zero.mpr (Or.inr hnzero)
    have hzero : total.val=0 := htotal.trans hvolume
    have hB := CommonLeafProgram.block_positive q
    have hblocks : PhysicalStreamCursor.blockCount q.block (3*cols.length*n.val)=0 := by
      unfold PhysicalStreamCursor.blockCount
      rw [hvolume,Nat.zero_add]
      exact Nat.div_eq_of_lt (Nat.sub_lt hB (by omega))
    have hout : CommonLeafBatchCorrectness.outputWords q cols=[] := by
      apply List.length_eq_zero_iff.mp
      rw [outputWords_length]
      exact hvolume
    refine ⟨initialStore q z n total source target s,disk,?_,?_,
      count_initial q z n total source target s,⟨rfl,rfl,rfl,rfl⟩,fun _ _ => rfl,resident_memory q⟩
    · rw [batch_empty q z n total source target s disk hzero,hblocks,Nat.mul_zero]
    · rw [hout]
      intro i hi
      simp only [BucketMachine.pack,List.length_nil] at hi
      omega

end CodedSorting.CommonLeafBatchEndpoint
end Endpoint

section RunFacts
/-! Arithmetic and resident-control facts for the fixed batch policy. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafBatchRunFacts
open WordControl CommonSortingNormalization CommonLeafBatchProgram
open CommonLeafProgram (Slots Store Disk phase setPhase)
open BucketMachine BucketReader CommonLeafBatchRead

@[simp] theorem position_setPhase (q : Configuration) (p : ℕ) (s : Store q) :
    position q (setPhase q p s)=position q s := by
  unfold position setPhase
  congr 1
  funext i
  apply Function.update_of_ne
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.coe_natAdd, CommonLeafProgram.phaseIndex] at hv
  omega

@[simp] theorem setPhase_setPosition (q : Configuration) (p k : ℕ) (s : Store q) :
    setPhase q p (setPosition q k s)=setPosition q k (setPhase q p s) := by
  unfold setPhase setPosition
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp only [CommonLeafProgram.phaseIndex,Fin.append_left,Function.update_self]
    change Function.update _ (0 : Fin (1+q.digits)) _ 0 = _
    exact Function.update_self _ _ _
  · intro j
    have hne : j.natAdd 1 ≠ CommonLeafProgram.phaseIndex q := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.coe_natAdd,CommonLeafProgram.phaseIndex] at hv
      omega
    simp only [setPhase,setPosition,Function.update_of_ne hne,Fin.append_right]

theorem reader_next_bound (q : Configuration) (disk : Disk q) (base total : ℕ)
    (reader next : Reader (Word q.w)) (a : Word q.w)
    (hview : ReaderView q disk base total reader)
    (hbound : reader.reads≤PhysicalStreamCursor.blockCount q.block total)
    (hpop : reader.pop=some (a,next)) :
    next.reads≤PhysicalStreamCursor.blockCount q.block total := by
  have hc := Reader.pop_conservation reader next a hpop
  have hd : reader.disk.length=PhysicalStreamCursor.blockCount q.block total-reader.reads := by
    rw [hview,suffix_length]
  rw [hd,Nat.add_sub_of_le hbound] at hc
  omega

end CodedSorting.CommonLeafBatchRunFacts
end RunFacts

section Policy
/-! A fixed, six-phase controller for the shared-buffer leaf batch.
Only the current source RAM is consulted. Disk transfers use the existing
transfer window; stream buffers remain resident across column boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonLeafBatchPolicy
open WordControl CommonSortingNormalization
open CommonLeafProgram (Slots Store RAM Disk Machine phase setPhase machine words)
open CommonLeafBatchProgram (position setPosition)
namespace S
export CommonSortingNormalizationStreams (decode popLocal refillLocal pushLocal cells)
end S

def lift (q : Configuration) (p : ℕ) (buffer : Words q.block q.w) (s : Store q) : Store q :=
  setPhase q p {s with transfer:=buffer}

def readAddress (q : Configuration) (z : Slots q) (s : Store q) : ℕ :=
  decodeWords (s.readers z.reader).base + (S.decode (s.readers z.reader).resident).2

def writeAddress (q : Configuration) (z : Slots q) (s : Store q) : ℕ :=
  decodeWords (s.writers z.writer).base + (S.decode (s.writers z.writer).resident).2

def readLive (q : Configuration) (z : Slots q) (s : Store q) : Prop :=
  (S.popLocal q.block q.digits q.w (s.readers z.reader).resident).isSome ∨
    (S.decode (s.readers z.reader).resident).2*q.block < decodeWords (s.readers z.reader).records
instance (q : Configuration) (z : Slots q) (s : Store q) : Decidable (readLive q z s) :=
  inferInstanceAs (Decidable (_ ∨ _))

def refillCode (q : Configuration) (z : Slots q) (s : Store q) : Words q.digits q.w :=
  PhysicalStreamCursor.encodeNat q.digits q.w
    (min q.block (decodeWords (s.readers z.reader).records-
      (S.decode (s.readers z.reader).resident).2*q.block)-1)

def popEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  match S.popLocal q.block q.digits q.w (s.readers z.reader).resident with
  | none => s
  | some (a,next) => CommonLeafBatchProgram.accept q z s a
      {(s.readers z.reader) with resident:=next}

def refillEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  match S.refillLocal q.block q.digits q.w (s.readers z.reader).resident s.transfer
      (refillCode q z s) with
  | none => s
  | some (a,next) => CommonLeafBatchProgram.accept q z s a
      {(s.readers z.reader) with resident:=next}

def pushResult (q : Configuration) (z : Slots q) (s : Store q) :=
  S.pushLocal q.block q.digits q.w (s.writers z.writer).resident
    (ResidentLeafBank.getWord s.leaf (position q s))

def emitCommit (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  setPosition q (position q s+1) {s with writers:=(Function.update s.writers z.writer
    {(s.writers z.writer) with resident:=(pushResult q z s).1})}

def emitEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  match (pushResult q z s).2 with
  | none => emitCommit q z s
  | some block => lift q 3 block s

def finishEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  let pending := (S.decode (s.writers z.writer).resident).1
  if pending=[] then setPhase q 5 s else lift q 4 (S.cells q.block pending) s

def cpuEffect (q : Configuration) (s : Store q) : Store q :=
  setPhase q 2 (CommonLeafBatchProgram.compute q s)

def enterEffect (q : Configuration) (s : Store q) : Store q :=
  setPhase q 1 (setPosition q 0 s)

def ramMap (q : Configuration) (f : Store q → Store q) (ram : RAM q) : RAM q :=
  pack (f (unpack ram))

/-- Codes: boundary 0, read 1, emit 2, normal flush 3, final flush 4,
halt 5. The scalar tail is solely the within-column word position. -/
def policy (q : Configuration) (z : Slots q) : SourcePolicy q := fun ram =>
  let s : Store q := unpack ram
  if phase q s=0 then
    if readLive q z s then some ⟨.localOp (ramMap q (enterEffect q)),id⟩
    else some ⟨.localOp (ramMap q (finishEffect q z)),id⟩
  else if phase q s=1 then
    if position q s < words q s then
      match S.popLocal q.block q.digits q.w (s.readers z.reader).resident with
      | some _ => some ⟨.localOp (ramMap q (popEffect q z)),id⟩
      | none =>
        if (S.decode (s.readers z.reader).resident).2*q.block < decodeWords (s.readers z.reader).records then
          if h : readAddress q z s < q.N^q.exponent then
            some ⟨.read ⟨readAddress q z s,h⟩
              (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
              ramMap q (refillEffect q z)⟩
          else none
        else none
    else some ⟨.localOp (ramMap q (cpuEffect q)),id⟩
  else if phase q s=2 then
    if position q s < words q s then
      some ⟨.localOp (ramMap q (emitEffect q z)),id⟩
    else some ⟨.localOp (ramMap q (setPhase q 0)),id⟩
  else if phase q s=3 then
    if h : writeAddress q z s < q.N^q.exponent then
      some ⟨.write ⟨writeAddress q z s,h⟩
        (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
        ramMap q (fun t => setPhase q 2 (emitCommit q z t))⟩
    else none
  else if phase q s=4 then
    if h : writeAddress q z s < q.N^q.exponent then
      some ⟨.write ⟨writeAddress q z s,h⟩
        (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
        ramMap q (setPhase q 5)⟩
    else none
  else none

abbrev run (q : Configuration) (z : Slots q) := ControlledNormalization.runLogical (policy q z)

theorem phase_capacity (q : Configuration) : 7 < 2^q.w := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) q.word_width
  norm_num at h
  omega

@[simp] theorem phase_lift (q : Configuration) (p : ℕ) (buffer : Words q.block q.w)
    (s : Store q) (hp : p≤7) : phase q (lift q p buffer s)=p :=
  CommonLeafProgram.phase_setPhase q p _ (by have:=phase_capacity q; omega)

@[simp] theorem position_setPhase (q : Configuration) (p : ℕ) (s : Store q) :
    position q (setPhase q p s)=position q s := by
  unfold position setPhase
  congr 1
  funext i
  dsimp only
  rw [Function.update_of_ne]
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.coe_natAdd,CommonLeafProgram.phaseIndex] at hv
  omega

@[simp] theorem position_lift (q : Configuration) (p : ℕ) (buffer : Words q.block q.w)
    (s : Store q) : position q (lift q p buffer s)=position q s := by
  rw [lift,position_setPhase]
  rfl

@[simp] theorem lift_lift (q : Configuration) (p k : ℕ) (b c : Words q.block q.w)
    (s : Store q) : lift q p b (lift q k c s)=lift q p b s := by
  simp only [lift,setPhase,Function.update_idem]

@[simp] theorem readAddress_lift (q : Configuration) (z : Slots q) (p : ℕ)
    (b : Words q.block q.w) (s : Store q) : readAddress q z (lift q p b s)=readAddress q z s := rfl
@[simp] theorem writeAddress_lift (q : Configuration) (z : Slots q) (p : ℕ)
    (b : Words q.block q.w) (s : Store q) : writeAddress q z (lift q p b s)=writeAddress q z s := rfl
@[simp] theorem words_lift (q : Configuration) (p : ℕ)
    (b : Words q.block q.w) (s : Store q) : words q (lift q p b s)=words q s := rfl
@[simp] theorem readLive_lift (q : Configuration) (z : Slots q) (p : ℕ)
    (b : Words q.block q.w) (s : Store q) : readLive q z (lift q p b s) ↔ readLive q z s := Iff.rfl

theorem run_add (q : Configuration) (z : Slots q) (n m : ℕ) (s : Machine q) :
    run q z (n+m) s =
      ((run q z m (run q z n s).1).1,(run q z n s).2+(run q z m (run q z n s).1).2) := by
  induction n generalizing s with
  | zero => simp [run,ControlledNormalization.runLogical]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [run,ControlledNormalization.runLogical]
    cases hp : policy q z s.ram with
    | none => cases m <;> simp [ControlledNormalization.runLogical,hp]
    | some i => simp only; rw [←run,ih]; simp [run,Nat.add_assoc]

theorem enter_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : readLive q z s) :
    run q z 1 (machine q s disk)=(machine q (enterEffect q s) disk,0) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,Normalization.transferCost]

theorem finish_prepare_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : ¬readLive q z s) :
    run q z 1 (machine q s disk)=(machine q (finishEffect q z s) disk,0) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,Normalization.transferCost]

theorem read_pending_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hl : position q s<words q s)
    (a : Word q.w) (next : CommonSortingNormalizationStreams.Resident q.block q.digits q.w)
    (hr : S.popLocal q.block q.digits q.w (s.readers z.reader).resident=some (a,next)) :
    run q z 1 (machine q s disk)=(machine q (CommonLeafBatchProgram.accept q z s a
      {(s.readers z.reader) with resident:=next}) disk,0) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,hr,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,popEffect,Normalization.transferCost]

theorem read_refill_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hl : position q s<words q s)
    (hr : S.popLocal q.block q.digits q.w (s.readers z.reader).resident=none)
    (hc : (S.decode (s.readers z.reader).resident).2*q.block<decodeWords (s.readers z.reader).records)
    (ha : readAddress q z s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (refillEffect q z {s with transfer:=disk ⟨readAddress q z s,ha⟩}) disk,1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,hr,hc,ha,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,Normalization.transferCost,
    CommonLeafWindow.load_transfer]

theorem compute_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hl : words q s≤position q s) :
    run q z 1 (machine q s disk)=(machine q (cpuEffect q s) disk,0) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,
    show ¬position q s<words q s from by omega,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,Normalization.transferCost]

theorem emit_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=2) (hl : position q s<words q s) :
    run q z 1 (machine q s disk)=(machine q (emitEffect q z s) disk,0) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,Normalization.transferCost]

theorem boundary_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=2) (hl : words q s≤position q s) :
    run q z 1 (machine q s disk)=(machine q (setPhase q 0 s) disk,0) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,
    show ¬position q s<words q s from by omega,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,Normalization.transferCost]

theorem flush_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=3) (ha : writeAddress q z s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (setPhase q 2 (emitCommit q z s))
        (Function.update disk ⟨writeAddress q z s,ha⟩ s.transfer),1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,ha,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,Normalization.transferCost,
    CommonLeafWindow.slice_transfer]

theorem final_flush_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=4) (ha : writeAddress q z s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (setPhase q 5 s)
        (Function.update disk ⟨writeAddress q z s,ha⟩ s.transfer),1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,ha,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,Normalization.transferCost,
    CommonLeafWindow.slice_transfer]

theorem halt (q : Configuration) (z : Slots q) (s : Store q) (hp : phase q s=5) :
    policy q z (pack s)=none := by simp [policy,hp]

@[simp] theorem accept_lift (q : Configuration) (z : Slots q) (p : ℕ)
    (b : Words q.block q.w) (s : Store q) (a : Word q.w)
    (reader : CommonSortingNormalizationStreams.InputState q.block q.digits q.w) :
    CommonLeafBatchProgram.accept q z (lift q p b s) a reader=
      lift q p b (CommonLeafBatchProgram.accept q z s a reader) := by
  unfold CommonLeafBatchProgram.accept
  rw [position_lift]
  change setPosition q (position q s+1)
      (setPhase q p {s with transfer:=b, readers:=Function.update s.readers z.reader reader, leaf:=ResidentLeafBank.putBlock (position q s) 1 (fun _ : Fin 1 => a) s.leaf})=
    setPhase q p (setPosition q (position q s+1)
      {s with transfer:=b, readers:=Function.update s.readers z.reader reader, leaf:=ResidentLeafBank.putBlock (position q s) 1 (fun _ : Fin 1 => a) s.leaf})
  exact (CommonLeafBatchRunFacts.setPhase_setPosition q p _ _).symm

/-- Each successful macro read is one source instruction: pending data is
local, while a refill is an actual transfer into the current RAM window. -/
theorem readOne_run (q : Configuration) (z : Slots q) (s next : Store q)
    (disk : Disk q) (buffer : Words q.block q.w) (cost : ℕ)
    (hpos : position q s<words q s)
    (haddr : readAddress q z s<q.N^q.exponent)
    (hread : CommonLeafBatchProgram.readOne q z disk s=some (next,cost)) :
    ∃ finalBuffer, run q z 1 (machine q (lift q 1 buffer s) disk)=
      (machine q (lift q 1 finalBuffer next) disk,cost) := by
  cases hr : S.popLocal q.block q.digits q.w (s.readers z.reader).resident with
  | some pair =>
    rcases pair with ⟨a,resident⟩
    simp only [CommonLeafBatchProgram.readOne,CommonSortingNormalizationStreams.readStep,
      hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hread
    rcases hread with ⟨rfl,rfl⟩
    refine ⟨buffer,?_⟩
    rw [read_pending_one q z (lift q 1 buffer s) disk (phase_lift q 1 buffer s (by decide))
      (by simpa using hpos) a resident hr,accept_lift]
    rfl
  | none =>
    by_cases hlive : (S.decode (s.readers z.reader).resident).2*q.block<
        decodeWords (s.readers z.reader).records
    · have hblock : CommonLeafBatchProgram.extendDisk q disk (readAddress q z s)=
          disk ⟨readAddress q z s,haddr⟩ := by
        simp [CommonLeafBatchProgram.extendDisk,haddr]
      cases hf : S.refillLocal q.block q.digits q.w (s.readers z.reader).resident
          (disk ⟨readAddress q z s,haddr⟩) (refillCode q z s) with
      | none =>
        simp only [CommonLeafBatchProgram.readOne,CommonSortingNormalizationStreams.readStep,
          hr,hlive,↓reduceIte]
          at hread
        change ((S.refillLocal q.block q.digits q.w (s.readers z.reader).resident
          (CommonLeafBatchProgram.extendDisk q disk (readAddress q z s))
          (refillCode q z s)).map _).map _ = some (next,cost) at hread
        rw [hblock,hf] at hread
        cases hread
      | some pair =>
        rcases pair with ⟨a,resident⟩
        simp only [CommonLeafBatchProgram.readOne,CommonSortingNormalizationStreams.readStep,
          hr,hlive,↓reduceIte] at hread
        change ((S.refillLocal q.block q.digits q.w (s.readers z.reader).resident
          (CommonLeafBatchProgram.extendDisk q disk (readAddress q z s))
          (refillCode q z s)).map _).map _ = some (next,cost) at hread
        rw [hblock,hf] at hread
        try simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at hread
        rcases hread with ⟨rfl,rfl⟩
        refine ⟨disk ⟨readAddress q z s,haddr⟩,?_⟩
        rw [read_refill_one q z (lift q 1 buffer s) disk
          (phase_lift q 1 buffer s (by decide)) (by simpa using hpos) hr hlive haddr]
        change (machine q (refillEffect q z (lift q 1 (disk ⟨readAddress q z s,haddr⟩) s)) disk,1)=_
        simp only [refillEffect]
        change (machine q (match S.refillLocal q.block q.digits q.w (s.readers z.reader).resident
          (disk ⟨readAddress q z s,haddr⟩) (refillCode q z s) with
          | none => _
          | some (a,r) => CommonLeafBatchProgram.accept q z
            (lift q 1 (disk ⟨readAddress q z s,haddr⟩) s) a {(s.readers z.reader) with resident:=r}) disk,1)=_
        simp only [hf,accept_lift]
    · simp [CommonLeafBatchProgram.readOne,CommonSortingNormalizationStreams.readStep,
        hr,hlive] at hread

/-- A zero-cost EOF distinguishes a true boundary from a live refill,
even without assumptions about the contents of the transfer buffer. -/
theorem eof_not_live (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (heof : CommonSortingNormalizationStreams.readStep (CommonLeafBatchProgram.extendDisk q disk)
      (s.readers z.reader)=(none,0)) : ¬readLive q z s := by
  cases hp : S.popLocal q.block q.digits q.w (s.readers z.reader).resident with
  | some pair =>
    rcases pair with ⟨a,r⟩
    simp [CommonSortingNormalizationStreams.readStep,hp] at heof
  | none =>
    by_cases hlive : (S.decode (s.readers z.reader).resident).2*q.block<
        decodeWords (s.readers z.reader).records
    · have hc := congrArg Prod.snd heof
      simp [CommonSortingNormalizationStreams.readStep,hp,hlive] at hc
    · simp [readLive,hp,hlive]

theorem readLive_of_readOne (q : Configuration) (z : Slots q) (s next : Store q)
    (disk : Disk q) (cost : ℕ)
    (hread : CommonLeafBatchProgram.readOne q z disk s=some (next,cost)) :
    readLive q z s := by
  cases hp : S.popLocal q.block q.digits q.w (s.readers z.reader).resident with
  | some pair => simp [readLive,hp]
  | none =>
    by_cases hlive : (S.decode (s.readers z.reader).resident).2*q.block<
        decodeWords (s.readers z.reader).records
    · exact Or.inr hlive
    · simp [CommonLeafBatchProgram.readOne,CommonSortingNormalizationStreams.readStep,hp,hlive] at hread

end CodedSorting.CommonLeafBatchPolicy
end Policy
