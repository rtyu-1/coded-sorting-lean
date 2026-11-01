import CodedSorting.Shared.Memory.Batch.Program

/-! Actual counted contiguous movement on the common finite disk.  The
program reads one block into the existing transfer window and writes that
same window to the counted destination.  Its loop state consists only of
encoded descriptors and the current source RAM. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMovementPolicy
open WordControl CommonSortingNormalization
open CommonLeafProgram (Slots Store RAM Disk Machine phase setPhase inputCursor
  sourceBase targetBase setInputCursor machine)

/-- Logical word count, read from its existing multiword input descriptor. -/
def words (q : Configuration) (z : Slots q) (s : Store q) : ℕ :=
  decodeWords (s.readers z.reader).records

def blocks (q : Configuration) (z : Slots q) (s : Store q) : ℕ :=
  PhysicalStreamCursor.blockCount q.block (words q z s)

/-- Initialization accepts addresses and a count, never the input payload. -/
def initialStore (q : Configuration) (z : Slots q)
    (n : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) : Store q :=
  setPhase q 0 {s with
    readers:=Function.update s.readers z.reader
      ⟨PhysicalStreamCursor.encodeNat q.digits q.w source.val,
        PhysicalStreamCursor.encodeNat q.digits q.w n.val,
        CommonSortingNormalizationStreams.encode q.block q.digits q.w [] 0⟩
    writers:=Function.update s.writers z.writer
      ⟨PhysicalStreamCursor.encodeNat q.digits q.w target.val,
        CommonSortingNormalizationStreams.encode q.block q.digits q.w [] 0⟩}

def readResume (q : Configuration) (ram : RAM q) : RAM q :=
  pack (setPhase q 1 (unpack ram : Store q))

def writeResume (q : Configuration) (z : Slots q) (ram : RAM q) : RAM q :=
  let s : Store q := unpack ram
  pack (setPhase q 0 (setInputCursor q z (inputCursor q z s+1) s))

/-- Each live iteration issues one read and one write.  The address and
continuation depend only on current RAM; no disk is captured by a local map. -/
def policy (q : Configuration) (z : Slots q) : SourcePolicy q := fun ram =>
  let s : Store q := unpack ram
  if phase q s=0 then
    if inputCursor q z s < blocks q z s then
      if h : sourceBase q z s+inputCursor q z s < q.N^q.exponent then
        some ⟨.read ⟨sourceBase q z s+inputCursor q z s,h⟩
          (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),readResume q⟩
      else none
    else none
  else if phase q s=1 then
    if h : targetBase q z s+inputCursor q z s < q.N^q.exponent then
      some ⟨.write ⟨targetBase q z s+inputCursor q z s,h⟩
        (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),writeResume q z⟩
    else none
  else none

abbrev run (q : Configuration) (z : Slots q) := ControlledNormalization.runLogical (policy q z)

def readEffect (q : Configuration) (s : Store q) (block : Words q.block q.w) : Store q :=
  setPhase q 1 {s with transfer:=block}

def pairEffect (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) : Store q :=
  setPhase q 0 (setInputCursor q z (inputCursor q z s+1) (readEffect q s block))

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

theorem read_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : inputCursor q z s < blocks q z s)
    (ha : sourceBase q z s+inputCursor q z s < q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (readEffect q s (disk ⟨sourceBase q z s+inputCursor q z s,ha⟩)) disk,1) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,ha,
    ↓reduceIte,↓reduceDIte,ControlledNormalization.logicalStep,Normalization.logicalStep,
    CommonLeafWindow.load_transfer,readResume,unpack_pack,Normalization.transferCost,Nat.add_zero]
  rfl

theorem write_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1)
    (ha : targetBase q z s+inputCursor q z s < q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (setPhase q 0 (setInputCursor q z (inputCursor q z s+1) s))
        (Function.update disk ⟨targetBase q z s+inputCursor q z s,ha⟩ s.transfer),1) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,
    one_ne_zero,ha,↓reduceIte,↓reduceDIte,ControlledNormalization.logicalStep,
    Normalization.logicalStep,CommonLeafWindow.slice_transfer,writeResume,unpack_pack,
    Normalization.transferCost,Nat.add_zero]
  try rfl

theorem pair_two (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : inputCursor q z s < blocks q z s)
    (hs : sourceBase q z s+inputCursor q z s < q.N^q.exponent)
    (ht : targetBase q z s+inputCursor q z s < q.N^q.exponent) :
    run q z 2 (machine q s disk)=
      (machine q (pairEffect q z s (disk ⟨sourceBase q z s+inputCursor q z s,hs⟩))
        (Function.update disk ⟨targetBase q z s+inputCursor q z s,ht⟩
          (disk ⟨sourceBase q z s+inputCursor q z s,hs⟩)),2) := by
  rw [show 2=1+1 from rfl,run_add,read_one q z s disk hp hl hs]
  dsimp only
  have hp' : phase q (readEffect q s (disk ⟨sourceBase q z s+inputCursor q z s,hs⟩))=1 :=
    CommonLeafProgram.phase_setPhase q 1 _ (by have:=CommonLeafProgram.phase_capacity q; omega)
  rw [write_one q z _ disk hp' ht]
  rfl

theorem halt (q : Configuration) (z : Slots q) (s : Store q)
    (hp : phase q s=0) (hc : blocks q z s ≤ inputCursor q z s) :
    policy q z (pack s)=none := by
  simp only [policy,unpack_pack,hp,show ¬inputCursor q z s<blocks q z s by omega,↓reduceIte]

/-- The control invariant names only decoded resident fields. -/
structure Control (q : Configuration) (z : Slots q) (source target total cursor : ℕ)
    (s : Store q) : Prop where
  phase_zero : phase q s=0
  source_base : sourceBase q z s=source
  target_base : targetBase q z s=target
  word_count : words q z s=total
  position : inputCursor q z s=cursor

/-- Slots needed by an enclosing recursive controller are untouched. -/
structure Preserved (q : Configuration) (s t : Store q) : Prop where
  leaf : t.leaf=s.leaf
  directories : t.directories=s.directories
  shapes : t.shapes=s.shapes
  top : t.top=s.top
  pcs : t.pcs=s.pcs

 theorem Preserved.refl (q : Configuration) (s : Store q) : Preserved q s s :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
 theorem Preserved.trans (q : Configuration) {s t u : Store q}
    (h : Preserved q s t) (g : Preserved q t u) : Preserved q s u :=
  ⟨g.leaf.trans h.leaf,g.directories.trans h.directories,g.shapes.trans h.shapes,
    g.top.trans h.top,g.pcs.trans h.pcs⟩

theorem pair_control (q : Configuration) (z : Slots q) (source target total cursor : ℕ)
    (s : Store q) (block : Words q.block q.w) (h : Control q z source target total cursor s)
    (hc : cursor+1<(2^q.w)^q.digits) :
    Control q z source target total (cursor+1) (pairEffect q z s block) := by
  constructor
  · exact CommonLeafProgram.phase_setPhase q 0 _ (by positivity)
  · simpa only [sourceBase,pairEffect,setPhase,setInputCursor,Function.update_self,readEffect]
      using h.source_base
  · exact h.target_base
  · simpa only [words,pairEffect,setPhase,setInputCursor,Function.update_self,readEffect]
      using h.word_count
  · unfold pairEffect
    change inputCursor q z (setInputCursor q z (inputCursor q z s+1) (readEffect q s block))=cursor+1
    rw [CommonLeafProgram.inputCursor_set q z _ _ (by rw [h.position]; exact hc),h.position]

theorem pair_preserved (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) : Preserved q s (pairEffect q z s block) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem initial_control (q : Configuration) (z : Slots q)
    (n : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    Control q z source.val target.val n.val 0 (initialStore q z n source target s) := by
  have hs := descriptor_capacity q source.val source.isLt.le
  have ht := descriptor_capacity q target.val target.isLt.le
  have hn := descriptor_capacity q n.val (by have:=n.isLt; omega)
  constructor
  · exact CommonLeafProgram.phase_setPhase q 0 _ (by positivity)
  · simp only [sourceBase,initialStore,setPhase,Function.update_self,
      PhysicalStreamCursor.decodeNat_encode _ _ _ hs]
  · simp only [targetBase,initialStore,setPhase,Function.update_self,
      PhysicalStreamCursor.decodeNat_encode _ _ _ ht]
  · simp only [words,initialStore,setPhase,Function.update_self,
      PhysicalStreamCursor.decodeNat_encode _ _ _ hn]
  · simp [inputCursor,initialStore,setPhase]

theorem initial_preserved (q : Configuration) (z : Slots q)
    (n : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    Preserved q s (initialStore q z n source target s) := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Full copied blocks and every disk block outside the written prefix.
Original payloads are proof parameters only, absent from the policy. -/
structure DiskInvariant (q : Configuration) (original current : Disk q)
    (source target count : ℕ) : Prop where
  copied : ∀ j, j<count → ∀ (hs : source+j<q.N^q.exponent)
    (ht : target+j<q.N^q.exponent),
    current ⟨target+j,ht⟩=original ⟨source+j,hs⟩
  outside : ∀ a : Fin (q.N^q.exponent),
    a.val<target ∨ target+count≤a.val → current a=original a

theorem diskInvariant_zero (q : Configuration) (disk : Disk q) (source target : ℕ) :
    DiskInvariant q disk disk source target 0 := by
  constructor
  · intro j hj; omega
  · intro a ha; rfl

/-- Disjoint counted extents allow reads and writes to be interleaved. -/
def Disjoint (source target length : ℕ) : Prop :=
  source+length≤target ∨ target+length≤source

theorem diskInvariant_read (q : Configuration) (original current : Disk q)
    (source target count k : ℕ) (h : DiskInvariant q original current source target k)
    (hsep : Disjoint source target count) (hk : k<count)
    (hs : source+k<q.N^q.exponent) :
    current ⟨source+k,hs⟩=original ⟨source+k,hs⟩ := by
  apply h.outside
  rcases hsep with hsep|hsep <;> simp only [Fin.val_mk] <;> omega

theorem diskInvariant_write (q : Configuration) (original current : Disk q)
    (source target k : ℕ) (h : DiskInvariant q original current source target k)
    (hs : source+k<q.N^q.exponent) (ht : target+k<q.N^q.exponent) :
    DiskInvariant q original
      (Function.update current ⟨target+k,ht⟩ (original ⟨source+k,hs⟩)) source target (k+1) := by
  constructor
  · intro j hj hs' ht'
    by_cases he : j=k
    · subst j
      exact Function.update_self _ _ _
    · have hne : (⟨target+j,ht'⟩ : Fin (q.N^q.exponent))≠⟨target+k,ht⟩ := by
        intro hh
        have := congrArg Fin.val hh
        simp only [Fin.val_mk] at this
        omega
      rw [Function.update_of_ne hne]
      exact h.copied j (by omega) hs' ht'
  · intro a ha
    have hne : a≠⟨target+k,ht⟩ := by
      intro hh
      have := congrArg Fin.val hh
      simp only [Fin.val_mk] at this
      omega
    rw [Function.update_of_ne hne]
    exact h.outside a (by omega)

/-- Complete execution from any established copied prefix.  Every loop
iteration is the two actual transfers established by `pair_two`. -/
theorem run_from (q : Configuration) (z : Slots q) (source target total k left : ℕ)
    (s : Store q) (original current : Disk q)
    (hcontrol : Control q z source target total k s)
    (hcount : k+left=PhysicalStreamCursor.blockCount q.block total)
    (hsource : source+PhysicalStreamCursor.blockCount q.block total ≤ q.N^q.exponent)
    (htarget : target+PhysicalStreamCursor.blockCount q.block total ≤ q.N^q.exponent)
    (hsep : Disjoint source target (PhysicalStreamCursor.blockCount q.block total))
    (hdisk : DiskInvariant q original current source target k) :
    ∃ finalStore finalDisk,
      run q z (2*left) (machine q s current)=(machine q finalStore finalDisk,2*left) ∧
      Control q z source target total (PhysicalStreamCursor.blockCount q.block total) finalStore ∧
      DiskInvariant q original finalDisk source target (PhysicalStreamCursor.blockCount q.block total) ∧
      Preserved q s finalStore := by
  induction left generalizing k s current with
  | zero =>
    have he : k=PhysicalStreamCursor.blockCount q.block total := by omega
    subst k
    exact ⟨s,current,rfl,hcontrol,hdisk,Preserved.refl q s⟩
  | succ left ih =>
    have hk : k<PhysicalStreamCursor.blockCount q.block total := by omega
    have hs : source+k<q.N^q.exponent := by omega
    have ht : target+k<q.N^q.exponent := by omega
    have hread := diskInvariant_read q original current source target _ k hdisk hsep hk hs
    let nextStore := pairEffect q z s (original ⟨source+k,hs⟩)
    let nextDisk := Function.update current ⟨target+k,ht⟩ (original ⟨source+k,hs⟩)
    have hpair : run q z 2 (machine q s current)=(machine q nextStore nextDisk,2) := by
      have hh := pair_two q z s current hcontrol.phase_zero
        (by simpa only [blocks,hcontrol.word_count,hcontrol.position] using hk)
        (by rw [hcontrol.source_base,hcontrol.position]; exact hs)
        (by rw [hcontrol.target_base,hcontrol.position]; exact ht)
      simpa only [hcontrol.source_base,hcontrol.target_base,hcontrol.position,hread] using hh
    have hncontrol : Control q z source target total (k+1) nextStore :=
      pair_control q z source target total k s _ hcontrol
        (descriptor_capacity q _ (by omega))
    have hndisk : DiskInvariant q original nextDisk source target (k+1) :=
      diskInvariant_write q original current source target k hdisk hs ht
    obtain ⟨finalStore,finalDisk,hrun,hfinalcontrol,hfinaldisk,hpres⟩ :=
      ih (k+1) nextStore nextDisk hncontrol (by omega) hndisk
    refine ⟨finalStore,finalDisk,?_,hfinalcontrol,hfinaldisk,
      (pair_preserved q z s _).trans q hpres⟩
    rw [show 2*(left+1)=2+2*left by omega,run_add,hpair]
    dsimp only
    rw [hrun]

/-- Initialized finite-disk copy, with exact cost, true policy halt, all
outside-target blocks preserved, and the existing resident-memory bound.
The destination is really written, including when it is the output prefix. -/
theorem run_initialized (q : Configuration) (z : Slots q)
    (n : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hsource : source.val+PhysicalStreamCursor.blockCount q.block n.val ≤ q.N^q.exponent)
    (htarget : target.val+PhysicalStreamCursor.blockCount q.block n.val ≤ q.N^q.exponent)
    (hsep : Disjoint source.val target.val (PhysicalStreamCursor.blockCount q.block n.val)) :
    ∃ finalStore finalDisk,
      run q z (2*PhysicalStreamCursor.blockCount q.block n.val)
        (machine q (initialStore q z n source target s) disk)=
        (machine q finalStore finalDisk,2*PhysicalStreamCursor.blockCount q.block n.val) ∧
      policy q z (pack finalStore)=none ∧
      Control q z source.val target.val n.val
        (PhysicalStreamCursor.blockCount q.block n.val) finalStore ∧
      DiskInvariant q disk finalDisk source.val target.val
        (PhysicalStreamCursor.blockCount q.block n.val) ∧
      Preserved q s finalStore ∧ Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨finalStore,finalDisk,hrun,hcontrol,hdisk,hpres⟩ :=
    run_from q z source.val target.val n.val 0 (PhysicalStreamCursor.blockCount q.block n.val)
      (initialStore q z n source target s) disk disk
      (initial_control q z n source target s) (by omega) hsource htarget hsep
      (diskInvariant_zero q disk source.val target.val)
  refine ⟨finalStore,finalDisk,hrun,?_,hcontrol,hdisk,
    (initial_preserved q z n source target s).trans q hpres,resident_memory q⟩
  apply halt q z finalStore hcontrol.phase_zero
  simp only [blocks,hcontrol.word_count,hcontrol.position,le_refl]

/-- Compaction's actual output prefix, with a charged read/write scan.
The copied handle has base zero only after the finite-disk writes occur. -/
theorem copy_to_prefix (q : Configuration) (z : Slots q)
    (n : Fin (q.N^q.exponent+1)) (source : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hsource : source.val+PhysicalStreamCursor.blockCount q.block n.val ≤ q.N^q.exponent)
    (hsep : PhysicalStreamCursor.blockCount q.block n.val ≤ source.val) :
    ∃ finalStore finalDisk,
      run q z (2*PhysicalStreamCursor.blockCount q.block n.val)
        (machine q (initialStore q z n source
          ⟨0,pow_pos (by have:=q.input_large; omega) _⟩ s) disk)=
        (machine q finalStore finalDisk,2*PhysicalStreamCursor.blockCount q.block n.val) ∧
      policy q z (pack finalStore)=none ∧
      DiskInvariant q disk finalDisk source.val 0 (PhysicalStreamCursor.blockCount q.block n.val) ∧
      Preserved q s finalStore := by
  obtain ⟨finalStore,finalDisk,hrun,hhalt,hcontrol,hdisk,hpres,hmemory⟩ :=
    run_initialized q z n source ⟨0,pow_pos (by have:=q.input_large; omega) _⟩ s disk
      hsource (by simp only [Fin.val_mk,Nat.zero_add]; omega)
      (Or.inr (by simpa only [Fin.val_mk,Nat.zero_add] using hsep))
  exact ⟨finalStore,finalDisk,hrun,hhalt,hdisk,hpres⟩

end CodedSorting.CommonMovementPolicy
