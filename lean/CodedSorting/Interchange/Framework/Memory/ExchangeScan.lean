import CodedSorting.Shared.Memory.Batch.Program
import CodedSorting.Shared.Memory.AllocatedDirectoryXor

section ExchangePolicy
/-! The existing XOR scan as a RAM-only source policy. Each live block
executes read/read/write on the common finite disk. The first reader's
payload retains the left block, its cursor is the scan cursor, and the
existing transfer window holds the right block and then the XOR result.
No file, disk, or input-specific state is captured by the policy. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace CodedSorting.CommonExchangePolicy
open WordControl CommonSortingNormalization PhysicalStreamCursor
open CommonLeafProgram (Store RAM Disk Machine phase setPhase machine phase_setPhase phase_capacity)
namespace Streams
export CommonSortingNormalizationStreams (payload lengthWords cursorWords)
end Streams

structure Slots (q : Configuration) where
  left : Fin q.inventory.readers
  right : Fin q.inventory.readers
  writer : Fin q.inventory.writers
  distinct : left ≠ right

def leftBase (q : Configuration) (z : Slots q) (s : Store q) := decodeWords (s.readers z.left).base
def rightBase (q : Configuration) (z : Slots q) (s : Store q) := decodeWords (s.readers z.right).base
def targetBase (q : Configuration) (z : Slots q) (s : Store q) := decodeWords (s.writers z.writer).base
def records (q : Configuration) (z : Slots q) (s : Store q) := decodeWords (s.readers z.left).records
def cursor (q : Configuration) (z : Slots q) (s : Store q) :=
  decodeWords (Streams.cursorWords (s.readers z.left).resident)
def leftBuffer (q : Configuration) (z : Slots q) (s : Store q) :=
  Streams.payload (s.readers z.left).resident

def setLeft (q : Configuration) (z : Slots q) (block : Words q.block q.w)
    (code : Words q.digits q.w) (s : Store q) : Store q :=
  {s with readers := Function.update s.readers z.left {(s.readers z.left) with
    resident := Fin.append (Fin.append block (Streams.lengthWords (s.readers z.left).resident)) code}}

def firstEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  setPhase q 1 (setLeft q z s.transfer (Streams.cursorWords (s.readers z.left).resident) s)
def secondEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  setPhase q 2 {s with transfer := PhysicalFileHandlesXor.xorBlock (leftBuffer q z s) s.transfer}
def thirdEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  setPhase q 0 (setLeft q z (leftBuffer q z s) (encodeNat q.digits q.w (cursor q z s+1)) s)

def resumeFirst (q : Configuration) (z : Slots q) (ram : RAM q) : RAM q :=
  pack (firstEffect q z (unpack ram))
def resumeSecond (q : Configuration) (z : Slots q) (ram : RAM q) : RAM q :=
  pack (secondEffect q z (unpack ram))
def resumeThird (q : Configuration) (z : Slots q) (ram : RAM q) : RAM q :=
  pack (thirdEffect q z (unpack ram))

/-- All branch conditions and addresses decode only the current common RAM. -/
def policy (q : Configuration) (z : Slots q) : SourcePolicy q := fun ram =>
  let s : Store q := unpack ram
  if phase q s=0 then
    if cursor q z s*(q.block*q.w)<records q z s then
      if h : leftBase q z s+cursor q z s<q.N^q.exponent then
        some ⟨.read ⟨leftBase q z s+cursor q z s,h⟩
          (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),resumeFirst q z⟩
      else none
    else none
  else if phase q s=1 then
    if h : rightBase q z s+cursor q z s<q.N^q.exponent then
      some ⟨.read ⟨rightBase q z s+cursor q z s,h⟩
        (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),resumeSecond q z⟩
    else none
  else if phase q s=2 then
    if h : targetBase q z s+cursor q z s<q.N^q.exponent then
      some ⟨.write ⟨targetBase q z s+cursor q z s,h⟩
        (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),resumeThird q z⟩
    else none
  else none

abbrev run (q : Configuration) (z : Slots q) := ControlledNormalization.runLogical (policy q z)

def cycleStore (q : Configuration) (z : Slots q) (s : Store q)
    (left right : Words q.block q.w) : Store q :=
  thirdEffect q z (secondEffect q z {(firstEffect q z {s with transfer:=left}) with transfer:=right})

@[simp] theorem setLeft_payload (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) (code : Words q.digits q.w) :
    leftBuffer q z (setLeft q z block code s)=block := by
  funext i
  simp [leftBuffer,setLeft,Streams.payload]
@[simp] theorem setLeft_cursorWords (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) (code : Words q.digits q.w) :
    Streams.cursorWords ((setLeft q z block code s).readers z.left).resident=code := by
  funext i
  simp [setLeft,Streams.cursorWords]

@[simp] theorem descriptors_setLeft (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) (code : Words q.digits q.w) :
    leftBase q z (setLeft q z block code s)=leftBase q z s ∧
    rightBase q z (setLeft q z block code s)=rightBase q z s ∧
    targetBase q z (setLeft q z block code s)=targetBase q z s ∧
    records q z (setLeft q z block code s)=records q z s := by
  simp [leftBase,rightBase,targetBase,records,setLeft,Ne.symm z.distinct]

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

theorem first_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : cursor q z s*(q.block*q.w)<records q z s)
    (ha : leftBase q z s+cursor q z s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (firstEffect q z {s with transfer:=disk ⟨leftBase q z s+cursor q z s,ha⟩}) disk,1) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,ha,
    ↓reduceIte,↓reduceDIte,ControlledNormalization.logicalStep,Normalization.logicalStep,
    CommonLeafWindow.load_transfer,resumeFirst,unpack_pack,Normalization.transferCost,Nat.add_zero]

theorem second_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (ha : rightBase q z s+cursor q z s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (secondEffect q z {s with transfer:=disk ⟨rightBase q z s+cursor q z s,ha⟩}) disk,1) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,one_ne_zero,ha,
    ↓reduceIte,↓reduceDIte,ControlledNormalization.logicalStep,Normalization.logicalStep,
    CommonLeafWindow.load_transfer,resumeSecond,unpack_pack,Normalization.transferCost,Nat.add_zero]

theorem third_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=2) (ha : targetBase q z s+cursor q z s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (thirdEffect q z s)
        (Function.update disk ⟨targetBase q z s+cursor q z s,ha⟩ s.transfer),1) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,
    show (2:ℕ)≠0 by decide,show (2:ℕ)≠1 by decide,ha,
    ↓reduceIte,↓reduceDIte,ControlledNormalization.logicalStep,Normalization.logicalStep,
    CommonLeafWindow.slice_transfer,resumeThird,unpack_pack,Normalization.transferCost,Nat.add_zero]

@[simp] theorem first_phase (q : Configuration) (z : Slots q) (s : Store q) :
    phase q (firstEffect q z s)=1 := phase_setPhase q 1 _ (by have := phase_capacity q; omega)
@[simp] theorem second_phase (q : Configuration) (z : Slots q) (s : Store q) :
    phase q (secondEffect q z s)=2 := phase_setPhase q 2 _ (phase_capacity q)
@[simp] theorem third_phase (q : Configuration) (z : Slots q) (s : Store q) :
    phase q (thirdEffect q z s)=0 := phase_setPhase q 0 _ (by positivity)
@[simp] theorem first_cursor (q : Configuration) (z : Slots q) (s : Store q) :
    cursor q z (firstEffect q z s)=cursor q z s := by
  simp only [firstEffect,cursor,setPhase,setLeft_cursorWords]
@[simp] theorem second_cursor (q : Configuration) (z : Slots q) (s : Store q) :
    cursor q z (secondEffect q z s)=cursor q z s := rfl
@[simp] theorem first_rightBase (q : Configuration) (z : Slots q) (s : Store q) :
    rightBase q z (firstEffect q z s)=rightBase q z s := by
  simp [firstEffect,rightBase,setPhase,setLeft,Ne.symm z.distinct]
@[simp] theorem first_targetBase (q : Configuration) (z : Slots q) (s : Store q) :
    targetBase q z (firstEffect q z s)=targetBase q z s := rfl
@[simp] theorem second_targetBase (q : Configuration) (z : Slots q) (s : Store q) :
    targetBase q z (secondEffect q z s)=targetBase q z s := rfl
@[simp] theorem first_buffer (q : Configuration) (z : Slots q) (s : Store q) :
    leftBuffer q z (firstEffect q z s)=s.transfer := by
  change leftBuffer q z (setLeft q z s.transfer _ s)=s.transfer
  exact setLeft_payload q z s _ _

/-- A real three-transfer segment, with the XOR computed solely in the
second read's RAM continuation. -/
theorem three_steps (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : cursor q z s*(q.block*q.w)<records q z s)
    (ha : leftBase q z s+cursor q z s<q.N^q.exponent)
    (hb : rightBase q z s+cursor q z s<q.N^q.exponent)
    (ht : targetBase q z s+cursor q z s<q.N^q.exponent) :
    run q z 3 (machine q s disk)=
      (machine q (cycleStore q z s (disk ⟨leftBase q z s+cursor q z s,ha⟩)
        (disk ⟨rightBase q z s+cursor q z s,hb⟩))
        (Function.update disk ⟨targetBase q z s+cursor q z s,ht⟩
          (PhysicalFileHandlesXor.xorBlock (disk ⟨leftBase q z s+cursor q z s,ha⟩)
            (disk ⟨rightBase q z s+cursor q z s,hb⟩))),3) := by
  let a : Fin (q.N^q.exponent) := ⟨leftBase q z s+cursor q z s,ha⟩
  let b : Fin (q.N^q.exponent) := ⟨rightBase q z s+cursor q z s,hb⟩
  let s1 := firstEffect q z {s with transfer:=disk a}
  let s2 := secondEffect q z {s1 with transfer:=disk b}
  have hp1 : phase q s1=1 := first_phase q z _
  have hp2 : phase q s2=2 := second_phase q z _
  have haddr1 : rightBase q z s1+cursor q z s1=rightBase q z s+cursor q z s := by
    change rightBase q z (firstEffect q z _)+cursor q z (firstEffect q z _)=_
    rw [first_rightBase,first_cursor]
    rfl
  have haddr2 : targetBase q z s2+cursor q z s2=targetBase q z s+cursor q z s := by
    change targetBase q z (secondEffect q z _)+cursor q z (secondEffect q z _)=_
    rw [second_targetBase,second_cursor]
    change targetBase q z (firstEffect q z _)+cursor q z (firstEffect q z _)=_
    rw [first_targetBase,first_cursor]
    rfl
  have htransfer : s2.transfer=PhysicalFileHandlesXor.xorBlock (disk a) (disk b) := by
    change PhysicalFileHandlesXor.xorBlock (leftBuffer q z s1) (disk b)=_
    change PhysicalFileHandlesXor.xorBlock (leftBuffer q z (firstEffect q z _)) (disk b)=_
    rw [first_buffer]
  have h1 : run q z 1 (machine q s disk)=(machine q s1 disk,1) := first_one q z s disk hp hl ha
  have h2 : run q z 1 (machine q s1 disk)=(machine q s2 disk,1) := by
    have hh := second_one q z s1 disk hp1 (by rw [haddr1]; exact hb)
    simpa only [haddr1] using hh
  have h3 := third_one q z s2 disk hp2 (by rw [haddr2]; exact ht)
  simp only [haddr2,htransfer] at h3
  rw [show 3=1+(1+1) from rfl,run_add,h1]
  dsimp only
  rw [run_add,h2]
  dsimp only
  rw [h3]
  rfl

/-- All persistent directories and call frames survive a scan block. -/
def SameFrame (q : Configuration) (s t : Store q) : Prop :=
  t.leaf=s.leaf ∧ t.directories=s.directories ∧ t.shapes=s.shapes ∧
    t.top=s.top ∧ t.pcs=s.pcs ∧ t.writers=s.writers

theorem cycle_frame (q : Configuration) (z : Slots q) (s : Store q)
    (a b : Words q.block q.w) : SameFrame q s (cycleStore q z s a b) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem cycle_descriptors (q : Configuration) (z : Slots q) (s : Store q)
    (a b : Words q.block q.w) :
    leftBase q z (cycleStore q z s a b)=leftBase q z s ∧
    rightBase q z (cycleStore q z s a b)=rightBase q z s ∧
    targetBase q z (cycleStore q z s a b)=targetBase q z s ∧
    records q z (cycleStore q z s a b)=records q z s := by
  simp [cycleStore,firstEffect,secondEffect,thirdEffect,setPhase,setLeft,
    leftBase,rightBase,targetBase,records,Ne.symm z.distinct]

theorem cycle_cursor (q : Configuration) (z : Slots q) (s : Store q)
    (a b : Words q.block q.w) (hc : cursor q z s+1<(2^q.w)^q.digits) :
    cursor q z (cycleStore q z s a b)=cursor q z s+1 := by
  have hcur : cursor q z (secondEffect q z {(firstEffect q z {s with transfer:=a}) with transfer:=b})=cursor q z s := by
    rw [second_cursor]
    change cursor q z (firstEffect q z _)=_
    rw [first_cursor]
    rfl
  change decodeWords (Streams.cursorWords ((setLeft q z _ _ _).readers z.left).resident)=_
  rw [setLeft_cursorWords,hcur]
  exact decodeNat_encode q.digits q.w _ hc

theorem halt (q : Configuration) (z : Slots q) (s : Store q)
    (hp : phase q s=0) (he : records q z s≤cursor q z s*(q.block*q.w)) :
    policy q z (pack s)=none := by
  simp [policy,unpack_pack,hp,show ¬cursor q z s*(q.block*q.w)<records q z s by omega]

end CodedSorting.CommonExchangePolicy
end ExchangePolicy

section ExchangeScan
/-! Complete finite execution of the common XOR source policy. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace CodedSorting.CommonExchangePolicy
open WordControl CommonSortingNormalization PhysicalStreamCursor
open CommonLeafProgram (Store RAM Disk Machine phase setPhase machine phase_setPhase phase_capacity)

open CommonLeafBatchProgram (extendDisk restrictDisk)

theorem extend_update (q : Configuration) (disk : Disk q)
    (a : Fin (q.N^q.exponent)) (block : Words q.block q.w) :
    extendDisk q (Function.update disk a block)=writeBlock (extendDisk q disk) a.val block := by
  funext i
  by_cases hi : i<q.N^q.exponent
  · by_cases he : i=a.val
    · subst i
      simp [extendDisk,writeBlock,a.isLt]
    · have hne : (⟨i,hi⟩ : Fin (q.N^q.exponent))≠a := by
        intro h
        exact he (congrArg Fin.val h)
      simp [extendDisk,writeBlock,hi,he,hne]
  · have he : i≠a.val := by intro h; subst i; exact hi a.isLt
    simp [extendDisk,writeBlock,hi,he]

def Descriptors (q : Configuration) (z : Slots q) (s t : Store q) : Prop :=
  leftBase q z t=leftBase q z s ∧ rightBase q z t=rightBase q z s ∧
    targetBase q z t=targetBase q z s ∧ records q z t=records q z s

theorem block_positive (q : Configuration) : 0<q.block*q.w := by
  exact Nat.mul_pos (CommonLeafProgram.block_positive q) (by have := q.word_width; omega)

/-- Finite execution of the whole counted scan. The reference disk on the
right is precisely the existing sequential XOR interpreter; it is never
an input to the executable policy. -/
theorem run_triples (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (left : ℕ) (hp : phase q s=0)
    (hlimit : cursor q z s+left≤blockCount (q.block*q.w) (records q z s))
    (hcap : cursor q z s+left<(2^q.w)^q.digits)
    (ha : leftBase q z s+cursor q z s+left≤q.N^q.exponent)
    (hb : rightBase q z s+cursor q z s+left≤q.N^q.exponent)
    (ht : targetBase q z s+cursor q z s+left≤q.N^q.exponent) :
    ∃ (t : Store q) (out : Disk q),
      run q z (3*left) (machine q s disk)=(machine q t out,3*left) ∧
      extendDisk q out=PhysicalFileHandlesXor.xorDisk (leftBase q z s) (rightBase q z s)
        (targetBase q z s) (cursor q z s) left (extendDisk q disk) ∧
      cursor q z t=cursor q z s+left ∧ phase q t=0 ∧
      Descriptors q z s t ∧ SameFrame q s t := by
  induction left generalizing s disk with
  | zero =>
      exact ⟨s,disk,rfl,rfl,by omega,hp,⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  | succ left ih =>
      have hl : cursor q z s*(q.block*q.w)<records q z s :=
        (cursor_live_iff _ _ _ (block_positive q)).1 (by omega)
      have ha' : leftBase q z s+cursor q z s<q.N^q.exponent := by omega
      have hb' : rightBase q z s+cursor q z s<q.N^q.exponent := by omega
      have ht' : targetBase q z s+cursor q z s<q.N^q.exponent := by omega
      let a : Fin (q.N^q.exponent) := ⟨leftBase q z s+cursor q z s,ha'⟩
      let b : Fin (q.N^q.exponent) := ⟨rightBase q z s+cursor q z s,hb'⟩
      let c : Fin (q.N^q.exponent) := ⟨targetBase q z s+cursor q z s,ht'⟩
      let next := cycleStore q z s (disk a) (disk b)
      let nextDisk := Function.update disk c (PhysicalFileHandlesXor.xorBlock (disk a) (disk b))
      have hs : run q z 3 (machine q s disk)=(machine q next nextDisk,3) :=
        three_steps q z s disk hp hl ha' hb' ht'
      have hd : Descriptors q z s next := cycle_descriptors q z s _ _
      have hc : cursor q z next=cursor q z s+1 := cycle_cursor q z s _ _ (by omega)
      have hn : phase q next=0 := third_phase q z _
      obtain ⟨t,out,hrun,hout,hcursor,hphase,hdesc,hframe⟩ := ih next nextDisk hn
        (by rw [hc,hd.2.2.2]; omega) (by rw [hc]; omega)
        (by rw [hd.1,hc]; omega) (by rw [hd.2.1,hc]; omega)
        (by rw [hd.2.2.1,hc]; omega)
      refine ⟨t,out,?_,?_,by omega,hphase,?_,?_⟩
      · rw [show 3*(left+1)=3+3*left by omega,run_add,hs]
        dsimp only
        rw [hrun]
      · rw [hout,hd.1,hd.2.1,hd.2.2.1,hc]
        rw [show extendDisk q nextDisk=writeBlock (extendDisk q disk) c.val
          (PhysicalFileHandlesXor.xorBlock (disk a) (disk b)) from extend_update q disk c _]
        simp only [PhysicalFileHandlesXor.xorDisk,extendDisk,ha',hb',dif_pos,a,b,c]
      · exact ⟨hdesc.1.trans hd.1,hdesc.2.1.trans hd.2.1,
          hdesc.2.2.1.trans hd.2.2.1,hdesc.2.2.2.trans hd.2.2.2⟩
      · have hf := cycle_frame q z s (disk a) (disk b)
        exact ⟨hframe.1.trans hf.1,hframe.2.1.trans hf.2.1,
          hframe.2.2.1.trans hf.2.2.1,hframe.2.2.2.1.trans hf.2.2.2.1,
          hframe.2.2.2.2.1.trans hf.2.2.2.2.1,hframe.2.2.2.2.2.trans hf.2.2.2.2.2⟩

theorem count_capacity (q : Configuration) (z : Slots q) (s : Store q) :
    blockCount (q.block*q.w) (records q z s)<(2^q.w)^q.digits := by
  exact (AllocatedDirectoryXor.blockCount_le_records _ _ (block_positive q)).trans_lt
    (finFunctionFinEquiv (s.readers z.left).records).isLt

/-- The counted policy reaches actual `none`, preserves every call frame,
and returns the same complete disk as the existing sequential XOR scan. -/
theorem complete_scan (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hc : cursor q z s=0)
    (ha : leftBase q z s+blockCount (q.block*q.w) (records q z s)≤q.N^q.exponent)
    (hb : rightBase q z s+blockCount (q.block*q.w) (records q z s)≤q.N^q.exponent)
    (ht : targetBase q z s+blockCount (q.block*q.w) (records q z s)≤q.N^q.exponent) :
    ∃ (t : Store q) (out : Disk q),
      run q z (3*blockCount (q.block*q.w) (records q z s)) (machine q s disk)=
        (machine q t out,3*blockCount (q.block*q.w) (records q z s)) ∧
      policy q z (pack t)=none ∧
      extendDisk q out=PhysicalFileHandlesXor.xorDisk (leftBase q z s) (rightBase q z s)
        (targetBase q z s) 0 (blockCount (q.block*q.w) (records q z s)) (extendDisk q disk) ∧
      Descriptors q z s t ∧ SameFrame q s t := by
  obtain ⟨t,out,hr,hd,hcur,hphase,hdesc,hframe⟩ :=
    run_triples q z s disk (blockCount (q.block*q.w) (records q z s)) hp
      (by rw [hc]; omega) (by rw [hc,Nat.zero_add]; exact count_capacity q z s)
      (by simpa only [hc,Nat.add_zero] using ha)
      (by simpa only [hc,Nat.add_zero] using hb)
      (by simpa only [hc,Nat.add_zero] using ht)
  refine ⟨t,out,hr,halt q z t hphase ?_,by simpa only [hc] using hd,hdesc,hframe⟩
  rw [hdesc.2.2.2,hcur,hc,Nat.zero_add]
  have he := cursor_live_iff (q.block*q.w) (records q z s)
    (blockCount (q.block*q.w) (records q z s)) (block_positive q)
  omega

/-- Pointwise output correctness and the full untouched-disk frame, for
fresh output spans. These are consequences of the same charged execution. -/
theorem complete_xor (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hc : cursor q z s=0)
    (ha : leftBase q z s+blockCount (q.block*q.w) (records q z s)≤q.N^q.exponent)
    (hb : rightBase q z s+blockCount (q.block*q.w) (records q z s)≤q.N^q.exponent)
    (ht : targetBase q z s+blockCount (q.block*q.w) (records q z s)≤q.N^q.exponent)
    (hleft : ∀ i j,i<blockCount (q.block*q.w) (records q z s) → 
      j<blockCount (q.block*q.w) (records q z s) → leftBase q z s+i≠targetBase q z s+j)
    (hright : ∀ i j,i<blockCount (q.block*q.w) (records q z s) → 
      j<blockCount (q.block*q.w) (records q z s) → rightBase q z s+i≠targetBase q z s+j) :
    ∃ (t : Store q) (out : Disk q),
      run q z (3*blockCount (q.block*q.w) (records q z s)) (machine q s disk)=
        (machine q t out,3*blockCount (q.block*q.w) (records q z s)) ∧
      policy q z (pack t)=none ∧ SameFrame q s t ∧
      (∀ i,i<blockCount (q.block*q.w) (records q z s) → 
        extendDisk q out (targetBase q z s+i)=PhysicalFileHandlesXor.xorBlock
          (extendDisk q disk (leftBase q z s+i)) (extendDisk q disk (rightBase q z s+i))) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<targetBase q z s ∨
        targetBase q z s+blockCount (q.block*q.w) (records q z s)≤a.val → out a=disk a) := by
  obtain ⟨t,out,hr,hh,hd,_,hf⟩ := complete_scan q z s disk hp hc ha hb ht
  refine ⟨t,out,hr,hh,hf,?_,?_⟩
  · intro i hi
    rw [hd]
    exact PhysicalFileHandlesXor.xorDisk_at _ _ _ _ 0 _ _ (by omega) hleft hright i
      ⟨Nat.zero_le _,by omega⟩
  · intro a haddr
    have he := congrFun hd a.val
    rw [PhysicalFileHandlesXor.xorDisk_outside _ _ _ 0 _ _ _ (by simpa only [Nat.add_zero] using haddr)] at he
    simpa only [extendDisk,dif_pos a.isLt] using he

end CodedSorting.CommonExchangePolicy
end ExchangeScan
