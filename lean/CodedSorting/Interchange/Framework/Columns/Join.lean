import CodedSorting.Interchange.Framework.Memory.ExchangeScan
import CodedSorting.Shared.Memory.Batch.Policy

/-! A counted join on the common finite disk. Each input slab block is read
once. Its at most B useful words are merged into at most two output blocks,
using read/modify/write. No column-file list or saved disk is resident. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonColumnJoin
open WordControl CommonSortingNormalization PhysicalStreamCursor
open CommonLeafProgram (Slots Store RAM Disk Machine phase setPhase machine phase_setPhase)
namespace S
export CommonSortingNormalizationStreams (payload lengthWords cursorWords)
end S

def source (q : Configuration) (z : Slots q) (s : Store q) := decodeWords (s.readers z.reader).base
def target (q : Configuration) (z : Slots q) (s : Store q) := decodeWords (s.writers z.writer).base
def width (q : Configuration) (z : Slots q) (s : Store q) := decodeWords (s.readers z.reader).records
def columns (q : Configuration) (z : Slots q) (s : Store q) :=
  decodeWords (S.lengthWords (s.readers z.reader).resident)
def cursor (q : Configuration) (z : Slots q) (s : Store q) :=
  decodeWords (S.cursorWords (s.readers z.reader).resident)
def buffer (q : Configuration) (z : Slots q) (s : Store q) := S.payload (s.readers z.reader).resident

def stride (q : Configuration) (z : Slots q) (s : Store q) := blockCount q.block (width q z s)
def count (q : Configuration) (z : Slots q) (s : Store q) := columns q z s * stride q z s

def start (B n k : ℕ) := k / blockCount B n * n + k % blockCount B n * B
def useful (B n k : ℕ) := min B (n-k % blockCount B n * B)
def first (B n k : ℕ) := start B n k / B
def last (B n k : ℕ) := (start B n k + useful B n k-1)/B

def address (q : Configuration) (z : Slots q) (lastBlock : Bool) (s : Store q) :=
  target q z s + (if lastBlock then last else first) q.block (width q z s) (cursor q z s)

/-- The source payload replaces only the useful word interval. -/
def merge {B w : ℕ} (n k j : ℕ) (input old : Words B w) : Words B w := fun i =>
  if h : start B n k ≤ j*B+i.val ∧ j*B+i.val < start B n k+useful B n k then
    input ⟨j*B+i.val-start B n k,by have : useful B n k ≤ B := Nat.min_le_left _ _; omega⟩
  else old i

def setBuffer (q : Configuration) (z : Slots q) (b : Words q.block q.w)
    (c : Words q.digits q.w) (s : Store q) : Store q :=
  {s with readers:=Function.update s.readers z.reader {(s.readers z.reader) with
    resident:=Fin.append (Fin.append b (S.lengthWords (s.readers z.reader).resident)) c}}

def hold (q : Configuration) (z : Slots q) (s : Store q) :=
  setPhase q 1 (setBuffer q z s.transfer (S.cursorWords (s.readers z.reader).resident) s)
def mix (q : Configuration) (z : Slots q) (lastBlock : Bool) (s : Store q) :=
  setPhase q (if lastBlock then 4 else 2) {s with transfer := merge (width q z s) (cursor q z s) ((if lastBlock then last else first) q.block (width q z s) (cursor q z s)) (buffer q z s) s.transfer}
def advance (q : Configuration) (z : Slots q) (s : Store q) :=
  setPhase q 0 (setBuffer q z (buffer q z s)
    (encodeNat q.digits q.w (cursor q z s+1)) s)
def mapRAM (q : Configuration) (f : Store q → Store q) (r : RAM q) := pack (f (unpack r))

/-- Five real transfers per slab block, including the second merge when
both endpoint addresses happen to coincide. All control comes from RAM. -/
def policy (q : Configuration) (z : Slots q) : SourcePolicy q := fun ram =>
  let s : Store q := unpack ram
  let win := CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits
  if phase q s=0 then
    if cursor q z s<count q z s then
      if h : source q z s+cursor q z s<q.N^q.exponent then
        some ⟨.read ⟨source q z s+cursor q z s,h⟩ win,mapRAM q (hold q z)⟩
      else none
    else none
  else if phase q s=1 then
    if h : address q z false s<q.N^q.exponent then
      some ⟨.read ⟨address q z false s,h⟩ win,mapRAM q (mix q z false)⟩
    else none
  else if phase q s=2 then
    if h : address q z false s<q.N^q.exponent then
      some ⟨.write ⟨address q z false s,h⟩ win,mapRAM q (setPhase q 3)⟩
    else none
  else if phase q s=3 then
    if h : address q z true s<q.N^q.exponent then
      some ⟨.read ⟨address q z true s,h⟩ win,mapRAM q (mix q z true)⟩
    else none
  else if phase q s=4 then
    if h : address q z true s<q.N^q.exponent then
      some ⟨.write ⟨address q z true s,h⟩ win,mapRAM q (advance q z)⟩
    else none
  else none
abbrev run (q : Configuration) (z : Slots q) := ControlledNormalization.runLogical (policy q z)

def SameFrame (q : Configuration) (s t : Store q) : Prop :=
  t.leaf=s.leaf ∧ t.directories=s.directories ∧ t.shapes=s.shapes ∧
    t.top=s.top ∧ t.pcs=s.pcs ∧ t.writers=s.writers

def Descriptor (q : Configuration) (z : Slots q) (s t : Store q) : Prop :=
  source q z t=source q z s ∧ target q z t=target q z s ∧
    width q z t=width q z s ∧ columns q z t=columns q z s

@[simp] theorem buffer_setBuffer (q : Configuration) (z : Slots q) (s : Store q)
    (b : Words q.block q.w) (c : Words q.digits q.w) : buffer q z (setBuffer q z b c s)=b := by
  funext i; simp [buffer,setBuffer,S.payload]
@[simp] theorem cursorWords_setBuffer (q : Configuration) (z : Slots q) (s : Store q)
    (b : Words q.block q.w) (c : Words q.digits q.w) :
    S.cursorWords ((setBuffer q z b c s).readers z.reader).resident=c := by
  funext i; simp [setBuffer,S.cursorWords]
@[simp] theorem columns_setBuffer (q : Configuration) (z : Slots q) (s : Store q)
    (b : Words q.block q.w) (c : Words q.digits q.w) : columns q z (setBuffer q z b c s)=columns q z s := by
  unfold columns
  congr 1
  funext i
  simp [setBuffer,S.lengthWords]

@[simp] theorem source_setBuffer (q : Configuration) (z : Slots q) (s : Store q)
    (b : Words q.block q.w) (c : Words q.digits q.w) : source q z (setBuffer q z b c s)=source q z s := by
  simp [source,setBuffer]
@[simp] theorem width_setBuffer (q : Configuration) (z : Slots q) (s : Store q)
    (b : Words q.block q.w) (c : Words q.digits q.w) : width q z (setBuffer q z b c s)=width q z s := by
  simp [width,setBuffer]

@[simp] theorem phase_hold (q : Configuration) (z : Slots q) (s : Store q) : phase q (hold q z s)=1 :=
  phase_setPhase q 1 _ (by have:=CommonLeafBatchPolicy.phase_capacity q; omega)
@[simp] theorem phase_mix (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) :
    phase q (mix q z b s)=(if b then 4 else 2) :=
  phase_setPhase q _ _ (by have:=CommonLeafBatchPolicy.phase_capacity q; cases b <;> simp <;> omega)
@[simp] theorem phase_advance (q : Configuration) (z : Slots q) (s : Store q) : phase q (advance q z s)=0 :=
  phase_setPhase q 0 _ (by positivity)

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

 theorem read_source (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : cursor q z s<count q z s)
    (ha : source q z s+cursor q z s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (hold q z {s with transfer:=disk ⟨source q z s+cursor q z s,ha⟩}) disk,1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,ha,
    ControlledNormalization.logicalStep,Normalization.logicalStep,CommonLeafWindow.load_transfer,
    mapRAM,Normalization.transferCost]

 theorem read_target (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) (disk : Disk q)
    (hp : phase q s=(if b then 3 else 1))
    (ha : address q z b s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (mix q z b {s with transfer:=disk ⟨address q z b s,ha⟩}) disk,1) := by
  cases b <;> simp_all [run,ControlledNormalization.runLogical,machine,policy,
    ControlledNormalization.logicalStep,Normalization.logicalStep,CommonLeafWindow.load_transfer,
    mapRAM,Normalization.transferCost]

 theorem write_first (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=2) (ha : address q z false s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (setPhase q 3 s) (Function.update disk ⟨address q z false s,ha⟩ s.transfer),1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,ha,
    ControlledNormalization.logicalStep,Normalization.logicalStep,CommonLeafWindow.slice_transfer,
    mapRAM,Normalization.transferCost]
 theorem write_last (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=4) (ha : address q z true s<q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (advance q z s) (Function.update disk ⟨address q z true s,ha⟩ s.transfer),1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,ha,
    ControlledNormalization.logicalStep,Normalization.logicalStep,CommonLeafWindow.slice_transfer,
    mapRAM,Normalization.transferCost]


@[simp] theorem source_phase (q : Configuration) (z : Slots q) (p : ℕ) (s : Store q) :
    source q z (setPhase q p s)=source q z s := rfl
@[simp] theorem source_transfer (q : Configuration) (z : Slots q) (b : Words q.block q.w) (s : Store q) :
    source q z {s with transfer:=b}=source q z s := rfl
@[simp] theorem source_hold (q : Configuration) (z : Slots q) (s : Store q) :
    source q z (hold q z s)=source q z s := by
  simp [source,hold,setPhase,setBuffer,S.cursorWords,S.lengthWords]
@[simp] theorem source_mix (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) :
    source q z (mix q z b s)=source q z s := rfl

@[simp] theorem target_phase (q : Configuration) (z : Slots q) (p : ℕ) (s : Store q) :
    target q z (setPhase q p s)=target q z s := rfl
@[simp] theorem target_transfer (q : Configuration) (z : Slots q) (b : Words q.block q.w) (s : Store q) :
    target q z {s with transfer:=b}=target q z s := rfl
@[simp] theorem target_hold (q : Configuration) (z : Slots q) (s : Store q) :
    target q z (hold q z s)=target q z s := by
  simp [target,hold,setPhase,setBuffer,S.cursorWords,S.lengthWords]
@[simp] theorem target_mix (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) :
    target q z (mix q z b s)=target q z s := rfl

@[simp] theorem width_phase (q : Configuration) (z : Slots q) (p : ℕ) (s : Store q) :
    width q z (setPhase q p s)=width q z s := rfl
@[simp] theorem width_transfer (q : Configuration) (z : Slots q) (b : Words q.block q.w) (s : Store q) :
    width q z {s with transfer:=b}=width q z s := rfl
@[simp] theorem width_hold (q : Configuration) (z : Slots q) (s : Store q) :
    width q z (hold q z s)=width q z s := by
  simp [width,hold,setPhase,setBuffer,S.cursorWords,S.lengthWords]
@[simp] theorem width_mix (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) :
    width q z (mix q z b s)=width q z s := rfl

@[simp] theorem columns_phase (q : Configuration) (z : Slots q) (p : ℕ) (s : Store q) :
    columns q z (setPhase q p s)=columns q z s := rfl
@[simp] theorem columns_transfer (q : Configuration) (z : Slots q) (b : Words q.block q.w) (s : Store q) :
    columns q z {s with transfer:=b}=columns q z s := rfl
@[simp] theorem columns_hold (q : Configuration) (z : Slots q) (s : Store q) :
    columns q z (hold q z s)=columns q z s := by
  simp only [hold,columns_phase,columns_setBuffer]
@[simp] theorem columns_mix (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) :
    columns q z (mix q z b s)=columns q z s := rfl

@[simp] theorem cursor_phase (q : Configuration) (z : Slots q) (p : ℕ) (s : Store q) :
    cursor q z (setPhase q p s)=cursor q z s := rfl
@[simp] theorem cursor_transfer (q : Configuration) (z : Slots q) (b : Words q.block q.w) (s : Store q) :
    cursor q z {s with transfer:=b}=cursor q z s := rfl
@[simp] theorem cursor_hold (q : Configuration) (z : Slots q) (s : Store q) :
    cursor q z (hold q z s)=cursor q z s := by
  change decodeWords (S.cursorWords ((setBuffer q z s.transfer _ s).readers z.reader).resident)=_
  rw [cursorWords_setBuffer]
  rfl
@[simp] theorem cursor_mix (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) :
    cursor q z (mix q z b s)=cursor q z s := rfl

@[simp] theorem buffer_hold (q : Configuration) (z : Slots q) (s : Store q) :
    buffer q z (hold q z s)=s.transfer := by
  change buffer q z (setBuffer q z s.transfer _ s)=s.transfer
  exact buffer_setBuffer q z s _ _
@[simp] theorem buffer_mix (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) :
    buffer q z (mix q z b s)=buffer q z s := rfl
@[simp] theorem buffer_phase (q : Configuration) (z : Slots q) (p : ℕ) (s : Store q) :
    buffer q z (setPhase q p s)=buffer q z s := rfl
@[simp] theorem buffer_transfer (q : Configuration) (z : Slots q) (b : Words q.block q.w) (s : Store q) :
    buffer q z {s with transfer:=b}=buffer q z s := rfl
@[simp] theorem address_hold (q : Configuration) (z : Slots q) (b : Bool) (s : Store q) :
    address q z b (hold q z s)=address q z b s := by simp [address]
@[simp] theorem address_mix (q : Configuration) (z : Slots q) (b c : Bool) (s : Store q) :
    address q z b (mix q z c s)=address q z b s := rfl
@[simp] theorem address_phase (q : Configuration) (z : Slots q) (b : Bool) (p : ℕ) (s : Store q) :
    address q z b (setPhase q p s)=address q z b s := rfl
@[simp] theorem address_transfer (q : Configuration) (z : Slots q) (b : Bool)
    (v : Words q.block q.w) (s : Store q) :
    address q z b {s with transfer:=v}=address q z b s := rfl

@[simp] theorem source_advance (q : Configuration) (z : Slots q) (s : Store q) :
    source q z (advance q z s)=source q z s := by
  simp only [advance,source_phase,source_setBuffer]
@[simp] theorem target_advance (q : Configuration) (z : Slots q) (s : Store q) :
    target q z (advance q z s)=target q z s := by
  rfl
@[simp] theorem width_advance (q : Configuration) (z : Slots q) (s : Store q) :
    width q z (advance q z s)=width q z s := by
  simp only [advance,width_phase,width_setBuffer]
@[simp] theorem columns_advance (q : Configuration) (z : Slots q) (s : Store q) :
    columns q z (advance q z s)=columns q z s := by
  simp only [advance,columns_phase,columns_setBuffer]

/-- The second target read observes the first target write, including when
both endpoint addresses are the same. -/
theorem five_steps (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : cursor q z s<count q z s)
    (hs : source q z s+cursor q z s<q.N^q.exponent)
    (hf : address q z false s<q.N^q.exponent)
    (he : address q z true s<q.N^q.exponent) :
    let a : Fin (q.N^q.exponent) := ⟨source q z s+cursor q z s,hs⟩
    let b : Fin (q.N^q.exponent) := ⟨address q z false s,hf⟩
    let c : Fin (q.N^q.exponent) := ⟨address q z true s,he⟩
    let firstBlock := merge (width q z s) (cursor q z s)
      (first q.block (width q z s) (cursor q z s)) (disk a) (disk b)
    let middle := Function.update disk b firstBlock
    let lastBlock := merge (width q z s) (cursor q z s)
      (last q.block (width q z s) (cursor q z s)) (disk a) (middle c)
    ∃ t : Store q,
      run q z 5 (machine q s disk)=
        (machine q t (Function.update middle c lastBlock),5) ∧
      phase q t=0 ∧ Descriptor q z s t ∧ SameFrame q s t ∧
      cursor q z t=(cursor q z s+1) % (2^q.w)^q.digits := by
  dsimp only
  let a : Fin (q.N^q.exponent) := ⟨source q z s+cursor q z s,hs⟩
  let b : Fin (q.N^q.exponent) := ⟨address q z false s,hf⟩
  let c : Fin (q.N^q.exponent) := ⟨address q z true s,he⟩
  let s1 := hold q z {s with transfer:=disk a}
  let s2 := mix q z false {s1 with transfer:=disk b}
  let d1 := Function.update disk b s2.transfer
  let s3 := setPhase q 3 s2
  let s4 := mix q z true {s3 with transfer:=d1 c}
  let s5 := advance q z s4
  have hb1 : address q z false s1=address q z false s := by simp [s1]
  have hb2 : address q z false s2=address q z false s := by simp [s2,s1]
  have hc3 : address q z true s3=address q z true s := by simp [s3,s2,s1]
  have hc4 : address q z true s4=address q z true s := by simp [s4,s3,s2,s1]
  have h1 : run q z 1 (machine q s disk)=(machine q s1 disk,1) := read_source q z s disk hp hl hs
  have h2 : run q z 1 (machine q s1 disk)=(machine q s2 disk,1) := by
    have h:=read_target q z false s1 disk (by simp [s1]) (by rw [hb1]; exact hf)
    simpa only [hb1] using h
  have h3 : run q z 1 (machine q s2 disk)=(machine q s3 d1,1) := by
    have h:=write_first q z s2 disk (by simp [s2]) (by rw [hb2]; exact hf)
    simpa only [hb2] using h
  have h4 : run q z 1 (machine q s3 d1)=(machine q s4 d1,1) := by
    have h:=read_target q z true s3 d1
      (phase_setPhase q 3 _ (by have:=CommonLeafBatchPolicy.phase_capacity q; omega))
      (by rw [hc3]; exact he)
    simpa only [hc3] using h
  have h5 : run q z 1 (machine q s4 d1)=
      (machine q s5 (Function.update d1 c s4.transfer),1) := by
    have h:=write_last q z s4 d1 (by simp [s4]) (by rw [hc4]; exact he)
    simpa only [hc4] using h
  have hfirst : s2.transfer=merge (width q z s) (cursor q z s)
      (first q.block (width q z s) (cursor q z s)) (disk a) (disk b) := by
    simp only [s2,mix,Bool.false_eq_true,↓reduceIte,setPhase]
    simp [s1]
  have hlast : s4.transfer=merge (width q z s) (cursor q z s)
      (last q.block (width q z s) (cursor q z s)) (disk a) (d1 c) := by
    simp only [s4,mix,↓reduceIte,setPhase]
    simp [s3,s2,s1]
  refine ⟨s5,?_,phase_advance q z s4,?_,?_,?_⟩
  · have hall : run q z 5 (machine q s disk)=
        (machine q s5 (Function.update d1 c s4.transfer),5) := by
      rw [show 5=1+(1+(1+(1+1))) from rfl,run_add,h1]
      dsimp only
      rw [run_add,h2]
      dsimp only
      rw [run_add,h3]
      dsimp only
      rw [run_add,h4]
      dsimp only
      rw [h5]
    simpa only [hlast,d1,hfirst] using hall
  · simp [Descriptor,s5,s4,s3,s2,s1]
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change decodeWords (S.cursorWords ((setBuffer q z _ _ _).readers z.reader).resident)=_
    rw [cursorWords_setBuffer]
    have hcur : cursor q z s4=cursor q z s := by simp [s4,s3,s2,s1]
    rw [hcur]
    change (finFunctionFinEquiv (finFunctionFinEquiv.symm _)).val=_
    exact congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply _)

/-- Reference disk semantics, used only in proofs. -/
def joinStep {B w : ℕ} (n source target k : ℕ) (disk : ℕ → Words B w) : ℕ → Words B w :=
  let input := disk (source+k)
  let middle := writeBlock disk (target+first B n k)
    (merge n k (first B n k) input (disk (target+first B n k)))
  writeBlock middle (target+last B n k)
    (merge n k (last B n k) input (middle (target+last B n k)))

def joinDisk {B w : ℕ} (n source target k : ℕ) : ℕ → (ℕ → Words B w) → (ℕ → Words B w)
  | 0,disk => disk
  | left+1,disk => joinDisk n source target (k+1) left (joinStep n source target k disk)

end CodedSorting.CommonColumnJoin
