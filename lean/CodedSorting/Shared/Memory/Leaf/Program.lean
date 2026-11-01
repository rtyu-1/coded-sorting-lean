import CodedSorting.Sorting.Resources.Framework.NormalizationFrames
import CodedSorting.Shared.Memory.ResidentLeafBank

section Window
/-! The common controller's transfer buffer is a concrete contiguous window
of its existing source RAM. Reading into that window and writing from it
agree exactly with the corresponding field of `SourceState`. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafWindow
open WordControl SortingResourceBudget CommonSortingNormalization
variable {v : Inventory} {H b d w : ℕ}

def rightWindow (a : ℕ) {L b : ℕ} (win : Normalization.Window L b) :
    Normalization.Window (a+L) b :=
  ⟨a+win.base, by have := win.fits; omega⟩

def firstWindow (b z : ℕ) : Normalization.Window (b+z) b :=
  ⟨0, by omega⟩

theorem load_right {a L b : ℕ} (x : Words a w) (y : Words L w)
    (win : Normalization.Window L b) (block : Words b w) :
    Normalization.load (Fin.append x y) (rightWindow a win) block =
      Fin.append x (Normalization.load y win block) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have hj : ¬ (a+win.base ≤ j.val ∧ j.val < a+win.base+b) := by
      have := j.isLt
      omega
    simp [Normalization.load, rightWindow, hj]
  · intro j
    simp only [Normalization.load, rightWindow, Fin.coe_natAdd, Fin.append_right]
    by_cases h : win.base ≤ j.val ∧ j.val < win.base+b
    · have h' : a+win.base ≤ a+j.val ∧ a+j.val < a+win.base+b := by omega
      simp only [dif_pos h, dif_pos h']
      congr 1
      apply Fin.ext
      change a+j.val-(a+win.base)=j.val-win.base
      omega
    · have h' : ¬ (a+win.base ≤ a+j.val ∧ a+j.val < a+win.base+b) := by omega
      simp only [dif_neg h, dif_neg h', Fin.append_right]

theorem load_first {b z : ℕ} (x block : Words b w) (y : Words z w) :
    Normalization.load (Fin.append x y) (firstWindow b z) block = Fin.append block y := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [Normalization.load, firstWindow, j.isLt]
  · intro j
    have hj : ¬ (0 ≤ b+j.val ∧ b+j.val < 0+b) := by omega
    simp [Normalization.load, firstWindow, hj]

theorem slice_right {a L b : ℕ} (x : Words a w) (y : Words L w)
    (win : Normalization.Window L b) :
    Normalization.slice (Fin.append x y) (rightWindow a win)=Normalization.slice y win := by
  funext j
  change Fin.append x y ⟨a+win.base+j.val, _⟩ = y ⟨win.base+j.val, _⟩
  have he : (⟨a+win.base+j.val, by have := win.fits; have := j.isLt; omega⟩ : Fin (a+L))=
      Fin.natAdd a ⟨win.base+j.val, by have := win.fits; have := j.isLt; omega⟩ := by
    apply Fin.ext
    simp only [Fin.coe_natAdd]
    omega
  rw [he, Fin.append_right]

theorem slice_first {b z : ℕ} (x : Words b w) (y : Words z w) :
    Normalization.slice (Fin.append x y) (firstWindow b z)=x := by
  funext j
  simpa only [Normalization.slice, firstWindow, Nat.zero_add] using Fin.append_left x y j

/-- Its offset skips the resident leaf, input streams, and output streams.
No separate RAM or implicit staging array is allocated by this window. -/
def transferWindow (v : Inventory) (H b d : ℕ) :
    Normalization.Window (sourceCells v H b d) b :=
  rightWindow (ResidentLeafSort.residentWords (512*H) d)
    (rightWindow (v.readers*inputCells b d)
      (rightWindow (v.writers*outputCells b d)
        (firstWindow b ((1+d)+(3*((2*v.keys)*d)+(3*(13*d)+(d+3*v.pc)))))))

theorem load_transfer (s : SourceState v H b d w) (block : Words b w) :
    Normalization.load (pack s) (transferWindow v H b d) block =
      pack {s with transfer:=block} := by
  simp only [pack, transferWindow, load_right, load_first]

theorem slice_transfer (s : SourceState v H b d w) :
    Normalization.slice (pack s) (transferWindow v H b d)=s.transfer := by
  simp only [pack, transferWindow, slice_right, slice_first]

theorem append_first_rest {a z : ℕ} (ram : Words (a+z) w) :
    Fin.append (first ram) (rest ram)=ram := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    exact Fin.append_left _ _ j
  · intro j
    exact Fin.append_right _ _ j

theorem input_pack_unpack (ram : Words (inputCells b d) w) :
    inputWords (inputOfWords ram)=ram := by
  simp only [inputOfWords,inputWords,append_first_rest]

theorem output_pack_unpack (ram : Words (outputCells b d) w) :
    outputWords (outputOfWords ram)=ram := by
  simp only [outputOfWords,outputWords,append_first_rest]

theorem family_pack_unpack {k a : ℕ} (ram : Words (k*a) w) :
    family (familyOfWords ram)=ram := by
  funext i
  change ram (finProdFinEquiv (finProdFinEquiv.symm i))=ram i
  rw [Equiv.apply_symm_apply]

/-- Every source-RAM word is represented by a field; unpacking and repacking
cannot discard hidden RAM state. -/
theorem pack_unpack (ram : Words (sourceCells v H b d) w) : pack (unpack ram)=ram := by
  simp only [unpack,pack,input_pack_unpack,output_pack_unpack,family_pack_unpack,
    append_first_rest]

end CodedSorting.CommonLeafWindow
end Window

section Program
/-! A leaf call is a fixed program on the existing source RAM and one
finite disk. A read transfers one block into the already reserved transfer
window, then its RAM-only continuation copies valid words into the leaf.
After the existing CPU sort, each output block is staged and physically
written. Source and target may overlap: all reads precede every write. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafProgram
open WordControl CommonSortingNormalization
namespace Streams
export CommonSortingNormalizationStreams (cursorWords encode)
end Streams

structure Slots (q : Configuration) where
  reader : Fin q.inventory.readers
  writer : Fin q.inventory.writers

abbrev Store (q : Configuration) :=
  SourceState q.inventory q.height q.block q.digits q.w
abbrev RAM (q : Configuration) := Words q.ramWords q.w
abbrev Disk (q : Configuration) := Normalization.Disk (q.N^q.exponent) q.block (Word q.w)
abbrev Machine (q : Configuration) := Normalization.LogicalState q.ramWords q.block (q.N^q.exponent) (Word q.w)

def phaseIndex (q : Configuration) : Fin (1+q.digits) := ⟨0,by omega⟩
def phase (q : Configuration) (s : Store q) : ℕ := (s.scalars (phaseIndex q)).val
def setPhase (q : Configuration) (p : ℕ) (s : Store q) : Store q :=
  {s with scalars := Function.update s.scalars (phaseIndex q) ⟨p % 2^q.w,Nat.mod_lt _ (by positivity)⟩}

def inputCursor (q : Configuration) (z : Slots q) (s : Store q) : ℕ :=
  decodeWords (Streams.cursorWords (s.readers z.reader).resident)
def outputCursor (q : Configuration) (z : Slots q) (s : Store q) : ℕ :=
  decodeWords (Streams.cursorWords (s.writers z.writer).resident)
def sourceBase (q : Configuration) (z : Slots q) (s : Store q) : ℕ :=
  decodeWords (s.readers z.reader).base
def targetBase (q : Configuration) (z : Slots q) (s : Store q) : ℕ :=
  decodeWords (s.writers z.writer).base

def words (q : Configuration) (s : Store q) : ℕ := 3*ResidentLeafSort.count s.leaf
def blocks (q : Configuration) (s : Store q) : ℕ :=
  PhysicalStreamCursor.blockCount q.block (words q s)

def setInputCursor (q : Configuration) (z : Slots q) (k : ℕ) (s : Store q) : Store q :=
  {s with readers := Function.update s.readers z.reader {(s.readers z.reader) with resident:=Streams.encode q.block q.digits q.w [] k}}
def setOutputCursor (q : Configuration) (z : Slots q) (k : ℕ) (s : Store q) : Store q :=
  {s with writers := Function.update s.writers z.writer {(s.writers z.writer) with resident:=Streams.encode q.block q.digits q.w [] k}}

/-- No record-valued input is accepted here: initialization changes only
counted descriptors and the leaf header. Its payload is filled by real reads. -/
def initialStore (q : Configuration) (z : Slots q) (n : Fin (512*q.height+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) : Store q :=
  setPhase q 0
    {s with
      leaf:=ResidentLeafBank.initializeCount (leaf_header_capacity q) n s.leaf
      readers:=Function.update s.readers z.reader
        ⟨PhysicalStreamCursor.encodeNat q.digits q.w source.val,
          PhysicalStreamCursor.encodeNat q.digits q.w (3*n.val),
          Streams.encode q.block q.digits q.w [] 0⟩
      writers:=Function.update s.writers z.writer
        ⟨PhysicalStreamCursor.encodeNat q.digits q.w target.val,
          Streams.encode q.block q.digits q.w [] 0⟩}

def machine (q : Configuration) (s : Store q) (disk : Disk q) : Machine q := ⟨pack s,disk⟩

/-- This function receives only current RAM, after the actual read. -/
def readResume (q : Configuration) (z : Slots q) (ram : RAM q) : RAM q :=
  let s : Store q := unpack ram
  let k := inputCursor q z s
  pack (setInputCursor q z (k+1)
    {s with leaf:=ResidentLeafBank.putBlock (k*q.block) (min q.block (words q s-k*q.block)) s.transfer s.leaf})

def compute (q : Configuration) (ram : RAM q) : RAM q :=
  let s : Store q := unpack ram
  pack (setPhase q 1 {s with leaf:=ResidentLeafSort.cpu (by have:=q.word_width; omega) s.leaf})

def prepareWrite (q : Configuration) (z : Slots q) (ram : RAM q) : RAM q :=
  let s : Store q := unpack ram
  let offset := outputCursor q z s*q.block
  pack (setPhase q 2 {s with transfer:=ResidentLeafBank.getBlock offset (words q s-offset) s.leaf})

def writeResume (q : Configuration) (z : Slots q) (ram : RAM q) : RAM q :=
  let s : Store q := unpack ram
  pack (setPhase q 1 (setOutputCursor q z (outputCursor q z s+1) s))

/-- The chosen address is read from the current encoded handle and cursor.
The resume closures contain no input state, original disk, or file list. -/
def policy (q : Configuration) (z : Slots q) : SourcePolicy q := fun ram =>
  let s : Store q := unpack ram
  if phase q s=0 then
    if inputCursor q z s*q.block < words q s then
      if h : sourceBase q z s+inputCursor q z s < q.N^q.exponent then
        some ⟨.read ⟨sourceBase q z s+inputCursor q z s,h⟩
          (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),readResume q z⟩
      else none
    else some ⟨.localOp (compute q),id⟩
  else if phase q s=1 then
    if outputCursor q z s*q.block < words q s then
      some ⟨.localOp (prepareWrite q z),id⟩
    else none
  else if phase q s=2 then
    if h : targetBase q z s+outputCursor q z s < q.N^q.exponent then
      some ⟨.write ⟨targetBase q z s+outputCursor q z s,h⟩
        (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),writeResume q z⟩
    else none
  else none

abbrev run (q : Configuration) (z : Slots q) := ControlledNormalization.runLogical (policy q z)

/-- Proof-side descriptions of the local effects. These do not contain a
disk; the one block argument is the result of the actual read operation. -/
def readEffect (q : Configuration) (z : Slots q) (s : Store q) (block : Words q.block q.w) : Store q :=
  setInputCursor q z (inputCursor q z s+1)
    {s with transfer:=block, leaf := ResidentLeafBank.putBlock (inputCursor q z s*q.block) (min q.block (words q s-inputCursor q z s*q.block)) block s.leaf}
def computeEffect (q : Configuration) (s : Store q) : Store q :=
  setPhase q 1 {s with leaf:=ResidentLeafSort.cpu (by have:=q.word_width; omega) s.leaf}
def prepareEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  setPhase q 2 {s with transfer := ResidentLeafBank.getBlock (outputCursor q z s*q.block) (words q s-outputCursor q z s*q.block) s.leaf}
def writeEffect (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  setPhase q 1 (setOutputCursor q z (outputCursor q z s+1) (prepareEffect q z s))

@[simp] theorem phase_setPhase (q : Configuration) (p : ℕ) (s : Store q) (hp : p < 2^q.w) :
    phase q (setPhase q p s)=p := by
  simp only [phase,setPhase,Function.update_self,Nat.mod_eq_of_lt hp]

@[simp] theorem inputCursor_set (q : Configuration) (z : Slots q) (k : ℕ) (s : Store q)
    (hk : k < (2^q.w)^q.digits) : inputCursor q z (setInputCursor q z k s)=k := by
  simp only [inputCursor,setInputCursor,Function.update_self,
    CommonSortingNormalizationStreams.cursor_encode,Nat.mod_eq_of_lt hk]
@[simp] theorem outputCursor_set (q : Configuration) (z : Slots q) (k : ℕ) (s : Store q)
    (hk : k < (2^q.w)^q.digits) : outputCursor q z (setOutputCursor q z k s)=k := by
  simp only [outputCursor,setOutputCursor,Function.update_self,
    CommonSortingNormalizationStreams.cursor_encode,Nat.mod_eq_of_lt hk]

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

/-- A complete read instruction costs one actual transfer into the named
window; its continuation only updates already-counted source words. -/
theorem read_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : inputCursor q z s*q.block < words q s)
    (ha : sourceBase q z s+inputCursor q z s < q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (readEffect q z s (disk ⟨sourceBase q z s+inputCursor q z s,ha⟩)) disk,1) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,ha,
    ↓reduceIte,↓reduceDIte,ControlledNormalization.logicalStep,Normalization.logicalStep,
    CommonLeafWindow.load_transfer,readResume,unpack_pack,Normalization.transferCost,Nat.add_zero]
  rfl

theorem compute_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : words q s ≤ inputCursor q z s*q.block) :
    run q z 1 (machine q s disk)=(machine q (computeEffect q s) disk,0) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,
    show ¬inputCursor q z s*q.block < words q s from by omega,↓reduceIte,
    ControlledNormalization.logicalStep,Normalization.logicalStep,compute,unpack_pack,
    Normalization.transferCost,Nat.add_zero]
  rfl

theorem halt (q : Configuration) (z : Slots q) (s : Store q)
    (hp : phase q s=1) (hl : words q s ≤ outputCursor q z s*q.block) :
    policy q z (pack s)=none := by
  simp only [policy,unpack_pack,hp,one_ne_zero,↓reduceIte,
    show ¬outputCursor q z s*q.block < words q s from by omega]

theorem block_positive (q : Configuration) : 0 < q.block :=
  Normalization.logical_block_positive _ _

theorem phase_capacity (q : Configuration) : 2 < 2^q.w := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) q.word_width
  norm_num at h
  omega

theorem prepare_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hl : outputCursor q z s*q.block < words q s) :
    run q z 1 (machine q s disk)=(machine q (prepareEffect q z s) disk,0) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,
    one_ne_zero,hl,↓reduceIte,ControlledNormalization.logicalStep,Normalization.logicalStep,
    prepareWrite,unpack_pack,Normalization.transferCost,Nat.add_zero]
  rfl

theorem flush_one (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=2)
    (ha : targetBase q z s+outputCursor q z s < q.N^q.exponent) :
    run q z 1 (machine q s disk)=
      (machine q (setPhase q 1 (setOutputCursor q z (outputCursor q z s+1) s))
        (Function.update disk ⟨targetBase q z s+outputCursor q z s,ha⟩ s.transfer),1) := by
  simp only [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,
    show (2:ℕ)≠0 by decide,show (2:ℕ)≠1 by decide,ha,↓reduceIte,↓reduceDIte,
    ControlledNormalization.logicalStep,Normalization.logicalStep,
    CommonLeafWindow.slice_transfer,writeResume,unpack_pack,Normalization.transferCost,Nat.add_zero]
  try rfl

theorem write_two (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hl : outputCursor q z s*q.block < words q s)
    (ha : targetBase q z s+outputCursor q z s < q.N^q.exponent) :
    run q z 2 (machine q s disk)=
      (machine q (writeEffect q z s)
        (Function.update disk ⟨targetBase q z s+outputCursor q z s,ha⟩
          (ResidentLeafBank.getBlock (outputCursor q z s*q.block)
            (words q s-outputCursor q z s*q.block) s.leaf)),1) := by
  rw [show 2=1+1 from rfl,run_add,prepare_one q z s disk hp hl]
  dsimp only
  have hphase : phase q (prepareEffect q z s)=2 := phase_setPhase q 2 _ (phase_capacity q)
  rw [flush_one q z (prepareEffect q z s) disk hphase ha]
  rfl

@[simp] theorem words_readEffect (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) : words q (readEffect q z s block)=words q s := by
  simp only [words,readEffect,setInputCursor,ResidentLeafBank.count_putBlock]
@[simp] theorem words_computeEffect (q : Configuration) (s : Store q) :
    words q (computeEffect q s)=words q s := by
  simp only [words,computeEffect,setPhase,ResidentLeafSort.count_cpu]
@[simp] theorem words_writeEffect (q : Configuration) (z : Slots q) (s : Store q) :
    words q (writeEffect q z s)=words q s := rfl

@[simp] theorem cursor_readEffect (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) (hc : inputCursor q z s+1 < (2^q.w)^q.digits) :
    inputCursor q z (readEffect q z s block)=inputCursor q z s+1 :=
  inputCursor_set q z _ _ hc
@[simp] theorem cursor_writeEffect (q : Configuration) (z : Slots q) (s : Store q)
    (hc : outputCursor q z s+1 < (2^q.w)^q.digits) :
    outputCursor q z (writeEffect q z s)=outputCursor q z s+1 := by
  exact outputCursor_set q z _ _ hc

@[simp] theorem sourceBase_readEffect (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) : sourceBase q z (readEffect q z s block)=sourceBase q z s := by
  simp only [sourceBase,readEffect,setInputCursor,Function.update_self]
@[simp] theorem targetBase_writeEffect (q : Configuration) (z : Slots q) (s : Store q) :
    targetBase q z (writeEffect q z s)=targetBase q z s := by
  simp only [targetBase,writeEffect,setPhase,setOutputCursor,prepareEffect,Function.update_self]

@[simp] theorem phase_readEffect (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) : phase q (readEffect q z s block)=phase q s := rfl
@[simp] theorem phase_computeEffect (q : Configuration) (s : Store q) :
    phase q (computeEffect q s)=1 := phase_setPhase q 1 _ (by have:=phase_capacity q; omega)
@[simp] theorem phase_writeEffect (q : Configuration) (z : Slots q) (s : Store q) :
    phase q (writeEffect q z s)=1 := phase_setPhase q 1 _ (by have:=phase_capacity q; omega)

end CodedSorting.CommonLeafProgram
end Program

section Load
/-! The complete leaf-loading loop executes real logical block reads.
`diskWord` and the prefix invariant are specifications only; the program
receives neither a contents function nor an initial-disk snapshot. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafLoad
open WordControl CommonSortingNormalization CommonLeafProgram
noncomputable section

def diskWord (q : Configuration) (disk : Disk q) (base i : ℕ) : Word q.w :=
  if h : base+i/q.block < q.N^q.exponent then
    disk ⟨base+i/q.block,h⟩ ⟨i%q.block,Nat.mod_lt _ (block_positive q)⟩
  else 0

theorem diskWord_block (q : Configuration) (disk : Disk q) (base k : ℕ)
    (ha : base+k < q.N^q.exponent) (j : Fin q.block) :
    diskWord q disk base (k*q.block+j.val)=disk ⟨base+k,ha⟩ j := by
  have hd : (k*q.block+j.val)/q.block=k := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (block_positive q),Nat.div_eq_of_lt j.isLt]
    omega
  have hm : (k*q.block+j.val)%q.block=j.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  simp only [diskWord,hd,ha,↓reduceDIte,hm]

/-- These fields are outside the leaf payload and its read cursor. -/
structure Preserved (q : Configuration) (before after : Store q) : Prop where
  header : ResidentLeafSort.header after.leaf=ResidentLeafSort.header before.leaf
  writers : after.writers=before.writers
  scalars : after.scalars=before.scalars
  directories : after.directories=before.directories
  shapes : after.shapes=before.shapes
  top : after.top=before.top
  pcs : after.pcs=before.pcs

theorem Preserved.refl (q : Configuration) (s : Store q) : Preserved q s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem Preserved.trans (q : Configuration) {a b c : Store q}
    (hab : Preserved q a b) (hbc : Preserved q b c) : Preserved q a c :=
  ⟨hbc.header.trans hab.header,hbc.writers.trans hab.writers,hbc.scalars.trans hab.scalars,
    hbc.directories.trans hab.directories,hbc.shapes.trans hab.shapes,
    hbc.top.trans hab.top,hbc.pcs.trans hab.pcs⟩

theorem preserved_readEffect (q : Configuration) (z : Slots q) (s : Store q)
    (block : Words q.block q.w) : Preserved q s (readEffect q z s block) := by
  constructor
  · exact ResidentLeafBank.header_putBlock _ _ _ _
  all_goals rfl

theorem Preserved.words (q : Configuration) {s t : Store q} (h : Preserved q s t) :
    words q t=words q s := by
  simp only [CommonLeafProgram.words,ResidentLeafSort.count,h.header]

theorem Preserved.outputCursor (q : Configuration) (z : Slots q) {s t : Store q}
    (h : Preserved q s t) : outputCursor q z t=outputCursor q z s := by
  simp only [CommonLeafProgram.outputCursor,h.writers]

theorem Preserved.targetBase (q : Configuration) (z : Slots q) {s t : Store q}
    (h : Preserved q s t) : targetBase q z t=targetBase q z s := by
  simp only [CommonLeafProgram.targetBase,h.writers]

structure Prefix (q : Configuration) (z : Slots q) (initial : Store q)
    (disk : Disk q) (k : ℕ) (loaded : Store q) : Prop where
  phase_zero : phase q loaded=0
  cursor : inputCursor q z loaded=k
  source : sourceBase q z loaded=sourceBase q z initial
  preserved : Preserved q initial loaded
  contents : ∀ i : Fin ((512*q.height)*3), i.val<min (words q initial) (k*q.block) →
    ResidentLeafBank.raw loaded.leaf i=diskWord q disk (sourceBase q z initial) i.val

/-- Run exactly k load instructions, leaving the common disk unchanged.
Every returned transfer count belongs to this same program execution. -/
theorem read_prefix (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hc : inputCursor q z s=0)
    (ha : sourceBase q z s+blocks q s≤q.N^q.exponent)
    (hcap : blocks q s<(2^q.w)^q.digits) (k : ℕ) (hk : k≤blocks q s) :
    ∃ loaded, run q z k (machine q s disk)=(machine q loaded disk,k) ∧
      Prefix q z s disk k loaded := by
  induction k with
  | zero =>
    refine ⟨s,rfl,⟨hp,hc,rfl,Preserved.refl q s,?_⟩⟩
    intro i hi
    omega
  | succ k ih =>
    obtain ⟨loaded,hrun,hinv⟩ := ih (by omega)
    have hlt : k<blocks q s := by omega
    have hlive : k*q.block<words q s :=
      (PhysicalStreamCursor.cursor_live_iff q.block (words q s) k (block_positive q)).1 hlt
    have haddr : sourceBase q z s+k<q.N^q.exponent := by omega
    let block := disk ⟨sourceBase q z s+k,haddr⟩
    let next := readEffect q z loaded block
    have hwords := hinv.preserved.words q
    have hactual : run q z 1 (machine q loaded disk)=(machine q next disk,1) := by
      have hr := read_one q z loaded disk hinv.phase_zero
        (by simpa only [hinv.cursor,hwords] using hlive)
        (by simpa only [hinv.source,hinv.cursor] using haddr)
      simpa only [hinv.source,hinv.cursor] using hr
    refine ⟨next,?_,?_⟩
    · rw [show k+1=k+1 from rfl,run_add,hrun]
      dsimp only
      rw [hactual]
    · refine ⟨?_,?_,?_,?_,?_⟩
      · exact (phase_readEffect q z loaded block).trans hinv.phase_zero
      · have hnext : inputCursor q z loaded+1<(2^q.w)^q.digits := by rw [hinv.cursor]; omega
        exact (cursor_readEffect q z loaded block hnext).trans (by rw [hinv.cursor])
      · exact (sourceBase_readEffect q z loaded block).trans hinv.source
      · exact hinv.preserved.trans q (preserved_readEffect q z loaded block)
      · intro i hi
        have he := ResidentLeafBank.putBlock_extends (k*q.block) (words q s) block loaded.leaf
          (diskWord q disk (sourceBase q z s))
          (fun j hj => hinv.contents j (by omega))
          (fun j _ => (diskWord_block q disk (sourceBase q z s) k haddr j).symm)
        have hpref := he i (by simpa only [Nat.succ_mul] using hi)
        change ResidentLeafBank.raw (ResidentLeafBank.putBlock
          (inputCursor q z loaded*q.block)
          (min q.block (words q loaded-inputCursor q z loaded*q.block)) block loaded.leaf) i=_
        simpa only [hinv.cursor,hwords] using hpref

theorem blocks_cover (q : Configuration) (s : Store q) : words q s≤blocks q s*q.block := by
  have hn : ¬blocks q s*q.block<words q s := by
    intro hl
    have hh := (PhysicalStreamCursor.cursor_live_iff q.block (words q s) (blocks q s)
      (block_positive q)).2 hl
    exact Nat.lt_irrefl _ hh
  omega

/-- The complete real read loop fills the valid leaf prefix. No payload
is supplied by the initializer, and no disk contents are used by a CPU step. -/
theorem load (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hc : inputCursor q z s=0)
    (ha : sourceBase q z s+blocks q s≤q.N^q.exponent)
    (hcap : blocks q s<(2^q.w)^q.digits) :
    ∃ loaded, run q z (blocks q s) (machine q s disk)=(machine q loaded disk,blocks q s) ∧
      phase q loaded=0 ∧ inputCursor q z loaded=blocks q s ∧
      sourceBase q z loaded=sourceBase q z s ∧ Preserved q s loaded ∧
      ∀ i : Fin ((512*q.height)*3), i.val<words q s →
        ResidentLeafBank.raw loaded.leaf i=diskWord q disk (sourceBase q z s) i.val := by
  obtain ⟨loaded,hrun,hinv⟩ := read_prefix q z s disk hp hc ha hcap (blocks q s) le_rfl
  refine ⟨loaded,hrun,hinv.phase_zero,hinv.cursor,hinv.source,hinv.preserved,?_⟩
  intro i hi
  exact hinv.contents i (by simpa only [Nat.min_eq_left (blocks_cover q s)] using hi)

end
end CodedSorting.CommonLeafLoad
end Load

section Init
/-! The actual leaf initializer writes only descriptors and the length
header. The common resource reserve implies that every possible leaf
length and cursor fits its existing multiword field. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafInit
open WordControl SortingResourceBudget CommonSortingNormalization CommonLeafProgram
noncomputable section

theorem height_positive (q : Configuration) : 0<q.height :=
  (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
    (by have := q.block_memory; omega)).1

theorem words_region (q : Configuration) (s : Store q) : words q s<q.N^q.exponent := by
  have hC : 1537≤reserve q.inventory q.c q.digits := by
    have hh := (reserve_bounds q.inventory q.c q.digits).1
    unfold payloadCoefficient at hh
    omega
  have hh := height_positive q
  have hn := ResidentLeafSort.count_le s.leaf
  have hdiv : q.height*reserve q.inventory q.c q.digits≤q.M := Nat.div_mul_le_self _ _
  have hwords : words q s<q.N := by
    unfold words
    nlinarith [q.memory_input]
  have hpow : q.N≤q.N^q.exponent := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (by have := q.input_large; omega : 0<q.N) q.exponent_pos
  exact hwords.trans_le hpow

theorem blocks_le_words (q : Configuration) (s : Store q) : blocks q s≤words q s := by
  have hb := block_positive q
  have hm : words q s≤words q s*q.block := Nat.le_mul_of_pos_right _ hb
  have hsub := Nat.sub_add_cancel (show 1≤words q s+q.block by omega)
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hb).2
  change words q s+q.block-1<(words q s+1)*q.block
  nlinarith only [hm,hsub]

theorem blocks_region (q : Configuration) (s : Store q) : blocks q s<q.N^q.exponent :=
  (blocks_le_words q s).trans_lt (words_region q s)

theorem blocks_capacity (q : Configuration) (s : Store q) :
    blocks q s<(2^q.w)^q.digits :=
  descriptor_capacity q _ (blocks_region q s).le

@[simp] theorem count_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    ResidentLeafSort.count (initialStore q z n source target s).leaf=n.val := by
  simp only [initialStore,setPhase,ResidentLeafBank.count_initializeCount]

@[simp] theorem words_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    words q (initialStore q z n source target s)=3*n.val := by
  simp only [words,count_initial]

@[simp] theorem blocks_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    blocks q (initialStore q z n source target s)=PhysicalStreamCursor.blockCount q.block (3*n.val) := by
  simp only [blocks,words_initial]

@[simp] theorem phase_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    phase q (initialStore q z n source target s)=0 := by
  apply phase_setPhase
  positivity

@[simp] theorem inputCursor_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    inputCursor q z (initialStore q z n source target s)=0 := by
  simp only [initialStore,setPhase,inputCursor,Function.update_self,
    CommonSortingNormalizationStreams.cursor_encode,Nat.zero_mod]

@[simp] theorem outputCursor_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    outputCursor q z (initialStore q z n source target s)=0 := by
  simp only [initialStore,setPhase,outputCursor,Function.update_self,
    CommonSortingNormalizationStreams.cursor_encode,Nat.zero_mod]

@[simp] theorem sourceBase_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    sourceBase q z (initialStore q z n source target s)=source.val := by
  simp only [initialStore,setPhase,sourceBase,Function.update_self]
  exact PhysicalStreamCursor.decodeNat_encode q.digits q.w source.val
    (descriptor_capacity q source.val source.isLt.le)

@[simp] theorem targetBase_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    targetBase q z (initialStore q z n source target s)=target.val := by
  simp only [initialStore,setPhase,targetBase,Function.update_self]
  exact PhysicalStreamCursor.decodeNat_encode q.digits q.w target.val
    (descriptor_capacity q target.val target.isLt.le)

/-- No input record is copied into RAM during initialization. -/
@[simp] theorem raw_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    ResidentLeafBank.raw (initialStore q z n source target s).leaf=ResidentLeafBank.raw s.leaf := by
  exact ResidentLeafBank.raw_initializeCount _ _ _

theorem frames_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent)) (s : Store q) :
    (initialStore q z n source target s).directories=s.directories ∧
      (initialStore q z n source target s).shapes=s.shapes ∧
      (initialStore q z n source target s).top=s.top ∧
      (initialStore q z n source target s).pcs=s.pcs := ⟨rfl,rfl,rfl,rfl⟩

/-- Concrete initialization discharges phase, cursor, and capacity premises
of the real load loop. Only the source span must lie on the common disk. -/
theorem load_initialized (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hsource : source.val+PhysicalStreamCursor.blockCount q.block (3*n.val)≤q.N^q.exponent) :
    let initial := initialStore q z n source target s
    ∃ loaded, run q z (blocks q initial) (machine q initial disk)=(machine q loaded disk,blocks q initial) ∧
      phase q loaded=0 ∧ inputCursor q z loaded=blocks q initial ∧
      sourceBase q z loaded=sourceBase q z initial ∧ CommonLeafLoad.Preserved q initial loaded ∧
      ∀ i : Fin ((512*q.height)*3), i.val<words q initial →
        ResidentLeafBank.raw loaded.leaf i=CommonLeafLoad.diskWord q disk (sourceBase q z initial) i.val := by
  apply CommonLeafLoad.load q z _ disk
  · exact phase_initial q z n source target s
  · exact inputCursor_initial q z n source target s
  · simpa only [sourceBase_initial,blocks_initial] using hsource
  · exact blocks_capacity q _

end
end CodedSorting.CommonLeafInit
end Init
