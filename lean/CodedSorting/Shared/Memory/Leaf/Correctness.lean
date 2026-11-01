import CodedSorting.Shared.Memory.Leaf.Program

section Disk
/-! A finite-disk reference for successive writes. This is used only in
execution specifications: the real leaf policy assembles each block from
its current resident bank and performs the corresponding write command. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafDisk
open WordControl
variable {R b w : ℕ}

abbrev Disk (R b w : ℕ) := Fin R → Words b w

def writeAt (disk : Disk R b w) (address : ℕ) (block : Words b w) : Disk R b w :=
  if h : address < R then Function.update disk ⟨address,h⟩ block else disk

def writePrefix (base : ℕ) (produce : ℕ → Words b w) : ℕ → Disk R b w → Disk R b w
  | 0,disk => disk
  | k+1,disk => writeAt (writePrefix base produce k disk) (base+k) (produce k)

theorem prefix_succ_of_lt {base k : ℕ} {produce : ℕ → Words b w} {disk : Disk R b w}
    (ha : base+k < R) :
    writePrefix base produce (k+1) disk=
      Function.update (writePrefix base produce k disk) ⟨base+k,ha⟩ (produce k) := by
  simp only [writePrefix,writeAt,dif_pos ha]

theorem prefix_at (base : ℕ) (produce : ℕ → Words b w) (k : ℕ) (disk : Disk R b w)
    (hfit : base+k ≤ R) (i : ℕ) (hi : i < k) :
    writePrefix base produce k disk ⟨base+i,by omega⟩=produce i := by
  induction k with
  | zero => omega
  | succ k ih =>
    have ha : base+k < R := by omega
    rw [prefix_succ_of_lt ha]
    by_cases he : i=k
    · subst i
      exact Function.update_self _ _ _
    · have hne : (⟨base+i,by omega⟩ : Fin R)≠⟨base+k,ha⟩ := by
        intro h
        have hv := congrArg Fin.val h
        dsimp only at hv
        omega
      rw [Function.update_of_ne hne]
      exact ih (by omega) (by omega)

theorem prefix_outside (base : ℕ) (produce : ℕ → Words b w) (k : ℕ) (disk : Disk R b w)
    (a : Fin R) (hout : a.val < base ∨ base+k ≤ a.val) :
    writePrefix base produce k disk a=disk a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hout' : a.val < base ∨ base+k ≤ a.val := by omega
    simp only [writePrefix,writeAt]
    split_ifs with ha
    · have hne : a≠⟨base+k,ha⟩ := by
        intro he
        have hv := congrArg Fin.val he
        dsimp only at hv
        omega
      rw [Function.update_of_ne hne]
      exact ih hout'
    · exact ih hout'

end CodedSorting.CommonLeafDisk
end Disk

section Write
/-! Actual finite-disk output of the already resident sorted leaf. The
reference prefix used in proofs is not stored by the running program. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafWrite
open WordControl CommonSortingNormalization CommonLeafProgram

def stores (q : Configuration) (z : Slots q) (s : Store q) : ℕ → Store q
  | 0 => s
  | k+1 => writeEffect q z (stores q z s k)

@[simp] theorem stores_leaf (q : Configuration) (z : Slots q) (s : Store q) (k : ℕ) :
    (stores q z s k).leaf=s.leaf := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

@[simp] theorem stores_words (q : Configuration) (z : Slots q) (s : Store q) (k : ℕ) :
    words q (stores q z s k)=words q s := by simp only [words,stores_leaf]

@[simp] theorem stores_base (q : Configuration) (z : Slots q) (s : Store q) (k : ℕ) :
    targetBase q z (stores q z s k)=targetBase q z s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [stores,targetBase_writeEffect,ih]

theorem stores_phase (q : Configuration) (z : Slots q) (s : Store q) (k : ℕ)
    (hp : phase q s=1) : phase q (stores q z s k)=1 := by
  cases k with
  | zero => exact hp
  | succ k => exact phase_writeEffect q z _

theorem stores_cursor (q : Configuration) (z : Slots q) (s : Store q) (k : ℕ)
    (hc : outputCursor q z s=0) (hk : k < (2^q.w)^q.digits) :
    outputCursor q z (stores q z s k)=k := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    have he := ih (by omega)
    rw [stores,cursor_writeEffect q z _ (by rw [he]; exact hk),he]

def frameView (q : Configuration) (s : Store q) :=
  (s.directories,s.shapes,s.top,s.pcs)

@[simp] theorem stores_frames (q : Configuration) (z : Slots q) (s : Store q) (k : ℕ) :
    frameView q (stores q z s k)=frameView q s := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- A word block is assembled only from the current resident bank, with
zero padding after the live prefix of the final block. -/
def block (q : Configuration) (s : Store q) (k : ℕ) : Words q.block q.w :=
  ResidentLeafBank.getBlock (k*q.block) (words q s-k*q.block) s.leaf

/-- Each iteration comprises one RAM-only staging instruction and one
actual write; all output bytes come from the unchanged current leaf bank. -/
theorem run_writes (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hc : outputCursor q z s=0)
    (hfit : targetBase q z s+blocks q s ≤ q.N^q.exponent)
    (hcap : blocks q s < (2^q.w)^q.digits) (k : ℕ) (hk : k ≤ blocks q s) :
    run q z (2*k) (machine q s disk)=
      (machine q (stores q z s k)
        (CommonLeafDisk.writePrefix (targetBase q z s) (block q s) k disk),k) := by
  induction k with
  | zero => simp only [Nat.mul_zero,run,ControlledNormalization.runLogical,stores,CommonLeafDisk.writePrefix]
  | succ k ih =>
    have hk' : k ≤ blocks q s := by omega
    have hr := ih hk'
    have hcur := stores_cursor q z s k hc (by omega)
    have hphase := stores_phase q z s k hp
    have hread : k*q.block < words q s :=
      (PhysicalStreamCursor.cursor_live_iff q.block (words q s) k (block_positive q)).1 (show k<blocks q s by omega)
    have hl : outputCursor q z (stores q z s k)*q.block < words q (stores q z s k) := by
      simpa only [hcur,stores_words] using hread
    have ha : targetBase q z (stores q z s k)+outputCursor q z (stores q z s k) < q.N^q.exponent := by
      rw [stores_base,hcur]
      omega
    rw [show 2*(k+1)=2*k+2 by omega,run_add,hr]
    dsimp only
    rw [write_two q z _ _ hphase hl ha]
    simp only [hcur,stores_base,stores_words,stores_leaf]
    rw [CommonLeafDisk.prefix_succ_of_lt (by omega)]
    rfl

/-- Termination, exact write charge, and the resulting common disk belong
to this very run. The final partial block is included in `blocks`. -/
theorem complete_write (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hc : outputCursor q z s=0)
    (hfit : targetBase q z s+blocks q s ≤ q.N^q.exponent)
    (hcap : blocks q s < (2^q.w)^q.digits) :
    let result := run q z (2*blocks q s) (machine q s disk)
    result.1.ram=pack (stores q z s (blocks q s)) ∧
    result.1.disk=CommonLeafDisk.writePrefix (targetBase q z s) (block q s) (blocks q s) disk ∧
    result.2=blocks q s ∧ policy q z result.1.ram=none := by
  dsimp only
  rw [run_writes q z s disk hp hc hfit hcap _ (by rfl)]
  refine ⟨rfl,rfl,rfl,?_⟩
  apply halt q z _ (stores_phase q z s _ hp)
  rw [stores_words,stores_cursor q z s _ hc hcap]
  have h := PhysicalStreamCursor.cursor_live_iff q.block (words q s) (blocks q s) (block_positive q)
  unfold blocks at h ⊢
  omega

end CodedSorting.CommonLeafWrite
end Write

section Correctness
/-! A complete disk-to-disk leaf call. Input records are specification
objects only: the fixed policy first reads their raw words into its one
resident bank, sorts that bank, and writes it back. All claims concern the
same execution and the same disk, including partial final blocks. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafCorrectness
open WordControl CommonSortingNormalization CommonLeafProgram CommonLeafLoad CommonLeafWrite

/-- Record coordinates are laid out in exactly three consecutive words. -/
def position {n : ℕ} (i : Fin n) (j : Fin 3) : ℕ := (finProdFinEquiv (i,j)).val

def InputRep (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (records : Fin (ResidentLeafSort.count s.leaf) → KeyRecordWords.Record q.w) : Prop :=
  ∀ i j, diskWord q disk (sourceBase q z s) (position i j)=
    KeyRecordWords.encode q.w (by have:=q.word_width; omega) (records i) j

/-- Reading back any live word of the written region recovers the current
leaf bank. Padding is excluded from this payload statement. -/
theorem written_word (q : Configuration) (s : Store q) (disk : Disk q) (base : ℕ)
    (hfit : base+blocks q s≤q.N^q.exponent)
    (i : Fin ((512*q.height)*3)) (hi : i.val<words q s) :
    diskWord q (CommonLeafDisk.writePrefix base (block q s) (blocks q s) disk) base i.val=
      ResidentLeafBank.raw s.leaf i := by
  let k := i.val/q.block
  let j : Fin q.block := ⟨i.val%q.block,Nat.mod_lt _ (block_positive q)⟩
  have he : k*q.block+j.val=i.val := by
    dsimp [k,j]
    simpa only [Nat.mul_comm] using Nat.div_add_mod i.val q.block
  have hk : k<blocks q s :=
    (PhysicalStreamCursor.cursor_live_iff q.block (words q s) k (block_positive q)).2 (by omega)
  have ha : base+k<q.N^q.exponent := by omega
  rw [←he,diskWord_block q _ base k ha j]
  rw [CommonLeafDisk.prefix_at base (block q s) (blocks q s) disk hfit k hk]
  unfold block
  rw [ResidentLeafBank.getBlock_at _ _ s.leaf j (by omega) (by omega)]
  congr 1
  apply Fin.ext
  exact he

/-- The actual composed run halts, uses exactly one read and one write per
live block, outputs the existing `sortColumn`, and preserves all unrelated
blocks and the resident recursive frames. The input/output regions may overlap. -/
theorem complete_leaf (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hin : inputCursor q z s=0) (hout : outputCursor q z s=0)
    (hsource : sourceBase q z s+blocks q s≤q.N^q.exponent)
    (htarget : targetBase q z s+blocks q s≤q.N^q.exponent)
    (records : Fin (ResidentLeafSort.count s.leaf) → KeyRecordWords.Record q.w)
    (hrecords : InputRep q z s disk records) :
    let result := run q z (3*blocks q s+1) (machine q s disk)
    result.2=2*blocks q s ∧ policy q z result.1.ram=none ∧
    (∀ i j, diskWord q result.1.disk (targetBase q z s) (position i j)=
      KeyRecordWords.encode q.w (by have:=q.word_width; omega)
        (Columnsort.sortColumn records i) j) ∧
    (∀ a : Fin (q.N^q.exponent), a.val<targetBase q z s ∨ targetBase q z s+blocks q s≤a.val →
      result.1.disk a=disk a) ∧
    frameView q (unpack result.1.ram)=frameView q s := by
  have hcap := CommonLeafInit.blocks_capacity q s
  obtain ⟨loaded,hr,hp',hc',hs',hpres,hpayload⟩ := load q z s disk hp hin hsource hcap
  have hwloaded := hpres.words q
  have hnloaded : ResidentLeafSort.count loaded.leaf=ResidentLeafSort.count s.leaf := by
    simp only [ResidentLeafSort.count,hpres.header]
  let sorted := computeEffect q loaded
  have hwsorted : words q sorted=words q s := (words_computeEffect q loaded).trans hwloaded
  have hbsorted : blocks q sorted=blocks q s := by simp only [blocks,hwsorted]
  have htsorted : targetBase q z sorted=targetBase q z s := hpres.targetBase q z
  have hcsorted : outputCursor q z sorted=0 := (hpres.outputCursor q z).trans hout
  have hpsorted : phase q sorted=1 := phase_computeEffect q loaded
  have hcompute : run q z 1 (machine q loaded disk)=(machine q sorted disk,0) :=
    compute_one q z loaded disk hp' (by rw [hc',hwloaded]; exact blocks_cover q s)
  have hwrite := run_writes q z sorted disk hpsorted hcsorted
    (by rw [htsorted,hbsorted]; exact htarget) (by rw [hbsorted]; exact hcap)
    (blocks q s) (by rw [hbsorted])
  let final := stores q z sorted (blocks q s)
  let finalDisk := CommonLeafDisk.writePrefix (targetBase q z s) (block q sorted) (blocks q s) disk
  have hwhole : run q z (3*blocks q s+1) (machine q s disk)=
      (machine q final finalDisk,2*blocks q s) := by
    rw [show 3*blocks q s+1=blocks q s+(1+2*blocks q s) by omega,run_add,hr]
    dsimp only
    rw [run_add,hcompute]
    dsimp only
    rw [hwrite,htsorted]
    dsimp only [final,finalDisk,machine]
    congr 1
    omega
  dsimp only
  rw [hwhole]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · apply halt q z final (stores_phase q z sorted _ hpsorted)
    change words q (stores q z sorted (blocks q s)) ≤
      outputCursor q z (stores q z sorted (blocks q s))*q.block
    rw [stores_words,stores_cursor q z sorted _ hcsorted hcap,hwsorted]
    exact blocks_cover q s
  · have hraw : ∀ (i : Fin (ResidentLeafSort.count s.leaf)) (j : Fin 3),
        ResidentLeafBank.raw loaded.leaf (finProdFinEquiv
          (⟨i.val,by have hc:=ResidentLeafSort.count_le loaded.leaf; have hi:=i.isLt; omega⟩,j))=
            KeyRecordWords.encode q.w (by have:=q.word_width; omega) (records i) j := by
      intro i j
      rw [hpayload _ (by
        have hh := (finProdFinEquiv (i,j)).isLt
        change (finProdFinEquiv (i,j)).val<3*ResidentLeafSort.count s.leaf
        omega)]
      exact hrecords i j
    have hcpu := ResidentLeafBank.cpu_exact_of_raw (by have:=q.word_width; omega)
      loaded.leaf hnloaded records hraw
    intro i j
    let idx : Fin ((512*q.height)*3) := finProdFinEquiv
      (⟨i.val,by have hc:=ResidentLeafSort.count_le loaded.leaf; have hi:=i.isLt; omega⟩,j)
    have hidx : idx.val<words q sorted := by
      rw [hwsorted]
      have hh := (finProdFinEquiv (i,j)).isLt
      change (finProdFinEquiv (i,j)).val<3*ResidentLeafSort.count s.leaf
      omega
    have hw := written_word q sorted disk (targetBase q z s)
      (by rw [hbsorted]; exact htarget) idx hidx
    rw [hbsorted] at hw
    exact hw.trans (hcpu i j)
  · intro a ha
    exact CommonLeafDisk.prefix_outside (targetBase q z s) (block q sorted) (blocks q s) disk a ha
  · simp only [machine,unpack_pack]
    rw [show final=stores q z sorted (blocks q s) from rfl,stores_frames]
    change (loaded.directories,loaded.shapes,loaded.top,loaded.pcs)=_
    rw [hpres.directories,hpres.shapes,hpres.top,hpres.pcs]
    rfl

/-- The real header/descriptor initializer discharges all phase and cursor
premises. The remaining hypotheses state the two allocated regions and the
input-file specification. `records` is never passed to initialization or policy. -/
theorem initialized_leaf (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hsource : source.val+PhysicalStreamCursor.blockCount q.block (3*n.val)≤q.N^q.exponent)
    (htarget : target.val+PhysicalStreamCursor.blockCount q.block (3*n.val)≤q.N^q.exponent)
    (records : Fin (ResidentLeafSort.count (initialStore q z n source target s).leaf) → KeyRecordWords.Record q.w)
    (hrecords : InputRep q z (initialStore q z n source target s) disk records) :
    let k := PhysicalStreamCursor.blockCount q.block (3*n.val)
    let result := run q z (3*k+1) (machine q (initialStore q z n source target s) disk)
    result.2=2*k ∧ policy q z result.1.ram=none ∧
    (∀ i j, diskWord q result.1.disk target.val (position i j)=
      KeyRecordWords.encode q.w (by have:=q.word_width; omega)
        (Columnsort.sortColumn records i) j) ∧
    (∀ a : Fin (q.N^q.exponent), a.val<target.val ∨ target.val+k≤a.val →
      result.1.disk a=disk a) ∧
    frameView q (unpack result.1.ram)=frameView q s := by
  have h := complete_leaf q z (initialStore q z n source target s) disk
    (CommonLeafInit.phase_initial _ _ _ _ _ _) (CommonLeafInit.inputCursor_initial _ _ _ _ _ _)
    (CommonLeafInit.outputCursor_initial _ _ _ _ _ _)
    (by simpa only [CommonLeafInit.sourceBase_initial,CommonLeafInit.blocks_initial] using hsource)
    (by simpa only [CommonLeafInit.targetBase_initial,CommonLeafInit.blocks_initial] using htarget)
    records hrecords
  simpa only [CommonLeafInit.blocks_initial,CommonLeafInit.targetBase_initial] using h

/-- The word slots used by the actual leaf policy plus the common physical
normalizer remain within M at every point of the run: their types never grow
with the input, the number of loop iterations, or recursion depth. -/
theorem resident_word_bound (q : Configuration) :
    q.ramWords+q.B+q.block+4*q.digits+3≤q.M := by
  have h := resident_memory q
  simp only [ResidentIndex,Fintype.card_sum,Fintype.card_fin] at h
  omega

end CodedSorting.CommonLeafCorrectness
end Correctness

section Transform
/-! The existing real load/write loops with a different bounded-RAM CPU.
The CPU receives only the existing leaf bank; it cannot inspect the disk.
This module is instantiated by the concrete bit-address exchange below. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace CodedSorting.CommonLeafTransform
open WordControl CommonSortingNormalization CommonLeafProgram CommonLeafLoad CommonLeafWrite

abbrev Bank (q : Configuration) := ResidentLeafSort.RAM (512*q.height) q.digits q.w

def computeEffect (q : Configuration) (cpu : Bank q → Bank q) (s : Store q) : Store q :=
  setPhase q 1 {s with leaf := cpu s.leaf}

def policy (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q) : SourcePolicy q := fun ram =>
  let s := unpack ram
  if phase q s=0 ∧ words q s≤ inputCursor q z s*q.block then
    some ⟨.localOp (fun current => pack (computeEffect q cpu (unpack current))),id⟩
  else CommonLeafProgram.policy q z ram

abbrev run (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q) :=
  ControlledNormalization.runLogical (policy q z cpu)

theorem run_add (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q)
    (n m : ℕ) (s : Machine q) :
    run q z cpu (n+m) s =
      ((run q z cpu m (run q z cpu n s).1).1,
       (run q z cpu n s).2+(run q z cpu m (run q z cpu n s).1).2) := by
  induction n generalizing s with
  | zero => simp [run,ControlledNormalization.runLogical]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [run,ControlledNormalization.runLogical]
    cases hp : policy q z cpu s.ram with
    | none => cases m <;> simp [ControlledNormalization.runLogical,hp]
    | some i => simp only; rw [←run,ih]; simp [run,Nat.add_assoc]

theorem one_unchanged (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q)
    (s : Store q) (disk : Disk q)
    (h : ¬(phase q s=0 ∧ words q s≤ inputCursor q z s*q.block)) :
    run q z cpu 1 (machine q s disk)=CommonLeafProgram.run q z 1 (machine q s disk) := by
  simp only [run,CommonLeafProgram.run,ControlledNormalization.runLogical,
    policy,machine,unpack_pack,if_neg h]

theorem read_one (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q)
    (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : inputCursor q z s*q.block<words q s)
    (ha : sourceBase q z s+inputCursor q z s<q.N^q.exponent) :
    run q z cpu 1 (machine q s disk)=
      (machine q (readEffect q z s (disk ⟨sourceBase q z s+inputCursor q z s,ha⟩)) disk,1) := by
  rw [one_unchanged q z cpu s disk (by omega)]
  exact CommonLeafProgram.read_one q z s disk hp hl ha

theorem compute_one (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q)
    (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : words q s≤ inputCursor q z s*q.block) :
    run q z cpu 1 (machine q s disk)=(machine q (computeEffect q cpu s) disk,0) := by
  simp only [run,ControlledNormalization.runLogical,policy,machine,unpack_pack,
    if_pos (And.intro hp hl),ControlledNormalization.logicalStep,
    Normalization.logicalStep,Normalization.transferCost,Nat.add_zero,id_eq]

theorem write_two (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q)
    (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hl : outputCursor q z s*q.block<words q s)
    (ha : targetBase q z s+outputCursor q z s<q.N^q.exponent) :
    run q z cpu 2 (machine q s disk)=
      (machine q (writeEffect q z s)
        (Function.update disk ⟨targetBase q z s+outputCursor q z s,ha⟩
          (ResidentLeafBank.getBlock (outputCursor q z s*q.block)
            (words q s-outputCursor q z s*q.block) s.leaf)),1) := by
  rw [show 2=1+1 from rfl,run_add,one_unchanged q z cpu s disk (by omega),
    CommonLeafProgram.prepare_one q z s disk hp hl]
  dsimp only
  have hphase : phase q (prepareEffect q z s)=2 := phase_setPhase q 2 _ (phase_capacity q)
  rw [one_unchanged q z cpu (prepareEffect q z s) disk (by omega),
    CommonLeafProgram.flush_one q z (prepareEffect q z s) disk hphase ha]
  rfl

theorem halt (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q) (s : Store q)
    (hp : phase q s=1) (hl : words q s≤outputCursor q z s*q.block) :
    policy q z cpu (pack s)=none := by
  rw [policy,unpack_pack,if_neg (by omega)]
  exact CommonLeafProgram.halt q z s hp hl

theorem read_prefix (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hc : inputCursor q z s=0)
    (ha : sourceBase q z s+blocks q s≤q.N^q.exponent)
    (hcap : blocks q s<(2^q.w)^q.digits) (k : ℕ) (hk : k≤blocks q s) :
    ∃ loaded, run q z cpu k (machine q s disk)=(machine q loaded disk,k) ∧
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
    have hactual : run q z cpu 1 (machine q loaded disk)=(machine q next disk,1) := by
      have hr := read_one q z cpu loaded disk hinv.phase_zero
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

theorem load (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hc : inputCursor q z s=0)
    (ha : sourceBase q z s+blocks q s≤q.N^q.exponent)
    (hcap : blocks q s<(2^q.w)^q.digits) :
    ∃ loaded, run q z cpu (blocks q s) (machine q s disk)=(machine q loaded disk,blocks q s) ∧
      phase q loaded=0 ∧ inputCursor q z loaded=blocks q s ∧
      sourceBase q z loaded=sourceBase q z s ∧ Preserved q s loaded ∧
      ∀ i : Fin ((512*q.height)*3), i.val<words q s →
        ResidentLeafBank.raw loaded.leaf i=diskWord q disk (sourceBase q z s) i.val := by
  obtain ⟨loaded,hrun,hinv⟩ := read_prefix q z cpu s disk hp hc ha hcap (blocks q s) le_rfl
  refine ⟨loaded,hrun,hinv.phase_zero,hinv.cursor,hinv.source,hinv.preserved,?_⟩
  intro i hi
  exact hinv.contents i (by simpa only [Nat.min_eq_left (blocks_cover q s)] using hi)

theorem run_writes (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q) (s : Store q) (disk : Disk q)
    (hp : phase q s=1) (hc : outputCursor q z s=0)
    (hfit : targetBase q z s+blocks q s ≤ q.N^q.exponent)
    (hcap : blocks q s < (2^q.w)^q.digits) (k : ℕ) (hk : k ≤ blocks q s) :
    run q z cpu (2*k) (machine q s disk)=
      (machine q (stores q z s k)
        (CommonLeafDisk.writePrefix (targetBase q z s) (block q s) k disk),k) := by
  induction k with
  | zero => simp only [Nat.mul_zero,run,ControlledNormalization.runLogical,stores,CommonLeafDisk.writePrefix]
  | succ k ih =>
    have hk' : k ≤ blocks q s := by omega
    have hr := ih hk'
    have hcur := stores_cursor q z s k hc (by omega)
    have hphase := stores_phase q z s k hp
    have hread : k*q.block < words q s :=
      (PhysicalStreamCursor.cursor_live_iff q.block (words q s) k (block_positive q)).1 (show k<blocks q s by omega)
    have hl : outputCursor q z (stores q z s k)*q.block < words q (stores q z s k) := by
      simpa only [hcur,stores_words] using hread
    have ha : targetBase q z (stores q z s k)+outputCursor q z (stores q z s k) < q.N^q.exponent := by
      rw [stores_base,hcur]
      omega
    rw [show 2*(k+1)=2*k+2 by omega,run_add,hr]
    dsimp only
    rw [write_two q z cpu _ _ hphase hl ha]
    simp only [hcur,stores_base,stores_words,stores_leaf]
    rw [CommonLeafDisk.prefix_succ_of_lt (by omega)]
    rfl


/-- One complete real read--CPU--write execution. Both payload equations,
termination and the exact charge belong to this same execution. -/
theorem complete (q : Configuration) (z : Slots q) (cpu : Bank q → Bank q)
    (hheader : ∀ bank, ResidentLeafSort.header (cpu bank)=ResidentLeafSort.header bank)
    (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hin : inputCursor q z s=0) (hout : outputCursor q z s=0)
    (hsource : sourceBase q z s+blocks q s≤q.N^q.exponent)
    (htarget : targetBase q z s+blocks q s≤q.N^q.exponent) :
    ∃ (loaded final : Store q) (out : Disk q),
      run q z cpu (3*blocks q s+1) (machine q s disk)=(machine q final out,2*blocks q s) ∧
      policy q z cpu (pack final)=none ∧
      (∀ i : Fin ((512*q.height)*3), i.val<words q s →
        ResidentLeafBank.raw loaded.leaf i=diskWord q disk (sourceBase q z s) i.val) ∧
      (∀ i : Fin ((512*q.height)*3), i.val<words q s →
        diskWord q out (targetBase q z s) i.val=ResidentLeafBank.raw (cpu loaded.leaf) i) ∧
      (∀ a : Fin (q.N^q.exponent), a.val<targetBase q z s ∨ targetBase q z s+blocks q s≤a.val →
        out a=disk a) ∧ frameView q final=frameView q s := by
  have hcap := CommonLeafInit.blocks_capacity q s
  obtain ⟨loaded,hr,hp',hc',hs',hpres,hpayload⟩ := load q z cpu s disk hp hin hsource hcap
  have hwloaded := hpres.words q
  let changed := computeEffect q cpu loaded
  have hwchanged : words q changed=words q s := by
    change 3*ResidentLeafSort.count (cpu loaded.leaf)=words q s
    simpa only [ResidentLeafSort.count,hheader] using hwloaded
  have hbchanged : blocks q changed=blocks q s := by simp only [blocks,hwchanged]
  have htchanged : targetBase q z changed=targetBase q z s := hpres.targetBase q z
  have hcchanged : outputCursor q z changed=0 := (hpres.outputCursor q z).trans hout
  have hpchanged : phase q changed=1 := phase_setPhase q 1 _ (by have := phase_capacity q; omega)
  have hcompute : run q z cpu 1 (machine q loaded disk)=(machine q changed disk,0) :=
    compute_one q z cpu loaded disk hp' (by rw [hc',hwloaded]; exact blocks_cover q s)
  have hwrite := run_writes q z cpu changed disk hpchanged hcchanged
    (by rw [htchanged,hbchanged]; exact htarget) (by rw [hbchanged]; exact hcap)
    (blocks q s) (by rw [hbchanged])
  let final := stores q z changed (blocks q s)
  let finalDisk := CommonLeafDisk.writePrefix (targetBase q z s) (block q changed) (blocks q s) disk
  have hwhole : run q z cpu (3*blocks q s+1) (machine q s disk)=
      (machine q final finalDisk,2*blocks q s) := by
    rw [show 3*blocks q s+1=blocks q s+(1+2*blocks q s) by omega,run_add,hr]
    dsimp only
    rw [run_add,hcompute]
    dsimp only
    rw [hwrite,htchanged]
    dsimp only [final,finalDisk,machine]
    congr 1
    omega
  refine ⟨loaded,final,finalDisk,hwhole,?_,hpayload,?_,?_,?_⟩
  · apply halt q z cpu final (stores_phase q z changed _ hpchanged)
    change words q (stores q z changed (blocks q s)) ≤
      outputCursor q z (stores q z changed (blocks q s))*q.block
    rw [stores_words,stores_cursor q z changed _ hcchanged hcap,hwchanged]
    exact blocks_cover q s
  · intro i hi
    have h := CommonLeafCorrectness.written_word q changed disk (targetBase q z s)
      (by rw [hbchanged]; exact htarget) i (by rw [hwchanged]; exact hi)
    simpa only [hbchanged] using h
  · intro a ha
    exact CommonLeafDisk.prefix_outside (targetBase q z s) (block q changed) (blocks q s) disk a ha
  · rw [show final=stores q z changed (blocks q s) from rfl,stores_frames]
    change (loaded.directories,loaded.shapes,loaded.top,loaded.pcs)=_
    rw [hpres.directories,hpres.shapes,hpres.top,hpres.pcs]
    rfl

end CodedSorting.CommonLeafTransform
end Transform
