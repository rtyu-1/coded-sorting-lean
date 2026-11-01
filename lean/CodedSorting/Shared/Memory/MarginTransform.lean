import CodedSorting.Shared.Memory.MovementPolicy

section MarginGather
/-! A fixed two-read/one-write block gather on the shared bounded machine.
The only custom code is an address calculation and a local combination of
two resident blocks. No input file or original disk occurs in the policy. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMarginGather
open WordControl CommonSortingNormalization
open CommonLeafProgram (Slots Store RAM Disk Machine phase setPhase inputCursor
  sourceBase targetBase setInputCursor machine)
namespace S
export CommonSortingNormalizationStreams (payload lengthWords cursorWords)
end S
abbrev Shape (q : Configuration) := Words (13*q.digits) q.w
structure Scheme (q : Configuration) where
  count : Shape q → ℕ
  first : Shape q → ℕ → ℕ → Fin (q.N^q.exponent)
  second : Shape q → ℕ → ℕ → Fin (q.N^q.exponent)
  assemble : Shape q → ℕ → Words q.block q.w → Words q.block q.w → Words q.block q.w

def saveFirst (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  setPhase q 1 {s with readers := (Function.update s.readers z.reader
    {(s.readers z.reader) with resident :=
      (Fin.append (Fin.append s.transfer (S.lengthWords (s.readers z.reader).resident))
        (S.cursorWords (s.readers z.reader).resident))})}
def combine (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) : Store q :=
  setPhase q 2 {s with transfer := (p.assemble (s.shapes f) (inputCursor q z s)
    (S.payload (s.readers z.reader).resident) s.transfer)}
def advance (q : Configuration) (z : Slots q) (s : Store q) : Store q :=
  setPhase q 0 (setInputCursor q z (inputCursor q z s+1) s)
def ramMap (q : Configuration) (fn : Store q → Store q) (ram : RAM q) : RAM q :=
  pack (fn (unpack ram))
def policy (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q) : SourcePolicy q := fun ram =>
  let s : Store q := unpack ram
  if phase q s=0 then
    if inputCursor q z s < p.count (s.shapes f) then
      some ⟨.read (p.first (s.shapes f) (sourceBase q z s) (inputCursor q z s))
        (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
        ramMap q (saveFirst q z)⟩
    else none
  else if phase q s=1 then
    some ⟨.read (p.second (s.shapes f) (sourceBase q z s) (inputCursor q z s))
      (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),ramMap q (combine q z f p)⟩
  else if phase q s=2 then
    if h : targetBase q z s+inputCursor q z s < q.N^q.exponent then
      some ⟨.write ⟨targetBase q z s+inputCursor q z s,h⟩
        (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),ramMap q (advance q z)⟩
    else none
  else none
abbrev run (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q) :=
  ControlledNormalization.runLogical (policy q z f p)

def firstEffect (q : Configuration) (z : Slots q) (s : Store q) (b : Words q.block q.w) :=
  saveFirst q z {s with transfer:=b}
def secondEffect (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (b : Words q.block q.w) := combine q z f p {s with transfer:=b}
def resultBlock (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) : Words q.block q.w :=
  p.assemble (s.shapes f) (inputCursor q z s)
    (disk (p.first (s.shapes f) (sourceBase q z s) (inputCursor q z s)))
    (disk (p.second (s.shapes f) (sourceBase q z s) (inputCursor q z s)))
def tripleEffect (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) : Store q :=
  advance q z (secondEffect q z f p
    (firstEffect q z s (disk (p.first (s.shapes f) (sourceBase q z s) (inputCursor q z s))))
    (disk (p.second (s.shapes f) (sourceBase q z s) (inputCursor q z s))))

theorem run_add (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (n m : ℕ) (s : Machine q) :
    run q z f p (n+m) s =
      ((run q z f p m (run q z f p n s).1).1,
        (run q z f p n s).2+(run q z f p m (run q z f p n s).1).2) := by
  induction n generalizing s with
  | zero => simp [run,ControlledNormalization.runLogical]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [run,ControlledNormalization.runLogical]
    cases hp : policy q z f p s.ram with
    | none => cases m <;> simp [ControlledNormalization.runLogical,hp]
    | some i => simp only; rw [←run,ih]; simp [run,Nat.add_assoc]

@[simp] theorem cursor_append (q : Configuration)
    (a : Words (q.block+q.digits) q.w) (b : Words q.digits q.w) :
    CommonSortingNormalizationStreams.cursorWords (Fin.append a b)=b := by
  funext i
  simp [CommonSortingNormalizationStreams.cursorWords]

@[simp] theorem cursor_saveFirst (q : Configuration) (z : Slots q) (s : Store q) :
    inputCursor q z (saveFirst q z s)=inputCursor q z s := by
  unfold inputCursor saveFirst setPhase
  simp only [Function.update_self]
  congr 1
  funext i
  simp [S.cursorWords]
@[simp] theorem source_saveFirst (q : Configuration) (z : Slots q) (s : Store q) :
    sourceBase q z (saveFirst q z s)=sourceBase q z s := by
  simp [sourceBase,saveFirst,setPhase]
@[simp] theorem payload_saveFirst (q : Configuration) (z : Slots q) (s : Store q) :
    S.payload ((saveFirst q z s).readers z.reader).resident=s.transfer := by
  funext i
  simp [S.payload,saveFirst,setPhase]
@[simp] theorem cursor_firstEffect (q : Configuration) (z : Slots q)
    (s : Store q) (b : Words q.block q.w) :
    inputCursor q z (firstEffect q z s b)=inputCursor q z s := by
  rw [firstEffect,cursor_saveFirst]; rfl
@[simp] theorem source_firstEffect (q : Configuration) (z : Slots q)
    (s : Store q) (b : Words q.block q.w) :
    sourceBase q z (firstEffect q z s b)=sourceBase q z s := by
  rw [firstEffect,source_saveFirst]; rfl
@[simp] theorem cursor_secondEffect (q : Configuration) (z : Slots q) (f : Fin 3)
    (p : Scheme q) (s : Store q) (b : Words q.block q.w) :
    inputCursor q z (secondEffect q z f p s b)=inputCursor q z s := rfl
@[simp] theorem source_secondEffect (q : Configuration) (z : Slots q) (f : Fin 3)
    (p : Scheme q) (s : Store q) (b : Words q.block q.w) :
    sourceBase q z (secondEffect q z f p s b)=sourceBase q z s := rfl

theorem read_first (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) (hp : phase q s=0)
    (hl : inputCursor q z s<p.count (s.shapes f)) :
    run q z f p 1 (machine q s disk)=
      (machine q (firstEffect q z s (disk (p.first (s.shapes f) (sourceBase q z s)
        (inputCursor q z s)))) disk,1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,hl,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,firstEffect,
    CommonLeafWindow.load_transfer,Normalization.transferCost]

theorem read_second (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) (hp : phase q s=1) :
    run q z f p 1 (machine q s disk)=
      (machine q (secondEffect q z f p s (disk (p.second (s.shapes f) (sourceBase q z s)
        (inputCursor q z s)))) disk,1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,secondEffect,
    CommonLeafWindow.load_transfer,Normalization.transferCost]

theorem write_one (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) (hp : phase q s=2)
    (ht : targetBase q z s+inputCursor q z s<q.N^q.exponent) :
    run q z f p 1 (machine q s disk)=
      (machine q (advance q z s)
        (Function.update disk ⟨targetBase q z s+inputCursor q z s,ht⟩ s.transfer),1) := by
  simp [run,ControlledNormalization.runLogical,machine,policy,unpack_pack,hp,ht,
    ControlledNormalization.logicalStep,Normalization.logicalStep,ramMap,
    CommonLeafWindow.slice_transfer,Normalization.transferCost]

theorem triple_three (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) (hp : phase q s=0)
    (hl : inputCursor q z s<p.count (s.shapes f))
    (ht : targetBase q z s+inputCursor q z s<q.N^q.exponent) :
    run q z f p 3 (machine q s disk)=
      (machine q (tripleEffect q z f p s disk)
        (Function.update disk ⟨targetBase q z s+inputCursor q z s,ht⟩
          (resultBlock q z f p s disk)),3) := by
  have hcap := CommonLeafProgram.phase_capacity q
  rw [show 3=1+(1+1) from rfl,run_add,read_first q z f p s disk hp hl]
  dsimp only
  have h1 : phase q (firstEffect q z s
      (disk (p.first (s.shapes f) (sourceBase q z s) (inputCursor q z s))))=1 :=
    CommonLeafProgram.phase_setPhase q 1 _ (by omega)
  rw [run_add,read_second q z f p _ disk h1]
  dsimp only
  have h2 : ∀ t b, phase q (secondEffect q z f p t b)=2 := by
    intro t b
    exact CommonLeafProgram.phase_setPhase q 2 _ (by omega)
  rw [write_one q z f p _ disk (h2 _ _) (by simpa using ht)]
  dsimp only
  simp only [tripleEffect,resultBlock,secondEffect,combine,firstEffect,
    cursor_saveFirst,source_saveFirst,payload_saveFirst]
  simp [saveFirst,setPhase,inputCursor,S.cursorWords,S.payload,sourceBase,targetBase]

structure Control (q : Configuration) (z : Slots q) (f : Fin 3)
    (shape : Shape q) (source target cursor : ℕ) (s : Store q) : Prop where
  phase_zero : phase q s=0
  shape_eq : s.shapes f=shape
  source_eq : sourceBase q z s=source
  target_eq : targetBase q z s=target
  cursor_eq : inputCursor q z s=cursor

theorem triple_control (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) (shape : Shape q) (source target k : ℕ)
    (h : Control q z f shape source target k s)
    (hc : k+1<(2^q.w)^q.digits) :
    Control q z f shape source target (k+1) (tripleEffect q z f p s disk) := by
  constructor
  · exact CommonLeafProgram.phase_setPhase q 0 _ (by positivity)
  · exact h.shape_eq
  · simpa [tripleEffect,advance,sourceBase,setPhase,setInputCursor,firstEffect,saveFirst,
      secondEffect,combine] using h.source_eq
  · exact h.target_eq
  · unfold tripleEffect advance
    change inputCursor q z (setInputCursor q z _ _)=k+1
    rw [CommonLeafProgram.inputCursor_set q z _ _ (by simpa [h.cursor_eq] using hc)]
    simp [h.cursor_eq]

theorem triple_preserved (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) :
    CommonMovementPolicy.Preserved q s (tripleEffect q z f p s disk) := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Specification of one destination block, determined by the ORIGINAL
finite disk and the fixed local arithmetic program. -/
def specBlock (q : Configuration) (p : Scheme q) (shape : Shape q)
    (source k : ℕ) (original : Disk q) : Words q.block q.w :=
  p.assemble shape k (original (p.first shape source k)) (original (p.second shape source k))
structure Written (q : Configuration) (p : Scheme q) (shape : Shape q)
    (source target k : ℕ) (original current : Disk q) : Prop where
  written : ∀ j, j<k → ∀ hj : target+j<q.N^q.exponent,
    current ⟨target+j,hj⟩=specBlock q p shape source j original
  outside : ∀ a : Fin (q.N^q.exponent),
    a.val<target ∨ target+k≤a.val → current a=original a

def ReadsOutside (q : Configuration) (p : Scheme q) (shape : Shape q)
    (source target : ℕ) : Prop := ∀ k, k<p.count shape →
  ((p.first shape source k).val<target ∨ target+p.count shape≤(p.first shape source k).val) ∧
  ((p.second shape source k).val<target ∨ target+p.count shape≤(p.second shape source k).val)

theorem written_succ (q : Configuration) (p : Scheme q) (shape : Shape q)
    (source target k : ℕ) (original current : Disk q)
    (h : Written q p shape source target k original current)
    (ht : target+k<q.N^q.exponent) :
    Written q p shape source target (k+1) original
      (Function.update current ⟨target+k,ht⟩ (specBlock q p shape source k original)) := by
  constructor
  · intro j hj hfit
    by_cases he : j=k
    · subst j; exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by intro heq; have := congrArg Fin.val heq; simp only [Fin.val_mk] at this; omega)]
      exact h.written j (by omega) hfit
  · intro a ha
    rw [Function.update_of_ne (by intro heq; have := congrArg Fin.val heq; simp only [Fin.val_mk] at this; omega)]
    exact h.outside a (by omega)

/-- Complete same-run output, halt, and exactly three I/Os per output block.
The scheme contains only current-descriptor address arithmetic and a local
map on two existing resident blocks. -/
theorem complete_from (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (shape : Shape q) (source target k remaining : ℕ) (s : Store q)
    (original disk : Disk q)
    (hctrl : Control q z f shape source target k s)
    (hlen : k+remaining=p.count shape)
    (hfit : target+p.count shape≤q.N^q.exponent)
    (hsep : ReadsOutside q p shape source target)
    (hinv : Written q p shape source target k original disk) :
    ∃ finalStore finalDisk,
      run q z f p (3*remaining) (machine q s disk)=(machine q finalStore finalDisk,3*remaining) ∧
      Control q z f shape source target (p.count shape) finalStore ∧
      policy q z f p (pack finalStore)=none ∧
      Written q p shape source target (p.count shape) original finalDisk ∧
      CommonMovementPolicy.Preserved q s finalStore := by
  induction remaining generalizing k s disk with
  | zero =>
    have hk : k=p.count shape := by omega
    refine ⟨s,disk,?_,hk ▸ hctrl,?_,hk ▸ hinv,CommonMovementPolicy.Preserved.refl q s⟩
    · rfl
    · simp [policy,unpack_pack,hctrl.phase_zero,hctrl.shape_eq,hctrl.cursor_eq,hk]
  | succ n ih =>
    have hk : k<p.count shape := by omega
    have ht : target+k<q.N^q.exponent := by omega
    have ht' : targetBase q z s+inputCursor q z s<q.N^q.exponent := by
      rw [hctrl.target_eq,hctrl.cursor_eq]; exact ht
    have hr1 := hinv.outside (p.first shape source k) (by
      rcases (hsep k hk).1 with hh|hh <;> (first | exact Or.inl hh | exact Or.inr (by omega)))
    have hr2 := hinv.outside (p.second shape source k) (by
      rcases (hsep k hk).2 with hh|hh <;> (first | exact Or.inl hh | exact Or.inr (by omega)))
    have hb : resultBlock q z f p s disk=specBlock q p shape source k original := by
      simp only [resultBlock,hctrl.shape_eq,hctrl.source_eq,hctrl.cursor_eq,hr1,hr2,specBlock]
    have hc : k+1<(2^q.w)^q.digits := descriptor_capacity q (k+1) (by omega)
    have hnext := triple_control q z f p s disk shape source target k hctrl hc
    have hwrite := written_succ q p shape source target k original disk hinv ht
    obtain ⟨sf,df,hrun,hcontrol,hhalt,hwritten,hpreserved⟩ :=
      ih (k+1) (tripleEffect q z f p s disk)
        (Function.update disk ⟨target+k,ht⟩ (specBlock q p shape source k original))
        hnext (by omega) hwrite
    refine ⟨sf,df,?_,hcontrol,hhalt,hwritten,
      CommonMovementPolicy.Preserved.trans q (triple_preserved q z f p s disk) hpreserved⟩
    rw [show 3*(n+1)=3+3*n by omega,run_add,
      triple_three q z f p s disk hctrl.phase_zero (by rw [hctrl.cursor_eq,hctrl.shape_eq]; exact hk) ht']
    simp only [hb,hctrl.target_eq,hctrl.cursor_eq]
    rw [hrun]

theorem complete (q : Configuration) (z : Slots q) (f : Fin 3) (p : Scheme q)
    (s : Store q) (disk : Disk q) (hp : phase q s=0) (hk : inputCursor q z s=0)
    (hfit : targetBase q z s+p.count (s.shapes f)≤q.N^q.exponent)
    (hsep : ReadsOutside q p (s.shapes f) (sourceBase q z s) (targetBase q z s)) :
    ∃ finalStore finalDisk,
      run q z f p (3*p.count (s.shapes f)) (machine q s disk)=
        (machine q finalStore finalDisk,3*p.count (s.shapes f)) ∧
      policy q z f p (pack finalStore)=none ∧
      Written q p (s.shapes f) (sourceBase q z s) (targetBase q z s)
        (p.count (s.shapes f)) disk finalDisk ∧
      CommonMovementPolicy.Preserved q s finalStore ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  have hi : Written q p (s.shapes f) (sourceBase q z s) (targetBase q z s) 0 disk disk := by
    constructor
    · intro j hj; omega
    · intro a ha; rfl
  obtain ⟨sf,df,hr,hc,hh,hw,hp'⟩ := complete_from q z f p (s.shapes f)
    (sourceBase q z s) (targetBase q z s) 0 (p.count (s.shapes f)) s disk disk
    ⟨hp,rfl,rfl,rfl,hk⟩ (by omega) hfit hsep hi
  exact ⟨sf,df,hr,hh,hw,hp',resident_memory q⟩
end CodedSorting.CommonMarginGather
end MarginGather

section MarginTransform
/-! Concrete contiguous-slice and sentinel-insertion specialization of the
complete gather machine. All extents and offsets are decoded from an existing
shape bank. The two input banks suffice even for block-unaligned margins. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMarginTransform
open WordControl CommonSortingNormalization CommonMarginGather
open CommonLeafProgram (Slots Store Disk phase inputCursor sourceBase targetBase machine)

def field (q : Configuration) (s : Shape q) (i : Fin 13) : ℕ :=
  decodeWords (familyOfWords s i)
def left (q : Configuration) (s : Shape q) := field q s 0
def retained (q : Configuration) (s : Shape q) := field q s 1
def right (q : Configuration) (s : Shape q) := field q s 2
def offset (q : Configuration) (s : Shape q) := field q s 3
def outWords (q : Configuration) (s : Shape q) := left q s+retained q s+right q s
def inBlocks (q : Configuration) (s : Shape q) :=
  max 1 (PhysicalStreamCursor.blockCount q.block (offset q s+retained q s))
def firstIndex (q : Configuration) (s : Shape q) (k : ℕ) :=
  (offset q s+(k*q.block-left q s))/q.block
/-- The inactive read is clamped within the reserved source extent. The
fallback is unreachable under the explicit address-fit condition. -/
def address (q : Configuration) (s : Shape q) (source a : ℕ) : Fin (q.N^q.exponent) :=
  if h : source+min a (inBlocks q s-1)<q.N^q.exponent then
    ⟨source+min a (inBlocks q s-1),h⟩
  else ⟨0, pow_pos (by have:=q.input_large; omega) _⟩

def assemble (q : Configuration) (s : Shape q) (k : ℕ)
    (a b : Words q.block q.w) : Words q.block q.w := fun i =>
  let j := k*q.block+i.val
  if j<left q s then 0
  else if j<left q s+retained q s then
    let word := offset q s+(j-left q s)
    let ix : Fin q.block := ⟨word%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩
    if word/q.block=firstIndex q s k then a ix else b ix
  else if (j-(left q s+retained q s))%3=0 then
    ⟨2,by have := q.word_width; have := Nat.pow_le_pow_right (by decide : 0<2) this; norm_num at this; omega⟩
  else 0

def scheme (q : Configuration) : Scheme q where
  count s := PhysicalStreamCursor.blockCount q.block (outWords q s)
  first s source k := address q s source (firstIndex q s k)
  second s source k := address q s source (firstIndex q s k+1)
  assemble := assemble q

/-- Division into blocks changes by at most one over any block-sized
contiguous slice, including a slice beginning inside the left margin. -/
theorem two_blocks (B L O k i : ℕ) (hB : 0<B) (hi : i<B) :
    (O+(k*B+i-L))/B=(O+(k*B-L))/B ∨
    (O+(k*B+i-L))/B=(O+(k*B-L))/B+1 := by
  let x := O+(k*B-L)
  let y := O+(k*B+i-L)
  have hxy : x≤y := by dsimp [x,y]; omega
  have hy : y<x+B := by dsimp [x,y]; omega
  have hd : x/B≤y/B := Nat.div_le_div_right hxy
  have hx := Nat.mod_lt x hB
  have hxm := Nat.mod_add_div x B
  have hym := Nat.mod_add_div y B
  have ht : y/B<x/B+2 := by
    apply (Nat.div_lt_iff_lt_mul hB).2
    nlinarith
  change y/B=x/B ∨ y/B=x/B+1
  omega

theorem address_val (q : Configuration) (s : Shape q) (source a : ℕ)
    (hfit : source+inBlocks q s≤q.N^q.exponent) :
    (address q s source a).val=source+min a (inBlocks q s-1) := by
  have hp : 0 < inBlocks q s := by unfold inBlocks; omega
  have hmin := Nat.min_le_right a (inBlocks q s-1)
  have h : source+min a (inBlocks q s-1)<q.N^q.exponent := by omega
  simp [address,h]

theorem reads_outside (q : Configuration) (s : Shape q) (source target : ℕ)
    (hfit : source+inBlocks q s≤q.N^q.exponent)
    (hsep : source+inBlocks q s≤target ∨ target+(scheme q).count s≤source) :
    ReadsOutside q (scheme q) s source target := by
  intro k hk
  have hp : 0 < inBlocks q s := by unfold inBlocks; omega
  have ha := Nat.min_le_right (firstIndex q s k) (inBlocks q s-1)
  have hb := Nat.min_le_right (firstIndex q s k+1) (inBlocks q s-1)
  simp only [scheme,address_val q s source _ hfit]
  simp only [scheme] at hsep
  rcases hsep with h|h
  · exact ⟨Or.inl (by omega),Or.inl (by omega)⟩
  · exact ⟨Or.inr (by omega),Or.inr (by omega)⟩

/-- The requested source word is selected at its original word offset.
No vector permutation or re-encoding is hidden in the local combination. -/
theorem retained_word (q : Configuration) (s : Shape q) (source k : ℕ)
    (disk : Disk q) (i : Fin q.block)
    (hl : left q s≤k*q.block+i.val)
    (hn : k*q.block+i.val<left q s+retained q s)
    (hfit : source+inBlocks q s≤q.N^q.exponent) :
    specBlock q (scheme q) s source k disk i =
      disk (address q s source ((offset q s+(k*q.block+i.val-left q s))/q.block))
        ⟨(offset q s+(k*q.block+i.val-left q s))%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ := by
  have ht := two_blocks q.block (left q s) (offset q s) k i.val (CommonLeafProgram.block_positive q) i.isLt
  simp only [specBlock,scheme,assemble,show ¬k*q.block+i.val<left q s by omega,↓reduceIte,hn]
  rcases ht with h|h
  · simp [firstIndex,h]
  · have hne : (offset q s+(k*q.block+i.val-left q s))/q.block≠firstIndex q s k := by
      unfold firstIndex; omega
    simp only [hne,↓reduceIte]
    simp only [firstIndex,h]

/-- Bottom and top sentinels use three-word record encoding: bottom is
[0,0,0], top is [2,0,0]. -/
theorem margin_word (q : Configuration) (s : Shape q) (source k : ℕ)
    (disk : Disk q) (i : Fin q.block) :
    (k*q.block+i.val<left q s → specBlock q (scheme q) s source k disk i=0) ∧
    (left q s+retained q s≤k*q.block+i.val →
      specBlock q (scheme q) s source k disk i=
        if (k*q.block+i.val-(left q s+retained q s))%3=0 then
          (⟨2,by have := q.word_width; have := Nat.pow_le_pow_right (by decide : 0<2) this; norm_num at this; omega⟩ : Word q.w)
        else 0) := by
  constructor
  · intro h; simp [specBlock,scheme,assemble,h]
  · intro h
    simp [specBlock,scheme,assemble,show ¬k*q.block+i.val<left q s by omega,
      show ¬k*q.block+i.val<left q s+retained q s by omega]

/-- Complete contiguous-slice / sentinel-insertion machine, with real
reads, real writes, successful halt, and one common resident bound. -/
theorem complete (q : Configuration) (z : Slots q) (f : Fin 3)
    (s : Store q) (disk : Disk q) (hp : phase q s=0) (hk : inputCursor q z s=0)
    (hsource : sourceBase q z s+inBlocks q (s.shapes f)≤q.N^q.exponent)
    (htarget : targetBase q z s+(scheme q).count (s.shapes f)≤q.N^q.exponent)
    (hsep : sourceBase q z s+inBlocks q (s.shapes f)≤targetBase q z s ∨
      targetBase q z s+(scheme q).count (s.shapes f)≤sourceBase q z s) :
    ∃ finalStore finalDisk,
      CommonMarginGather.run q z f (scheme q) (3*(scheme q).count (s.shapes f)) (machine q s disk)=
        (machine q finalStore finalDisk,3*(scheme q).count (s.shapes f)) ∧
      CommonMarginGather.policy q z f (scheme q) (pack finalStore)=none ∧
      Written q (scheme q) (s.shapes f) (sourceBase q z s) (targetBase q z s)
        ((scheme q).count (s.shapes f)) disk finalDisk ∧
      CommonMovementPolicy.Preserved q s finalStore ∧
      Fintype.card (ResidentIndex q)≤q.M :=
  CommonMarginGather.complete q z f (scheme q) s disk hp hk htarget
    (reads_outside q (s.shapes f) (sourceBase q z s) (targetBase q z s) hsource hsep)

/-- Whole-word view on the one finite disk, extended by zero only outside
its address space. Validity hypotheses below ensure live reads are inside. -/
def wordAt (q : Configuration) (disk : Disk q) (base j : ℕ) : Word q.w :=
  CommonLeafBatchProgram.extendDisk q disk (base+j/q.block)
    ⟨j%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩

theorem source_word (q : Configuration) (s : Shape q) (source word : ℕ)
    (disk : Disk q) (hw : word<offset q s+retained q s)
    (hfit : source+inBlocks q s≤q.N^q.exponent) :
    disk (address q s source (word/q.block))
      ⟨word%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ =
    wordAt q disk source word := by
  have hmul := Nat.div_mul_le_self word q.block
  have hb := (PhysicalStreamCursor.cursor_live_iff q.block (offset q s+retained q s)
    (word/q.block) (CommonLeafProgram.block_positive q)).2 (by omega)
  have hi : word/q.block < inBlocks q s := hb.trans_le (Nat.le_max_right _ _)
  have ha : source+word/q.block<q.N^q.exponent := by omega
  have hm : min (word/q.block) (inBlocks q s-1)=word/q.block := Nat.min_eq_left (by omega)
  simp [address,hm,ha,wordAt,CommonLeafBatchProgram.extendDisk]

def topWord (q : Configuration) (j : ℕ) : Word q.w :=
  if j%3=0 then ⟨2,by have := q.word_width; have := Nat.pow_le_pow_right (by decide : 0<2) this; norm_num at this; omega⟩ else 0

def expectedWord (q : Configuration) (s : Shape q) (source j : ℕ) (disk : Disk q) : Word q.w :=
  if j<left q s then 0
  else if j<left q s+retained q s then wordAt q disk source (offset q s+(j-left q s))
  else topWord q (j-(left q s+retained q s))

theorem spec_word (q : Configuration) (s : Shape q) (source k : ℕ)
    (disk : Disk q) (i : Fin q.block)
    (hfit : source+inBlocks q s≤q.N^q.exponent) :
    specBlock q (scheme q) s source k disk i=expectedWord q s source (k*q.block+i.val) disk := by
  by_cases hl : k*q.block+i.val<left q s
  · simp only [expectedWord,hl,↓reduceIte]
    exact (margin_word q s source k disk i).1 hl
  · by_cases hn : k*q.block+i.val<left q s+retained q s
    · simp only [expectedWord,hl,hn,↓reduceIte]
      rw [retained_word q s source k disk i (by omega) hn hfit]
      exact source_word q s source _ disk (by omega) hfit
    · simp only [expectedWord,hl,hn,↓reduceIte,topWord]
      exact (margin_word q s source k disk i).2 (by omega)

theorem written_words (q : Configuration) (s : Shape q) (source target : ℕ)
    (original finalDisk : Disk q)
    (hw : Written q (scheme q) s source target ((scheme q).count s) original finalDisk)
    (hsource : source+inBlocks q s≤q.N^q.exponent)
    (htarget : target+(scheme q).count s≤q.N^q.exponent) :
    ∀ j, j<outWords q s → wordAt q finalDisk target j=expectedWord q s source j original := by
  intro j hj
  have hc : j/q.block<(scheme q).count s :=
    (PhysicalStreamCursor.cursor_live_iff q.block (outWords q s) (j/q.block)
      (CommonLeafProgram.block_positive q)).2 ((Nat.div_mul_le_self j q.block).trans_lt hj)
  have ha : target+j/q.block<q.N^q.exponent := by omega
  unfold wordAt
  simp only [CommonLeafBatchProgram.extendDisk,ha,↓reduceDIte]
  rw [hw.written (j/q.block) hc ha]
  rw [spec_word q s source (j/q.block) original _ hsource]
  congr 1
  simpa only [Nat.mul_comm,Fin.val_mk] using Nat.div_add_mod j q.block

def shape (q : Configuration) (L N R O : ℕ) : Shape q :=
  family (fun i : Fin 13 => PhysicalStreamCursor.encodeNat q.digits q.w
    (if i=0 then L else if i=1 then N else if i=2 then R else if i=3 then O else 0))

theorem shape_fields (q : Configuration) (L N R O : ℕ)
    (hL : L<(2^q.w)^q.digits) (hN : N<(2^q.w)^q.digits)
    (hR : R<(2^q.w)^q.digits) (hO : O<(2^q.w)^q.digits) :
    left q (shape q L N R O)=L ∧ retained q (shape q L N R O)=N ∧
      right q (shape q L N R O)=R ∧ offset q (shape q L N R O)=O := by
  simp [left,retained,right,offset,field,shape,family_roundtrip,
    PhysicalStreamCursor.decodeNat_encode _ _ _ hL,
    PhysicalStreamCursor.decodeNat_encode _ _ _ hN,
    PhysicalStreamCursor.decodeNat_encode _ _ _ hR,
    PhysicalStreamCursor.decodeNat_encode _ _ _ hO]

/-- Public-count initialization is a RAM-only operation. It installs the
four finite multiword parameters and the two actual disk addresses. -/
def initialStore (q : Configuration) (z : Slots q) (f : Fin 3)
    (L N R O : ℕ) (source target : Fin (q.N^q.exponent)) (s : Store q) : Store q :=
  CommonMovementPolicy.initialStore q z ⟨0,by omega⟩ source target
    {s with shapes:=Function.update s.shapes f (shape q L N R O)}

/-- Same-run initialized endpoint: every logical output word is the
prescribed margin word or the original source word at its retained offset. -/
theorem initialized (q : Configuration) (z : Slots q) (f : Fin 3)
    (L N R O : Fin (q.N^q.exponent+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q)
    (hs : source.val+max 1 (PhysicalStreamCursor.blockCount q.block (O.val+N.val))≤q.N^q.exponent)
    (ht : target.val+PhysicalStreamCursor.blockCount q.block (L.val+N.val+R.val)≤q.N^q.exponent)
    (hsep : source.val+max 1 (PhysicalStreamCursor.blockCount q.block (O.val+N.val))≤target.val ∨
      target.val+PhysicalStreamCursor.blockCount q.block (L.val+N.val+R.val)≤source.val) :
    ∃ finalStore finalDisk,
      CommonMarginGather.run q z f (scheme q)
        (3*PhysicalStreamCursor.blockCount q.block (L.val+N.val+R.val))
        (machine q (initialStore q z f L.val N.val R.val O.val source target s) disk)=
        (machine q finalStore finalDisk,3*PhysicalStreamCursor.blockCount q.block (L.val+N.val+R.val)) ∧
      CommonMarginGather.policy q z f (scheme q) (pack finalStore)=none ∧
      (∀ j, j<L.val+N.val+R.val → wordAt q finalDisk target.val j=
        if j<L.val then 0 else if j<L.val+N.val then wordAt q disk source.val (O.val+(j-L.val))
        else topWord q (j-(L.val+N.val))) ∧
      (∀ a : Fin (q.N^q.exponent), a.val<target.val ∨
        target.val+PhysicalStreamCursor.blockCount q.block (L.val+N.val+R.val)≤a.val → finalDisk a=disk a) ∧
      CommonMovementPolicy.Preserved q
        (initialStore q z f L.val N.val R.val O.val source target s) finalStore ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  have caps (x : Fin (q.N^q.exponent+1)) : x.val<(2^q.w)^q.digits :=
    descriptor_capacity q x.val (by have:=x.isLt; omega)
  obtain ⟨hL,hN,hR,hO⟩ := shape_fields q L.val N.val R.val O.val (caps L) (caps N) (caps R) (caps O)
  let t := initialStore q z f L.val N.val R.val O.val source target s
  have hc := CommonMovementPolicy.initial_control q z ⟨0,by omega⟩ source target
    {s with shapes:=Function.update s.shapes f (shape q L.val N.val R.val O.val)}
  have hsb : sourceBase q z t=source.val := hc.source_base
  have htb : targetBase q z t=target.val := hc.target_base
  have hshape : t.shapes f=shape q L.val N.val R.val O.val := by
    simp [t,initialStore,CommonMovementPolicy.initialStore,CommonLeafProgram.setPhase]
  have hout : outWords q (t.shapes f)=L.val+N.val+R.val := by
    simp [outWords,hshape,hL,hN,hR]
  have hin : inBlocks q (t.shapes f)=max 1 (PhysicalStreamCursor.blockCount q.block (O.val+N.val)) := by
    simp [inBlocks,hshape,hO,hN]
  have hcount : (scheme q).count (t.shapes f)=PhysicalStreamCursor.blockCount q.block (L.val+N.val+R.val) := by
    simpa only [scheme] using congrArg (PhysicalStreamCursor.blockCount q.block) hout
  have hsource : sourceBase q z t+inBlocks q (t.shapes f)≤q.N^q.exponent := by rw [hsb,hin]; exact hs
  have htarget : targetBase q z t+(scheme q).count (t.shapes f)≤q.N^q.exponent := by rw [htb,hcount]; exact ht
  obtain ⟨sf,df,hrun,hhalt,hw,hpres,hm⟩ := complete q z f t disk hc.phase_zero hc.position hsource htarget
    (by rw [hsb,htb,hin,hcount]; exact hsep)
  refine ⟨sf,df,?_,hhalt,?_,?_,hpres,hm⟩
  · simpa only [hcount] using hrun
  · have hv := written_words q (t.shapes f) (sourceBase q z t) (targetBase q z t) disk df hw hsource htarget
    simpa only [hsb,htb,expectedWord,hshape,outWords,hL,hN,hR,hO] using hv
  · simpa only [htb,hcount] using hw.outside
end CodedSorting.CommonMarginTransform
end MarginTransform
