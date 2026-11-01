import CodedSorting.Shared.Memory.PhysicalStreamCursor

/-! Multiword pending-length refinement of the actual addressed stream
primitives. Every numeric stream descriptor uses d original words. In
particular this interface does not assume that a block length fits one word.
The only external-state access is one block at the counted address. -/
set_option autoImplicit false
namespace CodedSorting.CommonSortingNormalizationStreams
open WordControl BucketMachine BucketReader
open PhysicalStreamCursor (encodeNat decodeNat_encode blockView blockView_length
  suffix suffix_cons suffix_empty cursor_live_iff readerView_valid blockCount)

/-- B payload words, d pending-length words, and d cursor words. -/
abbrev Resident (B d w : ℕ) := Words (B+d+d) w

def cells {w : ℕ} (B : ℕ) (xs : List (Word w)) : Words B w :=
  fun i => xs[i.val]?.getD 0

/-- Length and cursor conversion are total. The refinement theorems below
explicitly require that neither modular conversion truncates a live value. -/
def encode (B d w : ℕ) (pending : List (Word w)) (cursor : ℕ) : Resident B d w :=
  Fin.append (Fin.append (cells B pending)
      (PhysicalStreamCursor.encodeNat d w pending.length))
    (finFunctionFinEquiv.symm
      ⟨cursor % (2^w)^d, Nat.mod_lt _ (by positivity)⟩)

def payload {B d w : ℕ} (ram : Resident B d w) : Words B w :=
  fun i => ram (Fin.castAdd d (Fin.castAdd d i))

def lengthWords {B d w : ℕ} (ram : Resident B d w) : Words d w :=
  fun i => ram (Fin.castAdd d (Fin.natAdd B i))

def pendingLength {B d w : ℕ} (ram : Resident B d w) : ℕ :=
  decodeWords (lengthWords ram)

def cursorWords {B d w : ℕ} (ram : Resident B d w) : Words d w :=
  fun i => ram (Fin.natAdd (B+d) i)

def decode {B d w : ℕ} (ram : Resident B d w) : List (Word w) × ℕ :=
  ((List.ofFn (payload ram)).take (pendingLength ram), decodeWords (cursorWords ram))

@[simp] theorem payload_encode (B d w : ℕ) (xs : List (Word w)) (c : ℕ) :
    payload (encode B d w xs c) = cells B xs := by
  funext i
  simp [payload,encode]

@[simp] theorem length_encode (B d w : ℕ) (xs : List (Word w)) (c : ℕ) :
    pendingLength (encode B d w xs c) = xs.length % (2^w)^d := by
  have hwords : lengthWords (encode B d w xs c) =
      PhysicalStreamCursor.encodeNat d w xs.length := by
    funext i
    simp [lengthWords,encode]
  unfold pendingLength
  rw [hwords]
  change (finFunctionFinEquiv (finFunctionFinEquiv.symm _)).val = _
  exact congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply _)

@[simp] theorem cursor_encode (B d w : ℕ) (xs : List (Word w)) (c : ℕ) :
    decodeWords (cursorWords (encode B d w xs c)) = c % (2^w)^d := by
  have hwords : cursorWords (encode B d w xs c) =
      finFunctionFinEquiv.symm ⟨c % (2^w)^d, Nat.mod_lt _ (by positivity)⟩ := by
    funext i
    exact Fin.append_right _ _ i
  rw [hwords]
  exact congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply _)

theorem take_cells {w : ℕ} (B : ℕ) (xs : List (Word w)) (h : xs.length ≤ B) :
    (List.ofFn (cells B xs)).take xs.length = xs := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i hi hi'
    simp only [List.getElem_take,List.getElem_ofFn,cells]
    simp [List.getElem?_eq_getElem hi']

/-- Every pending word is recovered at the same position, together with the
actual cursor. No external disk list is part of the resident encoding. -/
theorem decode_encode (B d w : ℕ) (xs : List (Word w)) (c : ℕ)
    (hx : xs.length < B) (hB : B ≤ (2^w)^d) (hc : c < (2^w)^d) :
    decode (encode B d w xs c) = (xs,c) := by
  simp only [decode,payload_encode,length_encode,cursor_encode]
  rw [Nat.mod_eq_of_lt (hx.trans_le hB),Nat.mod_eq_of_lt hc,
    take_cells B xs (Nat.le_of_lt hx)]

/-- Injection for the concrete live payload and cursor, not merely a bound
on how many mathematical states there might be. -/
theorem encode_injective (B d w : ℕ) (hB : B ≤ (2^w)^d)
    (xs ys : List (Word w)) (c e : ℕ)
    (hx : xs.length < B) (hy : ys.length < B)
    (hc : c < (2^w)^d) (he : e < (2^w)^d)
    (h : encode B d w xs c = encode B d w ys e) : xs=ys ∧ c=e := by
  have hd := congrArg decode h
  rw [decode_encode B d w xs c hx hB hc,
    decode_encode B d w ys e hy hB he] at hd
  exact Prod.mk.inj hd

/-- The cursor records the actual number of consumed disk blocks. -/
def encodeReader (B d w : ℕ) (s : Reader (Word w)) : Resident B d w :=
  encode B d w s.pending s.reads

/-- The output cursor is the actual number of completed external blocks. -/
def encodeWriter (B d w : ℕ) (s : Writer (Word w)) : Resident B d w :=
  encode B d w s.pending s.blocks.length

theorem reader_decode (B d w : ℕ) (s : Reader (Word w))
    (hs : s.Valid B) (hB : B ≤ (2^w)^d) (hc : s.reads < (2^w)^d) :
    decode (encodeReader B d w s) = (s.pending,s.reads) :=
  decode_encode B d w s.pending s.reads hs.2 hB hc

theorem writer_decode (B d w : ℕ) (s : Writer (Word w))
    (hs : s.Valid B) (hB : B ≤ (2^w)^d) (hc : s.blocks.length < (2^w)^d) :
    decode (encodeWriter B d w s) = (s.pending,s.blocks.length) :=
  decode_encode B d w s.pending s.blocks.length hs.2 hB hc

/-- Resident equality and equality of the external disk suffice to recover
the original Reader. An external stream is not silently stored in RAM. -/
theorem reader_recover (B d w : ℕ) (s t : Reader (Word w))
    (hs : s.Valid B) (ht : t.Valid B) (hB : B ≤ (2^w)^d)
    (hc : s.reads < (2^w)^d) (he : t.reads < (2^w)^d)
    (hr : encodeReader B d w s = encodeReader B d w t) (hd : s.disk=t.disk) : s=t := by
  have h := encode_injective B d w hB s.pending t.pending s.reads t.reads
    hs.2 ht.2 hc he hr
  cases s; cases t
  simp_all

theorem writer_recover (B d w : ℕ) (s t : Writer (Word w))
    (hs : s.Valid B) (ht : t.Valid B) (hB : B ≤ (2^w)^d)
    (hc : s.blocks.length < (2^w)^d) (he : t.blocks.length < (2^w)^d)
    (hr : encodeWriter B d w s = encodeWriter B d w t) (hd : s.blocks=t.blocks) : s=t := by
  have h := encode_injective B d w hB s.pending t.pending s.blocks.length t.blocks.length
    hs.2 ht.2 hc he hr
  cases s; cases t
  simp_all

/-- A fixed local function consumes a resident pending element. It sees no
disk or captured earlier RAM and performs no transfer. -/
def popLocal (B d w : ℕ) (ram : Resident B d w) : Option (Word w × Resident B d w) :=
  let (xs,c) := decode ram
  match xs with
  | [] => none
  | a::rest => some (a,encode B d w rest c)

theorem popLocal_refines (B d w : ℕ) (s : Reader (Word w))
    (hs : s.Valid B) (hB : B ≤ (2^w)^d) (hc : s.reads < (2^w)^d)
    (a : Word w) (rest : List (Word w)) (hp : s.pending=a::rest) :
    popLocal B d w (encodeReader B d w s) =
      some (a,encodeReader B d w ⟨s.disk,rest,s.reads⟩) ∧
      s.pop=some (a,⟨s.disk,rest,s.reads⟩) := by
  constructor
  · unfold popLocal
    rw [reader_decode B d w s hs hB hc]
    simp only [hp]
    rfl
  · simp [Reader.pop,hp]

/-- A fixed local function appends one word. Its optional output is exactly
one full physical block; completed output blocks remain on disk. -/
def pushLocal (B d w : ℕ) (ram : Resident B d w) (a : Word w) :
    Resident B d w × Option (Words B w) :=
  let (xs,c) := decode ram
  let next := xs++[a]
  if next.length=B then (encode B d w [] (c+1),some (cells B next))
    else (encode B d w next c,none)

/-- Appending the emitted block to external storage is the existing Writer
step, including the exact pending state and actual completed-block cursor. -/
theorem pushLocal_refines (B d w : ℕ) (s : Writer (Word w)) (a : Word w)
    (hs : s.Valid B) (hB : B ≤ (2^w)^d) (hc : s.blocks.length < (2^w)^d) :
    let result := pushLocal B d w (encodeWriter B d w s) a
    result.1 = encodeWriter B d w (s.push B a) ∧
    (match result.2 with
      | none => s.blocks
      | some block => s.blocks++[List.ofFn block]) = (s.push B a).blocks := by
  dsimp only [pushLocal]
  rw [writer_decode B d w s hs hB hc]
  dsimp only
  by_cases h : (s.pending++[a]).length=B
  · simp only [h,↓reduceIte,Writer.push,encodeWriter,List.length_append,
      List.length_singleton]
    constructor
    · trivial
    · congr 2
      have ht := take_cells B (s.pending++[a]) (Nat.le_of_eq h)
      rw [h] at ht
      simpa only [List.take_of_length_le (show (List.ofFn (cells B (s.pending++[a]))).length ≤ B by simp)] using ht
  · simp only [h,↓reduceIte,Writer.push,encodeWriter]
    trivial

/-- A flush corresponds to one actual new external block, with no transfer
for a purely resident append. -/
theorem pushLocal_transfer_count (B d w : ℕ) (s : Writer (Word w)) (a : Word w)
    (hs : s.Valid B) (hB : B ≤ (2^w)^d) (hc : s.blocks.length < (2^w)^d) :
    (s.push B a).blocks.length = s.blocks.length +
      (if (pushLocal B d w (encodeWriter B d w s) a).2.isSome then 1 else 0) := by
  have hh := (pushLocal_refines B d w s a hs hB hc).2
  cases ho : (pushLocal B d w (encodeWriter B d w s) a).2 with
  | none =>
    simp only [ho] at hh
    rw [← hh]
    simp only [ho,Option.isSome_none,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
  | some block =>
    simp only [ho] at hh
    rw [← hh]
    simp only [ho,Option.isSome_some,↓reduceIte,List.length_append,List.length_singleton]

/-- A physical read supplies one B-word bank. The refill length descriptor
uses d original words, just like the cursor and the pending length. -/
def refillLocal (B d w : ℕ) (ram : Resident B d w)
    (block : Words B w) (lengthMinusOne : Words d w) :
    Option (Word w × Resident B d w) :=
  match (List.ofFn block).take (decodeWords lengthMinusOne+1) with
  | [] => none
  | a::rest => some (a,encode B d w rest ((decode ram).2+1))

/-- Refill implements the exact existing Reader.pop, and advances its
actual read cursor by one. The transfer bank is additional resident storage. -/
theorem refillLocal_refines (B d w : ℕ) (a : Word w) (rest : List (Word w))
    (disk : List (List (Word w))) (c : ℕ)
    (hblock : (a::rest).length ≤ B) (hB : B ≤ (2^w)^d) (hc : c < (2^w)^d) :
    let lengthCode := PhysicalStreamCursor.encodeNat d w rest.length
    let s : Reader (Word w) := ⟨(a::rest)::disk,[],c⟩
    refillLocal B d w (encodeReader B d w s) (cells B (a::rest)) lengthCode =
      some (a,encodeReader B d w ⟨disk,rest,c+1⟩) ∧
      s.pop = some (a,⟨disk,rest,c+1⟩) := by
  dsimp only
  constructor
  · unfold refillLocal encodeReader
    have hpos : 0<B := by simp only [List.length_cons] at hblock; omega
    rw [decode_encode B d w [] c hpos hB hc]
    rw [PhysicalStreamCursor.decodeNat_encode d w rest.length (by
      simp only [List.length_cons] at hblock
      omega)]
    have hh := take_cells B (a::rest) hblock
    simp only [List.length_cons] at hh
    rw [hh]
  · rfl

/-- The next cursor must fit as well if the post-state is to be decoded.
This explicit hypothesis prevents a modular counter wrap from being hidden
by equality of encoded states. -/
theorem refillLocal_post_decode (B d w : ℕ) (a : Word w) (rest : List (Word w))
    (c : ℕ) (hblock : (a::rest).length ≤ B) (hB : B ≤ (2^w)^d)
    (hc : c+1 < (2^w)^d) :
    decode (encode B d w rest (c+1)) = (rest,c+1) := by
  apply decode_encode B d w rest (c+1) _ hB hc
  simp only [List.length_cons] at hblock
  omega

/-- Writer post-state decodability uses the true output cursor bound,
including its one-block advance in the flushing case. -/
theorem pushLocal_post_decode (B d w : ℕ) (s : Writer (Word w)) (a : Word w)
    (hs : s.Valid B) (hB : B ≤ (2^w)^d) (hc : s.blocks.length < (2^w)^d)
    (hc' : (s.push B a).blocks.length < (2^w)^d) :
    decode (pushLocal B d w (encodeWriter B d w s) a).1 =
      ((s.push B a).pending,(s.push B a).blocks.length) := by
  rw [(pushLocal_refines B d w s a hs hB hc).1]
  exact writer_decode B d w (s.push B a) (Writer.push_valid B s a hs) hB hc'


/-- Source base and record count are counted resident arrays, not free Nat
parameters captured by the input-specific stream procedure. -/
structure InputState (B d w : ℕ) where
  base : Words d w
  records : Words d w
  resident : Resident B d w

def input (B d w base records : ℕ) (s : Reader (Word w)) : InputState B d w :=
  ⟨encodeNat d w base,encodeNat d w records,encodeReader B d w s⟩

/-- The only disk access in this function is a single block at base+cursor.
The pending-data branch and EOF branch perform no read. The returned Nat is
ghost cost, not a resident field. -/
def readStep {B d w : ℕ} (disk : BlockDisk B w) (s : InputState B d w) :
    Option (Word w × InputState B d w) × ℕ :=
  match popLocal B d w s.resident with
  | some (a,next) => (some (a,{s with resident:=next}),0)
  | none =>
    let cursor := (decode s.resident).2
    let records := decodeWords s.records
    if cursor*B < records then
      let block := disk (decodeWords s.base+cursor)
      let length := min B (records-cursor*B)
      let code := encodeNat d w (length-1)
      ((refillLocal B d w s.resident block code).map
        (fun (a,next) => (a,{s with resident:=next})),1)
    else (none,0)

/-- Physical reads can be recovered as an actual bank-machine operation at
the descriptor-derived address, rather than a symbolic scan-cost charge. -/
theorem actual_refill {B d w : ℕ} (disk : BlockDisk B w) (s : InputState B d w)
    (buffer : Words B w) :
    let address := decodeWords s.base+(decode s.resident).2
    let machine : BitWordPacking.State (Words B w) 1 := ⟨fun _ => buffer,disk⟩
    (BitWordPacking.step (.read address 0) machine).ram 0 = disk address ∧
      BitWordPacking.transferCost (.read address 0 : BitWordPacking.Operation (Words B w) 1)=1 := by
  simp [BitWordPacking.step,BitWordPacking.transferCost]

/-- Resident pending data is consumed without examining any external block. -/
theorem readStep_pending (B d w base records : ℕ) (s : Reader (Word w))
    (disk : BlockDisk B w) (hs : s.Valid B) (hB : B≤(2^w)^d)
    (hc : s.reads<(2^w)^d) (a : Word w) (rest : List (Word w))
    (hp : s.pending=a::rest) :
    readStep disk (input B d w base records s) =
      (some (a,input B d w base records ⟨s.disk,rest,s.reads⟩),0) := by
  have h := (popLocal_refines B d w s hs hB hc a rest hp).1
  simp only [readStep,input,h]

/-- The nonempty block fetched at a public address has exactly the
length supplied to refillLocal by the stored file-size descriptor. -/
theorem readStep_refill (B d w base records cursor : ℕ) (disk : BlockDisk B w)
    (hBpos : 0<B) (hB : B≤(2^w)^d)
    (hb : base<(2^w)^d) (hn : records<(2^w)^d) (hc : cursor<(2^w)^d)
    (hlive : cursor*B<records) :
    ∃ a rest,
      blockView disk base records cursor=a::rest ∧
      readStep disk (input B d w base records ⟨suffix disk base records cursor,[],cursor⟩) =
        (some (a,input B d w base records ⟨suffix disk base records (cursor+1),rest,cursor+1⟩),1) ∧
      (Reader.pop (⟨suffix disk base records cursor,[],cursor⟩ : Reader (Word w)))=
        some (a,⟨suffix disk base records (cursor+1),rest,cursor+1⟩) := by
  have hv : 0<(blockView disk base records cursor).length := by
    rw [blockView_length]
    omega
  obtain ⟨a,rest,hview⟩ := List.exists_cons_of_length_pos hv
  refine ⟨a,rest,hview,?_,?_⟩
  · have hlen : 0<min B (records-cursor*B) := by omega
    have hsmall : min B (records-cursor*B)-1<(2^w)^d := by omega
    unfold readStep input popLocal encodeReader
    dsimp only
    simp only [decode_encode B d w [] cursor hBpos hB hc]
    simp only [decodeNat_encode d w records hn,decodeNat_encode d w base hb]
    simp only [hlive,↓reduceIte,refillLocal]
    rw [decodeNat_encode d w _ hsmall]
    have he : min B (records-cursor*B)-1+1=min B (records-cursor*B) := by omega
    rw [he]
    change ((match blockView disk base records cursor with
      | [] => none
      | a::rest => some (a,encode B d w rest ((decode (encode B d w [] cursor)).2+1))).map _,1) = _
    rw [hview,decode_encode B d w [] cursor hBpos hB hc]
    rfl
  · rw [suffix_cons disk base records cursor ((cursor_live_iff B records cursor hBpos).2 hlive),hview]
    rfl

/-- EOF is decided using counted descriptors even if unrelated disk blocks
contain arbitrary data immediately following the file. -/
theorem readStep_eof (B d w base records cursor : ℕ) (disk : BlockDisk B w)
    (hBpos : 0<B) (hB : B≤(2^w)^d) (hn : records<(2^w)^d) (hc : cursor<(2^w)^d)
    (hend : records≤cursor*B) :
    readStep disk (input B d w base records ⟨[],[],cursor⟩)=(none,0) := by
  unfold readStep input popLocal encodeReader
  dsimp only
  simp only [decode_encode B d w [] cursor hBpos hB hc]
  simp only [decodeNat_encode d w records hn]
  simp only [show ¬cursor*B<records by omega,↓reduceIte]

/-- Unified refinement of every reader branch against the existing logical
Reader.pop. The external list is solely a disk-view assertion in this
specification; readStep never inspects it. -/
theorem readStep_refines (B d w base records cursor : ℕ) (disk : BlockDisk B w)
    (pending : List (Word w)) (hp : pending.length<B)
    (hBpos : 0<B) (hB : B≤(2^w)^d)
    (hb : base<(2^w)^d) (hn : records<(2^w)^d) (hc : cursor<(2^w)^d) :
    let logical : Reader (Word w) := ⟨suffix disk base records cursor,pending,cursor⟩
    readStep disk (input B d w base records logical) =
      (logical.pop.map (fun (a,next) => (a,input B d w base records next)),
        if pending=[] ∧ cursor*B<records then 1 else 0) := by
  dsimp only
  cases pending with
  | cons a rest =>
    have hv := readerView_valid disk base records cursor (a::rest) hBpos hp
    rw [readStep_pending B d w base records _ disk hv hB hc a rest rfl]
    simp only [Reader.pop,Option.map_some,List.cons_ne_self,reduceCtorEq,false_and,↓reduceIte]
    rfl
  | nil =>
    by_cases hlive : cursor*B<records
    · obtain ⟨a,rest,hview,hread,hpop⟩ :=
        readStep_refill B d w base records cursor disk hBpos hB hb hn hc hlive
      rw [hread,hpop]
      simp only [Option.map_some,hlive,and_self,↓reduceIte]
      rfl
    · have he : suffix disk base records cursor=[] :=
        suffix_empty disk base records cursor (by
          have hh := cursor_live_iff B records cursor hBpos
          omega)
      rw [he,readStep_eof B d w base records cursor disk hBpos hB hn hc (by omega)]
      simp only [Reader.pop,Option.map_none,hlive,and_false,↓reduceIte]
      rfl

/-- Writer base is resident; completed blocks remain solely on disk. -/
structure OutputState (B d w : ℕ) where
  base : Words d w
  resident : Resident B d w

def output (B d w base : ℕ) (s : Writer (Word w)) : OutputState B d w :=
  ⟨encodeNat d w base,encodeWriter B d w s⟩

def writeStep {B d w : ℕ} (disk : BlockDisk B w) (s : OutputState B d w)
    (a : Word w) : OutputState B d w × BlockDisk B w × ℕ :=
  let result := pushLocal B d w s.resident a
  let next : OutputState B d w := {s with resident:=result.1}
  match result.2 with
  | none => (next,disk,0)
  | some block =>
    (next,writeBlock disk (decodeWords s.base+(decode s.resident).2) block,1)

/-- The emitted block is written at the decoded base plus the actual
completed-block cursor. No inspection of existing file contents is used. -/
theorem writeStep_refines (B d w base : ℕ) (s : Writer (Word w)) (a : Word w)
    (disk : BlockDisk B w) (hs : s.Valid B) (hB : B≤(2^w)^d)
    (hb : base<(2^w)^d) (hc : s.blocks.length<(2^w)^d) :
    (writeStep disk (output B d w base s) a).1 = output B d w base (s.push B a) ∧
    (writeStep disk (output B d w base s) a).2.2 =
      (s.push B a).blocks.length-s.blocks.length ∧
    ∀ address,address≠base+s.blocks.length →
      (writeStep disk (output B d w base s) a).2.1 address=disk address := by
  have href := (pushLocal_refines B d w s a hs hB hc).1
  have hcost := pushLocal_transfer_count B d w s a hs hB hc
  unfold writeStep output
  dsimp only
  rw [decodeNat_encode d w base hb,writer_decode B d w s hs hB hc]
  dsimp only
  cases ho : (pushLocal B d w (encodeWriter B d w s) a).2 with
  | none =>
    simp only [ho,Option.isSome_none,Bool.false_eq_true,↓reduceIte,Nat.add_zero] at hcost
    refine ⟨?_,?_,fun _ _ => rfl⟩
    · rw [href]
    · change 0=(s.push B a).blocks.length-s.blocks.length
      omega
  | some block =>
    simp only [ho,Option.isSome_some,↓reduceIte] at hcost
    refine ⟨?_,?_,?_⟩
    · rw [href]
    · change 1=(s.push B a).blocks.length-s.blocks.length
      omega
    · intro address hne
      simp [writeBlock,hne]

/-- A successful descriptor-bounded refill cannot overflow the cursor:
with B≥1, the number of consumed blocks never exceeds the record count. -/
theorem next_cursor_fits (B d w records cursor : ℕ) (hB : 0<B)
    (hn : records<(2^w)^d) (hlive : cursor*B<records) : cursor+1<(2^w)^d := by
  have hmul : cursor≤cursor*B := Nat.le_mul_of_pos_right _ hB
  omega

/-- Full-buffer emission writes the exact current logical block, at the
single address obtained from counted base and completed-block cursor. -/
theorem writeStep_flush (B d w base : ℕ) (s : Writer (Word w)) (a : Word w)
    (disk : BlockDisk B w) (hs : s.Valid B) (hB : B≤(2^w)^d)
    (hb : base<(2^w)^d) (hc : s.blocks.length<(2^w)^d)
    (hfull : (s.pending++[a]).length=B) :
    writeStep disk (output B d w base s) a =
      (output B d w base (s.push B a),
        writeBlock disk (base+s.blocks.length) (cells B (s.pending++[a])),1) := by
  unfold writeStep output pushLocal
  simp only [writer_decode B d w s hs hB hc]
  simp only [hfull,↓reduceIte,decodeNat_encode d w base hb]
  unfold encodeWriter Writer.push
  simp only [hfull,↓reduceIte,List.length_append,List.length_singleton]

/-- A final partial block is emitted once; an empty pending buffer performs
no I/O. Its record count is derived from the existing cursor and length. -/
def finishStep {B d w : ℕ} (disk : BlockDisk B w) (s : OutputState B d w) :
    BlockDisk B w × ℕ × ℕ :=
  let data := decode s.resident
  let records := data.2*B+data.1.length
  if data.1=[] then (disk,records,0)
  else (writeBlock disk (decodeWords s.base+data.2) (cells B data.1),records,1)

theorem finishStep_partial (B d w base : ℕ) (s : Writer (Word w))
    (disk : BlockDisk B w) (hs : s.Valid B) (hB : B≤(2^w)^d)
    (hb : base<(2^w)^d) (hc : s.blocks.length<(2^w)^d) (hne : s.pending≠[]) :
    finishStep disk (output B d w base s) =
      (writeBlock disk (base+s.blocks.length) (cells B s.pending),
        s.blocks.length*B+s.pending.length,1) := by
  simp only [finishStep,output,writer_decode B d w s hs hB hc]
  simp only [hne,↓reduceIte,decodeNat_encode d w base hb]

theorem finishStep_empty (B d w base : ℕ) (s : Writer (Word w))
    (disk : BlockDisk B w) (hs : s.Valid B) (hB : B≤(2^w)^d)
    (hc : s.blocks.length<(2^w)^d) (he : s.pending=[]) :
    finishStep disk (output B d w base s) = (disk,s.blocks.length*B,0) := by
  simp only [finishStep,output,writer_decode B d w s hs hB hc]
  simp only [he,↓reduceIte,List.length_nil,Nat.add_zero]

/-- The final record count is returned in d actual words. Its range is an
explicit obligation, rather than an unbounded Nat stored as free control. -/
def finalCount {B d w : ℕ} (s : OutputState B d w) : Words d w :=
  encodeNat d w ((decode s.resident).2*B+(decode s.resident).1.length)

theorem finalCount_decode (B d w base : ℕ) (s : Writer (Word w))
    (hs : s.Valid B) (hB : B≤(2^w)^d) (hc : s.blocks.length<(2^w)^d)
    (hn : s.blocks.length*B+s.pending.length<(2^w)^d) :
    decodeWords (finalCount (output B d w base s)) =
      s.blocks.length*B+s.pending.length := by
  simp only [finalCount,output,writer_decode B d w s hs hB hc]
  exact decodeNat_encode d w _ hn

/-- The emitted final bank recovers exactly the pending logical suffix when
read under its stored record-count descriptor. Padding words are ignored. -/
theorem finishStep_payload (B d w base : ℕ) (s : Writer (Word w))
    (disk : BlockDisk B w) (hs : s.Valid B) (hB : B≤(2^w)^d)
    (hb : base<(2^w)^d) (hc : s.blocks.length<(2^w)^d) (hne : s.pending≠[]) :
    blockView (finishStep disk (output B d w base s)).1 base
      (s.blocks.length*B+s.pending.length) s.blocks.length = s.pending := by
  rw [finishStep_partial B d w base s disk hs hB hb hc hne]
  simp only [blockView,writeBlock,↓reduceIte,Nat.add_sub_cancel_left]
  rw [Nat.min_eq_right (Nat.le_of_lt hs.2)]
  exact take_cells B s.pending (Nat.le_of_lt hs.2)

/-- An allocated file's public address is exactly the address used by the
stream primitives. A sufficient reservation bounds each live block cursor. -/
theorem allocated_refill_address (B : ℕ) (hB : 0<B)
    (spans : List WorkspaceAllocation.Span) (file : Fin spans.length)
    (records cursor : ℕ) (hreserve : blockCount B records≤(spans.get file).blocks)
    (hlive : cursor*B<records) :
    ∃ offset : Fin (spans.get file).blocks,
      offset.val=cursor ∧
      AllocatedFileMachine.address (spans:=spans) ⟨file,offset⟩=(spans.get file).start+cursor := by
  have hc := ((cursor_live_iff B records cursor hB).2 hlive).trans_le hreserve
  exact ⟨⟨cursor,hc⟩,rfl,rfl⟩

/-- When a reserved file interval fits the d-word address range, every
actual refill address fits it as well, including a partial final block. -/
theorem refill_address_fits (B d w base records cursor : ℕ) (hB : 0<B)
    (hcapacity : base+blockCount B records≤(2^w)^d) (hlive : cursor*B<records) :
    base+cursor<(2^w)^d := by
  have hc := (cursor_live_iff B records cursor hB).2 hlive
  omega

/-- A real writer flush preserves every source/sibling block in a distinct
allocated span. This uses the single shared disk, not disjoint disk objects. -/
theorem writeStep_preserves_other_file (B d w : ℕ)
    (spans : List WorkspaceAllocation.Span) (hspans : spans.Pairwise WorkspaceAllocation.Before)
    (target other : Fin spans.length) (hne : target≠other)
    (s : Writer (Word w)) (a : Word w) (disk : BlockDisk B w)
    (hs : s.Valid B) (hB : B≤(2^w)^d)
    (hb : (spans.get target).start<(2^w)^d) (hc : s.blocks.length<(2^w)^d)
    (hoffset : s.blocks.length<(spans.get target).blocks)
    (offset : Fin (spans.get other).blocks) :
    (writeStep disk (output B d w (spans.get target).start s) a).2.1
      (AllocatedFileMachine.address (spans:=spans) ⟨other,offset⟩) =
      disk (AllocatedFileMachine.address (spans:=spans) ⟨other,offset⟩) := by
  apply (writeStep_refines B d w (spans.get target).start s a disk hs hB hb hc).2.2
  intro he
  have haddr : AllocatedFileMachine.address (spans:=spans) ⟨other,offset⟩ =
      AllocatedFileMachine.address (spans:=spans) ⟨target,⟨s.blocks.length,hoffset⟩⟩ := he
  have hid := congrArg Sigma.fst (AllocatedFileMachine.address_injective hspans haddr)
  exact hne hid.symm


end CodedSorting.CommonSortingNormalizationStreams
