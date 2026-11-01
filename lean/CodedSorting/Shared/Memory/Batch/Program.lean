import CodedSorting.Shared.Memory.Leaf.Correctness

section Program
/-! A shared-buffer batch on the existing source RAM. The only external
accesses are the addressed stream primitives. The loop bounds below are
execution fuel; all payload positions and file descriptors are resident. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafBatchProgram
open WordControl CommonSortingNormalization
open CommonLeafProgram (Slots Store RAM Disk Machine phase setPhase machine)
namespace Stream
export CommonSortingNormalizationStreams (encode decode input output readStep writeStep finishStep)
end Stream

def position (q : Configuration) (s : Store q) : ℕ :=
  decodeWords (fun i : Fin q.digits => s.scalars (i.natAdd 1))

def setPosition (q : Configuration) (k : ℕ) (s : Store q) : Store q :=
  {s with scalars := Fin.append (fun _ : Fin 1 => s.scalars (CommonLeafProgram.phaseIndex q)) (PhysicalStreamCursor.encodeNat q.digits q.w k)}

@[simp] theorem position_setPosition (q : Configuration) (k : ℕ) (s : Store q)
    (hk : k < (2^q.w)^q.digits) : position q (setPosition q k s)=k := by
  unfold position setPosition
  simp only [Fin.append_right]
  exact PhysicalStreamCursor.decodeNat_encode _ _ _ hk

@[simp] theorem phase_setPosition (q : Configuration) (k : ℕ) (s : Store q) :
    phase q (setPosition q k s)=phase q s := by
  simp only [phase,setPosition,CommonLeafProgram.phaseIndex]
  exact congrArg Fin.val (Fin.append_left _ _ (0 : Fin 1))

/-- Extension is only the interface adapter to a natural-address primitive;
its stored disk is finite. No blocks beyond the finite disk are represented. -/
def extendDisk (q : Configuration) (disk : Disk q) : BlockDisk q.block q.w :=
  fun a => if h : a<q.N^q.exponent then disk ⟨a,h⟩ else fun _ => 0

def restrictDisk (q : Configuration) (disk : BlockDisk q.block q.w) : Disk q :=
  fun a => disk a.val

@[simp] theorem restrict_extend (q : Configuration) (disk : Disk q) :
    restrictDisk q (extendDisk q disk)=disk := by
  funext a
  simp [restrictDisk,extendDisk,a.isLt]

/-- Specification-side sequential description of the resident bank updates. -/
def loadWords {cap d w : ℕ} : ℕ → List (Word w) → ResidentLeafSort.RAM cap d w → ResidentLeafSort.RAM cap d w
  | _,[],ram => ram
  | offset,a::rest,ram => loadWords (offset+1) rest
      (ResidentLeafBank.putBlock offset 1 (fun _ : Fin 1 => a) ram)

/-- One decoded word enters a fixed one-word slice of the resident leaf.
The stream's pending block and block cursor are retained across leaves. -/
def accept (q : Configuration) (z : Slots q) (s : Store q) (a : Word q.w)
    (reader : CommonSortingNormalizationStreams.InputState q.block q.digits q.w) : Store q :=
  setPosition q (position q s+1)
    {s with readers:=Function.update s.readers z.reader reader,
            leaf:=ResidentLeafBank.putBlock (position q s) 1 (fun _ : Fin 1 => a) s.leaf}

/-- An actual single-address reader step followed by a RAM-only bank update. -/
def readOne (q : Configuration) (z : Slots q) (disk : Disk q) (s : Store q) :
    Option (Store q × ℕ) :=
  let result := Stream.readStep (extendDisk q disk) (s.readers z.reader)
  result.1.map (fun (a,reader) => (accept q z s a reader,result.2))

/-- The gas parameter counts words; it is not an additional resident counter. -/
def readN (q : Configuration) (z : Slots q) (disk : Disk q) :
    ℕ → Store q → Option (Store q × ℕ)
  | 0,s => some (s,0)
  | k+1,s => do
      let (next,cost) ← readOne q z disk s
      let (final,rest) ← readN q z disk k next
      return (final,cost+rest)

/-- A write fetches exactly the current resident bank word. No file or input
function is supplied to the writer or the leaf CPU. -/
def writeOne (q : Configuration) (z : Slots q) (disk : Disk q) (s : Store q) :
    Store q × Disk q × ℕ :=
  let result := Stream.writeStep (extendDisk q disk) (s.writers z.writer)
    (ResidentLeafBank.getWord s.leaf (position q s))
  (setPosition q (position q s+1)
    {s with writers:=Function.update s.writers z.writer result.1},
    restrictDisk q result.2.1,result.2.2)

def writeN (q : Configuration) (z : Slots q) :
    ℕ → Store q → Disk q → Store q × Disk q × ℕ
  | 0,s,disk => (s,disk,0)
  | k+1,s,disk =>
      let one := writeOne q z disk s
      let rest := writeN q z k one.1 one.2.1
      (rest.1,rest.2.1,one.2.2+rest.2.2)

def compute (q : Configuration) (s : Store q) : Store q :=
  setPosition q 0 {s with leaf:=ResidentLeafSort.cpu (by have:=q.word_width; omega) s.leaf}

/-- Columns use one reader and one writer; neither stream is finished or
reinitialized at a column boundary. -/
def columns (q : Configuration) (z : Slots q) :
    ℕ → Store q → Disk q → Option (Store q × Disk q × ℕ)
  | 0,s,disk => some (s,disk,0)
  | k+1,s,disk => do
      let loaded ← readN q z disk (3*ResidentLeafSort.count s.leaf) (setPosition q 0 s)
      let written := writeN q z (3*ResidentLeafSort.count s.leaf) (compute q loaded.1) disk
      let rest ← columns q z k written.1 written.2.1
      return (rest.1,rest.2.1,loaded.2+written.2.2+rest.2.2)

/-- Only the final batch boundary flushes a partial output block. -/
def finish (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q) : Disk q × ℕ :=
  let result := Stream.finishStep (extendDisk q disk) (s.writers z.writer)
  (restrictDisk q result.1,result.2.2)

/-- The number of columns is decoded from the counted total and leaf header.
Neither file contents nor a source-specific closure participates in control. -/
def batch (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q) :
    Option (Store q × Disk q × ℕ) := do
  let total := decodeWords (s.readers z.reader).records
  let words := 3*ResidentLeafSort.count s.leaf
  let result ← columns q z (total/words) s disk
  let eof := Stream.readStep (extendDisk q result.2.1) (result.1.readers z.reader)
  match eof.1 with
  | some _ => none
  | none =>
      let final := finish q z result.1 result.2.1
      return (result.1,final.1,result.2.2+eof.2+final.2)

/-- Initialization writes only counted descriptors and the leaf header. -/
def initialStore (q : Configuration) (z : Slots q) (n : Fin (512*q.height+1))
    (total : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) : Store q :=
  setPosition q 0 (setPhase q 0
    {s with leaf:=ResidentLeafBank.initializeCount (leaf_header_capacity q) n s.leaf,
            readers:=Function.update s.readers z.reader
              (Stream.input q.block q.digits q.w source.val total.val ⟨[],[],0⟩),
            writers:=Function.update s.writers z.writer
              (Stream.output q.block q.digits q.w target.val BucketMachine.Writer.empty)})

@[simp] theorem accept_reader (q : Configuration) (z : Slots q) (s : Store q)
    (a : Word q.w) (reader : CommonSortingNormalizationStreams.InputState q.block q.digits q.w) :
    (accept q z s a reader).readers z.reader=reader := by
  simp only [accept,setPosition,Function.update_self]

@[simp] theorem accept_count (q : Configuration) (z : Slots q) (s : Store q)
    (a : Word q.w) (reader : CommonSortingNormalizationStreams.InputState q.block q.digits q.w) :
    ResidentLeafSort.count (accept q z s a reader).leaf=ResidentLeafSort.count s.leaf := by
  simp only [accept,setPosition,ResidentLeafBank.count_putBlock]

@[simp] theorem accept_position (q : Configuration) (z : Slots q) (s : Store q)
    (a : Word q.w) (reader : CommonSortingNormalizationStreams.InputState q.block q.digits q.w)
    (hc : position q s+1<(2^q.w)^q.digits) :
    position q (accept q z s a reader)=position q s+1 :=
  position_setPosition q _ _ hc

/-- The bank update preserves every earlier word and installs this word at
its precise raw position, without decoding or rewriting adjacent records. -/
theorem accept_raw (q : Configuration) (z : Slots q) (s : Store q)
    (a : Word q.w) (reader : CommonSortingNormalizationStreams.InputState q.block q.digits q.w)
    (i : Fin ((512*q.height)*3)) :
    ResidentLeafBank.raw (accept q z s a reader).leaf i=
      if i.val=position q s then a else ResidentLeafBank.raw s.leaf i := by
  by_cases he : i.val=position q s
  · rw [if_pos he]
    exact ResidentLeafBank.raw_putBlock_inside (position q s) 1 (fun _ : Fin 1 => a)
      s.leaf i (by omega) (by omega) (by decide)
  · rw [if_neg he]
    exact ResidentLeafBank.raw_putBlock_outside (position q s) 1 (fun _ : Fin 1 => a)
      s.leaf i (by omega)

end CodedSorting.CommonLeafBatchProgram
end Program

section Read
/-! Exact repeated addressed reads into the one counted leaf bank. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafBatchRead
open WordControl CommonSortingNormalization CommonLeafBatchProgram
open CommonLeafProgram (Slots Store Disk)
open BucketMachine BucketReader
namespace S
export CommonSortingNormalizationStreams (input readStep)
end S

/-- A proof-only reader view: external blocks are recovered from the one
finite disk and are never part of the resident stream representation. -/
def ReaderView (q : Configuration) (disk : Disk q) (base total : ℕ)
    (reader : Reader (Word q.w)) : Prop :=
  reader.disk=PhysicalStreamCursor.suffix (extendDisk q disk) base total reader.reads

@[simp] theorem blocksFrom_length {B w : ℕ} (disk : BlockDisk B w)
    (base total cursor left : ℕ) :
    (PhysicalStreamCursor.blocksFrom disk base total cursor left).length=left := by
  induction left generalizing cursor with
  | zero => rfl
  | succ left ih => simp only [PhysicalStreamCursor.blocksFrom,List.length_cons,ih]

@[simp] theorem suffix_length {B w : ℕ} (disk : BlockDisk B w)
    (base total cursor : ℕ) :
    (PhysicalStreamCursor.suffix disk base total cursor).length=
      PhysicalStreamCursor.blockCount B total-cursor :=
  blocksFrom_length _ _ _ _ _

theorem blocksFrom_congr {B w : ℕ} (disk₁ disk₂ : BlockDisk B w)
    (base total cursor left : ℕ)
    (hbound : cursor+left≤PhysicalStreamCursor.blockCount B total)
    (hagree : ∀ k, k<PhysicalStreamCursor.blockCount B total → disk₁ (base+k)=disk₂ (base+k)) :
    PhysicalStreamCursor.blocksFrom disk₁ base total cursor left=
      PhysicalStreamCursor.blocksFrom disk₂ base total cursor left := by
  induction left generalizing cursor with
  | zero => rfl
  | succ left ih =>
    simp only [PhysicalStreamCursor.blocksFrom]
    congr 1
    · unfold PhysicalStreamCursor.blockView
      rw [hagree cursor (by omega)]
    · exact ih (cursor+1) (by omega)

/-- Output writes may proceed while an input block is partially retained:
all unread input blocks remain the very same finite-disk view. -/
theorem readerView_preserved (q : Configuration) (disk₁ disk₂ : Disk q)
    (base total target : ℕ) (reader : Reader (Word q.w))
    (hview : ReaderView q disk₁ base total reader)
    (hsep : base+PhysicalStreamCursor.blockCount q.block total≤target)
    (hfit : target≤q.N^q.exponent)
    (hunchanged : ∀ a : Fin (q.N^q.exponent), a.val<target → disk₂ a=disk₁ a) :
    ReaderView q disk₂ base total reader := by
  unfold ReaderView at *
  rw [hview]
  by_cases hc : reader.reads≤PhysicalStreamCursor.blockCount q.block total
  · apply blocksFrom_congr
    · omega
    · intro k hk
      have ha : base+k<q.N^q.exponent := by omega
      simp only [extendDisk,dif_pos ha]
      exact (hunchanged ⟨base+k,ha⟩ (by change base+k<target; omega)).symm
  · rw [PhysicalStreamCursor.suffix_empty _ _ _ _ (by omega),
      PhysicalStreamCursor.suffix_empty _ _ _ _ (by omega)]

/-- A successful physical word pop refines the logical reader and its exact
refill counter. The invariant also proves that a cursor never wraps. -/
theorem pop_refines (q : Configuration) (disk : Disk q) (base total : ℕ)
    (reader next : Reader (Word q.w)) (a : Word q.w)
    (hv : reader.Valid q.block) (hview : ReaderView q disk base total reader)
    (hB : q.block≤(2^q.w)^q.digits)
    (hb : base<(2^q.w)^q.digits) (ht : total<(2^q.w)^q.digits)
    (hc : reader.reads<(2^q.w)^q.digits) (hp : reader.pop=some (a,next)) :
    S.readStep (extendDisk q disk) (S.input q.block q.digits q.w base total reader)=
      (some (a,S.input q.block q.digits q.w base total next),next.reads-reader.reads) ∧
    ReaderView q disk base total next ∧ next.reads<(2^q.w)^q.digits ∧ reader.reads≤next.reads := by
  rcases reader with ⟨blocks,pending,cursor⟩
  cases pending with
  | cons x xs =>
    simp only [Reader.pop] at hp
    cases hp
    refine ⟨?_,hview,hc,le_rfl⟩
    simpa using CommonSortingNormalizationStreams.readStep_pending q.block q.digits q.w
      base total ⟨blocks,a::xs,cursor⟩ (extendDisk q disk) hv hB hc a xs rfl
  | nil =>
    have hpos := CommonLeafProgram.block_positive q
    by_cases hlive : cursor*q.block<total
    · obtain ⟨x,xs,hblock,hread,hpop⟩ := CommonSortingNormalizationStreams.readStep_refill
        q.block q.digits q.w base total cursor (extendDisk q disk) hpos hB hb ht hc hlive
      have hblocks : blocks=PhysicalStreamCursor.suffix (extendDisk q disk) base total cursor := hview
      rw [hblocks] at hp
      rw [hpop] at hp
      cases hp
      refine ⟨?_,rfl,CommonSortingNormalizationStreams.next_cursor_fits _ _ _ _ _ hpos ht hlive,by dsimp only; omega⟩
      simpa only [hblocks,Nat.add_sub_cancel_left] using hread
    · have hblocks : blocks=[] := by
        exact hview.trans (PhysicalStreamCursor.suffix_empty (extendDisk q disk) base total cursor
          (by have hi := PhysicalStreamCursor.cursor_live_iff q.block total cursor hpos; omega))
      simp only [hblocks,Reader.pop] at hp
      cases hp

/-- The batch terminates from the stored total, retained pending buffer,
and actual block cursor; unrelated later blocks cannot suppress EOF. -/
theorem eof_refines (q : Configuration) (disk : Disk q) (base total : ℕ)
    (reader : Reader (Word q.w)) (hv : reader.Valid q.block)
    (hview : ReaderView q disk base total reader) (hempty : reader.contents=[])
    (hB : q.block≤(2^q.w)^q.digits)
    (ht : total<(2^q.w)^q.digits) (hc : reader.reads<(2^q.w)^q.digits) :
    S.readStep (extendDisk q disk) (S.input q.block q.digits q.w base total reader)=(none,0) := by
  have hd := Reader.empty_contents_disk q.block reader hv hempty
  have hp : reader.pending=[] := by
    simpa only [Reader.contents,hd,List.flatten_nil,List.append_nil] using hempty
  have hlen := congrArg List.length hview
  rw [hd,List.length_nil,suffix_length] at hlen
  have hb : PhysicalStreamCursor.blockCount q.block total≤reader.reads := by omega
  have hpos := CommonLeafProgram.block_positive q
  have hend : total≤reader.reads*q.block := by
    have hh := PhysicalStreamCursor.cursor_live_iff q.block total reader.reads hpos
    omega
  have hr : reader=⟨[],[],reader.reads⟩ := by cases reader; cases hd; cases hp; rfl
  rw [hr]
  exact CommonSortingNormalizationStreams.readStep_eof _ _ _ _ _ _ _ hpos hB ht hc hend

/-- The exact resident descriptor and bank after consuming a finite prefix.
The reader retains its pending block at the end of the prefix, including a
column boundary. The theorem charges refills from this same execution. -/
theorem readN_correct (q : Configuration) (z : Slots q) (disk : Disk q)
    (base total : ℕ) (front back : List (Word q.w)) (reader : Reader (Word q.w))
    (s : Store q)
    (hv : reader.Valid q.block) (hview : ReaderView q disk base total reader)
    (hreader : s.readers z.reader=S.input q.block q.digits q.w base total reader)
    (hcontents : reader.contents=front++back)
    (hB : q.block≤(2^q.w)^q.digits)
    (hb : base<(2^q.w)^q.digits) (ht : total<(2^q.w)^q.digits)
    (hc : reader.reads<(2^q.w)^q.digits)
    (hposition : position q s+front.length<(2^q.w)^q.digits) :
    ∃ finalReader finalStore cost,
      readN q z disk front.length s=some (finalStore,cost) ∧
      finalReader.Valid q.block ∧ ReaderView q disk base total finalReader ∧
      finalReader.contents=back ∧ finalReader.reads<(2^q.w)^q.digits ∧
      finalStore.readers z.reader=S.input q.block q.digits q.w base total finalReader ∧
      cost+reader.reads=finalReader.reads ∧
      position q finalStore=position q s+front.length ∧
      finalStore.leaf=loadWords (position q s) front s.leaf ∧
      finalStore.writers=s.writers ∧ finalStore.directories=s.directories ∧
      finalStore.shapes=s.shapes ∧ finalStore.top=s.top ∧ finalStore.pcs=s.pcs ∧
      finalReader.reads+finalReader.disk.length=reader.reads+reader.disk.length := by
  induction front generalizing reader s with
  | nil =>
    exact ⟨reader,s,0,rfl,hv,hview,by simpa using hcontents,hc,hreader,by omega,
      by simp,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | cons a rest ih =>
    have hcontents' : reader.contents=a::(rest++back) := by simpa using hcontents
    obtain ⟨next,hpop⟩ := Reader.pop_exists q.block reader hv a (rest++back) hcontents'
    have hnextvalid := Reader.pop_valid q.block reader next a hv hpop
    have hnextcontents : next.contents=rest++back := by
      have hh := Reader.pop_contents reader next a hpop
      rw [hcontents'] at hh
      exact (List.cons.inj hh).2.symm
    obtain ⟨hstep,hnextview,hnextcap,hmono⟩ :=
      pop_refines q disk base total reader next a hv hview hB hb ht hc hpop
    let nextStore := accept q z s a (S.input q.block q.digits q.w base total next)
    have hnextpos : position q nextStore=position q s+1 :=
      accept_position q z s a _ (by simp only [List.length_cons] at hposition; omega)
    have hone : readOne q z disk s=some (nextStore,next.reads-reader.reads) := by
      simp only [readOne,hreader,hstep,Option.map_some]
      rfl
    obtain ⟨finalReader,finalStore,cost,hrun,hvalid,hfinalview,hfinalcontents,hcap,
      hfinalreader,hcost,hpos,hleaf,hwriters,hdirs,hshapes,htop,hpcs,hconserve⟩ :=
      ih next nextStore hnextvalid hnextview (accept_reader q z s a _) hnextcontents hnextcap
        (by rw [hnextpos]; simp only [List.length_cons] at hposition; omega)
    refine ⟨finalReader,finalStore,(next.reads-reader.reads)+cost,?_,hvalid,hfinalview,
      hfinalcontents,hcap,hfinalreader,by omega,?_,?_,hwriters,hdirs,hshapes,htop,hpcs,
      hconserve.trans (Reader.pop_conservation reader next a hpop)⟩
    · simp [readN,hone,hrun]
    · rw [hpos,hnextpos]
      simp only [List.length_cons]
      omega
    · rw [hleaf,hnextpos]
      rfl

end CodedSorting.CommonLeafBatchRead
end Read

section Init
/-! Descriptor-only initialization and capacity facts for the buffered batch. -/
set_option autoImplicit false
namespace CodedSorting.CommonLeafBatchInit
open WordControl CommonSortingNormalization CommonLeafBatchProgram
open CommonLeafProgram (Slots Store Disk)
open BucketMachine BucketReader

@[simp] theorem count_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (total : Fin (q.N^q.exponent+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) :
    ResidentLeafSort.count (initialStore q z n total source target s).leaf=n.val := by
  simp only [initialStore,setPosition,CommonLeafProgram.setPhase,ResidentLeafBank.count_initializeCount]

@[simp] theorem position_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (total : Fin (q.N^q.exponent+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) :
    position q (initialStore q z n total source target s)=0 := by
  apply position_setPosition
  positivity

/-- The ghost blocks do not enter RAM: all empty-reader encodings agree,
regardless of which source file is used in the specification. -/
@[simp] theorem reader_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (total : Fin (q.N^q.exponent+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) (blocks : List (List (Word q.w))) :
    (initialStore q z n total source target s).readers z.reader=
      CommonSortingNormalizationStreams.input q.block q.digits q.w source.val total.val
        (Reader.fromDisk blocks) := by
  simp only [initialStore,setPosition,CommonLeafProgram.setPhase,Function.update_self]
  rfl

@[simp] theorem writer_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (total : Fin (q.N^q.exponent+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) :
    (initialStore q z n total source target s).writers z.writer=
      CommonSortingNormalizationStreams.output q.block q.digits q.w target.val Writer.empty := by
  simp only [initialStore,setPosition,CommonLeafProgram.setPhase,Function.update_self]

@[simp] theorem total_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (total : Fin (q.N^q.exponent+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) :
    decodeWords ((initialStore q z n total source target s).readers z.reader).records=total.val := by
  rw [reader_initial q z n total source target s []]
  exact PhysicalStreamCursor.decodeNat_encode _ _ _ (descriptor_capacity q total.val (by have:=total.isLt; omega))

@[simp] theorem raw_initial (q : Configuration) (z : Slots q)
    (n : Fin (512*q.height+1)) (total : Fin (q.N^q.exponent+1))
    (source target : Fin (q.N^q.exponent)) (s : Store q) :
    ResidentLeafBank.raw (initialStore q z n total source target s).leaf=ResidentLeafBank.raw s.leaf :=
  ResidentLeafBank.raw_initializeCount _ _ _

theorem leaf_words_capacity (q : Configuration) (s : Store q) :
    3*ResidentLeafSort.count s.leaf<(2^q.w)^q.digits :=
  descriptor_capacity q _ (CommonLeafInit.words_region q s).le

theorem leaf_words_capacity_of_le (q : Configuration) (n : ℕ) (hn : n≤512*q.height) :
    3*n<(2^q.w)^q.digits := by
  let ram : ResidentLeafSort.RAM (512*q.height) q.digits q.w := fun _ => 0
  let s : Store q := ⟨ResidentLeafBank.initializeCount (leaf_header_capacity q) ⟨n,by omega⟩ ram,
    fun _ => ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩,
    fun _ => ⟨fun _ => 0,fun _ => 0⟩,fun _ => 0,fun _ => 0,fun _ => fun _ => 0,
    fun _ => fun _ => 0,fun _ => 0,fun _ => fun _ => 0⟩
  have hh := leaf_words_capacity q s
  simpa only [s,ResidentLeafBank.count_initializeCount] using hh

end CodedSorting.CommonLeafBatchInit
end Init
