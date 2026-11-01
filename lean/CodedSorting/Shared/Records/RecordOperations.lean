import CodedSorting.Sorting.Local.Framework.PhysicalLocalSortNode
import CodedSorting.Interchange.Framework.Memory.PaddedChunks
import CodedSorting.Shared.Memory.IntervalCopyBounds

section KeyRecordBits
/-! The concrete record codec used by the file-level local sorter.
Each record occupies the consecutive bits of its three existing words:
tag, key, and payload.  The codec changes neither their order nor their
physical positions.  Its parameters depend on the word width, not on the
input file. -/
set_option autoImplicit false

namespace CodedSorting.KeyRecordBits
open Circuit WordControl KeyRecordWords BitWordPacking
open PhysicalLocalSortEncoding PhysicalLocalSortLeafCodec

instance recordBot (w : ℕ) : OrderBot (Record w) where
  bot := .bottom
  bot_le a := by
    change (abstract (Record.bottom : Record w)) ≤ abstract a
    exact bot_le

instance recordTop (w : ℕ) : OrderTop (Record w) where
  top := .top
  le_top a := by
    change abstract a ≤ (abstract (Record.top : Record w))
    exact le_top

def code (w : ℕ) (hw : 2 ≤ w) (r : Record w) : Fin (3*w) → Bit :=
  blockBits 3 w (KeyRecordWords.encode w hw r)

def decode (w : ℕ) (bits : Fin (3*w) → Bit) : Record w :=
  KeyRecordWords.decode ((blockBits 3 w).symm bits)

@[simp] theorem decode_code (w : ℕ) (hw : 2 ≤ w) (r : Record w) :
    decode w (code w hw r) = r := by
  simp only [decode,code,Equiv.symm_apply_apply,KeyRecordWords.decode_encode]

theorem code_injective (w : ℕ) (hw : 2 ≤ w) :
    Function.Injective (code w hw) := by
  intro a b h
  simpa only [decode_code] using congrArg (decode w) h

/-- The j-th word and i-th bit retain the literal position j*w+i. -/
theorem code_at (w : ℕ) (hw : 2 ≤ w) (r : Record w)
    (j : Fin 3) (i : Fin w) :
    code w hw r (finProdFinEquiv (j,i)) =
      wordBits w (KeyRecordWords.encode w hw r j) i :=
  blockBits_at 3 w _ j i

theorem code_address (w : ℕ) (j : Fin 3) (i : Fin w) :
    (finProdFinEquiv (j,i)).val = j.val*w+i.val :=
  bit_address 3 w j i

/-- The CPU used by the generic leaf batch decodes exactly the stored
records and returns their sorted three-word encodings. -/
theorem ramSort_exact (w : ℕ) (hw : 2 ≤ w) (n : ℕ)
    (f : Fin n → Record w) :
    ramSort n (code w hw) (decode w) (bitList (code w hw) f) =
      bitList (code w hw) (Columnsort.sortColumn f) :=
  ramSort_bitList _ _ (decode_code w hw) f

/-- The bounded-word order agrees with the paper's key/payload order. -/
theorem abstract_sort (w : ℕ) (n : ℕ) (f : Fin n → Record w) :
    abstract ∘ Columnsort.sortColumn f =
      Columnsort.sortColumn (abstract ∘ f) :=
  Columnsort.monotone_map_sortColumn f (@abstract w)
    (ResidentLeafSort.abstract_monotone w)

end CodedSorting.KeyRecordBits
end KeyRecordBits

section Program
/-! In-place programs on the paper's concrete three-word records.
The input records occur only in the correctness specification; instructions
are fixed by public dimensions and never capture an input file. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonRecordProgram
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open KeyRecordWords Circuit
noncomputable section

abbrev Records (q : Configuration) (n : ℕ) := Fin n → Record q.w

def bits (q : Configuration) {n : ℕ} (f : Records q n) : Fin (n*(3*q.w)) → Bit :=
  fun i => KeyRecordBits.code q.w (by have:=q.word_width; omega) (f (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2

@[simp] theorem bits_at (q : Configuration) {n : ℕ} (f : Records q n)
    (i : Fin n) (j : Fin (3*q.w)) :
    bits q f (finProdFinEquiv (i,j))=KeyRecordBits.code q.w (by have:=q.word_width; omega) (f i) j := by
  simp only [bits,Equiv.symm_apply_apply]

def Encoded (q : Configuration) {n : ℕ} (disk : Disk q) (base : ℕ) (f : Records q n) : Prop :=
  ∀ i : Fin (n*(3*q.w)),readBit q disk base i.val=bits q f i

theorem encoded_iff (q : Configuration) {n : ℕ} (disk : Disk q) (base : ℕ)
    (f : Records q n) : Encoded q disk base f ↔
      ∀ (i : Fin n) (j : Fin (3*q.w)),
        readBit q disk base (i.val*(3*q.w)+j.val)=KeyRecordBits.code q.w (by have:=q.word_width; omega) (f i) j := by
  constructor
  · intro h i j
    have hh := h (finProdFinEquiv (i,j))
    simpa only [bits_at,BitWordPacking.bit_address] using hh
  · intro h y
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective y
    simpa only [bits_at,BitWordPacking.bit_address] using h i j

def recordBlocks (q : Configuration) (n : ℕ) := count q (n*(3*q.w))

structure Program (q : Configuration) (n source buffer limit : ℕ)
    (F : Records q n → Records q n) where
  instructions : List (Instruction q)
  charge : ℕ
  correct : ∀ (s : Machine q) (f : Records q n),Encoded q s.disk source f →
    Encoded q (executeRaw q instructions s).1.disk source (F f)
  frame : ∀ (s : Machine q) (a : Fin (q.N^q.exponent)),
    (a.val<source ∨ source+recordBlocks q n≤a.val) →
    (a.val<buffer ∨ limit≤a.val) →
    (executeRaw q instructions s).1.disk a=s.disk a
  safe : ∀ i∈instructions,RespectsPC q i
  cost_le : cost q instructions≤charge
  length_le : instructions.length≤charge

namespace Program
variable {q : Configuration} {n source buffer limit : ℕ}
variable {F G : Records q n→Records q n}

def identity (q : Configuration) (n source buffer limit : ℕ) :
    Program q n source buffer limit id where
  instructions := []
  charge := 0
  correct := fun _ _ h=>h
  frame := fun _ _ _ _=>rfl
  safe := by simp
  cost_le := Nat.le_refl 0
  length_le := Nat.le_refl 0

def append (p : Program q n source buffer limit F) (r : Program q n source buffer limit G) :
    Program q n source buffer limit (G∘F) where
  instructions := p.instructions++r.instructions
  charge := p.charge+r.charge
  correct := by
    intro s f hf
    rw [raw_append]
    exact r.correct _ _ (p.correct s f hf)
  frame := by
    intro s a hs hb
    rw [raw_append,r.frame _ a hs hb,p.frame s a hs hb]
  safe := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact p.safe i hi
    · exact r.safe i hi
  cost_le := by
    rw [cost_append]
    exact Nat.add_le_add p.cost_le r.cost_le
  length_le := by
    rw [List.length_append]
    exact Nat.add_le_add p.length_le r.length_le

def changeFunction (p : Program q n source buffer limit F) (h : F=G) :
    Program q n source buffer limit G := h ▸ p

end Program

theorem complete (q : Configuration) {n source buffer limit : ℕ}
    {F : Records q n→Records q n} (p : Program q n source buffer limit F)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : p.charge≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    Encoded q result.1.disk source (F f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧ result.2≤p.charge ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q p.instructions
    (p.length_le.trans hsize) p.safe s hpc
  exact ⟨by rw [hd]; exact p.correct s f hf,by rw [hd]; exact p.frame s,
    hh,hc.trans_le p.cost_le,hm⟩

end
end CodedSorting.CommonRecordProgram
end Program

section Encoding
/-! The record and bit specifications describe the same literal disk words. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonRecordEncoding
open CommonSortingNormalization CommonPermutationPairs CommonRecordProgram
open CommonLeafProgram (Disk)
open KeyRecordWords WordControl BitWordPacking
noncomputable section

theorem recordBlocks_eq_words (q : Configuration) (n : ℕ) :
    recordBlocks q n=PhysicalStreamCursor.blockCount q.block (3*n) := by
  have hb := CommonLeafProgram.block_positive q
  have hw : 0<q.w := by have:=q.word_width; omega
  apply Nat.le_antisymm
  · apply LayoutConversion.blockCount_minimal _ _ _ (width_pos q)
    have h := Nat.mul_le_mul_right q.w (LayoutConversion.blockCount_covers (3*n) q.block hb)
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,recordBlocks,count,width] using h
  · apply LayoutConversion.blockCount_minimal _ _ _ hb
    have h := LayoutConversion.blockCount_covers (n*(3*q.w)) (width q) (width_pos q)
    change n*(3*q.w)≤recordBlocks q n*(q.block*q.w) at h
    have h' : (3*n)*q.w≤(recordBlocks q n*q.block)*q.w := by nlinarith only [h]
    nlinarith only [h',hw]

def WordsEncoded (q : Configuration) {n : ℕ} (disk : Disk q) (base : ℕ)
    (f : Records q n) : Prop :=
  ∀ (i : Fin n) (j : Fin 3),CommonMarginTransform.wordAt q disk base (i.val*3+j.val)=
    encode q.w (by have:=q.word_width; omega) (f i) j

theorem wordAt_eq_diskWord (q : Configuration) (disk : Disk q) (base j : ℕ) :
    CommonMarginTransform.wordAt q disk base j=CommonLeafLoad.diskWord q disk base j := by
  unfold CommonMarginTransform.wordAt CommonLeafBatchProgram.extendDisk CommonLeafLoad.diskWord
  split_ifs <;> rfl

theorem word_fits (q : Configuration) (n base j : ℕ)
    (hs : base+recordBlocks q n≤q.N^q.exponent) (hj : j<3*n) :
    base+j/q.block<q.N^q.exponent := by
  rw [recordBlocks_eq_words] at hs
  have hlt := (PhysicalStreamCursor.cursor_live_iff q.block (3*n) (j/q.block)
    (CommonLeafProgram.block_positive q)).2 ((Nat.div_mul_le_self j q.block).trans_lt hj)
  omega

theorem readBit_wordAt (q : Configuration) (disk : Disk q) (base j : ℕ)
    (t : Fin q.w) (hj : base+j/q.block<q.N^q.exponent) :
    readBit q disk base (j*q.w+t.val)=
      wordBits q.w (CommonMarginTransform.wordAt q disk base j) t := by
  rw [CommonSlabReadBits.readBit_word]
  simp only [CommonColumnSplit.address,hj,↓reduceDIte,
    CommonMarginTransform.wordAt,CommonLeafBatchProgram.extendDisk]

theorem encoded_iff_words (q : Configuration) {n : ℕ} (disk : Disk q) (base : ℕ)
    (f : Records q n) (hs : base+recordBlocks q n≤q.N^q.exponent) :
    Encoded q disk base f ↔ WordsEncoded q disk base f := by
  rw [encoded_iff]
  constructor
  · intro h i j
    apply (wordBits q.w).injective
    funext t
    have hi : i.val*3+j.val<3*n := by have:=i.isLt; have:=j.isLt; omega
    have he : (i.val*3+j.val)*q.w+t.val=
        i.val*(3*q.w)+(finProdFinEquiv (j,t)).val := by rw [bit_address]; ring
    rw [←readBit_wordAt q disk base _ t (word_fits q n base _ hs hi),he,h,KeyRecordBits.code_at]
  · intro h i b
    obtain ⟨⟨j,t⟩,rfl⟩ := finProdFinEquiv.surjective b
    have hi : i.val*3+j.val<3*n := by have:=i.isLt; have:=j.isLt; omega
    have he : i.val*(3*q.w)+(finProdFinEquiv (j,t)).val=
        (i.val*3+j.val)*q.w+t.val := by rw [bit_address]; ring
    rw [he,readBit_wordAt q disk base _ t (word_fits q n base _ hs hi),h,KeyRecordBits.code_at]

end
end CodedSorting.CommonRecordEncoding
end Encoding

section Prefix
/-! Lift an actual record program through a larger zero-padded file and
copy back the original prefix.  Zero bits encode the declared bottom
sentinel, so the enlarged input is a valid record array. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonRecordPrefix
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonRecordProgram CommonFinitePadding
open CommonLeafProgram (Machine)
noncomputable section

def extendBottom {q : Configuration} {n m : ℕ} (f : Records q n) : Records q m :=
  fun i => if hi : i.val<n then f ⟨i.val,hi⟩ else .bottom

@[simp] theorem extend_prefix {q : Configuration} {n m : ℕ} (h : n≤m)
    (f : Records q n) (i : Fin n) : extendBottom (m:=m) f (Fin.castLE h i)=f i := by
  simp only [extendBottom,Fin.coe_castLE,dif_pos i.isLt]

theorem bottom_bit (q : Configuration) (j : Fin (3*q.w)) :
    KeyRecordBits.code q.w (by have:=q.word_width; omega) .bottom j=0 := by
  obtain ⟨⟨a,b⟩,rfl⟩ := finProdFinEquiv.surjective j
  rw [KeyRecordBits.code_at]
  have hz : KeyRecordWords.encode q.w (by have:=q.word_width; omega) .bottom a=0 := by
    fin_cases a <;> rfl
  rw [hz]
  simp [BitWordPacking.wordBits,finFunctionFinEquiv]

theorem prefix_encoded (q : Configuration) (reader : Fin q.inventory.readers)
    {n m : ℕ} (h : n≤m) (source target : ℕ)
    (hs : source+recordBlocks q n≤q.N^q.exponent)
    (ht : target+recordBlocks q m≤q.N^q.exponent)
    (hsep : source+recordBlocks q n≤target)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f) :
    Encoded q (executeRaw q (prefixCode q reader (n*(3*q.w)) (m*(3*q.w))
      source target) s).1.disk target (extendBottom (m:=m) f) := by
  have hh := prefix_raw q reader (n*(3*q.w)) (m*(3*q.w)) source target s
    (Nat.mul_le_mul_right _ h) hs ht (Or.inl hsep)
  apply (encoded_iff q _ _ _).2
  intro i j
  by_cases hi : i.val<n
  · let k : Fin (n*(3*q.w)) := finProdFinEquiv (⟨i.val,hi⟩,j)
    have hk : k.val=i.val*(3*q.w)+j.val := BitWordPacking.bit_address _ _ _ _
    rw [←hk,hh.1 k]
    simpa only [k,bits_at,extendBottom,dif_pos hi] using hf k
  · let k := finProdFinEquiv (i,j)
    have hk : k.val=i.val*(3*q.w)+j.val := BitWordPacking.bit_address _ _ _ _
    have hlo : n*(3*q.w)≤k.val := by
      rw [hk]
      exact (Nat.mul_le_mul_right _ (show n ≤ i.val by omega)).trans (Nat.le_add_right _ _)
    rw [←hk,hh.2.1 k hlo]
    simp only [extendBottom,dif_neg hi,bottom_bit]

def restrictOutput {q : Configuration} {n m : ℕ} (h : n≤m)
    (F : Records q m→Records q m) (f : Records q n) : Records q n :=
  fun i=>F (extendBottom f) (Fin.castLE h i)

def code {q : Configuration} (reader : Fin q.inventory.readers)
    {n m source buffer work limit : ℕ} {F : Records q m→Records q m}
    (p : Program q m buffer work limit F) : List (Instruction q) :=
  prefixCode q reader (n*(3*q.w)) (m*(3*q.w)) source buffer ++ p.instructions ++
    CommonRecursiveExchange.copyCode q reader (n*(3*q.w)) buffer source

def program {q : Configuration} (reader : Fin q.inventory.readers)
    {n m source buffer work limit : ℕ} {F : Records q m→Records q m}
    (h : n≤m) (p : Program q m buffer work limit F)
    (hs : source+recordBlocks q n≤buffer)
    (hw : buffer+recordBlocks q m≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent) :
    Program q n source buffer limit (restrictOutput h F) where
  instructions := code (n:=n) (source:=source) reader p
  charge := 12*recordBlocks q n+3*recordBlocks q m+p.charge
  correct := by
    intro s f hf
    have hm := count_mono q (Nat.mul_le_mul_right (3*q.w) h)
    change recordBlocks q n≤recordBlocks q m at hm
    have hen := prefix_encoded q reader h source buffer (by omega) (by omega) hs s f hf
    let mid := (executeRaw q (prefixCode q reader (n*(3*q.w)) (m*(3*q.w)) source buffer) s).1
    have hc := p.correct mid (extendBottom f) hen
    obtain ⟨hout,_⟩ := CommonRecursiveExchange.copyCode_raw q reader (n*(3*q.w)) buffer source
      (executeRaw q p.instructions mid).1 (by change buffer+recordBlocks q n≤_; omega)
      (by change source+recordBlocks q n≤_; omega) (Or.inr hs)
    rw [code,raw_append,raw_append]
    apply (encoded_iff q _ _ _).2
    intro i j
    let k := finProdFinEquiv (i,j)
    have hk : k.val=i.val*(3*q.w)+j.val := BitWordPacking.bit_address _ _ _ _
    rw [←hk,hout k]
    rw [hk]
    exact (encoded_iff q _ _ _).1 hc (Fin.castLE h i) j
  frame := by
    intro s a has hab
    have hm := count_mono q (Nat.mul_le_mul_right (3*q.w) h)
    change recordBlocks q n≤recordBlocks q m at hm
    have hp := prefix_raw q reader (n*(3*q.w)) (m*(3*q.w)) source buffer s
      (Nat.mul_le_mul_right _ h) (by change source+recordBlocks q n≤_; omega)
      (by change buffer+recordBlocks q m≤_; omega) (Or.inl hs)
    let mid := (executeRaw q (prefixCode q reader (n*(3*q.w)) (m*(3*q.w)) source buffer) s).1
    obtain ⟨_,hcopy⟩ := CommonRecursiveExchange.copyCode_raw q reader (n*(3*q.w)) buffer source
      (executeRaw q p.instructions mid).1 (by change buffer+recordBlocks q n≤_; omega)
      (by change source+recordBlocks q n≤_; omega) (Or.inr hs)
    rw [code,raw_append,raw_append,hcopy a has]
    rw [p.frame mid a (by omega) (by omega)]
    apply hp.2.2 a
    change a.val<buffer ∨ buffer+recordBlocks q m≤a.val
    omega
  safe := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · rcases List.mem_append.mp hi with hi|hi
      · exact prefix_safe q reader _ _ source buffer i hi
      · exact p.safe i hi
    · exact CommonRecursiveExchange.copyCode_safe q reader _ buffer source i hi
  cost_le := by
    rw [code,cost_append,cost_append]
    have hp := prefix_cost q reader (n*(3*q.w)) (m*(3*q.w)) source buffer
    have hc := CommonRecursiveExchange.copyCode_cost q reader (n*(3*q.w)) buffer source
    have hpc := p.cost_le
    dsimp only [recordBlocks] at *
    omega
  length_le := by
    rw [code,List.length_append,List.length_append]
    have hp := prefix_length q reader (n*(3*q.w)) (m*(3*q.w)) source buffer
    have hc := CommonRecursiveExchange.copyCode_length q reader (n*(3*q.w)) buffer source
    have hpc := p.length_le
    dsimp only [recordBlocks] at *
    omega

end
end CodedSorting.CommonRecordPrefix
end Prefix

section Reindex
/-! Equal numeric record counts are alternative index types for the same
stored file.  These casts create no instructions and charge no I/O. -/
set_option autoImplicit false
namespace CodedSorting.CommonRecordReindex
open CommonRecordProgram CommonSortingNormalization
open CommonStaticSchedule CommonPermutationPairs
noncomputable section

/-- Reindex the same records along an equality of their counts. -/
def castRecords {α : Type*} {n n' : ℕ} (h : n=n') (f : Fin n→α) : Fin n'→α :=
  fun i=>f ((finCongr h).symm i)

@[simp] theorem castRecords_at {α : Type*} {n n' : ℕ} (h : n=n')
    (f : Fin n→α) (i : Fin n) : castRecords h f (finCongr h i)=f i := by
  simp [castRecords]

@[simp] theorem castRecords_refl {α : Type*} {n : ℕ} (f : Fin n→α) : castRecords rfl f=f := rfl

@[simp] theorem castRecords_cancel {α : Type*} {n n' : ℕ} (h : n=n')
    (f : Fin n→α) : castRecords h.symm (castRecords h f)=f := by
  subst n'
  rfl

theorem encoded_cast (q : Configuration) {n n' : ℕ} (h : n=n')
    (disk : CommonLeafProgram.Disk q) (base : ℕ) (f : Records q n) :
    Encoded q disk base (castRecords h f) ↔ Encoded q disk base f := by
  subst n'
  rfl

def castFunction (q : Configuration) {n n' : ℕ} (h : n=n')
    (F : Records q n→Records q n) : Records q n'→Records q n' :=
  fun f=>castRecords h (F (castRecords h.symm f))

/-- The instruction list and charge stay exactly the same under reindexing. -/
def castProgram {q : Configuration} {n n' source buffer limit : ℕ}
    {F : Records q n→Records q n} (p : Program q n source buffer limit F) (h : n=n') :
    Program q n' source buffer limit (castFunction q h F) where
  instructions := p.instructions
  charge := p.charge
  correct := by
    subst n'
    exact p.correct
  frame := by
    subst n'
    exact p.frame
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

@[simp] theorem castProgram_charge {q : Configuration} {n n' source buffer limit : ℕ}
    {F : Records q n→Records q n} (p : Program q n source buffer limit F) (h : n=n') :
    (castProgram p h).charge=p.charge := rfl

theorem changeFunction_charge {q : Configuration} {n source buffer limit : ℕ}
    {F G : Records q n→Records q n} (p : Program q n source buffer limit F) (h : F=G) :
    (p.changeFunction h).charge=p.charge := by
  subst G
  rfl

end
end CodedSorting.CommonRecordReindex
end Reindex

section Interval
/-! Literal three-word records at arbitrary record offsets in a packed
file. The interval interface preserves both unused boundary words and all
disk regions outside the specified scratch allocation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonRecordInterval
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonLeafProgram (Machine Disk)
open CommonMarginTransform (wordAt)
noncomputable section

def EncodedAt (q : Configuration) {n : ℕ} (disk : Disk q) (base O : ℕ)
    (f : Records q n) : Prop :=
  ∀ (i : Fin n) (j : Fin 3),wordAt q disk base (3*O+i.val*3+j.val)=
    KeyRecordWords.encode q.w (by have:=q.word_width;omega) (f i) j

theorem encodedAt_zero (q : Configuration) {n : ℕ} (disk : Disk q) (base : ℕ)
    (f : Records q n) (hs : base+recordBlocks q n≤q.N^q.exponent) :
    EncodedAt q disk base 0 f ↔ Encoded q disk base f := by
  rw [CommonRecordEncoding.encoded_iff_words q disk base f hs]
  simp only [EncodedAt,CommonRecordEncoding.WordsEncoded,Nat.mul_zero,Nat.zero_add]

theorem word_congr (q : Configuration) (a b : Disk q) (base j : ℕ)
    (hfit : base+j/q.block<q.N^q.exponent)
    (heq : a ⟨base+j/q.block,hfit⟩=b ⟨base+j/q.block,hfit⟩) :
    wordAt q a base j=wordAt q b base j := by
  simp only [wordAt,CommonLeafBatchProgram.extendDisk,hfit,↓reduceDIte,heq]

theorem interval_end (q : Configuration) (D N : ℕ) :
    D/q.block+CommonIntervalCopy.pages q D N=
      PhysicalStreamCursor.blockCount q.block (D+N) := by
  have hb := CommonLeafProgram.block_positive q
  have he : D/q.block*q.block+D%q.block=D := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod D q.block
  have hnum : D+N+q.block-1=D/q.block*q.block+(D%q.block+N+q.block-1) := by
    omega
  unfold CommonIntervalCopy.pages PhysicalStreamCursor.blockCount
  rw [hnum,Nat.add_comm (D/q.block*q.block) (D%q.block+N+q.block-1),
    Nat.add_mul_div_right _ _ hb]
  omega

structure Program (q : Configuration) (n base O buffer limit : ℕ)
    (F : Records q n → Records q n) where
  instructions : List (Instruction q)
  charge : ℕ
  correct : ∀ (s : Machine q) (f : Records q n),EncodedAt q s.disk base O f →
    EncodedAt q (executeRaw q instructions s).1.disk base O (F f)
  word_frame : ∀ (s : Machine q) (j : ℕ),base+j/q.block<q.N^q.exponent →
    (j<3*O ∨ 3*O+3*n≤j) →
    (base+j/q.block<buffer ∨ limit≤base+j/q.block) →
    wordAt q (executeRaw q instructions s).1.disk base j=wordAt q s.disk base j
  frame : ∀ (s : Machine q) (a : Fin (q.N^q.exponent)),
    (a.val<base+3*O/q.block ∨ base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)≤a.val) →
    (a.val<buffer ∨ limit≤a.val) →
    (executeRaw q instructions s).1.disk a=s.disk a
  safe : ∀ i∈instructions,RespectsPC q i
  cost_le : cost q instructions≤charge
  length_le : instructions.length≤charge

namespace Program
variable {q : Configuration} {n base O buffer limit : ℕ}
variable {F G : Records q n → Records q n}

def identity (q : Configuration) (n base O buffer limit : ℕ) :
    Program q n base O buffer limit id where
  instructions := []
  charge := 0
  correct := fun _ _ h => h
  word_frame := fun _ _ _ _ _ => rfl
  frame := fun _ _ _ _ => rfl
  safe := by simp
  cost_le := le_rfl
  length_le := le_rfl

def append (p : Program q n base O buffer limit F)
    (r : Program q n base O buffer limit G) : Program q n base O buffer limit (G∘F) where
  instructions := p.instructions++r.instructions
  charge := p.charge+r.charge
  correct := by
    intro s f hf
    rw [CommonPermutationPairs.raw_append]
    exact r.correct _ _ (p.correct s f hf)
  word_frame := by
    intro s j hj ho hw
    rw [CommonPermutationPairs.raw_append,r.word_frame _ j hj ho hw,p.word_frame s j hj ho hw]
  frame := by
    intro s a ha hw
    rw [CommonPermutationPairs.raw_append,r.frame _ a ha hw,p.frame s a ha hw]
  safe := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact p.safe i hi
    · exact r.safe i hi
  cost_le := by
    rw [CommonPermutationPairs.cost_append]
    exact Nat.add_le_add p.cost_le r.cost_le
  length_le := by
    rw [List.length_append]
    exact Nat.add_le_add p.length_le r.length_le

end Program

theorem complete (q : Configuration) {n base O buffer limit : ℕ}
    {F : Records q n → Records q n} (p : Program q n base O buffer limit F)
    (s : Machine q) (f : Records q n) (hf : EncodedAt q s.disk base O f)
    (hsize : p.charge≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    EncodedAt q result.1.disk base O (F f) ∧
    (∀ j,base+j/q.block<q.N^q.exponent → (j<3*O ∨ 3*O+3*n≤j) →
      (base+j/q.block<buffer ∨ limit≤base+j/q.block) →
      wordAt q result.1.disk base j=wordAt q s.disk base j) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<base+3*O/q.block ∨ base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧ result.2≤p.charge ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q p.instructions
    (p.length_le.trans hsize) p.safe s hpc
  exact ⟨by rw [hd];exact p.correct s f hf,
    by rw [hd];exact p.word_frame s,by rw [hd];exact p.frame s,
    hh,hc.trans_le p.cost_le,hm⟩

end
end CodedSorting.CommonRecordInterval
end Interval

section IntervalSplice
/-! Restricting a packed record file to a bucket and inserting a returned
bucket into that same file. These lemmas connect interval-program semantics
to the full-array invariant used by the global controller. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecordIntervalSplice
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonRecordInterval (EncodedAt)
open CommonLeafProgram (Machine Disk)
open CommonMarginTransform (wordAt)
noncomputable section

def slice {q : Configuration} {N n O : ℕ} (h : O+n≤N) (f : Records q N) : Records q n :=
  fun i => f ⟨O+i.val,by have:=i.isLt;omega⟩

def replace {q : Configuration} {N n O : ℕ} (h : O+n≤N)
    (f : Records q N) (g : Records q n) : Records q N := fun i =>
  if hi : O≤ i.val ∧ i.val<O+n then g ⟨i.val-O,by omega⟩ else f i

theorem slice_encodedAt (q : Configuration) {N n O : ℕ} (h : O+n≤N)
    (disk : Disk q) (base outer : ℕ) (f : Records q N)
    (hf : EncodedAt q disk base outer f) :
    EncodedAt q disk base (outer+O) (slice h f) := by
  intro i j
  have hi : O+i.val<N := by have:=i.isLt;omega
  have hh := hf ⟨O+i.val,hi⟩ j
  have he : 3*(outer+O)+i.val*3+j.val=3*outer+(O+i.val)*3+j.val := by ring
  rw [he]
  exact hh

theorem slice_encoded (q : Configuration) {N n O : ℕ} (h : O+n≤N)
    (disk : Disk q) (base : ℕ) (f : Records q N)
    (hfit : base+recordBlocks q N≤q.N^q.exponent)
    (hf : Encoded q disk base f) : EncodedAt q disk base O (slice h f) := by
  have hh := slice_encodedAt q h disk base 0 f
    ((CommonRecordInterval.encodedAt_zero q disk base f hfit).2 hf)
  simpa only [Nat.zero_add] using hh

theorem replace_encodedAt (q : Configuration) {N n O : ℕ} (h : O+n≤N)
    (original current : Disk q) (base : ℕ) (f : Records q N) (g : Records q n)
    (hf : EncodedAt q original base 0 f) (hg : EncodedAt q current base O g)
    (hframe : ∀ j,j<3*N → (j<3*O ∨ 3*O+3*n≤j) →
      wordAt q current base j=wordAt q original base j) :
    EncodedAt q current base 0 (replace h f g) := by
  intro i j
  simp only [Nat.mul_zero,Nat.zero_add]
  unfold replace
  by_cases hi : O≤ i.val ∧ i.val<O+n
  · rw [dif_pos hi]
    have hj : i.val-O<n := by omega
    have he : i.val*3+j.val=3*O+(i.val-O)*3+j.val := by omega
    rw [he]
    exact hg ⟨i.val-O,hj⟩ j
  · rw [dif_neg hi]
    have hj : i.val*3+j.val<3*N := by have:=i.isLt;have:=j.isLt;omega
    rw [hframe _ hj (by have:=j.isLt;omega)]
    simpa only [Nat.mul_zero,Nat.zero_add] using hf i j

/-- One actual interval execution updates the literal full-array encoding;
no agreement between two separately chosen input files is assumed. -/
theorem program_global (q : Configuration) {N n O base buffer limit : ℕ}
    (h : O+n≤N) {F : Records q n → Records q n}
    (p : CommonRecordInterval.Program q n base O buffer limit F)
    (hb : base+recordBlocks q N≤buffer) (hc : buffer≤q.N^q.exponent)
    (s : Machine q) (f : Records q N) (hf : Encoded q s.disk base f) :
    Encoded q (executeRaw q p.instructions s).1.disk base (replace h f (F (slice h f))) := by
  have hfit := hb.trans hc
  apply (CommonRecordInterval.encodedAt_zero q _ base _ hfit).1
  apply replace_encodedAt q h s.disk _ base f _
    ((CommonRecordInterval.encodedAt_zero q s.disk base f hfit).2 hf)
    (p.correct s _ (slice_encoded q h s.disk base f hfit hf))
  intro j hj ho
  have hblock : j/q.block<recordBlocks q N := by
    rw [CommonRecordEncoding.recordBlocks_eq_words]
    apply (PhysicalStreamCursor.cursor_live_iff q.block (3*N) _
      (CommonLeafProgram.block_positive q)).2
    exact (Nat.div_mul_le_self _ _).trans_lt hj
  apply p.word_frame s j (by omega) ho
  exact Or.inl (by omega)

/-- The same interval code can be viewed as an ordinary full-file program;
its semantic operation replaces only the selected contiguous subarray. -/
def lift (q : Configuration) {N n O base buffer limit : ℕ}
    (h : O+n≤N) {F : Records q n → Records q n}
    (p : CommonRecordInterval.Program q n base O buffer limit F)
    (hb : base+recordBlocks q N≤buffer) (hc : buffer≤q.N^q.exponent) :
    CommonRecordProgram.Program q N base buffer limit
      (fun f => replace h f (F (slice h f))) where
  instructions := p.instructions
  charge := p.charge
  correct := program_global q h p hb hc
  frame := by
    intro s a ha hw
    have hspan : PhysicalStreamCursor.blockCount q.block (3*O+3*n)≤recordBlocks q N := by
      rw [CommonRecordEncoding.recordBlocks_eq_words]
      unfold PhysicalStreamCursor.blockCount
      apply Nat.div_le_div_right
      omega
    apply p.frame s a _ hw
    rcases ha with ha|ha
    · exact Or.inl (ha.trans_le (Nat.le_add_right base (3*O/q.block)))
    · exact Or.inr (by omega)
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

@[simp] theorem lift_charge (q : Configuration) {N n O base buffer limit : ℕ}
    (h : O+n≤N) {F : Records q n → Records q n}
    (p : CommonRecordInterval.Program q n base O buffer limit F)
    (hb : base+recordBlocks q N≤buffer) (hc : buffer≤q.N^q.exponent) :
    (lift q h p hb hc).charge=p.charge := rfl


theorem slice_list (q : Configuration) {N n O : ℕ} (h : O+n≤N) (f : Records q N) :
    List.ofFn (slice h f)=((List.ofFn f).drop O).take n := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_take,List.getElem_drop,slice]

/-- The vector-level physical update is exactly the usual list splice. -/
theorem replace_list (q : Configuration) {N n O : ℕ} (h : O+n≤N)
    (f : Records q N) (g : Records q n) :
    List.ofFn (replace h f g)=
      (List.ofFn f).take O++List.ofFn g++(List.ofFn f).drop (O+n) := by
  have hO : O≤N := by omega
  have hlen : ((List.ofFn f).take O).length=O := by simp [Nat.min_eq_left hO]
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_append,List.length_drop,hlen]
    omega
  · intro i hi hj
    have hiN : i<N := by simpa only [List.length_ofFn] using hi
    rw [List.getElem_ofFn]
    unfold replace
    simp only [Fin.val_mk]
    by_cases hiO : i<O
    · rw [dif_neg (by omega),List.getElem_append_left (by simp only [List.length_append,hlen,List.length_ofFn];omega),
        List.getElem_append_left (by simpa only [hlen] using hiO),List.getElem_take,List.getElem_ofFn]
    · by_cases hin : i<O+n
      · rw [dif_pos (by omega),List.getElem_append_left (by simp only [List.length_append,hlen,List.length_ofFn];omega),
          List.getElem_append_right (by simpa only [hlen] using (show O≤ i by omega))]
        simp only [hlen,List.getElem_ofFn]
      · rw [dif_neg (by omega),List.getElem_append_right (by simp only [List.length_append,hlen,List.length_ofFn];omega)]
        simp only [List.length_append,hlen,List.length_ofFn,List.getElem_drop,List.getElem_ofFn]
        congr 1
        apply Fin.ext
        simp only [Fin.val_mk]
        omega

end
end CodedSorting.CommonRecordIntervalSplice
end IntervalSplice

section IntervalList
/-! List-valued encodings at arbitrary offsets, for the actual global MSD
recursion. Replacing one returned child preserves the enclosing interval;
the unchanged front and suffix follow from the physical word frame. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonRecordIntervalList
open CommonSortingNormalization CommonRecordProgram CommonRecordInterval
open CommonLeafProgram (Disk)
open CommonMarginTransform (wordAt)
noncomputable section

def EncodedListAt (q : Configuration) (disk : Disk q) (base O : ℕ)
    (xs : List (KeyRecordWords.Record q.w)) : Prop :=
  EncodedAt q disk base O xs.get

theorem ofFn (q : Configuration) {n : ℕ} (disk : Disk q) (base O : ℕ)
    (f : Records q n) : EncodedListAt q disk base O (List.ofFn f) ↔
      EncodedAt q disk base O f := by
  constructor
  · intro h i j
    have hh := h ⟨i.val,by simpa only [List.length_ofFn] using i.isLt⟩ j
    simpa only [List.get_eq_getElem,List.getElem_ofFn] using hh
  · intro h i j
    have hh := h ⟨i.val,by simpa only [List.length_ofFn] using i.isLt⟩ j
    simpa only [List.get_eq_getElem,List.getElem_ofFn] using hh

/-- A length-certified list presented as the existing finite-record interface. -/
def recordsOfList (q : Configuration) (n : ℕ) (xs : List (KeyRecordWords.Record q.w))
    (hlen : xs.length=n) : Records q n :=
  fun i => xs.get ⟨i.val,by have:=i.isLt;omega⟩

theorem ofFn_records (q : Configuration) (n : ℕ) (xs : List (KeyRecordWords.Record q.w))
    (hlen : xs.length=n) : List.ofFn (recordsOfList q n xs hlen)=xs := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,hlen]
  · intro i hi hj
    simp only [List.getElem_ofFn,recordsOfList,List.get_eq_getElem]

theorem encoded_records (q : Configuration) (disk : Disk q) (base O n : ℕ)
    (xs : List (KeyRecordWords.Record q.w)) (hlen : xs.length=n) :
    EncodedAt q disk base O (recordsOfList q n xs hlen) ↔
      EncodedListAt q disk base O xs := by
  rw [←ofFn q disk base O (recordsOfList q n xs hlen),ofFn_records]

theorem append_iff (q : Configuration) (disk : Disk q) (base O : ℕ)
    (xs ys : List (KeyRecordWords.Record q.w)) :
    EncodedListAt q disk base O (xs++ys) ↔
      EncodedListAt q disk base O xs ∧ EncodedListAt q disk base (O+xs.length) ys := by
  constructor
  · intro h
    constructor
    · intro i j
      have hh := h ⟨i.val,by simp only [List.length_append];omega⟩ j
      simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt] using hh
    · intro i j
      have hh := h ⟨xs.length+i.val,by simp only [List.length_append];omega⟩ j
      have he : 3*(O+xs.length)+i.val*3+j.val=3*O+(xs.length+i.val)*3+j.val := by ring
      rw [he]
      simpa only [List.get_eq_getElem,
        List.getElem_append_right (show xs.length≤xs.length+i.val by omega),
        Nat.add_sub_cancel_left] using hh
  · rintro ⟨hx,hy⟩ i j
    change wordAt q disk base (3*O+i.val*3+j.val)=_
    simp only [List.get_eq_getElem]
    by_cases hi : i.val<xs.length
    · rw [List.getElem_append_left hi]
      exact hx ⟨i.val,hi⟩ j
    · rw [List.getElem_append_right (by omega)]
      have hiy : i.val-xs.length<ys.length := by
        have := i.isLt
        simp only [List.length_append] at this
        omega
      have he : 3*O+i.val*3+j.val=3*(O+xs.length)+(i.val-xs.length)*3+j.val := by omega
      rw [he]
      exact hy ⟨i.val-xs.length,hiy⟩ j

theorem congr (q : Configuration) (original current : Disk q) (base O : ℕ)
    (xs : List (KeyRecordWords.Record q.w))
    (h : EncodedListAt q original base O xs)
    (hword : ∀ w,3*O≤w → w<3*O+3*xs.length →
      wordAt q current base w=wordAt q original base w) :
    EncodedListAt q current base O xs := by
  intro i j
  rw [hword _ (by omega) (by have:=i.isLt;have:=j.isLt;omega)]
  exact h i j

/-- Extract a child at its literal offset within an arbitrarily aligned parent. -/
theorem child (q : Configuration) (disk : Disk q) (base O : ℕ)
    (front xs suffix : List (KeyRecordWords.Record q.w))
    (h : EncodedListAt q disk base O (front++xs++suffix)) :
    EncodedListAt q disk base (O+front.length) xs :=
  ((append_iff q disk base O front xs).1
    ((append_iff q disk base O (front++xs) suffix).1 h).1).2

/-- Word-accurate replacement in the parent interval, including both boundary blocks. -/
theorem splice (q : Configuration) (original current : Disk q) (base O : ℕ)
    (front xs suffix returned : List (KeyRecordWords.Record q.w))
    (hlen : returned.length=xs.length)
    (h : EncodedListAt q original base O (front++xs++suffix))
    (hc : EncodedListAt q current base (O+front.length) returned)
    (hframe : ∀ w,3*O≤w → w<3*O+3*(front++xs++suffix).length →
      (w<3*(O+front.length) ∨ 3*(O+front.length)+3*xs.length≤w) →
      wordAt q current base w=wordAt q original base w) :
    EncodedListAt q current base O (front++returned++suffix) := by
  obtain ⟨hpx,hs⟩ := (append_iff q original base O (front++xs) suffix).1 h
  obtain ⟨hp,_⟩ := (append_iff q original base O front xs).1 hpx
  have hp' : EncodedListAt q current base O front := by
    apply congr q original current base O front hp
    intro w hw hw'
    apply hframe w hw
    · simp only [List.length_append]
      omega
    · exact Or.inl (by omega)
  have hs' : EncodedListAt q current base (O+(front++returned).length) suffix := by
    have he : O+(front++returned).length=O+(front++xs).length := by simp only [List.length_append,hlen]
    rw [he]
    apply congr q original current base _ suffix hs
    intro w hw hw'
    have hw0 : 3*O≤w := by simp only [List.length_append] at hw;omega
    apply hframe w hw0
    · simp only [List.length_append] at hw' ⊢
      omega
    · right
      simp only [List.length_append] at hw
      omega
  exact (append_iff q current base O (front++returned) suffix).2
    ⟨(append_iff q current base O front returned).2 ⟨hp',hc⟩,hs'⟩

/-- Vector form of the same replacement, with an arbitrary parent offset. -/
theorem replace_encodedAt (q : Configuration) {N n start : ℕ} (h : start+n≤N)
    (original current : Disk q) (base O : ℕ) (f : Records q N) (g : Records q n)
    (hf : EncodedAt q original base O f) (hg : EncodedAt q current base (O+start) g)
    (hframe : ∀ w,3*O≤w → w<3*O+3*N →
      (w<3*(O+start) ∨ 3*(O+start)+3*n≤w) →
      wordAt q current base w=wordAt q original base w) :
    EncodedAt q current base O (CommonRecordIntervalSplice.replace h f g) := by
  intro i j
  unfold CommonRecordIntervalSplice.replace
  by_cases hi : start≤ i.val ∧ i.val<start+n
  · rw [dif_pos hi]
    have hj : i.val-start<n := by omega
    have he : 3*O+i.val*3+j.val=3*(O+start)+(i.val-start)*3+j.val := by omega
    rw [he]
    exact hg ⟨i.val-start,hj⟩ j
  · rw [dif_neg hi]
    rw [hframe _ (by omega) (by have:=i.isLt;have:=j.isLt;omega)
      (by have:=j.isLt;omega)]
    exact hf i j

end
end CodedSorting.CommonRecordIntervalList
end IntervalList
