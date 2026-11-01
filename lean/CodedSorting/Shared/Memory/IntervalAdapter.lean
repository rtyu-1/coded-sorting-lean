import CodedSorting.Shared.Records.RecordOperations

/-! Transport an aligned record program to an arbitrary interval of the
main packed file. Extraction and reinsertion are real charged copies;
reinsertion preserves the neighboring words of both boundary blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonIntervalAdapter
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonRecordInterval (EncodedAt)
open CommonLeafProgram (Machine Disk)
open CommonMarginTransform (wordAt)
noncomputable section

structure Fits (q : Configuration) (n base O buffer work limit : ℕ) : Prop where
  source_before : base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)+2≤buffer
  scratch_before : buffer+recordBlocks q n+2≤work
  workspace : work≤limit
  capacity : limit≤q.N^q.exponent

theorem scratch_fits (q : Configuration) {n base O buffer work limit : ℕ}
    (h : Fits q n base O buffer work limit) :
    buffer+recordBlocks q n≤q.N^q.exponent := by
  have := h.scratch_before;have := h.workspace;have := h.capacity;omega

theorem main_end (q : Configuration) {n base O buffer work limit : ℕ}
    (h : Fits q n base O buffer work limit) :
    base+3*O/q.block+CommonIntervalCopy.pages q (3*O) (3*n)≤buffer := by
  rw [Nat.add_assoc,CommonRecordInterval.interval_end]
  have := h.source_before;omega

def extract (q : Configuration) (reader : Fin q.inventory.readers)
    (n base O buffer : ℕ) : List (Instruction q) :=
  CommonIntervalCopy.code q reader (3*O) 0 (3*n) base buffer

def restore (q : Configuration) (reader : Fin q.inventory.readers)
    (n base O buffer : ℕ) : List (Instruction q) :=
  CommonIntervalCopy.code q reader 0 (3*O) (3*n) buffer base

theorem extract_pages (q : Configuration) (n : ℕ) :
    CommonIntervalCopy.pages q 0 (3*n)=recordBlocks q n := by
  rw [CommonRecordEncoding.recordBlocks_eq_words]
  simp only [CommonIntervalCopy.pages,Nat.zero_mod,Nat.zero_add]

theorem extract_raw (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} (h : Fits q n base O buffer work limit)
    (s : Machine q) :
    CommonIntervalCopy.Written q (3*O) 0 (3*n) base buffer 0 (recordBlocks q n) s.disk
      (executeRaw q (extract q reader n base O buffer) s).1.disk := by
  have hs : base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)+2≤q.N^q.exponent := by
    have := h.source_before;have := scratch_fits q h;omega
  have ht := scratch_fits q h
  have hsep := CommonIntervalCopyBounds.readsOutside q (3*O) 0 (3*n) base buffer hs
    (Or.inl (by simpa using h.source_before))
  have hr := CommonIntervalCopy.raw q reader (3*O) 0 (3*n) base buffer s
    (by simpa only [Nat.zero_div,Nat.add_zero,extract_pages] using ht) hsep
  simpa only [Nat.zero_div,Nat.zero_add,extract_pages] using hr

theorem restore_raw (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} (h : Fits q n base O buffer work limit)
    (s : Machine q) :
    CommonIntervalCopy.Written q 0 (3*O) (3*n) buffer base (3*O/q.block)
      (3*O/q.block+CommonIntervalCopy.pages q (3*O) (3*n)) s.disk
      (executeRaw q (restore q reader n base O buffer) s).1.disk := by
  have hs : buffer+PhysicalStreamCursor.blockCount q.block (0+3*n)+2≤q.N^q.exponent := by
    rw [Nat.zero_add,←CommonRecordEncoding.recordBlocks_eq_words]
    exact h.scratch_before.trans (h.workspace.trans h.capacity)
  have hsep := CommonIntervalCopyBounds.readsOutside q 0 (3*O) (3*n) buffer base hs
    (Or.inr (main_end q h))
  exact CommonIntervalCopy.raw q reader 0 (3*O) (3*n) buffer base s
    ((main_end q h).trans (by have:=scratch_fits q h;omega)) hsep

theorem extract_correct (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} (h : Fits q n base O buffer work limit)
    (s : Machine q) (f : Records q n) (hf : EncodedAt q s.disk base O f) :
    Encoded q (executeRaw q (extract q reader n base O buffer) s).1.disk buffer f := by
  apply (CommonRecordEncoding.encoded_iff_words q _ buffer f (scratch_fits q h)).2
  intro i j
  have hij : i.val*3+j.val<3*n := by have:=i.isLt;have:=j.isLt;omega
  have hsrc : base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)+2≤q.N^q.exponent := by
    have:=h.source_before;have:=scratch_fits q h;omega
  have hh := CommonIntervalCopyBounds.raw_word q reader (3*O) 0 (3*n) base buffer s hsrc
    (by simpa only [Nat.zero_div,Nat.add_zero,extract_pages] using scratch_fits q h)
    (Or.inl (by simpa using h.source_before)) (i.val*3+j.val)
    (CommonRecordEncoding.word_fits q n buffer _ (scratch_fits q h) hij)
  simp only [Nat.zero_le,Nat.zero_add,Nat.sub_zero,true_and,hij,if_true] at hh
  change wordAt q (executeRaw q (extract q reader n base O buffer) s).1.disk buffer _=_ at hh
  rw [hh]
  simpa only [Nat.add_assoc] using hf i j

theorem restore_correct (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} (h : Fits q n base O buffer work limit)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk buffer f) :
    EncodedAt q (executeRaw q (restore q reader n base O buffer) s).1.disk base O f := by
  have hw := (CommonRecordEncoding.encoded_iff_words q _ buffer f (scratch_fits q h)).1 hf
  intro i j
  have hij : i.val*3+j.val<3*n := by have:=i.isLt;have:=j.isLt;omega
  have hs : buffer+PhysicalStreamCursor.blockCount q.block (0+3*n)+2≤q.N^q.exponent := by
    rw [Nat.zero_add,←CommonRecordEncoding.recordBlocks_eq_words]
    exact h.scratch_before.trans (h.workspace.trans h.capacity)
  have hkey : 3*O≤3*O+i.val*3+j.val ∧ 3*O+i.val*3+j.val<3*O+3*n := by omega
  have hpage := (CommonIntervalCopyBounds.live_page q (3*O) (3*n) _ hkey.1 hkey.2).2
  have hm := main_end q h
  have hvalid : base+(3*O+i.val*3+j.val)/q.block<q.N^q.exponent := by
    have:=scratch_fits q h;omega
  have hh := CommonIntervalCopyBounds.raw_word q reader 0 (3*O) (3*n) buffer base s hs
    (hm.trans (by have:=scratch_fits q h;omega)) (Or.inr hm) _ hvalid
  rw [if_pos hkey,Nat.zero_add] at hh
  have he : 3*O+i.val*3+j.val-3*O=i.val*3+j.val := by omega
  rw [he] at hh
  exact hh.trans (hw i j)

def code (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F) : List (Instruction q) :=
  (extract q reader n base O buffer++p.instructions)++restore q reader n base O buffer

def charge (q : Configuration) (n O innerCharge : ℕ) : ℕ :=
  6*recordBlocks q n+innerCharge+6*CommonIntervalCopy.pages q (3*O) (3*n)

theorem prepare_frame (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F)
    (h : Fits q n base O buffer work limit) (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<buffer ∨ limit≤a.val) :
    (executeRaw q (extract q reader n base O buffer++p.instructions) s).1.disk a=s.disk a := by
  have hb := h.scratch_before
  have hw := h.workspace
  rw [CommonPermutationPairs.raw_append,p.frame _ a (by omega) (by omega)]
  exact (extract_raw q reader h s).outside a (by omega)

theorem code_correct (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F)
    (h : Fits q n base O buffer work limit) (s : Machine q)
    (f : Records q n) (hf : EncodedAt q s.disk base O f) :
    EncodedAt q (executeRaw q (code q reader (base:=base) (O:=O) p) s).1.disk base O (F f) := by
  rw [code,CommonPermutationPairs.raw_append,CommonPermutationPairs.raw_append]
  exact restore_correct q reader h _ _ (p.correct _ _ (extract_correct q reader h s f hf))

theorem code_frame (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F)
    (h : Fits q n base O buffer work limit) (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<base+3*O/q.block ∨ base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)≤a.val)
    (hw : a.val<buffer ∨ limit≤a.val) :
    (executeRaw q (code q reader (base:=base) (O:=O) p) s).1.disk a=s.disk a := by
  rw [code,CommonPermutationPairs.raw_append]
  have hf := (restore_raw q reader h
    (executeRaw q (extract q reader n base O buffer++p.instructions) s).1).outside a
  have he := CommonRecordInterval.interval_end q (3*O) (3*n)
  rw [hf (by omega)]
  exact prepare_frame q reader p h s a hw

theorem code_word_frame (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F)
    (h : Fits q n base O buffer work limit) (s : Machine q) (j : ℕ)
    (hj : base+j/q.block<q.N^q.exponent) (ho : j<3*O ∨ 3*O+3*n≤j)
    (hw : base+j/q.block<buffer ∨ limit≤base+j/q.block) :
    wordAt q (executeRaw q (code q reader (base:=base) (O:=O) p) s).1.disk base j=wordAt q s.disk base j := by
  rw [code,CommonPermutationPairs.raw_append]
  have ht := main_end q h
  have hs : buffer+PhysicalStreamCursor.blockCount q.block (0+3*n)+2≤q.N^q.exponent := by
    rw [Nat.zero_add,←CommonRecordEncoding.recordBlocks_eq_words]
    exact h.scratch_before.trans (h.workspace.trans h.capacity)
  rw [restore,CommonIntervalCopyBounds.raw_word q reader 0 (3*O) (3*n) buffer base _ hs
    (ht.trans (by have:=scratch_fits q h;omega)) (Or.inr ht) j hj,if_neg (by omega)]
  apply CommonRecordInterval.word_congr q _ s.disk base j hj
  exact prepare_frame q reader p h s ⟨base+j/q.block,hj⟩ hw


theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F) :
    ∀ i∈code q reader (base:=base) (O:=O) p,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · rcases List.mem_append.mp hi with hi|hi
    · exact CommonIntervalCopy.code_safe q reader _ _ _ _ _ i hi
    · exact p.safe i hi
  · exact CommonIntervalCopy.code_safe q reader _ _ _ _ _ i hi

theorem code_cost_le (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F) :
    cost q (code q reader (base:=base) (O:=O) p)≤charge q n O p.charge := by
  simp only [code,CommonPermutationPairs.cost_append,extract,restore,
    CommonIntervalCopy.code_cost,extract_pages,charge]
  exact Nat.add_le_add_right (Nat.add_le_add_left p.cost_le _) _

theorem code_length_le (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F) :
    (code q reader (base:=base) (O:=O) p).length≤charge q n O p.charge := by
  simp only [code,List.length_append,extract,restore,
    CommonIntervalCopy.code_length,extract_pages,charge]
  exact Nat.add_le_add_right (Nat.add_le_add_left p.length_le _) _

def program (q : Configuration) (reader : Fin q.inventory.readers)
    {n base O buffer work limit : ℕ} {F : Records q n → Records q n}
    (p : CommonRecordProgram.Program q n buffer work limit F)
    (h : Fits q n base O buffer work limit) :
    CommonRecordInterval.Program q n base O buffer limit F where
  instructions := code q reader p
  charge := charge q n O p.charge
  correct := code_correct q reader p h
  word_frame := code_word_frame q reader p h
  frame := code_frame q reader p h
  safe := code_safe q reader p
  cost_le := code_cost_le q reader p
  length_le := code_length_le q reader p

/-- Extraction and reinsertion add only a scan and one boundary page. -/
theorem charge_le (q : Configuration) (n O inner : ℕ) :
    charge q n O inner≤ inner+12*(recordBlocks q n+1) := by
  have h := CommonIntervalCopyBounds.pages_le q (3*O) (3*n)
  rw [←CommonRecordEncoding.recordBlocks_eq_words] at h
  unfold charge
  omega

end
end CodedSorting.CommonIntervalAdapter
