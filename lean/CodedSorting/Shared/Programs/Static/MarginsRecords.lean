import CodedSorting.Shared.Records.RecordOperations

section Margins
/-! Actual sentinel insertion and contiguous erasure in three-word record
storage. The offsets and lengths may be unaligned with disk blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonStaticMargins
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine Disk)
open CommonMarginGather (Written)
open CommonMarginTransform (shape topWord wordAt)
noncomputable section

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (L N R O source target : ℕ) : List (Instruction q) :=
  CommonStaticMarginGather.code q reader (CommonMarginTransform.scheme q)
    (shape q L N R O) source target

def ShapeFits (q : Configuration) (L N R O : ℕ) : Prop :=
  L<(2^q.w)^q.digits ∧ N<(2^q.w)^q.digits ∧
    R<(2^q.w)^q.digits ∧ O<(2^q.w)^q.digits

theorem shape_count (q : Configuration) (L N R O : ℕ) (h : ShapeFits q L N R O) :
    (CommonMarginTransform.scheme q).count (shape q L N R O)=
      PhysicalStreamCursor.blockCount q.block (L+N+R) := by
  obtain ⟨hL,hN,hR,hO⟩ := CommonMarginTransform.shape_fields q L N R O h.1 h.2.1 h.2.2.1 h.2.2.2
  simp only [CommonMarginTransform.scheme,CommonMarginTransform.outWords,hL,hN,hR]

theorem shape_source (q : Configuration) (L N R O : ℕ) (h : ShapeFits q L N R O) :
    CommonMarginTransform.inBlocks q (shape q L N R O)=
      max 1 (PhysicalStreamCursor.blockCount q.block (O+N)) := by
  obtain ⟨hL,hN,hR,hO⟩ := CommonMarginTransform.shape_fields q L N R O h.1 h.2.1 h.2.2.1 h.2.2.2
  simp only [CommonMarginTransform.inBlocks,hO,hN]

theorem cost_eq (q : Configuration) (reader : Fin q.inventory.readers)
    (L N R O source target : ℕ) (h : ShapeFits q L N R O) :
    cost q (code q reader L N R O source target)=
      3*PhysicalStreamCursor.blockCount q.block (L+N+R) := by
  rw [code,CommonStaticMarginGather.code,CommonStaticMarginGather.codeFrom_cost,shape_count q L N R O h]

theorem length_eq (q : Configuration) (reader : Fin q.inventory.readers)
    (L N R O source target : ℕ) (h : ShapeFits q L N R O) :
    (code q reader L N R O source target).length=
      3*PhysicalStreamCursor.blockCount q.block (L+N+R) := by
  rw [code,CommonStaticMarginGather.code,CommonStaticMarginGather.codeFrom_length,shape_count q L N R O h]

theorem safe (q : Configuration) (reader : Fin q.inventory.readers)
    (L N R O source target : ℕ) :
    ∀ i∈code q reader L N R O source target,RespectsPC q i :=
  CommonStaticMarginGather.codeFrom_safe q reader _ _ source target 0 _

/-- Every retained word is read from its actual original source offset;
the two margins are the literal bottom/top word patterns. -/
theorem raw (q : Configuration) (reader : Fin q.inventory.readers)
    (L N R O source target : ℕ) (s : Machine q) (h : ShapeFits q L N R O)
    (hs : source+max 1 (PhysicalStreamCursor.blockCount q.block (O+N))≤q.N^q.exponent)
    (ht : target+PhysicalStreamCursor.blockCount q.block (L+N+R)≤q.N^q.exponent)
    (hsep : source+max 1 (PhysicalStreamCursor.blockCount q.block (O+N))≤target ∨
      target+PhysicalStreamCursor.blockCount q.block (L+N+R)≤source) :
    (∀ j,j<L+N+R → wordAt q (executeRaw q (code q reader L N R O source target) s).1.disk target j=
      if j<L then 0 else if j<L+N then wordAt q s.disk source (O+(j-L)) else topWord q (j-(L+N))) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨
      target+PhysicalStreamCursor.blockCount q.block (L+N+R)≤a.val →
        (executeRaw q (code q reader L N R O source target) s).1.disk a=s.disk a) := by
  have hc := shape_count q L N R O h
  have hi := shape_source q L N R O h
  have hs' : source+CommonMarginTransform.inBlocks q (shape q L N R O)≤q.N^q.exponent := by rwa [hi]
  have ht' : target+(CommonMarginTransform.scheme q).count (shape q L N R O)≤q.N^q.exponent := by rwa [hc]
  have hsep' : source+CommonMarginTransform.inBlocks q (shape q L N R O)≤target ∨
      target+(CommonMarginTransform.scheme q).count (shape q L N R O)≤source := by rwa [hi,hc]
  have hh := CommonStaticMarginGather.raw q reader (CommonMarginTransform.scheme q)
    (shape q L N R O) source target s ht'
    (CommonMarginTransform.reads_outside q (shape q L N R O) source target hs' hsep')
  obtain ⟨hL,hN,hR,hO⟩ := CommonMarginTransform.shape_fields q L N R O h.1 h.2.1 h.2.2.1 h.2.2.2
  constructor
  · intro j hj
    have hw := CommonMarginTransform.written_words q (shape q L N R O) source target s.disk
      (executeRaw q (code q reader L N R O source target) s).1.disk hh hs' ht' j
      (by simpa only [CommonMarginTransform.outWords,hL,hN,hR] using hj)
    simpa only [CommonMarginTransform.expectedWord,hL,hN,hO] using hw
  · simpa only [hc] using hh.outside

/-- Extract a contiguous interval, including one beginning inside a block. -/
theorem erase_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (N O source target : ℕ) (s : Machine q) (h : ShapeFits q 0 N 0 O)
    (hs : source+max 1 (PhysicalStreamCursor.blockCount q.block (O+N))≤q.N^q.exponent)
    (ht : target+PhysicalStreamCursor.blockCount q.block N≤q.N^q.exponent)
    (hsep : source+max 1 (PhysicalStreamCursor.blockCount q.block (O+N))≤target ∨
      target+PhysicalStreamCursor.blockCount q.block N≤source) :
    ∀ j,j<N → wordAt q (executeRaw q (code q reader 0 N 0 O source target) s).1.disk target j=
      wordAt q s.disk source (O+j) := by
  have hr := (raw q reader 0 N 0 O source target s h hs (by simpa using ht) (by simpa using hsep)).1
  intro j hj
  simpa only [Nat.zero_add,Nat.add_zero,Nat.not_lt_zero,ite_false,hj,ite_true,Nat.sub_zero] using hr j (by omega)

/-- The public finite policy executes this same margin scan, halts, and
charges precisely its actual reads and writes. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (L N R O source target : ℕ) (s : Machine q) (h : ShapeFits q L N R O)
    (hs : source+max 1 (PhysicalStreamCursor.blockCount q.block (O+N))≤q.N^q.exponent)
    (ht : target+PhysicalStreamCursor.blockCount q.block (L+N+R)≤q.N^q.exponent)
    (hsep : source+max 1 (PhysicalStreamCursor.blockCount q.block (O+N))≤target ∨
      target+PhysicalStreamCursor.blockCount q.block (L+N+R)≤source)
    (hsize : 3*PhysicalStreamCursor.blockCount q.block (L+N+R)≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let instructions := code q reader L N R O source target
    let result := ControlledNormalization.runLogical (policy q instructions) instructions.length s
    (∀ j,j<L+N+R → wordAt q result.1.disk target j=
      if j<L then 0 else if j<L+N then wordAt q s.disk source (O+(j-L)) else topWord q (j-(L+N))) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨
      target+PhysicalStreamCursor.blockCount q.block (L+N+R)≤a.val → result.1.disk a=s.disk a) ∧
    policy q instructions result.1.ram=none ∧
    result.2=3*PhysicalStreamCursor.blockCount q.block (L+N+R) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (code q reader L N R O source target)
    (by rwa [length_eq q reader L N R O source target h])
    (safe q reader L N R O source target) s hpc
  obtain ⟨hw,hf⟩ := raw q reader L N R O source target s h hs ht hsep
  exact ⟨by rw [hd];exact hw,by rw [hd];exact hf,hh,
    hc.trans (cost_eq q reader L N R O source target h),hm⟩

end
end CodedSorting.CommonStaticMargins
end Margins

section MarginsRecords
/-! The literal word scan implements the record-level margin operation.
In particular its two inserted patterns are the declared record codec. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonStaticMarginsRecords
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine Disk)
open CommonMarginTransform (wordAt topWord)
open KeyRecordWords (Record encode)
noncomputable section

abbrev WordEncoded (q : Configuration) {n : ℕ} (disk : Disk q) (base : ℕ)
    (f : Fin n → Record q.w) := CommonRecordEncoding.WordsEncoded q disk base f

/-- Insert bottom and top sentinels around a retained contiguous slice. -/
def margin {w K : ℕ} (L N R O : ℕ) (h : O+N≤K) (f : Fin K → Record w) :
    Fin (L+N+R) → Record w := fun i =>
  if hl : i.val<L then .bottom
  else if hu : i.val<L+N then f ⟨O+(i.val-L),by omega⟩ else .top

theorem encode_bottom (q : Configuration) (j : Fin 3) :
    encode q.w (by have := q.word_width; omega) Record.bottom j=0 := by
  fin_cases j <;> rfl

theorem encode_top (q : Configuration) (j : Fin 3) (i : ℕ) :
    encode q.w (by have := q.word_width; omega) Record.top j=topWord q (3*i+j.val) := by
  have hj := j.isLt
  simp only [topWord,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,
    Nat.zero_add,Nat.mod_eq_of_lt hj]
  fin_cases j <;> rfl

theorem raw_words (q : Configuration) (reader : Fin q.inventory.readers)
    {K : ℕ} (L N R O source target : ℕ) (hKN : O+N≤K)
    (f : Fin K → Record q.w) (s : Machine q) (hin : WordEncoded q s.disk source f)
    (hshape : CommonStaticMargins.ShapeFits q (3*L) (3*N) (3*R) (3*O))
    (hs : source+max 1 (PhysicalStreamCursor.blockCount q.block (3*O+3*N))≤q.N^q.exponent)
    (ht : target+PhysicalStreamCursor.blockCount q.block (3*L+3*N+3*R)≤q.N^q.exponent)
    (hsep : source+max 1 (PhysicalStreamCursor.blockCount q.block (3*O+3*N))≤target ∨
      target+PhysicalStreamCursor.blockCount q.block (3*L+3*N+3*R)≤source) :
    WordEncoded q (executeRaw q (CommonStaticMargins.code q reader (3*L) (3*N) (3*R) (3*O)
      source target) s).1.disk target (margin L N R O hKN f) := by
  intro i j
  rw [Nat.mul_comm i.val 3]
  have hi := i.isLt
  have hj := j.isLt
  have hr := (CommonStaticMargins.raw q reader (3*L) (3*N) (3*R) (3*O) source target s
    hshape hs ht hsep).1 (3*i.val+j.val) (by omega)
  rw [hr]
  by_cases hl : i.val<L
  · have hh : 3*i.val+j.val<3*L := by omega
    simp only [margin,dif_pos hl,hh,ite_true,encode_bottom]
  · by_cases hu : i.val<L+N
    · have hh : ¬3*i.val+j.val<3*L := by omega
      have hh' : 3*i.val+j.val<3*L+3*N := by omega
      simp only [margin,dif_neg hl,dif_pos hu,hh,ite_false,hh',ite_true]
      have he : 3*O+(3*i.val+j.val-3*L)=3*(O+(i.val-L))+j.val := by omega
      rw [he]
      simpa only [Nat.mul_comm] using hin ⟨O+(i.val-L),by omega⟩ j
    · have hh : ¬3*i.val+j.val<3*L := by omega
      have hh' : ¬3*i.val+j.val<3*L+3*N := by omega
      simp only [margin,dif_neg hl,dif_neg hu,hh,ite_false,hh']
      have he : 3*i.val+j.val-(3*L+3*N)=3*(i.val-(L+N))+j.val := by omega
      rw [he,←encode_top]

/-- The same actual scan in the common record-bit specification. -/
theorem raw_encoded (q : Configuration) (reader : Fin q.inventory.readers)
    {K : ℕ} (L N R O source target : ℕ) (hKN : O+N≤K)
    (f : CommonRecordProgram.Records q K) (s : Machine q)
    (hin : CommonRecordProgram.Encoded q s.disk source f)
    (hshape : CommonStaticMargins.ShapeFits q (3*L) (3*N) (3*R) (3*O))
    (hsource : source+CommonRecordProgram.recordBlocks q K≤q.N^q.exponent)
    (hs : source+max 1 (PhysicalStreamCursor.blockCount q.block (3*O+3*N))≤q.N^q.exponent)
    (ht : target+PhysicalStreamCursor.blockCount q.block (3*L+3*N+3*R)≤q.N^q.exponent)
    (hsep : source+max 1 (PhysicalStreamCursor.blockCount q.block (3*O+3*N))≤target ∨
      target+PhysicalStreamCursor.blockCount q.block (3*L+3*N+3*R)≤source) :
    CommonRecordProgram.Encoded q
      (executeRaw q (CommonStaticMargins.code q reader (3*L) (3*N) (3*R) (3*O) source target) s).1.disk
      target (margin L N R O hKN f) := by
  apply (CommonRecordEncoding.encoded_iff_words q _ target _ ?_).2
  · exact raw_words q reader L N R O source target hKN f s
      ((CommonRecordEncoding.encoded_iff_words q s.disk source f hsource).1 hin) hshape hs ht hsep
  · rw [CommonRecordEncoding.recordBlocks_eq_words]
    simpa only [Nat.mul_add] using ht

end
end CodedSorting.CommonStaticMarginsRecords
end MarginsRecords
