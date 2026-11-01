import CodedSorting.Shared.Programs.Static.RecordLeaf
import CodedSorting.Shared.Records.RecordOperations
import CodedSorting.Shared.Programs.Static.Fusion

/-! Resident transformations returned in place on the concrete record disk.
The read--CPU--write pass and exact copy-back execute consecutively on the
same machine, and fusion retains their complete payload semantics and cost. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonResidentRecordProgram
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonRecordProgram CommonRecordEncoding
noncomputable section

theorem blocks_eq (q : Configuration) (n : ℕ) :
    CommonStaticRecordLeaf.blocks q n=recordBlocks q n :=
  (recordBlocks_eq_words q n).symm

theorem encoded_word (q : Configuration) {n : ℕ} (disk : CommonLeafProgram.Disk q)
    (base : ℕ) (f : Records q n) (hs : base+recordBlocks q n≤q.N^q.exponent) :
    Encoded q disk base f ↔ CommonStaticRecordLeaf.WordEncoded q n disk base f := by
  rw [encoded_iff_words q disk base f hs]
  unfold WordsEncoded CommonStaticRecordLeaf.WordEncoded
  simp only [wordAt_eq_diskWord]

def rawCode (q : Configuration) (reader : Fin q.inventory.readers)
    (n : ℕ) (hn : n≤512*q.height) (F : Records q n→Records q n)
    (source buffer : ℕ) : List (Instruction q) :=
  CommonStaticRecordLeaf.code q n hn F source buffer ++
    CommonRecursiveExchange.copyCode q reader (n*(3*q.w)) buffer source

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (n : ℕ) (hn : n≤512*q.height) (F : Records q n→Records q n)
    (source buffer : ℕ) : List (Instruction q) :=
  CommonStaticFusion.fuse q (rawCode q reader n hn F source buffer)

def charge (q : Configuration) (n : ℕ) := 8*recordBlocks q n+1

theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (n : ℕ) (hn : n≤512*q.height) (F : Records q n→Records q n)
    (source buffer limit : ℕ)
    (hs : source+recordBlocks q n≤buffer)
    (hb : buffer+recordBlocks q n≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f) :
    Encoded q (executeRaw q (code q reader n hn F source buffer) s).1.disk source (F f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) →
      (executeRaw q (code q reader n hn F source buffer) s).1.disk a=s.disk a) := by
  have hsource : source+recordBlocks q n≤q.N^q.exponent := by omega
  have hbuffer : buffer+recordBlocks q n≤q.N^q.exponent := by omega
  obtain ⟨final,out,hr,hwords,houtside⟩ := CommonStaticRecordLeaf.raw_complete q n hn F
    source buffer (unpack s.ram) s.disk (by rw [blocks_eq]; exact hsource)
    (by rw [blocks_eq]; exact hbuffer) f ((encoded_word q s.disk source f hsource).1 hf)
  rw [CommonBlockPair.machine_eta q s] at hr
  have henc : Encoded q out buffer (F f) := (encoded_word q out buffer (F f) hbuffer).2 hwords
  let mid := (executeRaw q (CommonStaticRecordLeaf.code q n hn F source buffer) s).1
  have hmid : mid.disk=out := by simp only [mid,hr,CommonLeafProgram.machine]
  obtain ⟨hcopy,hframe⟩ := CommonRecursiveExchange.copyCode_raw q reader (n*(3*q.w))
    buffer source mid hbuffer hsource (Or.inr hs)
  rw [code,CommonStaticFusion.executeRaw_fuse,rawCode,raw_append]
  constructor
  · intro i
    change readBit q (executeRaw q (CommonRecursiveExchange.copyCode q reader
      (n*(3*q.w)) buffer source) mid).1.disk source i.val=_
    rw [hcopy i,hmid]
    exact henc i
  · intro a has hab
    change (executeRaw q (CommonRecursiveExchange.copyCode q reader
      (n*(3*q.w)) buffer source) mid).1.disk a=_
    rw [hframe a has,hmid]
    apply houtside a
    rw [blocks_eq]
    omega

theorem raw_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (n : ℕ) (hn : n≤512*q.height) (F : Records q n→Records q n)
    (source buffer limit : ℕ)
    (hs : source+recordBlocks q n≤buffer)
    (hb : buffer+recordBlocks q n≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (has : a.val<source ∨ source+recordBlocks q n≤a.val)
    (hab : a.val<buffer ∨ limit≤a.val) :
    (executeRaw q (code q reader n hn F source buffer) s).1.disk a=s.disk a := by
  have hsource : source+recordBlocks q n≤q.N^q.exponent := by omega
  have hbuffer : buffer+recordBlocks q n≤q.N^q.exponent := by omega
  let loaded := (executeRaw q (CommonStaticLeaf.readCode q source (3*n)
    (CommonStaticRecordLeaf.blocks q n)) s).1
  obtain ⟨r,hr,_,_,_⟩ := CommonStaticLeaf.read_prefix q source (3*n)
    (CommonStaticRecordLeaf.blocks q n) (unpack s.ram) s.disk (by rw [blocks_eq]; exact hsource) le_rfl
  rw [CommonBlockPair.machine_eta q s] at hr
  obtain ⟨t,hw,_,_⟩ := CommonStaticLeaf.write_prefix q buffer (3*n)
    (CommonStaticRecordLeaf.blocks q n)
    {r with leaf:=CommonStaticRecordLeaf.cpu q n hn F r.leaf} s.disk
    (by rw [blocks_eq]; exact hbuffer)
  have hleaf : (executeRaw q (CommonStaticRecordLeaf.code q n hn F source buffer) s).1.disk a=s.disk a := by
    rw [CommonStaticRecordLeaf.code,raw_append,raw_append,hr]
    dsimp only
    simp only [executeRaw,CommonStaticRecordLeaf.compute_step]
    rw [hw]
    apply CommonLeafDisk.prefix_outside buffer _ _ s.disk a
    rw [blocks_eq]
    omega
  obtain ⟨_,hcopy⟩ := CommonRecursiveExchange.copyCode_raw q reader (n*(3*q.w)) buffer source
    (executeRaw q (CommonStaticRecordLeaf.code q n hn F source buffer) s).1
    hbuffer hsource (Or.inr hs)
  rw [code,CommonStaticFusion.executeRaw_fuse,rawCode,raw_append,hcopy a has,hleaf]

theorem raw_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (n : ℕ) (hn : n≤512*q.height) (F : Records q n→Records q n) (source buffer : ℕ) :
    ∀ i∈rawCode q reader n hn F source buffer,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact CommonStaticRecordLeaf.code_safe q n hn F source buffer i hi
  · exact CommonRecursiveExchange.copyCode_safe q reader _ buffer source i hi

theorem raw_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (n : ℕ) (hn : n≤512*q.height) (F : Records q n→Records q n) (source buffer limit : ℕ)
    (hs : source+recordBlocks q n≤buffer)
    (hb : buffer+recordBlocks q n≤limit) (hl : limit≤q.N^q.exponent) :
    cost q (rawCode q reader n hn F source buffer)≤8*recordBlocks q n := by
  rw [rawCode,cost_append,CommonStaticRecordLeaf.code_cost q n hn F source buffer
    (by rw [blocks_eq]; omega) (by rw [blocks_eq]; omega),blocks_eq]
  have h := CommonRecursiveExchange.copyCode_cost q reader (n*(3*q.w)) buffer source
  change cost q (CommonRecursiveExchange.copyCode q reader (n*(3*q.w)) buffer source)≤6*recordBlocks q n at h
  omega

/-- A completely implemented resident group. Its only assumptions are
numeric capacity and separated file regions; there is no child-success
or input-dependent computation supplied to the program. -/
def program (q : Configuration) (reader : Fin q.inventory.readers)
    (n : ℕ) (hn : n≤512*q.height) (F : Records q n→Records q n) (source buffer limit : ℕ)
    (hs : source+recordBlocks q n≤buffer)
    (hb : buffer+recordBlocks q n≤limit) (hl : limit≤q.N^q.exponent) :
    Program q n source buffer limit F where
  instructions := code q reader n hn F source buffer
  charge := charge q n
  correct := fun s f hf => (raw_correct q reader n hn F source buffer limit hs hb hl s f hf).1
  frame := raw_frame q reader n hn F source buffer limit hs hb hl
  safe := CommonStaticFusion.fuse_safe q _ (raw_safe q reader n hn F source buffer)
  cost_le := by
    rw [code,CommonStaticFusion.cost_fuse]
    exact (raw_cost q reader n hn F source buffer limit hs hb hl).trans (by dsimp [charge]; omega)
  length_le := (CommonStaticFusion.length_fuse q _).trans
    (Nat.add_le_add_right (raw_cost q reader n hn F source buffer limit hs hb hl) 1)

@[simp] theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (n : ℕ) (hn : n≤512*q.height) (F : Records q n→Records q n) (source buffer limit : ℕ)
    (hs : source+recordBlocks q n≤buffer)
    (hb : buffer+recordBlocks q n≤limit) (hl : limit≤q.N^q.exponent) :
    (program q reader n hn F source buffer limit hs hb hl).charge=8*recordBlocks q n+1 := rfl

end
end CodedSorting.CommonResidentRecordProgram
