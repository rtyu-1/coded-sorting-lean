import CodedSorting.Shared.Programs.Static.Leaf
import CodedSorting.Shared.Records.RecordOperations

/-! Public static read--CPU--write programs for bounded resident record
arrays. The CPU decodes only the already loaded bank and writes the fixed
three-word record codec. The operation can sort several columns together,
so a later aligned grouping wrapper need not flush at column boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonStaticRecordLeaf
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store Disk Machine machine)
open CommonLeafLoad (diskWord)
open KeyRecordWords
noncomputable section

abbrev Records (q : Configuration) (n : ℕ) := Fin n → Record q.w
abbrev Bank (q : Configuration) := CommonLeafTransform.Bank q

def readRecords (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (bank : Bank q) : Records q n := fun i =>
  ResidentLeafSort.recordAt bank (i.castLE hn)

def cpu (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (bank : Bank q) : Bank q :=
  Fin.append (ResidentLeafSort.header bank) (fun j =>
    let p := finProdFinEquiv.symm j
    if h : p.1.val<n then
      encode q.w (by have:=q.word_width; omega) (F (readRecords q n hn bank) ⟨p.1.val,h⟩) p.2
    else ResidentLeafBank.raw bank j)

@[simp] theorem cpu_raw (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (bank : Bank q) (i : Fin n) (j : Fin 3) :
    ResidentLeafBank.raw (cpu q n hn F bank) (finProdFinEquiv (i.castLE hn,j))=
      encode q.w (by have:=q.word_width; omega) (F (readRecords q n hn bank) i) j := by
  simp only [ResidentLeafBank.raw,cpu,Fin.append_right,Equiv.symm_apply_apply,
    Fin.coe_castLE,i.isLt,↓reduceDIte,Fin.eta]

@[simp] theorem cpu_header (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (bank : Bank q) :
    ResidentLeafSort.header (cpu q n hn F bank)=ResidentLeafSort.header bank := by
  funext i
  simp only [ResidentLeafSort.header,cpu,Fin.append_left]

def compute (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) : Instruction q :=
  ⟨.localOp (fun ram => let s := unpack ram; pack {s with leaf:=cpu q n hn F s.leaf}),id⟩

def blocks (q : Configuration) (n : ℕ) := PhysicalStreamCursor.blockCount q.block (3*n)

def code (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (source target : ℕ) : List (Instruction q) :=
  CommonStaticLeaf.readCode q source (3*n) (blocks q n) ++ [compute q n hn F] ++
    CommonStaticLeaf.writeCode q target (3*n) (blocks q n)

theorem compute_step (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (compute q n hn F) (machine q s disk)=
      machine q {s with leaf:=cpu q n hn F s.leaf} disk := by
  simp only [compute,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,unpack_pack,id_eq]

def WordEncoded (q : Configuration) (n : ℕ) (disk : Disk q) (base : ℕ)
    (f : Records q n) : Prop :=
  ∀ (i : Fin n) (j : Fin 3), diskWord q disk base (i.val*3+j.val)=
    encode q.w (by have:=q.word_width; omega) (f i) j

theorem raw_complete (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (source target : ℕ) (s : Store q) (disk : Disk q)
    (hsource : source+blocks q n≤q.N^q.exponent)
    (htarget : target+blocks q n≤q.N^q.exponent)
    (f : Records q n) (hf : WordEncoded q n disk source f) :
    ∃ (final : Store q) (out : Disk q),
      executeRaw q (code q n hn F source target) (machine q s disk)=
        (machine q final out,2*blocks q n) ∧
      WordEncoded q n out target (F f) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+blocks q n≤a.val → out a=disk a) := by
  obtain ⟨loaded,hr,hread,_,_⟩ := CommonStaticLeaf.read_prefix q source (3*n) (blocks q n)
    s disk hsource le_rfl
  have hcover : 3*n≤blocks q n*q.block :=
    LayoutConversion.blockCount_covers (3*n) q.block (CommonLeafProgram.block_positive q)
  have hall : ∀ i : Fin (CommonExchangeLeaf.bankWords q),i.val<3*n →
      ResidentLeafBank.raw loaded.leaf i=diskWord q disk source i.val := by
    intro i hi
    exact hread i (by simpa only [Nat.min_eq_left hcover] using hi)
  have hdecoded : readRecords q n hn loaded.leaf=f := by
    funext i
    apply ResidentLeafBank.recordAt_eq_of_words (by have:=q.word_width; omega)
    intro j
    have hv : (finProdFinEquiv (i.castLE hn,j)).val=i.val*3+j.val := by
      simpa only [Fin.coe_castLE] using BitWordPacking.bit_address (512*q.height) 3 (i.castLE hn) j
    have hi : (finProdFinEquiv (i.castLE hn,j)).val<3*n := by rw [hv]; have:=i.isLt; have:=j.isLt; omega
    exact (hall _ hi).trans (by simpa only [hv] using hf i j)
  let changed : Store q := {loaded with leaf:=cpu q n hn F loaded.leaf}
  obtain ⟨final,hw,hbank,_⟩ := CommonStaticLeaf.write_prefix q target (3*n) (blocks q n) changed disk htarget
  let out := CommonLeafDisk.writePrefix target
    (fun j => CommonStaticLeaf.outputBlock q (3*n) j changed.leaf) (blocks q n) disk
  refine ⟨final,out,?_,?_,?_⟩
  · rw [code,CommonStaticLeaf.raw_append,CommonStaticLeaf.raw_append,hr]
    dsimp only
    simp only [executeRaw,compute_step]
    simp only [compute,Normalization.transferCost,Nat.add_zero]
    change ((executeRaw q (CommonStaticLeaf.writeCode q target (3*n) (blocks q n))
      (machine q changed disk)).1,blocks q n+(executeRaw q
      (CommonStaticLeaf.writeCode q target (3*n) (blocks q n)) (machine q changed disk)).2)=_
    rw [hw]
    change (machine q final out,blocks q n+blocks q n)=_
    congr 1
    omega
  · intro i j
    have hv : (finProdFinEquiv (i.castLE hn,j)).val=i.val*3+j.val := by
      simpa only [Fin.coe_castLE] using BitWordPacking.bit_address (512*q.height) 3 (i.castLE hn) j
    have hi : (finProdFinEquiv (i.castLE hn,j)).val<3*n := by rw [hv]; have:=i.isLt; have:=j.isLt; omega
    have hwrite := CommonStaticLeaf.written_word q changed.leaf disk target (3*n) htarget
      (finProdFinEquiv (i.castLE hn,j)) hi
    change diskWord q out target (finProdFinEquiv (i.castLE hn,j)).val=
      ResidentLeafBank.raw changed.leaf (finProdFinEquiv (i.castLE hn,j)) at hwrite
    change diskWord q out target (i.val*3+j.val)=_
    rw [←hv,hwrite]
    change ResidentLeafBank.raw (cpu q n hn F loaded.leaf) _=_
    rw [cpu_raw,hdecoded]
  · intro a ha
    exact CommonLeafDisk.prefix_outside target _ (blocks q n) disk a ha

theorem code_length (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (source target : ℕ) :
    (code q n hn F source target).length=3*blocks q n+1 := by
  simp only [code,List.length_append,CommonStaticLeaf.readCode_length,
    CommonStaticLeaf.writeCode_length,List.length_singleton]
  omega

theorem code_cost (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (source target : ℕ)
    (hs : source+blocks q n≤q.N^q.exponent) (ht : target+blocks q n≤q.N^q.exponent) :
    cost q (code q n hn F source target)=2*blocks q n := by
  rw [code,CommonStaticLeaf.cost_append,CommonStaticLeaf.cost_append,
    CommonStaticLeaf.readCode_cost q source _ _ hs,CommonStaticLeaf.writeCode_cost q target _ _ ht]
  simp only [cost,compute,Normalization.transferCost,Nat.add_zero]
  omega

theorem compute_safe (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) : RespectsPC q (compute q n hn F) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [compute_step,CommonBlockPair.erasePC_machine]

theorem code_safe (q : Configuration) (n : ℕ) (hn : n≤512*q.height)
    (F : Records q n → Records q n) (source target : ℕ) :
    ∀ i∈code q n hn F source target,RespectsPC q i := by
  intro i hi
  simp only [code,List.mem_append,List.mem_singleton] at hi
  rcases hi with (hi|hi)|hi
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    exact CommonStaticLeaf.readAt_safe q source _ j
  · subst i; exact compute_safe q n hn F
  · obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj|hj
    · subst i; exact CommonStaticLeaf.stage_safe q _ j
    · subst i; exact CommonStaticLeaf.writeAt_safe q target j

/-- Every column is sorted independently, although its group is loaded
and written as one resident array. The index is column-major. -/
def sortColumns (q : Configuration) (c r : ℕ) (f : Records q (c*r)) : Records q (c*r) :=
  fun k => let p := finProdFinEquiv.symm k;
    Columnsort.sortColumn (fun j => f (finProdFinEquiv (p.1,j))) p.2

@[simp] theorem sortColumns_at (q : Configuration) (c r : ℕ)
    (f : Records q (c*r)) (i : Fin c) (j : Fin r) :
    sortColumns q c r f (finProdFinEquiv (i,j))=
      Columnsort.sortColumn (fun k => f (finProdFinEquiv (i,k))) j := by
  simp only [sortColumns,Equiv.symm_apply_apply]

end
end CodedSorting.CommonStaticRecordLeaf
