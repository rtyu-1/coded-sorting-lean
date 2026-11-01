import CodedSorting.Sorting.Radix.Framework.CountSemantics
import CodedSorting.Shared.Memory.TaggedController
import CodedSorting.Sorting.Local.Framework.Program

section Directory
/-! Persisted bucket lengths and prefix offsets, generated from actual
input reads.  The directory occupies a designated interval of the same
finite disk.  Its two d-word fields are (start,length), in bucket order;
formatting sees only resident counters and stores no payload snapshot. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDDirectory
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonMSDDirectoryScan (counter counterWords putCounters counts)
noncomputable section
variable {K : ℕ}

def start (values : Fin K → ℕ) (k : Fin K) : ℕ :=
  ∑ j : Fin K, if j<k then values j else 0

def value (values : Fin K → ℕ) (i : Fin (K*2)) : ℕ :=
  let p := finProdFinEquiv.symm i
  if p.2.val=0 then start values p.1 else values p.1

@[simp] theorem value_at (values : Fin K → ℕ) (k : Fin K) (field : Fin 2) :
    value values (finProdFinEquiv (k,field))=
      if field.val=0 then start values k else values k := by
  simp only [value,Equiv.symm_apply_apply]

theorem start_le (values : Fin K → ℕ) (k : Fin K) :
    start values k≤∑ j : Fin K, values j := by
  apply Finset.sum_le_sum
  intro j _
  split <;> omega

def smallFit (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) :
    K*q.digits≤CommonExchangeLeaf.bankWords q := by nlinarith

def formatStore (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (s : Store q) : Store q :=
  putCounters q (value (fun k => counter q (smallFit q hfit) s k)) s

def formatInstruction (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) : Instruction q :=
  ⟨.localOp (fun ram => pack (formatStore q hfit (unpack ram))),id⟩

def blocks (q : Configuration) (K : ℕ) : ℕ :=
  PhysicalStreamCursor.blockCount q.block ((K*2)*q.digits)

def code (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ) : List (Instruction q) :=
  CommonMSDDirectoryScan.code q (smallFit q hfit) key source n ++
    [formatInstruction q hfit] ++
    CommonStaticLeaf.writeCode q target ((K*2)*q.digits) (blocks q K)

def entryWords (q : Configuration) (disk : Disk q) (target : ℕ)
    (k : Fin K) (field : Fin 2) : Words q.digits q.w := fun j =>
  CommonLeafLoad.diskWord q disk target ((k.val*2+field.val)*q.digits+j.val)

def entry (q : Configuration) (disk : Disk q) (target : ℕ)
    (k : Fin K) (field : Fin 2) : ℕ := decodeWords (entryWords q disk target k field)

theorem format_step (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (formatInstruction q hfit) (machine q s disk)=
      machine q (formatStore q hfit s) disk := by
  simp only [formatInstruction,ControlledNormalization.logicalStep,
    Normalization.logicalStep,machine,unpack_pack,id_eq]

theorem format_words (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (s : Store q) (k : Fin K) (field : Fin 2) :
    counterWords q hfit (formatStore q hfit s) (finProdFinEquiv (k,field))=
      PhysicalStreamCursor.encodeNat q.digits q.w
        (if field.val=0 then start (counter q (smallFit q hfit) s) k
        else counter q (smallFit q hfit) s k) := by
  rw [formatStore,CommonMSDDirectoryScan.counterWords_put,value_at]

theorem raw_complete (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ) (s : Store q) (disk : Disk q)
    (hs : source+CommonRecordProgram.recordBlocks q n≤q.N^q.exponent)
    (ht : target+blocks q K≤q.N^q.exponent)
    (hc : CommonRecordProgram.recordBlocks q n*q.block<(2^q.w)^q.digits) :
    ∃ (final : Store q) (out : Disk q),
      executeRaw q (code q hfit key source n target) (machine q s disk)=
        (machine q final out,CommonRecordProgram.recordBlocks q n+blocks q K) ∧
      (∀ k : Fin K, entry q out target k 0=
        start (counts q key source n (CommonRecordProgram.recordBlocks q n) disk) k) ∧
      (∀ k : Fin K, entry q out target k 1=
        counts q key source n (CommonRecordProgram.recordBlocks q n) disk k) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+blocks q K≤a.val → out a=disk a) := by
  obtain ⟨loaded,hr,hcount⟩ := CommonMSDDirectoryScan.raw_complete q (smallFit q hfit)
    key source n s disk hs hc
  let changed := formatStore q hfit loaded
  obtain ⟨final,hw,hbank,hframe⟩ := CommonStaticLeaf.write_prefix q target
    ((K*2)*q.digits) (blocks q K) changed disk ht
  let out := CommonLeafDisk.writePrefix target
    (fun j => CommonStaticLeaf.outputBlock q ((K*2)*q.digits) j changed.leaf) (blocks q K) disk
  have hwords (k : Fin K) (field : Fin 2) : entryWords q out target k field=
      PhysicalStreamCursor.encodeNat q.digits q.w
        (if field.val=0 then start (counts q key source n (CommonRecordProgram.recordBlocks q n) disk) k
        else counts q key source n (CommonRecordProgram.recordBlocks q n) disk k) := by
    have he : counter q (smallFit q hfit) loaded=
        counts q key source n (CommonRecordProgram.recordBlocks q n) disk := funext hcount
    rw [←he,←format_words q hfit loaded k field]
    funext j
    let i := finProdFinEquiv (finProdFinEquiv (k,field),j)
    have hi : i.val<(K*2)*q.digits := i.isLt
    have hv : i.val=(k.val*2+field.val)*q.digits+j.val := by
      simp only [i,finProdFinEquiv_apply_val]
      ring
    have hw := CommonStaticLeaf.written_word q changed.leaf disk target ((K*2)*q.digits)
      ht (i.castLE hfit) hi
    simpa only [entryWords,CommonMSDDirectoryScan.counterWords,Fin.coe_castLE,hv]
      using hw
  have hbound (k : Fin K) :
      counts q key source n (CommonRecordProgram.recordBlocks q n) disk k < (2^q.w)^q.digits :=
    (CommonMSDDirectoryScan.counts_le q key source n _ disk k).trans_lt hc
  have hstart (k : Fin K) :
      start (counts q key source n (CommonRecordProgram.recordBlocks q n) disk) k <
        (2^q.w)^q.digits :=
    ((start_le _ k).trans (CommonMSDDirectoryScan.sum_counts_le q key source n _ disk)).trans_lt hc
  refine ⟨final,out,?_,?_,?_,?_⟩
  · rw [code,CommonStaticLeaf.raw_append,CommonStaticLeaf.raw_append,hr]
    dsimp only
    simp only [executeRaw]
    rw [format_step]
    simp only [formatInstruction,Normalization.transferCost,Nat.add_zero]
    change ((executeRaw q (CommonStaticLeaf.writeCode q target ((K*2)*q.digits) (blocks q K))
      (machine q changed disk)).1,CommonRecordProgram.recordBlocks q n+
      (executeRaw q (CommonStaticLeaf.writeCode q target ((K*2)*q.digits) (blocks q K))
      (machine q changed disk)).2)=_
    rw [hw]
  · intro k
    unfold entry
    rw [hwords]
    simp only [Fin.val_zero,↓reduceIte]
    exact PhysicalStreamCursor.decodeNat_encode _ _ _ (hstart k)
  · intro k
    unfold entry
    rw [hwords]
    simp only [Fin.val_one,one_ne_zero,↓reduceIte]
    exact PhysicalStreamCursor.decodeNat_encode _ _ _ (hbound k)
  · intro a ha
    exact CommonLeafDisk.prefix_outside target _ (blocks q K) disk a ha


theorem format_safe (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) :
    RespectsPC q (formatInstruction q hfit) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [format_step,CommonBlockPair.erasePC_machine]
  rfl

theorem code_safe (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ) :
    ∀ i ∈ code q hfit key source n target, RespectsPC q i := by
  intro i hi
  simp only [code,List.mem_append,List.mem_singleton] at hi
  rcases hi with (hi | rfl) | hi
  · exact CommonMSDDirectoryScan.code_safe q (smallFit q hfit) key source n i hi
  · exact format_safe q hfit
  · obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl
    · exact CommonStaticLeaf.stage_safe q _ j
    · exact CommonStaticLeaf.writeAt_safe q target j

theorem code_length (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ) :
    (code q hfit key source n target).length=
      CommonRecordProgram.recordBlocks q n+2*blocks q K+2 := by
  simp only [code,List.length_append,CommonMSDDirectoryScan.code_length,
    List.length_singleton,CommonStaticLeaf.writeCode_length]
  omega

theorem code_cost (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ)
    (hs : source+CommonRecordProgram.recordBlocks q n≤q.N^q.exponent)
    (ht : target+blocks q K≤q.N^q.exponent) :
    cost q (code q hfit key source n target)=
      CommonRecordProgram.recordBlocks q n+blocks q K := by
  rw [code,CommonStaticLeaf.cost_append,CommonStaticLeaf.cost_append,
    CommonMSDDirectoryScan.code_cost q (smallFit q hfit) key source n hs,
    CommonStaticLeaf.writeCode_cost q target _ _ ht]
  simp only [cost,formatInstruction,Normalization.transferCost,Nat.add_zero]

/-- The fixed RAM-controlled program halts with the actual directory on
its actual finite disk.  Input reading, directory writing, decoded values,
and the counted memory bound all concern this one run. -/
theorem complete (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ) (s : Store q) (disk : Disk q)
    (hs : source+CommonRecordProgram.recordBlocks q n≤q.N^q.exponent)
    (ht : target+blocks q K≤q.N^q.exponent)
    (hc : CommonRecordProgram.recordBlocks q n*q.block<(2^q.w)^q.digits)
    (hsize : (code q hfit key source n target).length≤q.N^q.exponent)
    (hpc : pc q (pack s)=0) :
    let program := code q hfit key source n target
    let result := ControlledNormalization.runLogical (CommonStaticSchedule.policy q program)
      program.length (machine q s disk)
    CommonStaticSchedule.policy q program result.1.ram=none ∧
    result.2=CommonRecordProgram.recordBlocks q n+blocks q K ∧
    (∀ k : Fin K, entry q result.1.disk target k 0=
      start (counts q key source n (CommonRecordProgram.recordBlocks q n) disk) k) ∧
    (∀ k : Fin K, entry q result.1.disk target k 1=
      counts q key source n (CommonRecordProgram.recordBlocks q n) disk k) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+blocks q K≤a.val →
      result.1.disk a=disk a) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  dsimp only
  obtain ⟨final,out,hr,hstart,hcount,hframe⟩ := raw_complete q hfit key source n target s disk hs ht hc
  obtain ⟨hd,hh,hcost,hm⟩ := CommonStaticSchedule.run_code_disk q
    (code q hfit key source n target) hsize (code_safe q hfit key source n target)
    (machine q s disk) hpc
  rw [hr] at hd
  dsimp only at hd
  refine ⟨hh,?_,?_,?_,?_,hm⟩
  · rw [hcost,code_cost q hfit key source n target hs ht]
  · simpa only [hd] using hstart
  · simpa only [hd] using hcount
  · simpa only [hd] using hframe

end
end CodedSorting.CommonMSDDirectory
end Directory

section DirectoryRead
/-! Read one persisted two-field directory entry into the existing leaf
bank. The read covers exactly the physical pages meeting its 2d words;
subsequent control can use only the decoded resident fields. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDDirectoryRead
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
noncomputable section

def offset (q : Configuration) (e : ℕ) : ℕ := e*(2*q.digits)
def lead (q : Configuration) (e : ℕ) : ℕ := offset q e % q.block
def total (q : Configuration) (e : ℕ) : ℕ := lead q e+2*q.digits
def base (q : Configuration) (target e : ℕ) : ℕ := target+offset q e/q.block
def blocks (q : Configuration) (e : ℕ) : ℕ := PhysicalStreamCursor.blockCount q.block (total q e)

def code (q : Configuration) (target e : ℕ) : List (Instruction q) :=
  CommonStaticLeaf.readCode q (base q target e) (total q e) (blocks q e)

def fieldWords (q : Configuration) (e : ℕ) (field : Fin 2) (s : Store q) : Words q.digits q.w :=
  fun j => ResidentLeafBank.getWord s.leaf (lead q e+field.val*q.digits+j.val)

def field (q : Configuration) (e : ℕ) (which : Fin 2) (s : Store q) : ℕ :=
  decodeWords (fieldWords q e which s)

def storedWords (q : Configuration) (disk : Disk q) (target e : ℕ) (field : Fin 2) :
    Words q.digits q.w := fun j =>
  CommonLeafLoad.diskWord q disk target (offset q e+field.val*q.digits+j.val)

def stored (q : Configuration) (disk : Disk q) (target e : ℕ) (which : Fin 2) : ℕ :=
  decodeWords (storedWords q disk target e which)

theorem diskWord_shift (q : Configuration) (disk : Disk q) (target chunks i : ℕ) :
    CommonLeafLoad.diskWord q disk (target+chunks) i=
      CommonLeafLoad.diskWord q disk target (chunks*q.block+i) := by
  have hd : (chunks*q.block+i)/q.block=chunks+i/q.block := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (CommonLeafProgram.block_positive q)]
    omega
  have hm : (chunks*q.block+i)%q.block=i%q.block := Nat.mul_add_mod_self_right _ _ _
  simp only [CommonLeafLoad.diskWord,hd,hm,Nat.add_assoc]

theorem stored_shift (q : Configuration) (disk : Disk q) (target e : ℕ)
    (which : Fin 2) (j : Fin q.digits) :
    CommonLeafLoad.diskWord q disk (base q target e)
      (lead q e+which.val*q.digits+j.val)=storedWords q disk target e which j := by
  rw [base,diskWord_shift]
  unfold storedWords lead
  congr 1
  have hh := Nat.div_add_mod (offset q e) q.block
  nlinarith

theorem raw_complete (q : Configuration) (target e : ℕ) (s : Store q) (disk : Disk q)
    (hs : base q target e+blocks q e≤q.N^q.exponent)
    (hw : total q e≤CommonExchangeLeaf.bankWords q) :
    ∃ final : Store q,
      executeRaw q (code q target e) (machine q s disk)=(machine q final disk,blocks q e) ∧
      (∀ which : Fin 2,fieldWords q e which final=storedWords q disk target e which) ∧
      (∀ which : Fin 2,field q e which final=stored q disk target e which) := by
  obtain ⟨final,hr,hwords,hframe,hheader⟩ := CommonStaticLeaf.read_prefix q (base q target e)
    (total q e) (blocks q e) s disk hs le_rfl
  have hcover : total q e≤blocks q e*q.block :=
    LayoutConversion.blockCount_covers _ _ (CommonLeafProgram.block_positive q)
  have hf : ∀ which : Fin 2,fieldWords q e which final=storedWords q disk target e which := by
    intro which
    funext j
    have hi : lead q e+which.val*q.digits+j.val<total q e := by
      have := which.isLt
      have := j.isLt
      unfold total
      nlinarith
    have hic : lead q e+which.val*q.digits+j.val<CommonExchangeLeaf.bankWords q := hi.trans_le hw
    unfold fieldWords
    change lead q e+which.val*q.digits+j.val<512*q.height*3 at hic
    rw [ResidentLeafBank.getWord, dif_pos hic]
    rw [hwords _ (by simpa only [Nat.min_eq_left hcover] using hi)]
    exact stored_shift q disk target e which j
  exact ⟨final,hr,hf,fun which => congrArg decodeWords (hf which)⟩

theorem stored_entry (q : Configuration) (disk : Disk q) (target : ℕ)
    {K : ℕ} (k : Fin K) (which : Fin 2) :
    stored q disk target k.val which=CommonMSDDirectory.entry q disk target k which := by
  unfold stored CommonMSDDirectory.entry
  congr 1
  funext j
  unfold storedWords CommonMSDDirectory.entryWords offset
  congr 1
  ring

theorem code_safe (q : Configuration) (target e : ℕ) :
    ∀ i ∈ code q target e, RespectsPC q i := by
  intro i hi
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  exact CommonStaticLeaf.readAt_safe q _ _ j

theorem code_length (q : Configuration) (target e : ℕ) :
    (code q target e).length=blocks q e := CommonStaticLeaf.readCode_length q _ _ _

theorem code_cost (q : Configuration) (target e : ℕ)
    (hs : base q target e+blocks q e≤q.N^q.exponent) :
    cost q (code q target e)=blocks q e := CommonStaticLeaf.readCode_cost q _ _ _ hs

/-- The compiled run exposes the two actual fields in RAM, so a following
branch may dispatch on their values without consulting a proof-side disk. -/
theorem complete (q : Configuration) (target e : ℕ) (s : Store q) (disk : Disk q)
    (hs : base q target e+blocks q e≤q.N^q.exponent)
    (hw : total q e≤CommonExchangeLeaf.bankWords q)
    (hsize : (code q target e).length≤q.N^q.exponent)
    (hpc : pc q (pack s)=0) :
    let program := code q target e
    let result := ControlledNormalization.runLogical (CommonStaticSchedule.policy q program)
      program.length (machine q s disk)
    CommonStaticSchedule.policy q program result.1.ram=none ∧
    result.2=blocks q e ∧
    result.1.disk=disk ∧
    (∀ which : Fin 2,field q e which (unpack result.1.ram)=stored q disk target e which) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  dsimp only
  obtain ⟨final,hraw,hwords,hfields⟩ := raw_complete q target e s disk hs hw
  obtain ⟨hrun,hh,hcost,hm⟩ := CommonStaticSchedule.run_code q (code q target e)
    hsize (machine q s disk) hpc
  have he := CommonStaticSchedule.execute_payload q (code q target e) (code_safe q target e)
    0 (machine q s disk) (machine q s disk) rfl
  rw [hraw] at he
  have hleaf := congrArg (fun t : Machine q => (unpack t.ram : Store q).leaf) he
  simp only [erasePC,setPC,unpack_pack,machine] at hleaf
  have hd := congrArg (fun t : Machine q => t.disk) he
  simp only [erasePC,machine] at hd
  refine ⟨?_,?_,?_,?_,hm⟩
  · rw [hrun]
    exact hh
  · rw [hcost,code_cost q target e hs]
  · rw [hrun]
    exact hd
  · intro which
    rw [hrun]
    exact (congrArg (fun bank => decodeWords (fun j : Fin q.digits =>
      ResidentLeafBank.getWord bank (lead q e+which.val*q.digits+j.val))) hleaf).trans (hfields which)

end
end CodedSorting.CommonMSDDirectoryRead
end DirectoryRead

section DirectoryBounds
/-! The per-entry read fits the common RAM automatically. Its covered
pages lie inside the already allocated complete directory. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDDirectoryBounds
open CommonSortingNormalization SortingResourceBudget CommonMSDDirectoryRead

theorem digits_le_height (q : Configuration) : q.digits≤q.height := by
  let C := reserve q.inventory q.c q.digits
  have hC : 0<C := reserve_pos q.inventory q.c q.digits
  have hd : q.digits≤C := by
    have hh := (reserve_bounds q.inventory q.c q.digits).2.2.1
    change 16*(4*q.digits+3)≤C at hh
    omega
  have hCH : C≤q.height := by
    change C≤q.M/C
    apply (Nat.le_div_iff_mul_le hC).2
    simpa only [C,pow_two] using q.memory_large
  exact hd.trans hCH

theorem read_window_fits (q : Configuration) (e : ℕ) :
    total q e≤CommonExchangeLeaf.bankWords q := by
  have hd := digits_le_height q
  have hb : q.block≤q.height :=
    (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory; omega)).2.1
  have hl : lead q e<q.block := Nat.mod_lt _ (CommonLeafProgram.block_positive q)
  unfold total CommonExchangeLeaf.bankWords
  omega

theorem covered_end (q : Configuration) (e : ℕ) :
    offset q e/q.block+blocks q e=
      PhysicalStreamCursor.blockCount q.block (offset q e+2*q.digits) := by
  have hb := CommonLeafProgram.block_positive q
  have hdiv := Nat.div_add_mod (offset q e) q.block
  have hdiv' : offset q e/q.block*q.block+offset q e%q.block=offset q e := by nlinarith [hdiv]
  have he : offset q e+2*q.digits+q.block-1=
      offset q e/q.block*q.block+(offset q e%q.block+2*q.digits+q.block-1) := by
    omega
  unfold blocks PhysicalStreamCursor.blockCount total lead
  rw [he,Nat.add_comm (offset q e/q.block*q.block),Nat.add_mul_div_right _ _ hb]
  omega

theorem read_inside_directory (q : Configuration) (target K : ℕ) (k : Fin K)
    (hfit : target+CommonMSDDirectory.blocks q K≤q.N^q.exponent) :
    base q target k.val+blocks q k.val≤q.N^q.exponent := by
  have he : offset q k.val+2*q.digits≤(K*2)*q.digits := by
    unfold offset
    have := Nat.mul_le_mul_right (2*q.digits) (show k.val+1≤K by omega)
    nlinarith
  have hc : PhysicalStreamCursor.blockCount q.block (offset q k.val+2*q.digits)≤
      CommonMSDDirectory.blocks q K := by
    apply Nat.div_le_div_right
    omega
  unfold base
  rw [Nat.add_assoc,covered_end]
  omega

end CodedSorting.CommonMSDDirectoryBounds
end DirectoryBounds

section DirectoryTagged
/-! The actual directory read remains valid inside the common tagged
controller; counter bookkeeping does not alter the loaded fields. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDDirectoryTagged
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store Machine machine)
open CommonMSDDirectoryRead
noncomputable section

theorem field_eq_of_erasePC (q : Configuration) (e : ℕ) (which : Fin 2)
    (s t : Machine q) (h : erasePC q s=erasePC q t) :
    field q e which (unpack s.ram)=field q e which (unpack t.ram) := by
  have hh := congrArg (fun m : Machine q => (unpack m.ram : Store q).leaf) h
  simp only [erasePC,setPC,unpack_pack] at hh
  exact congrArg (fun bank => WordControl.decodeWords (fun j : Fin q.digits =>
    ResidentLeafBank.getWord bank (lead q e+which.val*q.digits+j.val))) hh

theorem execute_complete (q : Configuration) (stride tag pcOffset target e : ℕ)
    (s : Machine q)
    (hs : base q target e+blocks q e≤q.N^q.exponent)
    (hw : total q e≤CommonExchangeLeaf.bankWords q) :
    let result := CommonTaggedSchedule.execute q stride tag pcOffset (code q target e) s
    result.1.disk=s.disk ∧ result.2=blocks q e ∧
    (∀ which : Fin 2,field q e which (unpack result.1.ram)=stored q s.disk target e which) := by
  obtain ⟨final,hraw,hwords,hfields⟩ := raw_complete q target e (unpack s.ram) s.disk hs hw
  rw [CommonBlockPair.machine_eta] at hraw
  have he := CommonTaggedSchedule.execute_payload q stride tag pcOffset (code q target e)
    (code_safe q target e) s s rfl
  rw [hraw] at he
  dsimp only at he ⊢
  refine ⟨?_,?_,?_⟩
  · simpa only [erasePC,machine] using congrArg (fun m : Machine q => m.disk) he
  · rw [CommonTaggedSchedule.execute_cost,code_cost q target e hs]
  · intro which
    exact (field_eq_of_erasePC q e which _ _ he).trans
      (by simpa only [machine,unpack_pack] using hfields which)

end
end CodedSorting.CommonMSDDirectoryTagged
end DirectoryTagged

section ChildCount
/-! Determine one child length from the actual parent directories. A
single public static macro reads that key's entry from each row directory
and adds its length into a d-word accumulator in shape slot zero. Input
records and directory contents are never captured in its code. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDChildCount
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
noncomputable section

def accWords (q : Configuration) (s : Store q) : Words q.digits q.w :=
  fun j => s.shapes 0 ⟨j.val,by have:=j.isLt;omega⟩

def acc (q : Configuration) (s : Store q) : ℕ := decodeWords (accWords q s)

def setAcc (q : Configuration) (value : ℕ) (s : Store q) : Store q :=
  {s with shapes:=Function.update s.shapes 0 (fun i =>
    if h : i.val<q.digits then PhysicalStreamCursor.encodeNat q.digits q.w value ⟨i.val,h⟩
    else s.shapes 0 i)}

@[simp] theorem accWords_set (q : Configuration) (value : ℕ) (s : Store q) :
    accWords q (setAcc q value s)=PhysicalStreamCursor.encodeNat q.digits q.w value := by
  funext j
  simp only [accWords,setAcc,Function.update_self,j.isLt,↓reduceDIte,Fin.eta]

@[simp] theorem acc_set (q : Configuration) (value : ℕ) (s : Store q)
    (hv : value<(2^q.w)^q.digits) : acc q (setAcc q value s)=value := by
  unfold acc
  rw [accWords_set]
  exact PhysicalStreamCursor.decodeNat_encode _ _ _ hv

def initInstruction (q : Configuration) : Instruction q :=
  ⟨.localOp (fun ram => pack (setAcc q 0 (unpack ram))),id⟩

def addStore (q : Configuration) (key : ℕ) (s : Store q) : Store q :=
  setAcc q (acc q s+CommonMSDDirectoryRead.field q key 1 s) s

def addInstruction (q : Configuration) (key : ℕ) : Instruction q :=
  ⟨.localOp (fun ram => pack (addStore q key (unpack ram))),id⟩

def fragment (q : Configuration) (directory key : ℕ) : List (Instruction q) :=
  CommonMSDDirectoryRead.code q directory key++[addInstruction q key]

def body (q : Configuration) (directories : List ℕ) (key : ℕ) : List (Instruction q) :=
  directories.flatMap (fun target => fragment q target key)

def code (q : Configuration) (directories : List ℕ) (key : ℕ) : List (Instruction q) :=
  initInstruction q :: body q directories key

def totalCount (q : Configuration) (disk : Disk q) (directories : List ℕ) (key : ℕ) : ℕ :=
  (directories.map (fun target => CommonMSDDirectoryRead.stored q disk target key 1)).sum

theorem read_raw (q : Configuration) (directory key : ℕ) (s : Store q) (disk : Disk q)
    (hs : CommonMSDDirectoryRead.base q directory key+CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent) :
    ∃ final : Store q,
      executeRaw q (CommonMSDDirectoryRead.code q directory key) (machine q s disk)=
        (machine q final disk,CommonMSDDirectoryRead.blocks q key) ∧
      acc q final=acc q s ∧
      CommonMSDDirectoryRead.field q key 1 final=CommonMSDDirectoryRead.stored q disk directory key 1 := by
  obtain ⟨final,hr,_,hfields⟩ := CommonMSDDirectoryRead.raw_complete q directory key s disk hs
    (CommonMSDDirectoryBounds.read_window_fits q key)
  obtain ⟨other,hr',_,hframe,_⟩ := CommonStaticLeaf.read_prefix q
    (CommonMSDDirectoryRead.base q directory key) (CommonMSDDirectoryRead.total q key)
    (CommonMSDDirectoryRead.blocks q key) s disk hs le_rfl
  change executeRaw q (CommonMSDDirectoryRead.code q directory key) (machine q s disk)=_ at hr'
  have he := congrArg (fun result : Machine q × ℕ => (unpack result.1.ram : Store q).shapes)
    (hr.symm.trans hr')
  simp only [machine,unpack_pack] at he
  have hf := congrArg (fun p => p.2.1) hframe
  change other.shapes=s.shapes at hf
  refine ⟨final,hr,?_,hfields 1⟩
  unfold acc accWords
  rw [he,hf]

theorem add_step (q : Configuration) (key : ℕ) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (addInstruction q key) (machine q s disk)=
      machine q (addStore q key s) disk := by
  simp only [addInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem init_step (q : Configuration) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (initInstruction q) (machine q s disk)=
      machine q (setAcc q 0 s) disk := by
  simp only [initInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem fragment_raw (q : Configuration) (directory key : ℕ) (s : Store q) (disk : Disk q)
    (hs : CommonMSDDirectoryRead.base q directory key+CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent)
    (hc : acc q s+CommonMSDDirectoryRead.stored q disk directory key 1<(2^q.w)^q.digits) :
    ∃ final : Store q,
      executeRaw q (fragment q directory key) (machine q s disk)=
        (machine q final disk,CommonMSDDirectoryRead.blocks q key) ∧
      acc q final=acc q s+CommonMSDDirectoryRead.stored q disk directory key 1 := by
  obtain ⟨loaded,hr,ha,hfield⟩ := read_raw q directory key s disk hs
  refine ⟨addStore q key loaded,?_,?_⟩
  · rw [fragment,CommonStaticLeaf.raw_append,hr]
    dsimp only
    simp only [executeRaw]
    rw [add_step]
    simp only [addInstruction,Normalization.transferCost,Nat.add_zero]
  · unfold addStore
    rw [acc_set q _ loaded (by rw [ha,hfield];exact hc),ha,hfield]

theorem body_raw (q : Configuration) (directories : List ℕ) (key : ℕ) (s : Store q) (disk : Disk q)
    (hs : ∀ target ∈ directories, CommonMSDDirectoryRead.base q target key+
      CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent)
    (hc : acc q s+totalCount q disk directories key<(2^q.w)^q.digits) :
    ∃ final : Store q,
      executeRaw q (body q directories key) (machine q s disk)=
        (machine q final disk,directories.length*CommonMSDDirectoryRead.blocks q key) ∧
      acc q final=acc q s+totalCount q disk directories key := by
  induction directories generalizing s with
  | nil => exact ⟨s,by simp [body,executeRaw],by simp [totalCount]⟩
  | cons target rest ih =>
    have hsum : totalCount q disk (target::rest) key=
        CommonMSDDirectoryRead.stored q disk target key 1+totalCount q disk rest key := rfl
    rw [hsum] at hc
    obtain ⟨mid,hr,ha⟩ := fragment_raw q target key s disk (hs target (by simp)) (by omega)
    obtain ⟨final,ht,hf⟩ := ih mid (fun target ht => hs target (by simp [ht])) (by rw [ha];omega)
    refine ⟨final,?_,?_⟩
    · change executeRaw q (fragment q target key++body q rest key) (machine q s disk)=_
      rw [CommonStaticLeaf.raw_append,hr]
      dsimp only
      rw [ht]
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm]
    · rw [hf,ha,hsum]
      omega

/-- One whole macro reads every relevant real directory entry and returns
its exact child length in counted RAM. The common disk is untouched. -/
theorem raw_complete (q : Configuration) (directories : List ℕ) (key : ℕ)
    (s : Store q) (disk : Disk q)
    (hs : ∀ target ∈ directories, CommonMSDDirectoryRead.base q target key+
      CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent)
    (hc : totalCount q disk directories key<(2^q.w)^q.digits) :
    ∃ final : Store q,
      executeRaw q (code q directories key) (machine q s disk)=
        (machine q final disk,directories.length*CommonMSDDirectoryRead.blocks q key) ∧
      acc q final=totalCount q disk directories key := by
  have hz : acc q (setAcc q 0 s)=0 := acc_set q 0 s (by positivity)
  obtain ⟨final,hr,ha⟩ := body_raw q directories key (setAcc q 0 s) disk hs (by simpa only [hz,Nat.zero_add] using hc)
  refine ⟨final,?_,by simpa only [hz,Nat.zero_add] using ha⟩
  rw [code,executeRaw,init_step]
  simpa only [initInstruction,Normalization.transferCost,Nat.zero_add,Prod.eta] using hr

theorem init_safe (q : Configuration) : RespectsPC q (initInstruction q) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [init_step,CommonBlockPair.erasePC_machine]
  rfl

theorem add_safe (q : Configuration) (key : ℕ) : RespectsPC q (addInstruction q key) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [add_step,CommonBlockPair.erasePC_machine]
  rfl

theorem fragment_safe (q : Configuration) (directory key : ℕ) :
    ∀ i ∈ fragment q directory key,RespectsPC q i := by
  intro i hi
  simp only [fragment,List.mem_append,List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact CommonMSDDirectoryRead.code_safe q directory key i hi
  · exact add_safe q key

theorem code_safe (q : Configuration) (directories : List ℕ) (key : ℕ) :
    ∀ i ∈ code q directories key,RespectsPC q i := by
  intro i hi
  simp only [code,List.mem_cons] at hi
  rcases hi with rfl | hi
  · exact init_safe q
  · obtain ⟨target,_,hi⟩ := List.mem_flatMap.mp hi
    exact fragment_safe q target key i hi

theorem fragment_cost (q : Configuration) (directory key : ℕ)
    (hs : CommonMSDDirectoryRead.base q directory key+CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent) :
    cost q (fragment q directory key)=CommonMSDDirectoryRead.blocks q key := by
  rw [fragment,CommonStaticLeaf.cost_append,CommonMSDDirectoryRead.code_cost q directory key hs]
  simp [cost,addInstruction,Normalization.transferCost]

theorem body_cost (q : Configuration) (directories : List ℕ) (key : ℕ)
    (hs : ∀ target ∈ directories,CommonMSDDirectoryRead.base q target key+
      CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent) :
    cost q (body q directories key)=directories.length*CommonMSDDirectoryRead.blocks q key := by
  induction directories with
  | nil => simp [body,cost]
  | cons target rest ih =>
    change cost q (fragment q target key++body q rest key)=_
    rw [CommonStaticLeaf.cost_append,fragment_cost q target key (hs target (by simp)),
      ih (fun target ht => hs target (by simp [ht]))]
    simp [Nat.add_mul,Nat.add_comm]

theorem code_cost (q : Configuration) (directories : List ℕ) (key : ℕ)
    (hs : ∀ target ∈ directories,CommonMSDDirectoryRead.base q target key+
      CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent) :
    cost q (code q directories key)=directories.length*CommonMSDDirectoryRead.blocks q key := by
  simpa only [code,cost,initInstruction,Normalization.transferCost,Nat.zero_add] using
    body_cost q directories key hs

theorem fragment_length (q : Configuration) (directory key : ℕ) :
    (fragment q directory key).length=CommonMSDDirectoryRead.blocks q key+1 := by
  simp only [fragment,List.length_append,CommonMSDDirectoryRead.code_length,List.length_singleton]

theorem body_length (q : Configuration) (directories : List ℕ) (key : ℕ) :
    (body q directories key).length=directories.length*(CommonMSDDirectoryRead.blocks q key+1) := by
  induction directories with
  | nil => simp [body,cost]
  | cons target rest ih =>
    change (fragment q target key++body q rest key).length=_
    rw [List.length_append,fragment_length,ih]
    simp [Nat.add_mul,Nat.add_comm]

theorem code_length (q : Configuration) (directories : List ℕ) (key : ℕ) :
    (code q directories key).length=directories.length*(CommonMSDDirectoryRead.blocks q key+1)+1 := by
  simp only [code,List.length_cons,body_length]

theorem acc_eq_of_erasePC (q : Configuration) (s t : Machine q)
    (h : erasePC q s=erasePC q t) : acc q (unpack s.ram)=acc q (unpack t.ram) := by
  have hh := congrArg (fun m : Machine q => (unpack m.ram : Store q).shapes) h
  simp only [erasePC,setPC,unpack_pack] at hh
  unfold acc accWords
  rw [hh]

/-- The child length is available to the actual controller as a RAM value
at the end of its single tagged body. -/
theorem tagged_complete (q : Configuration) (stride tag pcOffset : ℕ)
    (directories : List ℕ) (key : ℕ) (s : Machine q)
    (hs : ∀ target ∈ directories,CommonMSDDirectoryRead.base q target key+
      CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent)
    (hc : totalCount q s.disk directories key<(2^q.w)^q.digits) :
    let result := CommonTaggedSchedule.execute q stride tag pcOffset (code q directories key) s
    result.1.disk=s.disk ∧
      result.2=directories.length*CommonMSDDirectoryRead.blocks q key ∧
      acc q (unpack result.1.ram)=totalCount q s.disk directories key := by
  obtain ⟨final,hraw,ha⟩ := raw_complete q directories key (unpack s.ram) s.disk hs hc
  rw [CommonBlockPair.machine_eta] at hraw
  have he := CommonTaggedSchedule.execute_payload q stride tag pcOffset (code q directories key)
    (code_safe q directories key) s s rfl
  rw [hraw] at he
  dsimp only at he ⊢
  refine ⟨?_,?_,?_⟩
  · simpa only [erasePC,machine] using congrArg (fun t : Machine q => t.disk) he
  · rw [CommonTaggedSchedule.execute_cost,code_cost q directories key hs]
  · exact (acc_eq_of_erasePC q _ _ he).trans (by simpa only [machine,unpack_pack] using ha)

end
end CodedSorting.CommonMSDChildCount
end ChildCount

section Parameters
/-! A radix chosen from the available resident words. The fixed descriptor
width is counted, and the existing large-memory normalization supplies all
directory-counter and per-entry read windows. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDParameters
open CommonSortingNormalization SortingResourceBudget

def radix (q : Configuration) : ℕ := q.height/(2*q.digits)

theorem digits_positive (q : Configuration) : 0<q.digits := by
  have hc := (WordConvention.positive_words q.N q.w q.c q.input_large q.word_convention).2
  unfold Configuration.digits digits
  positivity

theorem height_reserve (q : Configuration) :
    reserve q.inventory q.c q.digits≤q.height := by
  apply (Nat.le_div_iff_mul_le (reserve_pos q.inventory q.c q.digits)).2
  simpa only [pow_two] using q.memory_large

theorem radix_two (q : Configuration) : 2≤radix q := by
  have h := (reserve_bounds q.inventory q.c q.digits).2.2.1
  have hh := height_reserve q
  apply (Nat.le_div_iff_mul_le (by have:=digits_positive q; omega)).2
  omega

theorem radix_fields (q : Configuration) : (radix q*2)*q.digits≤q.height := by
  have h := Nat.div_mul_le_self q.height (2*q.digits)
  simpa only [radix,Nat.mul_assoc] using h

theorem directory_fits (q : Configuration) :
    (radix q*2)*q.digits≤CommonExchangeLeaf.bankWords q := by
  have h := radix_fields q
  unfold CommonExchangeLeaf.bankWords
  omega

theorem radix_le_height (q : Configuration) : radix q≤q.height :=
  Nat.div_le_self _ _

theorem radix_block (q : Configuration) : radix q*q.block≤q.height^2 := by
  have hb : q.block≤q.height :=
    (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory; omega)).2.1
  simpa only [pow_two] using Nat.mul_le_mul (radix_le_height q) hb

/-- The scan's rounded word count fits the already reserved descriptor
width for every subproblem of the original input. -/
theorem count_capacity (q : Configuration) (n : ℕ) (hn : n≤q.N)
    (he : 2≤q.exponent) :
    CommonRecordProgram.recordBlocks q n*q.block<(2^q.w)^q.digits := by
  have hc := CommonLocalDescriptorBounds.capacity_of_input q q.N le_rfl he
  have hbn : q.block≤q.N := by
    have hb : q.block≤q.height :=
      (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
        (by have:=q.block_memory; omega)).2.1
    have hH := CommonLocalDescriptorBounds.height_scaled_le_input q
    omega
  have hround := LocalSortingCost.blockCount_capacity q.block
    (CommonLeafProgram.block_positive q) (3*n)
  rw [CommonRecordEncoding.recordBlocks_eq_words]
  change PhysicalStreamCursor.blockCount q.block (3*n)*q.block≤3*n+q.block at hround
  have hnmax : max q.N 1=q.N := max_eq_left (by have:=q.input_large; omega)
  rw [hnmax] at hc
  omega

end CodedSorting.CommonMSDParameters
end Parameters

section ChildCountPayload
/-! The actual directory-count result, abstracted before it is inserted
in the global control graph. No control tag or generated body is unfolded
when the caller inspects the returned counted RAM. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.CommonMSDChildCountPayload
open CommonSortingNormalization CommonStaticSchedule CommonMSDChildCount
open CommonLeafProgram (Machine machine)
noncomputable section
attribute [local irreducible] code acc totalCount executeRaw

theorem complete (q : Configuration) (directories : List ℕ) (key : ℕ)
    (s : Machine q)
    (hs : ∀ target∈directories,CommonMSDDirectoryRead.base q target key+
      CommonMSDDirectoryRead.blocks q key≤q.N^q.exponent)
    (hc : totalCount q s.disk directories key<(2^q.w)^q.digits) :
    ∃ out : Machine q,
      erasePC q (executeRaw q (code q directories key) s).1=out ∧
      out.disk=s.disk ∧ acc q (unpack out.ram)=totalCount q s.disk directories key := by
  obtain ⟨final,hr,ha⟩ := raw_complete q directories key (unpack s.ram) s.disk hs hc
  rw [CommonBlockPair.machine_eta] at hr
  refine ⟨erasePC q (machine q final s.disk),?_,rfl,?_⟩
  · rw [hr]
  · have h := acc_eq_of_erasePC q (erasePC q (machine q final s.disk)) (machine q final s.disk)
      (by simp only [erasePC,setPC_setPC])
    exact h.trans (by simpa only [machine,unpack_pack] using ha)

end
end CodedSorting.CommonMSDChildCountPayload
end ChildCountPayload

section DirectoryCost
/-! The real row-directory builder includes an alignment copy, its input
scan, and its directory writes. All row boundary costs are charged. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDDirectoryCost
open CommonSortingNormalization

def rowCharge (q : Configuration) (K L : ℕ) : ℕ :=
  7*CommonRecordProgram.recordBlocks q L+CommonMSDDirectory.blocks q K

theorem row_scaled (q : Configuration) (K L : ℕ) :
    rowCharge q K L*q.block≤21*L+(K*2)*q.digits+8*q.block := by
  have hb := CommonLeafProgram.block_positive q
  have hr := LocalSortingCost.blockCount_capacity q.block hb (3*L)
  have hd := LocalSortingCost.blockCount_capacity q.block hb ((K*2)*q.digits)
  change CommonMSDDirectory.blocks q K*q.block≤(K*2)*q.digits+q.block at hd
  change PhysicalStreamCursor.blockCount q.block (3*L)*q.block≤3*L+q.block at hr
  rw [←CommonRecordEncoding.recordBlocks_eq_words] at hr
  unfold rowCharge
  nlinarith

theorem scan_bound (q : Configuration) (n : ℕ) (hn : q.height^2≤n)
    {J : ℕ} (length : Fin J→ℕ)
    (hJ : J≤PhysicalStreamCursor.blockCount (q.height^2) n)
    (hlen : (∑ i,length i)≤n) :
    (∑ i,rowCharge q (CommonMSDParameters.radix q) (length i))*q.block≤39*n := by
  have hH : 0<q.height :=
    (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory; omega)).1
  have hb : q.block≤q.height :=
    (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory; omega)).2.1
  have hfields := CommonMSDParameters.radix_fields q
  have hsq : q.height≤q.height^2 := by nlinarith
  have hper : (CommonMSDParameters.radix q*2)*q.digits+8*q.block≤9*q.height^2 := by omega
  have hrows := LocalSortingCost.blockCount_capacity (q.height^2) (Nat.pow_pos hH) n
  change PhysicalStreamCursor.blockCount (q.height^2) n*q.height^2≤n+q.height^2 at hrows
  have hJ' := Nat.mul_le_mul_right (q.height^2) hJ
  have hbound := Nat.mul_le_mul_left J hper
  have hboundary : J*((CommonMSDParameters.radix q*2)*q.digits+8*q.block)≤18*n := by nlinarith
  have hsum : (∑ i,rowCharge q (CommonMSDParameters.radix q) (length i))*q.block≤
      21*(∑ i,length i)+J*((CommonMSDParameters.radix q*2)*q.digits+8*q.block) := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i : Fin J,(21*length i+(CommonMSDParameters.radix q*2)*q.digits+8*q.block) :=
        Finset.sum_le_sum (fun i _=>row_scaled q _ (length i))
      _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]; ring
  omega

end CodedSorting.CommonMSDDirectoryCost
end DirectoryCost
