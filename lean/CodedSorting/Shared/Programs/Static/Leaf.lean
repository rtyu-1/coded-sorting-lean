import CodedSorting.Shared.Memory.BlockPair
import CodedSorting.Interchange.Framework.Memory.ExchangeLeaf

/-! A resident bit permutation compiled as public static instructions.
All source blocks are actually read before the one bounded-RAM CPU step;
every output block is then staged in RAM and actually written. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonStaticLeaf
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonLeafLoad (diskWord diskWord_block)
open BitWordPacking Circuit
noncomputable section

def loadEffect (q : Configuration) (total k : ℕ) (s : Store q) : Store q :=
  {s with leaf := ResidentLeafBank.putBlock (k*q.block) (min q.block (total-k*q.block)) s.transfer s.leaf}

def readAt (q : Configuration) (source total k : ℕ) : Instruction q :=
  if h : source+k<q.N^q.exponent then
    ⟨.read ⟨source+k,h⟩ (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
      fun ram => pack (loadEffect q total k (unpack ram))⟩
  else ⟨.localOp id,id⟩

def readCode (q : Configuration) (source total k : ℕ) : List (Instruction q) :=
  (List.range k).map (readAt q source total)

def outputBlock (q : Configuration) (total k : ℕ) (bank : CommonLeafTransform.Bank q) :
    CommonBlockPair.Block q := ResidentLeafBank.getBlock (k*q.block) (total-k*q.block) bank

def stage (q : Configuration) (total k : ℕ) : Instruction q :=
  ⟨.localOp (fun ram => let s := unpack ram;
    pack {s with transfer:=outputBlock q total k s.leaf}),id⟩

def writeAt (q : Configuration) (target k : ℕ) : Instruction q :=
  if h : target+k<q.N^q.exponent then CommonBlockPair.targetWrite q ⟨target+k,h⟩
  else ⟨.localOp id,id⟩

def writeCode (q : Configuration) (target total k : ℕ) : List (Instruction q) :=
  (List.range k).flatMap (fun j => [stage q total j,writeAt q target j])

def compute (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) : Instruction q :=
  ⟨.localOp (fun ram => let s := unpack ram;
    pack {s with leaf:=CommonExchangeLeaf.cpu q V hV π s.leaf}),id⟩

def code (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) (source target : ℕ) : List (Instruction q) :=
  let total := 3*(CommonExchangeLeaf.roundedCount q V hV).val
  let k := PhysicalStreamCursor.blockCount q.block total
  readCode q source total k++[compute q V hV π]++writeCode q target total k

theorem raw_append (q : Configuration) (a b : List (Instruction q)) (s : Machine q) :
    executeRaw q (a++b) s=
      ((executeRaw q b (executeRaw q a s).1).1,
        (executeRaw q a s).2+(executeRaw q b (executeRaw q a s).1).2) := by
  induction a generalizing s with
  | nil => simp [executeRaw]
  | cons i is ih => simp only [List.cons_append,executeRaw,ih,Nat.add_assoc]

theorem readCode_succ (q : Configuration) (source total k : ℕ) :
    readCode q source total (k+1)=readCode q source total k++[readAt q source total k] := by
  simp [readCode,List.range_succ]

theorem writeCode_succ (q : Configuration) (target total k : ℕ) :
    writeCode q target total (k+1)=writeCode q target total k++[stage q total k,writeAt q target k] := by
  simp [writeCode,List.range_succ]

theorem readAt_step (q : Configuration) (source total k : ℕ)
    (h : source+k<q.N^q.exponent) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (readAt q source total k) (machine q s disk)=
      machine q (loadEffect q total k {s with transfer:=disk ⟨source+k,h⟩}) disk := by
  simp only [readAt,dif_pos h,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,CommonLeafWindow.load_transfer,unpack_pack]

theorem stage_step (q : Configuration) (total k : ℕ) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (stage q total k) (machine q s disk)=
      machine q {s with transfer:=outputBlock q total k s.leaf} disk := by
  simp only [stage,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,unpack_pack,id_eq]

theorem writeAt_step (q : Configuration) (target k : ℕ)
    (h : target+k<q.N^q.exponent) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (writeAt q target k) (machine q s disk)=
      machine q s (Function.update disk ⟨target+k,h⟩ s.transfer) := by
  rw [writeAt,dif_pos h,CommonBlockPair.targetWrite_step]

theorem compute_step (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (compute q V hV π) (machine q s disk)=
      machine q {s with leaf:=CommonExchangeLeaf.cpu q V hV π s.leaf} disk := by
  simp only [compute,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,unpack_pack,id_eq]

theorem read_prefix (q : Configuration) (source total k : ℕ)
    (s : Store q) (disk : Disk q) (hfit : source+k≤q.N^q.exponent)
    (hk : k≤PhysicalStreamCursor.blockCount q.block total) :
    ∃ loaded : Store q,
      executeRaw q (readCode q source total k) (machine q s disk)=(machine q loaded disk,k) ∧
      (∀ i : Fin (CommonExchangeLeaf.bankWords q),i.val<min total (k*q.block) →
        ResidentLeafBank.raw loaded.leaf i=diskWord q disk source i.val) ∧
      CommonLeafWrite.frameView q loaded=CommonLeafWrite.frameView q s ∧
      ResidentLeafSort.header loaded.leaf=ResidentLeafSort.header s.leaf := by
  induction k with
  | zero =>
    refine ⟨s,rfl,?_,rfl,rfl⟩
    intro i hi
    omega
  | succ k ih =>
    obtain ⟨loaded,hr,hread,hframe,hheader⟩ := ih (by omega) (by omega)
    have hlive : k*q.block<total :=
      (PhysicalStreamCursor.cursor_live_iff q.block total k (CommonLeafProgram.block_positive q)).1 (by omega)
    have haddr : source+k<q.N^q.exponent := by omega
    let next := loadEffect q total k {loaded with transfer:=disk ⟨source+k,haddr⟩}
    refine ⟨next,?_,?_,hframe,?_⟩
    · rw [readCode_succ,raw_append,hr]
      dsimp only
      simp only [executeRaw]
      rw [readAt_step q source total k haddr]
      simp only [readAt,dif_pos haddr,Normalization.transferCost,Nat.add_zero]
      rfl
    · intro i hi
      have hpref := ResidentLeafBank.putBlock_extends (k*q.block) total
        (disk ⟨source+k,haddr⟩) loaded.leaf (diskWord q disk source)
        (fun j hj => hread j (by omega))
        (fun j _ => (diskWord_block q disk source k haddr j).symm)
      exact hpref i (by simpa only [Nat.succ_mul] using hi)
    · exact (ResidentLeafBank.header_putBlock _ _ _ _).trans hheader

theorem write_prefix (q : Configuration) (target total k : ℕ)
    (s : Store q) (disk : Disk q) (hfit : target+k≤q.N^q.exponent) :
    ∃ final : Store q,
      executeRaw q (writeCode q target total k) (machine q s disk)=
        (machine q final (CommonLeafDisk.writePrefix target (fun j => outputBlock q total j s.leaf) k disk),k) ∧
      final.leaf=s.leaf ∧ CommonLeafWrite.frameView q final=CommonLeafWrite.frameView q s := by
  induction k with
  | zero => exact ⟨s,rfl,rfl,rfl⟩
  | succ k ih =>
    obtain ⟨mid,hr,hbank,hframe⟩ := ih (by omega)
    have haddr : target+k<q.N^q.exponent := by omega
    refine ⟨{mid with transfer:=outputBlock q total k mid.leaf},?_,hbank,hframe⟩
    rw [writeCode_succ,raw_append,hr]
    dsimp only
    simp only [executeRaw,stage_step,writeAt_step q target k haddr]
    rw [CommonLeafDisk.prefix_succ_of_lt haddr]
    simp only [stage,writeAt,dif_pos haddr,CommonBlockPair.targetWrite,Normalization.transferCost,
      Nat.add_zero,Nat.zero_add,hbank]


theorem written_word (q : Configuration) (bank : CommonLeafTransform.Bank q) (disk : Disk q)
    (base total : ℕ) (hfit : base+PhysicalStreamCursor.blockCount q.block total≤q.N^q.exponent)
    (i : Fin (CommonExchangeLeaf.bankWords q)) (hi : i.val<total) :
    diskWord q (CommonLeafDisk.writePrefix base (fun j => outputBlock q total j bank)
      (PhysicalStreamCursor.blockCount q.block total) disk) base i.val=ResidentLeafBank.raw bank i := by
  let k := i.val/q.block
  let j : Fin q.block := ⟨i.val%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩
  have he : k*q.block+j.val=i.val := by
    dsimp [k,j]
    simpa only [Nat.mul_comm] using Nat.div_add_mod i.val q.block
  have hk : k<PhysicalStreamCursor.blockCount q.block total :=
    (PhysicalStreamCursor.cursor_live_iff q.block total k (CommonLeafProgram.block_positive q)).2 (by omega)
  have ha : base+k<q.N^q.exponent := by omega
  rw [←he,diskWord_block q _ base k ha j]
  rw [CommonLeafDisk.prefix_at base _ _ disk hfit k hk]
  unfold outputBlock
  rw [ResidentLeafBank.getBlock_at _ _ bank j (by omega) (by rw [he]; exact i.isLt)]
  congr 1
  apply Fin.ext
  exact he

/-- Complete raw chronological execution of the static leaf. Every bit
comes from an actual source read, including when the two file regions overlap. -/
theorem raw_complete (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) (source target : ℕ) (s : Store q) (disk : Disk q)
    (hsource : source+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q V hV).val)≤q.N^q.exponent)
    (htarget : target+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q V hV).val)≤q.N^q.exponent) :
    let total := 3*(CommonExchangeLeaf.roundedCount q V hV).val
    let K := PhysicalStreamCursor.blockCount q.block total
    ∃ (final : Store q) (out : Disk q),
      executeRaw q (code q V hV π source target) (machine q s disk)=(machine q final out,2*K) ∧
      (∀ i : Fin V,CommonExchangeLeaf.diskBits q out target (i.castLE hV)=
        CommonExchangeLeaf.diskBits q disk source ((π i).castLE hV)) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+K≤a.val → out a=disk a) ∧
      CommonLeafWrite.frameView q final=CommonLeafWrite.frameView q s ∧
      ResidentLeafSort.header final.leaf=ResidentLeafSort.header s.leaf := by
  dsimp only
  let total := 3*(CommonExchangeLeaf.roundedCount q V hV).val
  let K := PhysicalStreamCursor.blockCount q.block total
  obtain ⟨loaded,hr,hread,hframe,hheader⟩ := read_prefix q source total K s disk hsource le_rfl
  have hcover : total≤K*q.block := LayoutConversion.blockCount_covers total q.block
    (CommonLeafProgram.block_positive q)
  have hall : ∀ i : Fin (CommonExchangeLeaf.bankWords q),i.val<total →
      ResidentLeafBank.raw loaded.leaf i=diskWord q disk source i.val := by
    intro i hi
    exact hread i (by simpa only [Nat.min_eq_left hcover] using hi)
  let changed : Store q := {loaded with leaf:=CommonExchangeLeaf.cpu q V hV π loaded.leaf}
  obtain ⟨final,hw,hbank,hframe'⟩ := write_prefix q target total K changed disk htarget
  let out := CommonLeafDisk.writePrefix target (fun j => outputBlock q total j changed.leaf) K disk
  have hwhole : executeRaw q (code q V hV π source target) (machine q s disk)=
      (machine q final out,2*K) := by
    rw [code,raw_append,raw_append,hr]
    dsimp only
    simp only [executeRaw,compute_step]
    simp only [compute,Normalization.transferCost,Nat.add_zero]
    change ((executeRaw q (writeCode q target total K) (machine q changed disk)).1,
      K+(executeRaw q (writeCode q target total K) (machine q changed disk)).2)=_
    rw [hw]
    change (machine q final out,K+K)=_
    congr 1
    omega
  refine ⟨final,out,hwhole,?_,?_,hframe'.trans hframe,?_⟩
  · intro i
    have hwrite : ∀ j : Fin (CommonExchangeLeaf.bankWords q),j.val<total →
        ResidentLeafBank.raw changed.leaf j=diskWord q out target j.val := by
      intro j hj
      exact (written_word q changed.leaf disk target total htarget j hj).symm
    have hbits := CommonExchangeLeaf.rounded_cover q V hV
    rw [←CommonExchangeLeaf.payload_eq_diskBits q changed.leaf out target total hwrite
      (i.castLE hV) (i.isLt.trans_le hbits)]
    change CommonExchangeLeaf.payload q (CommonExchangeLeaf.cpu q V hV π loaded.leaf) _=_
    rw [CommonExchangeLeaf.cpu_bits]
    exact CommonExchangeLeaf.payload_eq_diskBits q loaded.leaf disk source total hall
      ((π i).castLE hV) ((π i).isLt.trans_le hbits)
  · intro a ha
    exact CommonLeafDisk.prefix_outside target _ K disk a ha
  · rw [hbank]
    exact (CommonExchangeLeaf.cpu_header q V hV π loaded.leaf).trans hheader


@[simp] theorem readCode_length (q : Configuration) (source total k : ℕ) :
    (readCode q source total k).length=k := by simp [readCode]

@[simp] theorem writeCode_length (q : Configuration) (target total k : ℕ) :
    (writeCode q target total k).length=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [writeCode_succ,List.length_append,ih]; simp; omega

@[simp] theorem length_code (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) (source target : ℕ) :
    (code q V hV π source target).length=
      3*PhysicalStreamCursor.blockCount q.block (3*(CommonExchangeLeaf.roundedCount q V hV).val)+1 := by
  simp only [code,List.length_append,readCode_length,List.length_singleton,writeCode_length]
  omega

theorem cost_append (q : Configuration) (a b : List (Instruction q)) :
    cost q (a++b)=cost q a+cost q b := by
  induction a with
  | nil => simp [cost]
  | cons i is ih => simp only [List.cons_append,cost,ih,Nat.add_assoc]

theorem readCode_cost (q : Configuration) (source total k : ℕ)
    (hfit : source+k≤q.N^q.exponent) : cost q (readCode q source total k)=k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [readCode_succ,cost_append,ih (by omega)]
    simp only [cost,readAt,dif_pos (show source+k<q.N^q.exponent by omega),
      Normalization.transferCost,Nat.add_zero]

theorem writeCode_cost (q : Configuration) (target total k : ℕ)
    (hfit : target+k≤q.N^q.exponent) : cost q (writeCode q target total k)=k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [writeCode_succ,cost_append,ih (by omega)]
    simp only [cost,stage,writeAt,dif_pos (show target+k<q.N^q.exponent by omega),
      CommonBlockPair.targetWrite,Normalization.transferCost,Nat.add_zero,Nat.zero_add]

theorem cost_code (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) (source target : ℕ)
    (hsource : source+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q V hV).val)≤q.N^q.exponent)
    (htarget : target+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q V hV).val)≤q.N^q.exponent) :
    cost q (code q V hV π source target)=
      2*PhysicalStreamCursor.blockCount q.block (3*(CommonExchangeLeaf.roundedCount q V hV).val) := by
  rw [code,cost_append,cost_append,readCode_cost q source _ _ hsource,writeCode_cost q target _ _ htarget]
  simp only [cost,compute,Normalization.transferCost,Nat.add_zero]
  omega

theorem readAt_safe (q : Configuration) (source total k : ℕ) :
    RespectsPC q (readAt q source total k) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  by_cases h : source+k<q.N^q.exponent
  · simp only [readAt_step q source total k h,CommonBlockPair.erasePC_machine]
    rfl
  · simp only [readAt,dif_neg h,ControlledNormalization.logicalStep,Normalization.logicalStep,id_eq]

theorem stage_safe (q : Configuration) (total k : ℕ) : RespectsPC q (stage q total k) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [stage_step,CommonBlockPair.erasePC_machine]

theorem writeAt_safe (q : Configuration) (target k : ℕ) : RespectsPC q (writeAt q target k) := by
  unfold writeAt
  split
  · exact CommonBlockPair.targetWrite_respectsPC q _
  · apply CommonBlockPair.respectsPC_of_commutes
    intro s
    simp only [ControlledNormalization.logicalStep,Normalization.logicalStep,id_eq]

theorem compute_safe (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) : RespectsPC q (compute q V hV π) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [compute_step,CommonBlockPair.erasePC_machine]

theorem safe (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) (source target : ℕ) :
    ∀ i∈code q V hV π source target,RespectsPC q i := by
  intro i hi
  simp only [code,List.mem_append,List.mem_singleton] at hi
  rcases hi with (hi|hi)|hi
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    exact readAt_safe q source _ j
  · subst i
    exact compute_safe q V hV π
  · obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj|hj
    · subst i; exact stage_safe q _ j
    · subst i; exact writeAt_safe q target j


/-- The concrete compiled fixed policy, including its resident program
counter, returns the specified bit permutation with its same-run charge. -/
theorem compiled_complete (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q)
    (π : Equiv.Perm (Fin V)) (source target : ℕ) (s : Store q) (disk : Disk q)
    (hsource : source+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q V hV).val)≤q.N^q.exponent)
    (htarget : target+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q V hV).val)≤q.N^q.exponent)
    (hsize : (code q V hV π source target).length≤q.N^q.exponent)
    (hpc : pc q (pack s)=0) :
    let program := code q V hV π source target
    let result := ControlledNormalization.runLogical (CommonStaticSchedule.policy q program)
      program.length (machine q s disk)
    CommonStaticSchedule.policy q program result.1.ram=none ∧
    result.2=2*PhysicalStreamCursor.blockCount q.block (3*(CommonExchangeLeaf.roundedCount q V hV).val) ∧
    (∀ i : Fin V,CommonExchangeLeaf.diskBits q result.1.disk target (i.castLE hV)=
      CommonExchangeLeaf.diskBits q disk source ((π i).castLE hV)) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨
      target+PhysicalStreamCursor.blockCount q.block (3*(CommonExchangeLeaf.roundedCount q V hV).val)≤a.val →
      result.1.disk a=disk a) ∧ Fintype.card (ResidentIndex q)≤q.M := by
  dsimp only
  obtain ⟨final,out,hr,hbits,houtside,_,_⟩ := raw_complete q V hV π source target s disk hsource htarget
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (code q V hV π source target)
    hsize (safe q V hV π source target) (machine q s disk) hpc
  rw [hr] at hd
  rw [cost_code q V hV π source target hsource htarget] at hc
  refine ⟨hh,hc,?_,?_,hm⟩
  · simpa only [hd] using hbits
  · simpa only [hd] using houtside

/-- Public dimensions determine the exact exchange permutation; neither
addresses nor code inspect the input bits. -/
def exchangeCode (q : Configuration) (P Q G S : ℕ)
    (hV : BaseExchangeProgram.Volume P Q G S≤CommonExchangeLeaf.bankBits q)
    (source target : ℕ) : List (Instruction q) :=
  code q _ hV (BaseExchangeProgram.permutation (P:=P) (Q:=Q) (G:=G) (S:=S)) source target

theorem exchange_raw (q : Configuration) (P Q G S : ℕ)
    (hV : BaseExchangeProgram.Volume P Q G S≤CommonExchangeLeaf.bankBits q)
    (source target : ℕ) (s : Store q) (disk : Disk q)
    (hsource : source+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q (BaseExchangeProgram.Volume P Q G S) hV).val)≤q.N^q.exponent)
    (htarget : target+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q (BaseExchangeProgram.Volume P Q G S) hV).val)≤q.N^q.exponent) :
    let result := executeRaw q (exchangeCode q P Q G S hV source target) (machine q s disk)
    (∀ a : Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin S),
      CommonExchangeLeaf.diskBits q result.1.disk target ((CoordinateScans.lowLayout a).castLE hV)=
        CommonExchangeLeaf.diskBits q disk source ((CoordinateScans.lowLayout (Address.exchange a)).castLE hV)) ∧
    result.2=2*PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q (BaseExchangeProgram.Volume P Q G S) hV).val) ∧
    result.2≤12*(BaseExchangeProgram.Volume P Q G S/(q.block*q.w)+1) := by
  dsimp only
  obtain ⟨final,out,hr,hbits,_,_,_⟩ := raw_complete q _ hV
    (BaseExchangeProgram.permutation (P:=P) (Q:=Q) (G:=G) (S:=S)) source target s disk hsource htarget
  change executeRaw q (exchangeCode q P Q G S hV source target) _=_ at hr
  rw [hr]
  refine ⟨?_,rfl,CommonExchangeLeaf.leaf_charge_bound q _ hV⟩
  intro a
  simpa only [BaseExchangeProgram.permutation_encoded] using hbits (CoordinateScans.lowLayout a)

end
end CodedSorting.CommonStaticLeaf
