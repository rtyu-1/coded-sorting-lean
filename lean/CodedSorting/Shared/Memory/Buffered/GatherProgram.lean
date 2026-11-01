import CodedSorting.Interchange.Framework.Recursion.ExchangeBudget

section Allocation
/-! Block-aligned bucket files in one finite scratch arena.  All bounds
refer to actual finite-disk addresses, including the source frame. -/
set_option autoImplicit false
namespace CodedSorting.CommonBufferedAllocation
open CommonSortingNormalization CommonPermutationPairs
open CommonLeafProgram (Disk)
noncomputable section

variable {K : ℕ}

def bucketAddress (q : Configuration) (arena L : ℕ) (k : Fin K) (page : ℕ) :
    Fin (q.N^q.exponent) :=
  CommonColumnSplit.address q arena (k.val*count q L+page)

theorem offset_bound (q : Configuration) (L : ℕ) (k : Fin K) (page : ℕ)
    (hp : page<count q L) : k.val*count q L+page<K*count q L := by
  have h := Nat.mul_le_mul_right (count q L) (show k.val+1≤K by omega)
  rw [Nat.add_mul,Nat.one_mul] at h
  omega

@[simp] theorem bucketAddress_val (q : Configuration) (arena L : ℕ)
    (k : Fin K) (page : ℕ) (hp : page<count q L)
    (hfit : arena+K*count q L≤q.N^q.exponent) :
    (bucketAddress q arena L k page).val=arena+(k.val*count q L+page) := by
  apply CommonColumnSplit.address_val
  have h := offset_bound q L k page hp
  omega

theorem bucketAddress_bounds (q : Configuration) (arena L : ℕ)
    (k : Fin K) (page : ℕ) (hp : page<count q L)
    (hfit : arena+K*count q L≤q.N^q.exponent) :
    arena≤(bucketAddress q arena L k page).val ∧
      (bucketAddress q arena L k page).val<arena+K*count q L := by
  rw [bucketAddress_val q arena L k page hp hfit]
  have h := offset_bound q L k page hp
  omega

theorem bucketAddress_injective (q : Configuration) (arena L : ℕ)
    (k other : Fin K) (page otherPage : ℕ)
    (hp : page<count q L) (hop : otherPage<count q L)
    (hfit : arena+K*count q L≤q.N^q.exponent)
    (he : bucketAddress q arena L k page=bucketAddress q arena L other otherPage) :
    k=other ∧ page=otherPage := by
  have hv := congrArg Fin.val he
  rw [bucketAddress_val q arena L k page hp hfit,
    bucketAddress_val q arena L other otherPage hop hfit] at hv
  have hk : k.val=other.val := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlo|hhi
    · have h := Nat.mul_le_mul_right (count q L) (show k.val+1≤other.val by omega)
      rw [Nat.add_mul,Nat.one_mul] at h
      omega
    · have h := Nat.mul_le_mul_right (count q L) (show other.val+1≤k.val by omega)
      rw [Nat.add_mul,Nat.one_mul] at h
      omega
  exact ⟨Fin.ext hk,by rw [hk] at hv; omega⟩

theorem bucketAddress_ne (q : Configuration) (arena L : ℕ)
    (k other : Fin K) (page otherPage : ℕ)
    (hp : page<count q L) (hop : otherPage<count q L)
    (hfit : arena+K*count q L≤q.N^q.exponent)
    (hne : k≠other ∨ page≠otherPage) :
    bucketAddress q arena L k page≠bucketAddress q arena L other otherPage := by
  intro he
  obtain ⟨hk,hp⟩ := bucketAddress_injective q arena L k other page otherPage hp hop hfit he
  rcases hne with hn|hn
  · exact hn hk
  · exact hn hp

theorem bucketAddress_ne_outside (q : Configuration) (arena L : ℕ)
    (k : Fin K) (page : ℕ) (hp : page<count q L)
    (hfit : arena+K*count q L≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<arena ∨ arena+K*count q L≤a.val) :
    bucketAddress q arena L k page≠a := by
  have hb := bucketAddress_bounds q arena L k page hp hfit
  intro he
  have hv := congrArg Fin.val he
  omega

theorem bucketAddress_ne_source (q : Configuration) (source arena V L : ℕ)
    (k : Fin K) (page inputPage : ℕ)
    (hp : page<count q L) (hi : inputPage<count q V)
    (hsource : source+count q V≤q.N^q.exponent)
    (hfit : arena+K*count q L≤q.N^q.exponent)
    (hsep : source+count q V≤arena ∨ arena+K*count q L≤source) :
    bucketAddress q arena L k page≠CommonColumnSplit.address q source inputPage := by
  apply bucketAddress_ne_outside q arena L k page hp hfit
  rw [CommonColumnSplit.address_val q source inputPage (by omega)]
  omega

theorem update_other (q : Configuration) (arena L : ℕ)
    (k other : Fin K) (page otherPage : ℕ)
    (hp : page<count q L) (hop : otherPage<count q L)
    (hfit : arena+K*count q L≤q.N^q.exponent)
    (hne : other≠k ∨ otherPage≠page)
    (disk : Disk q) (block : CommonBlockPair.Block q) :
    Function.update disk (bucketAddress q arena L k page) block
      (bucketAddress q arena L other otherPage)=disk (bucketAddress q arena L other otherPage) :=
  Function.update_of_ne (bucketAddress_ne q arena L other k otherPage page hop hp hfit hne) _ _

theorem update_outside (q : Configuration) (arena L : ℕ)
    (k : Fin K) (page : ℕ) (hp : page<count q L)
    (hfit : arena+K*count q L≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<arena ∨ arena+K*count q L≤a.val)
    (disk : Disk q) (block : CommonBlockPair.Block q) :
    Function.update disk (bucketAddress q arena L k page) block a=disk a :=
  Function.update_of_ne (Ne.symm (bucketAddress_ne_outside q arena L k page hp hfit a ha)) _ _

theorem update_source (q : Configuration) (source arena V L : ℕ)
    (k : Fin K) (page inputPage : ℕ)
    (hp : page<count q L) (hi : inputPage<count q V)
    (hsource : source+count q V≤q.N^q.exponent)
    (hfit : arena+K*count q L≤q.N^q.exponent)
    (hsep : source+count q V≤arena ∨ arena+K*count q L≤source)
    (disk : Disk q) (block : CommonBlockPair.Block q) :
    Function.update disk (bucketAddress q arena L k page) block
      (CommonColumnSplit.address q source inputPage)=disk (CommonColumnSplit.address q source inputPage) :=
  Function.update_of_ne (Ne.symm
    (bucketAddress_ne_source q source arena V L k page inputPage hp hi hsource hfit hsep)) _ _

theorem update_readBit (q : Configuration) (source arena V L : ℕ)
    (k : Fin K) (page : ℕ) (i : Fin V)
    (hp : page<count q L) (hsource : source+count q V≤q.N^q.exponent)
    (hfit : arena+K*count q L≤q.N^q.exponent)
    (hsep : source+count q V≤arena ∨ arena+K*count q L≤source)
    (disk : Disk q) (block : CommonBlockPair.Block q) :
    readBit q (Function.update disk (bucketAddress q arena L k page) block) source i.val=
      readBit q disk source i.val := by
  unfold readBit
  rw [update_source q source arena V L k page (i.val/width q) hp
    (bit_block_lt q i) hsource hfit hsep]

end
end CodedSorting.CommonBufferedAllocation
end Allocation

section Bank
/-! Several block buffers inside the existing resident leaf bank.  Buffer
positions and selection maps are public program text; payload enters only
through actual reads or through the existing resident reader cache. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace CodedSorting.CommonBufferedBank
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonBlockPair (Block BitIndex Selection)
open BitWordPacking Circuit
noncomputable section

variable {K : ℕ}

theorem slot_bound (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (j : Fin q.block) :
    slot.val*q.block+j.val<CommonExchangeLeaf.bankWords q := by
  have h := Nat.mul_le_mul_right q.block (show slot.val+1≤K by omega)
  have hj := j.isLt
  rw [Nat.add_mul,one_mul] at h
  omega

def get (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (s : Store q) : Block q :=
  fun j => ResidentLeafBank.raw s.leaf ⟨slot.val*q.block+j.val,slot_bound q hfit slot j⟩

def put (q : Configuration) (slot : Fin K) (block : Block q) (s : Store q) : Store q :=
  {s with leaf:=ResidentLeafBank.putBlock (slot.val*q.block) q.block block s.leaf}

@[simp] theorem get_transfer (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (block : Block q) (s : Store q) :
    get q hfit slot {s with transfer:=block}=get q hfit slot s := rfl

@[simp] theorem get_stash (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (reader : Fin q.inventory.readers) (block : Block q) (s : Store q) :
    get q hfit slot (CommonBlockPair.stash q reader block s)=get q hfit slot s := rfl

@[simp] theorem get_put_self (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (block : Block q) (s : Store q) :
    get q hfit slot (put q slot block s)=block := by
  funext j
  exact ResidentLeafBank.raw_putBlock_at _ _ block s.leaf j j.isLt (le_refl _)
    (slot_bound q hfit slot j)

@[simp] theorem get_put_ne (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot other : Fin K) (hne : other≠slot) (block : Block q) (s : Store q) :
    get q hfit other (put q slot block s)=get q hfit other s := by
  funext j
  apply ResidentLeafBank.raw_putBlock_outside
  have hn : other.val≠slot.val := fun h => hne (Fin.ext h)
  have hj := j.isLt
  rcases lt_or_gt_of_ne hn with hlt|hgt
  · left
    have h := Nat.mul_le_mul_right q.block (show other.val+1≤slot.val by omega)
    rw [Nat.add_mul,one_mul] at h
    change other.val*q.block+j.val<slot.val*q.block
    omega
  · right
    have h := Nat.mul_le_mul_right q.block (show slot.val+1≤other.val by omega)
    rw [Nat.add_mul,one_mul] at h
    change slot.val*q.block+q.block≤other.val*q.block+j.val
    omega

@[simp] theorem put_readers (q : Configuration) (slot : Fin K)
    (block : Block q) (s : Store q) : (put q slot block s).readers=s.readers := rfl

@[simp] theorem buffer_put (q : Configuration) (reader : Fin q.inventory.readers)
    (slot : Fin K) (block : Block q) (s : Store q) :
    CommonBlockPair.buffer q reader (put q slot block s)=CommonBlockPair.buffer q reader s := rfl

def blendStore (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (select : Selection q)
    (s : Store q) : Store q :=
  put q slot (CommonBlockPair.blend q select (CommonBlockPair.buffer q reader s)
    (get q hfit slot s)) s

@[simp] theorem blendStore_get (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (select : Selection q)
    (s : Store q) (i : BitIndex q) :
    blockBits q.block q.w (get q hfit slot (blendStore q hfit reader slot select s)) i=
      match select i with
      | none => blockBits q.block q.w (get q hfit slot s) i
      | some j => blockBits q.block q.w (CommonBlockPair.buffer q reader s) j := by
  simp only [blendStore,get_put_self,CommonBlockPair.blend_bits]
  rfl

@[simp] theorem blendStore_other (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot other : Fin K) (hne : other≠slot)
    (select : Selection q) (s : Store q) :
    get q hfit other (blendStore q hfit reader slot select s)=get q hfit other s :=
  get_put_ne q hfit slot other hne _ s

@[simp] theorem blendStore_buffer (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader cache : Fin q.inventory.readers) (slot : Fin K)
    (select : Selection q) (s : Store q) :
    CommonBlockPair.buffer q cache (blendStore q hfit reader slot select s)=
      CommonBlockPair.buffer q cache s := rfl

def blendInstruction (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (select : Selection q) : Instruction q :=
  ⟨.localOp (fun ram => pack (blendStore q hfit reader slot select (unpack ram))),id⟩

def zeroInstruction (q : Configuration) (slot : Fin K) : Instruction q :=
  ⟨.localOp (fun ram => pack (put q slot (fun _ => 0) (unpack ram))),id⟩

def loadInstruction (q : Configuration) (slot : Fin K)
    (source : Fin (q.N^q.exponent)) : Instruction q :=
  ⟨.read source (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    fun ram => let s := unpack ram; pack (put q slot s.transfer s)⟩

def prepareInstruction (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) : Instruction q :=
  ⟨.localOp (fun ram => let s := unpack ram; pack {s with transfer:=get q hfit slot s}),id⟩

def writeCode (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (target : Fin (q.N^q.exponent)) : List (Instruction q) :=
  [prepareInstruction q hfit slot,CommonBlockPair.targetWrite q target]

theorem blendInstruction_step (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (select : Selection q)
    (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (blendInstruction q hfit reader slot select) (machine q s disk)=
      machine q (blendStore q hfit reader slot select s) disk := by
  simp only [blendInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem loadInstruction_step (q : Configuration) (slot : Fin K)
    (source : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (loadInstruction q slot source) (machine q s disk)=
      machine q (put q slot (disk source) {s with transfer:=disk source}) disk := by
  simp only [loadInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,
    CommonLeafWindow.load_transfer,unpack_pack]

theorem zeroInstruction_step (q : Configuration) (slot : Fin K)
    (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (zeroInstruction q slot) (machine q s disk)=
      machine q (put q slot (fun _ => 0) s) disk := by
  simp only [zeroInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem prepareInstruction_step (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (prepareInstruction q hfit slot) (machine q s disk)=
      machine q {s with transfer:=get q hfit slot s} disk := by
  simp only [prepareInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem writeCode_run (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    executeRaw q (writeCode q hfit slot target) (machine q s disk)=
      (machine q {s with transfer:=get q hfit slot s}
        (Function.update disk target (get q hfit slot s)),1) := by
  simp only [writeCode,executeRaw,prepareInstruction_step,CommonBlockPair.targetWrite_step]
  rfl

theorem writeCode_get (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot other : Fin K) (target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    get q hfit other (unpack (executeRaw q (writeCode q hfit slot target)
      (machine q s disk)).1.ram)=get q hfit other s := by
  rw [writeCode_run]
  simp only [machine,unpack_pack,get_transfer]

theorem writeCode_buffer (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (reader : Fin q.inventory.readers)
    (target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    CommonBlockPair.buffer q reader (unpack (executeRaw q (writeCode q hfit slot target)
      (machine q s disk)).1.ram)=CommonBlockPair.buffer q reader s := by
  rw [writeCode_run]
  simp only [machine,unpack_pack]
  rfl

theorem sourceRead_get (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (reader : Fin q.inventory.readers)
    (source : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    get q hfit slot (unpack (ControlledNormalization.logicalStep
      (CommonBlockPair.sourceRead q reader source) (machine q s disk)).ram)=
        get q hfit slot s := by
  rw [CommonBlockPair.sourceRead_step]
  simp only [machine,unpack_pack,get_stash,get_transfer]

theorem sourceRead_buffer (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    CommonBlockPair.buffer q reader (unpack (ControlledNormalization.logicalStep
      (CommonBlockPair.sourceRead q reader source) (machine q s disk)).ram)=disk source := by
  rw [CommonBlockPair.sourceRead_step]
  simp only [machine,unpack_pack,CommonBlockPair.buffer_stash]

@[simp] theorem writeCode_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (target : Fin (q.N^q.exponent)) :
    cost q (writeCode q hfit slot target)=1 := rfl

@[simp] theorem writeCode_length (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (target : Fin (q.N^q.exponent)) :
    (writeCode q hfit slot target).length=2 := rfl

theorem blendInstruction_respectsPC (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (select : Selection q) :
    RespectsPC q (blendInstruction q hfit reader slot select) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [blendInstruction_step,CommonBlockPair.erasePC_machine]
  rfl

theorem loadInstruction_respectsPC (q : Configuration) (slot : Fin K)
    (source : Fin (q.N^q.exponent)) : RespectsPC q (loadInstruction q slot source) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [loadInstruction_step,CommonBlockPair.erasePC_machine]
  rfl

theorem zeroInstruction_respectsPC (q : Configuration) (slot : Fin K) :
    RespectsPC q (zeroInstruction q slot) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [zeroInstruction_step,CommonBlockPair.erasePC_machine]
  rfl

theorem prepareInstruction_respectsPC (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) : RespectsPC q (prepareInstruction q hfit slot) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [prepareInstruction_step,CommonBlockPair.erasePC_machine]
  rfl

theorem writeCode_safe (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (slot : Fin K) (target : Fin (q.N^q.exponent)) :
    ∀ i∈writeCode q hfit slot target,RespectsPC q i := by
  intro i hi
  simp only [writeCode,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with hi|hi
  · subst i; exact prepareInstruction_respectsPC q hfit slot
  · subst i; exact CommonBlockPair.targetWrite_respectsPC q target

end
end CodedSorting.CommonBufferedBank
end Bank

section GatherProgram
/-! Concrete reconstruction of a packed file from equal-length bucket files.
The bucket buffers occupy the existing leaf bank, and the partially assembled
output block occupies an existing reader cache. All addresses and bit selections
are public; payloads enter only through actual disk reads. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBufferedGather
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonBlockPair (Block BitIndex Selection)
open CommonPermutationPairs (width count address)
open BitWordPacking Circuit
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V K L : ℕ}

def position (q : Configuration) (i : ℕ) : BitIndex q :=
  ⟨i % width q,Nat.mod_lt _ (CommonPermutationPairs.width_pos q)⟩

def selection (q : Configuration) (destination source : ℕ) : Selection q :=
  fun j => if j=position q destination then some (position q source) else none

def assemble (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (destination source : ℕ)
    (s : Store q) : Store q :=
  CommonBlockPair.stash q reader
    (CommonBlockPair.blend q (selection q destination source)
      (CommonBufferedBank.get q hfit slot s) (CommonBlockPair.buffer q reader s)) s

def assembleInstruction (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (destination source : ℕ) : Instruction q :=
  ⟨.localOp (fun ram => pack (assemble q hfit reader slot destination source (unpack ram))),id⟩

def prepareInstruction (q : Configuration) (reader : Fin q.inventory.readers) : Instruction q :=
  ⟨.localOp (fun ram => let s := unpack ram;
    pack {s with transfer:=CommonBlockPair.buffer q reader s}),id⟩

def writeCode (q : Configuration) (reader : Fin q.inventory.readers)
    (target : Fin (q.N^q.exponent)) : List (Instruction q) :=
  [prepareInstruction q reader,CommonBlockPair.targetWrite q target]

def fragment (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (i : Fin V) : List (Instruction q) :=
  (if (e i).2.val % width q=0 then
    [CommonBufferedBank.loadInstruction q (e i).1
      (address q arena ((e i).1.val*count q L+(e i).2.val/width q))] else []) ++
  [assembleInstruction q hfit reader (e i).1 i.val (e i).2.val] ++
  (if i.val % width q=width q-1 ∨ i.val+1=V then
    writeCode q reader (address q target (i.val/width q)) else [])

def code (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) : List (Instruction q) :=
  (List.finRange V).flatMap (fragment q hfit reader e arena target)

theorem assemble_buffer (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (destination source : ℕ)
    (s : Store q) :
    blockBits q.block q.w (CommonBlockPair.buffer q reader
      (assemble q hfit reader slot destination source s)) =
    Function.update (blockBits q.block q.w (CommonBlockPair.buffer q reader s))
      (position q destination)
      (blockBits q.block q.w (CommonBufferedBank.get q hfit slot s) (position q source)) := by
  funext j
  simp only [assemble,CommonBlockPair.buffer_stash,CommonBlockPair.blend_bits,selection]
  by_cases hj : j=position q destination
  · subst j; simp
  · simp [hj,Function.update_of_ne hj]

theorem assemble_bank (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot other : Fin K) (destination source : ℕ)
    (s : Store q) :
    CommonBufferedBank.get q hfit other (assemble q hfit reader slot destination source s)=
      CommonBufferedBank.get q hfit other s := rfl

theorem assemble_step (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (destination source : ℕ)
    (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep
      (assembleInstruction q hfit reader slot destination source) (machine q s disk)=
      machine q (assemble q hfit reader slot destination source s) disk := by
  simp only [assembleInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem prepare_step (q : Configuration) (reader : Fin q.inventory.readers)
    (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (prepareInstruction q reader) (machine q s disk)=
      machine q {s with transfer:=CommonBlockPair.buffer q reader s} disk := by
  simp only [prepareInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem write_run (q : Configuration) (reader : Fin q.inventory.readers)
    (target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    executeRaw q (writeCode q reader target) (machine q s disk)=
      (machine q {s with transfer:=CommonBlockPair.buffer q reader s}
        (Function.update disk target (CommonBlockPair.buffer q reader s)),1) := by
  simp only [writeCode,executeRaw,prepare_step,CommonBlockPair.targetWrite_step]
  rfl

theorem assemble_safe (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (slot : Fin K) (destination source : ℕ) :
    RespectsPC q (assembleInstruction q hfit reader slot destination source) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [← CommonBlockPair.machine_eta q s]
  simp only [assemble_step,CommonBlockPair.erasePC_machine]
  rfl

theorem prepare_safe (q : Configuration) (reader : Fin q.inventory.readers) :
    RespectsPC q (prepareInstruction q reader) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [← CommonBlockPair.machine_eta q s]
  simp only [prepare_step,CommonBlockPair.erasePC_machine]
  rfl

theorem write_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (target : Fin (q.N^q.exponent)) :
    ∀ i∈writeCode q reader target,RespectsPC q i := by
  intro i hi
  simp only [writeCode,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl
  · exact prepare_safe q reader
  · exact CommonBlockPair.targetWrite_respectsPC q target

theorem fragment_safe (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (i : Fin V) :
    ∀ j∈fragment q hfit reader e arena target i,RespectsPC q j := by
  intro j hj
  unfold fragment at hj
  rcases List.mem_append.mp hj with hj|hj
  · rcases List.mem_append.mp hj with hj|hj
    · split_ifs at hj with h
      · have he := List.mem_singleton.mp hj
        subst j
        exact CommonBufferedBank.loadInstruction_respectsPC q _ _
      · simp at hj
    · have he := List.mem_singleton.mp hj
      subst j
      exact assemble_safe q hfit reader _ _ _
  · split_ifs at hj with h
    · exact write_safe q reader _ j hj
    · simp at hj

theorem code_safe (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) : ∀ i∈code q hfit reader e arena target,RespectsPC q i := by
  intro i hi
  obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hi
  exact fragment_safe q hfit reader e arena target j i hj

theorem fragment_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (i : Fin V) :
    cost q (fragment q hfit reader e arena target i)=
      (if (e i).2.val%width q=0 then 1 else 0)+
      (if i.val%width q=width q-1 ∨ i.val+1=V then 1 else 0) := by
  simp only [fragment,CommonPermutationPairs.cost_append]
  split_ifs <;> rfl

end
end CodedSorting.CommonBufferedGather
end GatherProgram

section Recursion
/-! Workspace, resident-buffer conditions, and public recursive budgets for
fast buffered leaves. This does not change the existing recursion tree or
its internal network implementation. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecursiveExchange.Buffered
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open CommonRecursiveExchangeCost PhysicalStreamCursor Address Circuit
noncomputable section
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

def buckets (f : ℕ) : ℕ := (radix^f)*(radix^f)

def space (q : Configuration) : {f P G S : ℕ} → Tree q f P G S → ℕ
  | f,P,G,S,.leaf _ _ _ _ => count q (ScalarVolume f P G S)+buckets f
  | _,_,_,_,.node f R G S _ _ children =>
      parentCount q f R G S+CommonResidentNetwork.fileCount*childCount q f R G S+
        childCount q f R G S+∑ c : Child,space q (children c)

/-- A leaf needs one original-word block per bucket in the already reserved
leaf bank. There is no assumption about successful child execution. -/
def Fits (q : Configuration) : {f P G S : ℕ} → Tree q f P G S → Prop
  | f,_,_,_,.leaf _ _ _ _ => buckets f*q.block≤CommonExchangeLeaf.bankWords q
  | _,_,_,_,.node _ _ _ _ _ _ children => ∀ c : Child,Fits q (children c)

theorem old_space_le (q : Configuration) {f P G S : ℕ} (t : Tree q f P G S) :
    CommonRecursiveExchange.space q t≤space q t := by
  induction t with
  | leaf => simp only [CommonRecursiveExchange.space,space]; omega
  | node f R G S hG hS children ih =>
    have hh := Finset.sum_le_sum (fun c (_ : c∈(Finset.univ : Finset Child)) => ih c)
    simp only [CommonRecursiveExchange.space,space,parentCount,childCount] at *
    omega

theorem volume_le_space (q : Configuration) {f P G S : ℕ} (t : Tree q f P G S) :
    count q (ScalarVolume f P G S)≤space q t :=
  (CommonRecursiveExchange.volume_le_space q t).trans (old_space_le q t)

theorem child_space_le (q : Configuration) (f R G S : ℕ)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c)) (c : Child) :
    space q (children c)≤∑ d : Child,space q (children d) :=
  Finset.single_le_sum (f:=fun d : Child => space q (children d))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

def allocation (q : Configuration) (f R G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hs : source+count q (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w))≤buffer)
    (hw : buffer+space q (.node f R G S hG hS children)≤limit)
    (hl : limit≤q.N^q.exponent) : NodeAllocation q f R G S source buffer limit :=
  treeAllocation q f R G S source buffer limit hG hS children hs
    ((Nat.add_le_add_left (old_space_le q (.node f R G S hG hS children)) buffer).trans hw) hl

theorem child_workspace (q : Configuration) (f R G S buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c))
    (hw : buffer+space q (.node f R G S hG hS children)≤limit) (c : Child) :
    childBase q f R G S buffer+space q (children c)≤limit := by
  have hc := child_space_le q f R G S children c
  dsimp only [space] at hw
  dsimp only [childBase,networkBase]
  omega

def leafCharge (q : Configuration) (f P G S : ℕ) : ℕ :=
  4*count q (ScalarVolume f P G S)+2*buckets f+1

def budget (q : Configuration) : {f P G S : ℕ} → Tree q f P G S → ℕ
  | f,P,G,S,.leaf _ _ _ _ => leafCharge q f P G S
  | _,_,_,_,.node f R G S hG hS children =>
      (72*Parameters.m+12*Parameters.W)*parentCount q f R G S+
      12*Parameters.W*blockCount q.block (longVolume f R G S)+
      networkCharge q f R G (S*q.w) hG
        (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>budget q (children c))+
      6*parentCount q f R G S

/-- The unchanged internal-node cost plus exactly the selected child
budgets. The improved leaf charge is already part of this recurrence. -/
theorem budget_node_le (q : Configuration) (f R G S : ℕ) (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c) (childS f (S*q.w) c)) :
    budget q (.node f R G S hG hS children)≤
      (72*Parameters.m+12*Parameters.W+6)*parentCount q f R G S+
      (12*Parameters.W+3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
        CommonRankEdge.constructionConstant)*childCount q f R G S+
      ∑ c : Child,budget q (children c) := by
  have hh := CommonRecursiveExchange.networkCharge_le q f R G (S*q.w) hG
    (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>budget q (children c))
  have hc : blockCount q.block (longVolume f R G S)=childCount q f R G S :=
    (CommonOneLevelAllocation.local_count q f R G S).symm
  dsimp only [budget]
  rw [hc]
  change _≤(72*Parameters.m+12*Parameters.W+6)*parentCount q f R G S+
    (12*Parameters.W+3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
      CommonRankEdge.constructionConstant)*count q (longVolume f R G (S*q.w))+_
  dsimp only [childCount]
  nlinarith

end
end CodedSorting.CommonRecursiveExchange.Buffered
end Recursion

section GatherEffects
/-! Exact state transitions of the actual reconstruction instructions. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBufferedGather
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonBlockPair (Block BitIndex Selection)
open CommonPermutationPairs (width count address)
open CommonBufferedAllocation (bucketAddress)
open BitWordPacking Circuit
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V K L : ℕ}

def loaded (q : Configuration) (e : Fin V ≃ Fin K × Fin L) (arena : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q) : Store q :=
  if (e i).2.val%width q=0 then
    let block := disk (bucketAddress q arena L (e i).1 ((e i).2.val/width q))
    CommonBufferedBank.put q (e i).1 block {s with transfer:=block}
  else s

def assembled (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L) (arena : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q) : Store q :=
  assemble q hfit reader (e i).1 i.val (e i).2.val (loaded q e arena i s disk)

def stepStore (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L) (arena : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q) : Store q :=
  let t := assembled q hfit reader e arena i s disk
  if i.val%width q=width q-1 ∨ i.val+1=V then
    {t with transfer:=CommonBlockPair.buffer q reader t} else t

def stepDisk (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L) (arena target : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q) : Disk q :=
  if i.val%width q=width q-1 ∨ i.val+1=V then
    Function.update disk (address q target (i.val/width q))
      (CommonBlockPair.buffer q reader (assembled q hfit reader e arena i s disk))
  else disk

theorem fragment_run (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L) (arena target : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q) :
    (executeRaw q (fragment q hfit reader e arena target i) (machine q s disk)).1=
      machine q (stepStore q hfit reader e arena i s disk)
        (stepDisk q hfit reader e arena target i s disk) := by
  unfold fragment stepStore stepDisk assembled loaded
  split_ifs <;>
    simp only [CommonPermutationPairs.raw_append,List.nil_append,
      executeRaw,CommonBufferedBank.loadInstruction_step,assemble_step,write_run]
  all_goals rfl

theorem loaded_buffer (q : Configuration) (reader : Fin q.inventory.readers)
    (e : Fin V ≃ Fin K × Fin L) (arena : ℕ) (i : Fin V) (s : Store q) (disk : Disk q) :
    CommonBlockPair.buffer q reader (loaded q e arena i s disk)=
      CommonBlockPair.buffer q reader s := by
  unfold loaded
  split_ifs <;> rfl

theorem loaded_bank (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (e : Fin V ≃ Fin K × Fin L) (arena : ℕ) (i : Fin V) (s : Store q) (disk : Disk q) :
    (fun k => CommonBufferedBank.get q hfit k (loaded q e arena i s disk))=
      if (e i).2.val%width q=0 then
        Function.update (fun k => CommonBufferedBank.get q hfit k s) (e i).1
          (disk (bucketAddress q arena L (e i).1 ((e i).2.val/width q)))
      else (fun k => CommonBufferedBank.get q hfit k s) := by
  funext k
  unfold loaded
  split_ifs with h
  · by_cases hk : k=(e i).1
    · subst k; simp only [CommonBufferedBank.get_put_self,Function.update_self]
    · rw [CommonBufferedBank.get_put_ne q hfit _ _ hk,
        Function.update_of_ne hk,CommonBufferedBank.get_transfer]
  · rfl

theorem stepStore_bank (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L) (arena : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q) (k : Fin K) :
    CommonBufferedBank.get q hfit k (stepStore q hfit reader e arena i s disk)=
      CommonBufferedBank.get q hfit k (loaded q e arena i s disk) := by
  unfold stepStore
  split_ifs <;> rfl

theorem stepStore_buffer (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L) (arena : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q) :
    CommonBlockPair.buffer q reader (stepStore q hfit reader e arena i s disk)=
      CommonBlockPair.buffer q reader (assembled q hfit reader e arena i s disk) := by
  unfold stepStore
  split_ifs <;> rfl

theorem stepDisk_outside (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L) (arena target : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q)
    (ht : target+count q V≤q.N^q.exponent) (a : Fin (q.N^q.exponent))
    (ha : a.val<target ∨ target+count q V≤a.val) :
    stepDisk q hfit reader e arena target i s disk a=disk a := by
  unfold stepDisk
  split_ifs
  · apply Function.update_of_ne
    intro he
    subst a
    have hi := CommonPermutationPairs.bit_block_lt q i
    rw [CommonColumnSplit.address_val q target _ (by omega)] at ha
    rcases ha with ha|ha
    · exact (Nat.not_lt_of_ge (Nat.le_add_right target _)) ha
    · exact (Nat.not_le_of_lt (Nat.add_lt_add_left hi target)) ha
  · rfl

theorem stepDisk_at (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L) (arena target : ℕ)
    (i : Fin V) (s : Store q) (disk : Disk q)
    (ht : target+count q V≤q.N^q.exponent) (page : ℕ) (hp : page<count q V) :
    stepDisk q hfit reader e arena target i s disk (address q target page)=
      if (i.val%width q=width q-1 ∨ i.val+1=V) ∧ page=i.val/width q then
        CommonBlockPair.buffer q reader (assembled q hfit reader e arena i s disk)
      else disk (address q target page) := by
  unfold stepDisk
  by_cases hf : i.val%width q=width q-1 ∨ i.val+1=V
  · rw [if_pos hf]
    by_cases he : page=i.val/width q
    · subst page; simp only [Function.update_self,hf,true_and,if_pos]
    · have ha : address q target page≠address q target (i.val/width q) := by
        intro hh
        have hv := congrArg Fin.val hh
        have hi := CommonPermutationPairs.bit_block_lt q i
        rw [CommonColumnSplit.address_val q target _ (by omega),
          CommonColumnSplit.address_val q target _ (by omega)] at hv
        omega
      rw [Function.update_of_ne ha,if_neg (by tauto)]
  · rw [if_neg hf,if_neg (by tauto)]

end
end CodedSorting.CommonBufferedGather
end GatherEffects
