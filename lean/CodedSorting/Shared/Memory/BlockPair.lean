import CodedSorting.Shared.Programs.Static.Fusion
import CodedSorting.Shared.Words.WordConvention

/-! Three real I/O instructions transfer a chosen set of bits from one
source block to one target block. Both blocks are read before the write.
The static selection map is program text; the payload comes only from
the current finite disk through the existing reader and transfer banks. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace CodedSorting.CommonBlockPair
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
open BitWordPacking Circuit
noncomputable section

abbrev Block (q : Configuration) := Words q.block q.w
abbrev BitIndex (q : Configuration) := Fin (q.block*q.w)
abbrev Selection (q : Configuration) := BitIndex q → Option (BitIndex q)

def blend (q : Configuration) (select : Selection q) (source target : Block q) : Block q :=
  (blockBits q.block q.w).symm (fun i => match select i with
    | none => blockBits q.block q.w target i
    | some j => blockBits q.block q.w source j)

@[simp] theorem blend_bits (q : Configuration) (select : Selection q)
    (source target : Block q) (i : BitIndex q) :
    blockBits q.block q.w (blend q select source target) i=
      match select i with
      | none => blockBits q.block q.w target i
      | some j => blockBits q.block q.w source j := by
  simp only [blend,Equiv.apply_symm_apply]

def buffer (q : Configuration) (reader : Fin q.inventory.readers) (s : Store q) : Block q :=
  CommonSortingNormalizationStreams.payload (s.readers reader).resident

def stash (q : Configuration) (reader : Fin q.inventory.readers)
    (block : Block q) (s : Store q) : Store q :=
  {s with readers := Function.update s.readers reader {(s.readers reader) with
    resident := Fin.append (Fin.append block
      (CommonSortingNormalizationStreams.lengthWords (s.readers reader).resident))
      (CommonSortingNormalizationStreams.cursorWords (s.readers reader).resident)}}

@[simp] theorem buffer_stash (q : Configuration) (reader : Fin q.inventory.readers)
    (block : Block q) (s : Store q) : buffer q reader (stash q reader block s)=block := by
  funext i
  simp [buffer,stash,CommonSortingNormalizationStreams.payload]

def sourceRead (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin (q.N^q.exponent)) : Instruction q :=
  ⟨.read source (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    fun ram => let s := unpack ram; pack (stash q reader s.transfer s)⟩

def targetRead (q : Configuration) (reader : Fin q.inventory.readers)
    (target : Fin (q.N^q.exponent)) (select : Selection q) : Instruction q :=
  ⟨.read target (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    fun ram => let s := unpack ram; pack {s with transfer:=blend q select (buffer q reader s) s.transfer}⟩

def targetWrite (q : Configuration) (target : Fin (q.N^q.exponent)) : Instruction q :=
  ⟨.write target (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),id⟩

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q) : List (Instruction q) :=
  [sourceRead q reader source,targetRead q reader target select,targetWrite q target]

@[simp] theorem length_code (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q) :
    (code q reader source target select).length=3 := rfl

@[simp] theorem cost_code (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q) :
    cost q (code q reader source target select)=3 := rfl

theorem sourceRead_step (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (sourceRead q reader source) (machine q s disk)=
      machine q (stash q reader (disk source) {s with transfer:=disk source}) disk := by
  simp only [sourceRead,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,
    CommonLeafWindow.load_transfer,unpack_pack]

theorem targetRead_step (q : Configuration) (reader : Fin q.inventory.readers)
    (target : Fin (q.N^q.exponent)) (select : Selection q) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (targetRead q reader target select) (machine q s disk)=
      machine q {s with transfer:=blend q select (buffer q reader s) (disk target)} disk := by
  simp only [targetRead,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,
    CommonLeafWindow.load_transfer,unpack_pack]
  rfl

theorem targetWrite_step (q : Configuration) (target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (targetWrite q target) (machine q s disk)=
      machine q s (Function.update disk target s.transfer) := by
  simp only [targetWrite,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,
    CommonLeafWindow.slice_transfer,id_eq]

/-- The entire fragment on the actual finite disk. Source and target are
allowed to coincide: the two reads precede the only write. -/
theorem raw_run (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q)
    (s : Store q) (disk : Disk q) :
    executeRaw q (code q reader source target select) (machine q s disk)=
      (machine q {stash q reader (disk source) s with
          transfer:=blend q select (disk source) (disk target)}
        (Function.update disk target (blend q select (disk source) (disk target))),3) := by
  simp only [code,executeRaw]
  rw [sourceRead_step,targetRead_step,targetWrite_step]
  simp only [buffer_stash]
  rfl

theorem raw_bits (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q)
    (s : Store q) (disk : Disk q) (i : BitIndex q) :
    blockBits q.block q.w
      ((executeRaw q (code q reader source target select) (machine q s disk)).1.disk target) i=
      match select i with
      | none => blockBits q.block q.w (disk target) i
      | some j => blockBits q.block q.w (disk source) j := by
  rw [raw_run]
  simp only [machine,Function.update_self,blend_bits]

theorem raw_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q)
    (s : Store q) (disk : Disk q) (a : Fin (q.N^q.exponent)) (ha : a≠target) :
    (executeRaw q (code q reader source target select) (machine q s disk)).1.disk a=disk a := by
  rw [raw_run]
  exact Function.update_of_ne ha _ _


@[simp] theorem erasePC_machine (q : Configuration) (s : Store q) (disk : Disk q) :
    erasePC q (machine q s disk)=
      machine q {s with top:=PhysicalStreamCursor.encodeNat q.digits q.w 0} disk := by
  simp only [erasePC,setPC,machine,unpack_pack]

theorem machine_eta (q : Configuration) (s : Machine q) :
    machine q (unpack s.ram) s.disk=s := by
  cases s
  simp only [machine,CommonLeafWindow.pack_unpack]

/-- Disk-only form for concatenating fragments without exposing their
private resident scratch contents in the outer invariant. -/
theorem raw_disk (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q) (s : Machine q) :
    (executeRaw q (code q reader source target select) s).1.disk=
      Function.update s.disk target (blend q select (s.disk source) (s.disk target)) := by
  rw [←machine_eta q s,raw_run]
  rfl

theorem raw_bits_machine (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q) (s : Machine q) (i : BitIndex q) :
    blockBits q.block q.w ((executeRaw q (code q reader source target select) s).1.disk target) i=
      match select i with
      | none => blockBits q.block q.w (s.disk target) i
      | some j => blockBits q.block q.w (s.disk source) j := by
  rw [raw_disk,Function.update_self,blend_bits]


theorem respectsPC_of_commutes (q : Configuration) (i : Instruction q)
    (h : ∀ s : Machine q,erasePC q (ControlledNormalization.logicalStep i s)=
      ControlledNormalization.logicalStep i (erasePC q s)) : RespectsPC q i := by
  intro s t hst
  rw [h,h,hst]

theorem sourceRead_respectsPC (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin (q.N^q.exponent)) : RespectsPC q (sourceRead q reader source) := by
  apply respectsPC_of_commutes
  intro s
  rw [←machine_eta q s]
  simp only [sourceRead_step,erasePC_machine]
  rfl

theorem targetRead_respectsPC (q : Configuration) (reader : Fin q.inventory.readers)
    (target : Fin (q.N^q.exponent)) (select : Selection q) :
    RespectsPC q (targetRead q reader target select) := by
  apply respectsPC_of_commutes
  intro s
  rw [←machine_eta q s]
  simp only [targetRead_step,erasePC_machine]
  rfl

theorem targetWrite_respectsPC (q : Configuration) (target : Fin (q.N^q.exponent)) :
    RespectsPC q (targetWrite q target) := by
  apply respectsPC_of_commutes
  intro s
  rw [←machine_eta q s]
  simp only [targetWrite_step,erasePC_machine]

theorem safe (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q) :
    ∀ i∈code q reader source target select,RespectsPC q i := by
  intro i hi
  simp only [code,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with h|h|h
  · subst i; exact sourceRead_respectsPC q reader source
  · subst i; exact targetRead_respectsPC q reader target select
  · subst i; exact targetWrite_respectsPC q target

/-- The statically indexed policy performs the same concrete block update
and halts after three instructions; all three disk transfers are counted. -/
theorem compiled (q : Configuration) (reader : Fin q.inventory.readers)
    (source target : Fin (q.N^q.exponent)) (select : Selection q)
    (s : Store q) (disk : Disk q) (hsize : 3≤q.N^q.exponent)
    (hpc : pc q (pack s)=0) :
    let program := code q reader source target select
    let result := ControlledNormalization.runLogical (CommonStaticSchedule.policy q program)
      3 (machine q s disk)
    result.1.disk=Function.update disk target (blend q select (disk source) (disk target)) ∧
    CommonStaticSchedule.policy q program result.1.ram=none ∧ result.2=3 ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (code q reader source target select)
    hsize (safe q reader source target select) (machine q s disk) hpc
  rw [raw_run] at hd
  exact ⟨hd,hh,hc,hm⟩

end
end CodedSorting.CommonBlockPair
