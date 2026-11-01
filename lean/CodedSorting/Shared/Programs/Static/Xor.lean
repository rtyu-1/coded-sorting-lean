import CodedSorting.Shared.Memory.BlockPair
import CodedSorting.Interchange.Framework.Columns.ColumnOperations
import CodedSorting.Shared.Memory.AllocatedDirectoryXor

/-! A public static program that XORs two block streams. Each block executes
one left read, one right read with a resident XOR, and one output write.
Either input may be the output itself; otherwise its allocated extent must
be disjoint. No input values or original disk are captured by the code. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace CodedSorting.CommonStaticXor
open WordControl CommonSortingNormalization CommonStaticSchedule BitWordPacking Circuit
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonBlockPair (Block buffer stash sourceRead targetWrite)
open PhysicalFileHandlesXor (xorBlock xorBlock_bits)
noncomputable section

abbrev address := CommonColumnSplit.address

def width (q : Configuration) := q.block*q.w

theorem width_pos (q : Configuration) : 0<width q :=
  Nat.mul_pos (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega)

def count (q : Configuration) (V : ℕ) := PhysicalStreamCursor.blockCount (width q) V

def readBit (q : Configuration) (disk : Disk q) (base i : ℕ) : Bit :=
  blockBits q.block q.w (disk (address q base (i/width q)))
    ⟨i%width q,Nat.mod_lt _ (width_pos q)⟩

def secondRead (q : Configuration) (reader : Fin q.inventory.readers)
    (right : Fin (q.N^q.exponent)) : Instruction q :=
  ⟨.read right (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    fun ram => let s := unpack ram; pack {s with transfer:=xorBlock (buffer q reader s) s.transfer}⟩

def blockCode (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target : Fin (q.N^q.exponent)) : List (Instruction q) :=
  [sourceRead q reader left,secondRead q reader right,targetWrite q target]

theorem secondRead_step (q : Configuration) (reader : Fin q.inventory.readers)
    (right : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (secondRead q reader right) (machine q s disk)=
      machine q {s with transfer:=xorBlock (buffer q reader s) (disk right)} disk := by
  simp only [secondRead,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,
    CommonLeafWindow.load_transfer,unpack_pack]
  rfl

theorem block_run (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q) :
    executeRaw q (blockCode q reader left right target) (machine q s disk)=
      (machine q {stash q reader (disk left) s with transfer:=xorBlock (disk left) (disk right)}
        (Function.update disk target (xorBlock (disk left) (disk right))),3) := by
  simp only [blockCode,executeRaw]
  rw [CommonBlockPair.sourceRead_step,secondRead_step,CommonBlockPair.targetWrite_step]
  simp only [CommonBlockPair.buffer_stash]
  rfl

theorem block_disk (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target : Fin (q.N^q.exponent)) (s : Machine q) :
    (executeRaw q (blockCode q reader left right target) s).1.disk=
      Function.update s.disk target (xorBlock (s.disk left) (s.disk right)) := by
  rw [←CommonBlockPair.machine_eta q s,block_run]
  rfl

theorem secondRead_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (right : Fin (q.N^q.exponent)) : RespectsPC q (secondRead q reader right) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [secondRead_step,CommonBlockPair.erasePC_machine]
  rfl

theorem block_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target : Fin (q.N^q.exponent)) :
    ∀ i∈blockCode q reader left right target,RespectsPC q i := by
  intro i hi
  simp only [blockCode,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with h|h|h
  · subst i; exact CommonBlockPair.sourceRead_respectsPC q reader left
  · subst i; exact secondRead_safe q reader right
  · subst i; exact CommonBlockPair.targetWrite_respectsPC q target

def blocks (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target : ℕ) : ℕ→ℕ→List (Instruction q)
  | _,0 => []
  | cursor,n+1 => blockCode q reader (address q left cursor) (address q right cursor)
      (address q target cursor) ++ blocks q reader left right target (cursor+1) n

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (V left right target : ℕ) : List (Instruction q) :=
  blocks q reader left right target 0 (count q V)

def xorDisk (q : Configuration) (left right target : ℕ) : ℕ→ℕ→Disk q→Disk q
  | _,0,disk => disk
  | cursor,n+1,disk => xorDisk q left right target (cursor+1) n
      (Function.update disk (address q target cursor)
        (xorBlock (disk (address q left cursor)) (disk (address q right cursor))))

theorem blocks_length (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target cursor n : ℕ) :
    (blocks q reader left right target cursor n).length=3*n := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih => simp only [blocks,List.length_append,blockCode,List.length_cons,List.length_nil,ih]; omega

theorem blocks_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target cursor n : ℕ) : cost q (blocks q reader left right target cursor n)=3*n := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih =>
    change cost q (sourceRead q reader _ :: secondRead q reader _ :: targetWrite q _ ::
      blocks q reader left right target (cursor+1) n)=_
    simp only [cost,sourceRead,secondRead,targetWrite,Normalization.transferCost,ih]
    omega

theorem blocks_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target cursor n : ℕ) :
    ∀ i∈blocks q reader left right target cursor n,RespectsPC q i := by
  induction n generalizing cursor with
  | zero => simp [blocks]
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact block_safe q reader _ _ _ i hi
    · exact ih (cursor+1) i hi

theorem blocks_disk (q : Configuration) (reader : Fin q.inventory.readers)
    (left right target cursor n : ℕ) (s : Machine q) :
    (executeRaw q (blocks q reader left right target cursor n) s).1.disk=
      xorDisk q left right target cursor n s.disk := by
  induction n generalizing cursor s with
  | zero => rfl
  | succ n ih =>
    simp only [blocks,blockCode,List.cons_append,List.nil_append,executeRaw]
    rw [←CommonBlockPair.machine_eta q s,CommonBlockPair.sourceRead_step,secondRead_step,
      CommonBlockPair.targetWrite_step]
    simp only [CommonBlockPair.buffer_stash]
    rw [ih]
    rfl

theorem disk_outside (q : Configuration) (left right target cursor n : ℕ)
    (disk : Disk q) (hfit : target+cursor+n≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<target+cursor ∨ target+cursor+n≤a.val) :
    xorDisk q left right target cursor n disk a=disk a := by
  induction n generalizing cursor disk with
  | zero => rfl
  | succ n ih =>
    rw [xorDisk,ih (cursor+1) _ (by omega) (by omega)]
    apply Function.update_of_ne
    intro he
    have hv:=congrArg Fin.val he
    rw [CommonColumnSplit.address_val q target cursor (by omega)] at hv
    rcases ha with ha|ha <;> omega

/-- Each source either is the output itself or has a disjoint allocated extent. -/
def Compatible (source target K : ℕ) : Prop :=
  source=target ∨ source+K≤target ∨ target+K≤source

theorem cross_ne (q : Configuration) (source target K : ℕ)
    (hs : source+K≤q.N^q.exponent) (ht : target+K≤q.N^q.exponent)
    (hsep : Compatible source target K) (i j : ℕ) (hi : i<K) (hj : j<K) (hne : i≠j) :
    address q source i≠address q target j := by
  intro h
  have hv:=congrArg Fin.val h
  rw [CommonColumnSplit.address_val q source i (by omega),
    CommonColumnSplit.address_val q target j (by omega)] at hv
  rcases hsep with h|h|h <;> omega

theorem disk_at (q : Configuration) (left right target K cursor n : ℕ)
    (disk : Disk q) (hbound : cursor+n≤K) (ht : target+K≤q.N^q.exponent)
    (hl : ∀ i j,i<K→j<K→i≠j→address q left i≠address q target j)
    (hr : ∀ i j,i<K→j<K→i≠j→address q right i≠address q target j)
    (i : ℕ) (hi : cursor ≤ i ∧ i < cursor+n) :
    xorDisk q left right target cursor n disk (address q target i)=
      xorBlock (disk (address q left i)) (disk (address q right i)) := by
  induction n generalizing cursor disk with
  | zero => omega
  | succ n ih =>
    rw [xorDisk]
    by_cases he : i=cursor
    · subst i
      rw [disk_outside q left right target (cursor+1) n _ (by omega)
        (address q target cursor) (Or.inl (by
          rw [CommonColumnSplit.address_val q target cursor (by omega)]
          omega)),Function.update_self]
    · rw [ih (cursor+1) _ (by omega) ⟨by omega,by omega⟩]
      rw [Function.update_of_ne (hl i cursor (by omega) (by omega) he),
        Function.update_of_ne (hr i cursor (by omega) (by omega) he)]

@[simp] theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (V left right target : ℕ) : (code q reader V left right target).length=3*count q V :=
  blocks_length q reader left right target 0 (count q V)

@[simp] theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (V left right target : ℕ) : cost q (code q reader V left right target)=3*count q V :=
  blocks_cost q reader left right target 0 (count q V)

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (V left right target : ℕ) : ∀ i∈code q reader V left right target,RespectsPC q i :=
  blocks_safe q reader left right target 0 (count q V)

/-- Actual sequential reads and writes give the XOR of the two original
input streams, including in-place updates when either source is the target. -/
theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (V left right target : ℕ) (s : Machine q)
    (hlfit : left+count q V≤q.N^q.exponent) (hrfit : right+count q V≤q.N^q.exponent)
    (htfit : target+count q V≤q.N^q.exponent)
    (hlsep : Compatible left target (count q V)) (hrsep : Compatible right target (count q V))
    (i : Fin V) :
    readBit q (executeRaw q (code q reader V left right target) s).1.disk target i.val=
      readBit q s.disk left i.val+readBit q s.disk right i.val := by
  have hi : i.val/width q<count q V := by
    apply (PhysicalStreamCursor.cursor_live_iff (width q) V _ (width_pos q)).2
    exact (Nat.div_mul_le_self _ _).trans_lt i.isLt
  unfold code readBit
  rw [blocks_disk,disk_at q left right target (count q V) 0 (count q V) s.disk
    (by omega) htfit (cross_ne q left target _ hlfit htfit hlsep)
    (cross_ne q right target _ hrfit htfit hrsep) _ ⟨Nat.zero_le _,by omega⟩,
    xorBlock_bits]

theorem raw_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (V left right target : ℕ) (s : Machine q) (htfit : target+count q V≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<target ∨ target+count q V≤a.val) :
    (executeRaw q (code q reader V left right target) s).1.disk a=s.disk a := by
  unfold code
  rw [blocks_disk]
  exact disk_outside q left right target 0 (count q V) s.disk (by simpa using htfit) a (by simpa using ha)

/-- One fixed policy, actual output and halt, with every disk transfer
counted and the existing finite resident-memory bound. -/
theorem compiled (q : Configuration) (reader : Fin q.inventory.readers)
    (V left right target : ℕ) (s : Machine q)
    (hlfit : left+count q V≤q.N^q.exponent) (hrfit : right+count q V≤q.N^q.exponent)
    (htfit : target+count q V≤q.N^q.exponent)
    (hlsep : Compatible left target (count q V)) (hrsep : Compatible right target (count q V))
    (hsize : 3*count q V≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let program := code q reader V left right target
    let result := ControlledNormalization.runLogical (policy q program) program.length s
    (∀ i : Fin V,readBit q result.1.disk target i.val=
      readBit q s.disk left i.val+readBit q s.disk right i.val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q V≤a.val →
      result.1.disk a=s.disk a) ∧
    policy q program result.1.ram=none ∧ result.2=3*count q V ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (code q reader V left right target)
    (by simpa only [code_length] using hsize) (code_safe q reader V left right target) s hpc
  refine ⟨?_,?_,hh,?_,hm⟩
  · intro i
    rw [hd]
    exact raw_correct q reader V left right target s hlfit hrfit htfit hlsep hrsep i
  · intro a ha
    rw [hd]
    exact raw_outside q reader V left right target s htfit a ha
  · simpa only [code_cost] using hc

end
end CodedSorting.CommonStaticXor
