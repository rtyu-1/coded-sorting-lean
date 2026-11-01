import CodedSorting.Sorting.Bounds.SortingResourceBudget
import CodedSorting.Sorting.Resources.Framework.NormalizationStreams
import CodedSorting.Shared.Memory.PhysicalLevelFrameGeneral
import CodedSorting.Sorting.Local.Framework.ResidentLeafSort

section Normalization
/-! Explicit source-RAM slots inside the actual common normalization
controller. Three call frames and directories coexist with the addressed
stream buffers and the 512H-record resident leaf. No type in this resident
layout contains an external file or an unbounded runtime natural number. -/
set_option autoImplicit false
namespace CodedSorting.CommonSortingNormalization
open WordControl SortingResourceBudget
variable {v : Inventory} {H b d w : ℕ}

def inputCells (b d : ℕ) := d+(d+(b+d+d))
def outputCells (b d : ℕ) := d+(b+d+d)

def inputWords (s : CommonSortingNormalizationStreams.InputState b d w) : Words (inputCells b d) w :=
  Fin.append s.base (Fin.append s.records s.resident)
def outputWords (s : CommonSortingNormalizationStreams.OutputState b d w) : Words (outputCells b d) w :=
  Fin.append s.base s.resident

def first {a z w : ℕ} (ram : Words (a+z) w) : Words a w := fun i => ram (i.castAdd z)
def rest {a z w : ℕ} (ram : Words (a+z) w) : Words z w := fun i => ram (i.natAdd a)
@[simp] theorem first_append {a z w : ℕ} (x : Words a w) (y : Words z w) :
    first (Fin.append x y)=x := by funext i; exact Fin.append_left x y i
@[simp] theorem rest_append {a z w : ℕ} (x : Words a w) (y : Words z w) :
    rest (Fin.append x y)=y := by funext i; exact Fin.append_right x y i

def inputOfWords (ram : Words (inputCells b d) w) : CommonSortingNormalizationStreams.InputState b d w :=
  ⟨first ram,first (rest ram),rest (rest ram)⟩
def outputOfWords (ram : Words (outputCells b d) w) : CommonSortingNormalizationStreams.OutputState b d w :=
  ⟨first ram,rest ram⟩
@[simp] theorem input_roundtrip (s : CommonSortingNormalizationStreams.InputState b d w) :
    inputOfWords (inputWords s)=s := by cases s; simp [inputOfWords,inputWords]
@[simp] theorem output_roundtrip (s : CommonSortingNormalizationStreams.OutputState b d w) :
    outputOfWords (outputWords s)=s := by cases s; simp [outputOfWords,outputWords]

def family {k a w : ℕ} (x : Fin k → Words a w) : Words (k*a) w :=
  fun i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
def familyOfWords {k a w : ℕ} (ram : Words (k*a) w) : Fin k → Words a w :=
  fun i j => ram (finProdFinEquiv (i,j))
@[simp] theorem family_roundtrip {k a w : ℕ} (x : Fin k → Words a w) :
    familyOfWords (family x)=x := by funext i j; simp [familyOfWords,family]

structure SourceState (v : Inventory) (H b d w : ℕ) where
  leaf : ResidentLeafSort.RAM (512*H) d w
  readers : Fin v.readers → CommonSortingNormalizationStreams.InputState b d w
  writers : Fin v.writers → CommonSortingNormalizationStreams.OutputState b d w
  transfer : Words b w
  scalars : Words (1+d) w
  directories : Fin 3 → Words ((2*v.keys)*d) w
  shapes : Fin 3 → Words (13*d) w
  top : Words d w
  pcs : Fin 3 → Words v.pc w

def tailCells (v : Inventory) (b d : ℕ) : ℕ :=
  v.readers*inputCells b d+(v.writers*outputCells b d+
    (b+((1+d)+(3*((2*v.keys)*d)+(3*(13*d)+(d+3*v.pc))))))
def sourceCells (v : Inventory) (H b d : ℕ) : ℕ :=
  ResidentLeafSort.residentWords (512*H) d+tailCells v b d

def pack (s : SourceState v H b d w) : Words (sourceCells v H b d) w :=
  Fin.append s.leaf (Fin.append (family (fun i => inputWords (s.readers i)))
    (Fin.append (family (fun i => outputWords (s.writers i))) (Fin.append s.transfer
      (Fin.append s.scalars (Fin.append (family s.directories)
        (Fin.append (family s.shapes) (Fin.append s.top (family s.pcs))))))))

def unpack (ram : Words (sourceCells v H b d) w) : SourceState v H b d w :=
  ⟨first ram,
   fun i => inputOfWords (familyOfWords (first (rest ram)) i),
   fun i => outputOfWords (familyOfWords (first (rest (rest ram))) i),
   first (rest (rest (rest ram))),
   first (rest (rest (rest (rest ram)))),
   familyOfWords (first (rest (rest (rest (rest (rest ram)))))),
   familyOfWords (first (rest (rest (rest (rest (rest (rest ram))))))),
   first (rest (rest (rest (rest (rest (rest (rest ram))))))),
   familyOfWords (rest (rest (rest (rest (rest (rest (rest (rest ram))))))))⟩

@[simp] theorem unpack_pack (s : SourceState v H b d w) : unpack (pack s)=s := by
  cases s
  simp only [unpack,pack,first_append,rest_append,family_roundtrip,input_roundtrip,output_roundtrip]

theorem pack_injective : Function.Injective (@pack v H b d w) := by
  intro s t h
  simpa only [unpack_pack] using congrArg unpack h

theorem sourceCells_eq (v : Inventory) (H b d : ℕ) :
    sourceCells v H b d=sourceWords v H b d := by
  unfold sourceCells tailCells inputCells outputCells ResidentLeafSort.residentWords
    sourceWords metadata
  ring

/-- The existing exact leaf CPU is installed as a local map of its existing
prefix of the source RAM. All other resident slots are preserved. -/
def leafCpu (hw : 2 ≤ w) (ram : Words (sourceCells v H b d) w) : Words (sourceCells v H b d) w :=
  Fin.append (ResidentLeafSort.cpu hw (first ram)) (rest ram)

@[simp] theorem leafCpu_pack (hw : 2 ≤ w) (s : SourceState v H b d w) :
    leafCpu hw (pack s)=pack {s with leaf:=ResidentLeafSort.cpu hw s.leaf} := by
  simp only [leafCpu,pack,first_append,rest_append]

/-- Three original words per active record, including both sentinels, with
one counted length header. This is precisely the previous Columnsort leaf. -/
theorem leafCpu_exact (hw : 2 ≤ w) (s : SourceState v H b d w) :
    let out := (unpack (leafCpu hw (pack s))).leaf
    (fun i : Fin (ResidentLeafSort.count s.leaf) => KeyRecordWords.abstract
      (ResidentLeafSort.recordAt out
        ⟨i.val,i.isLt.trans_le (ResidentLeafSort.count_le s.leaf)⟩)) =
      Columnsort.sortColumn (KeyRecordWords.abstract ∘ ResidentLeafSort.active s.leaf) := by
  rw [leafCpu_pack,unpack_pack]
  exact ResidentLeafSort.abstract_leaf_exact hw s.leaf

def leafInstruction {R : ℕ} (hw : 2 ≤ w) :
    ControlledNormalization.Instruction (sourceCells v H b d) b R (Word w) :=
  ⟨.localOp (leafCpu hw),id⟩

theorem leafInstruction_same_ram {R : ℕ} (hw : 2 ≤ w)
    (s : Normalization.LogicalState (sourceCells v H b d) b R (Word w)) :
    (ControlledNormalization.logicalStep (leafInstruction hw) s).ram=leafCpu hw s.ram ∧
    (ControlledNormalization.logicalStep (leafInstruction hw) s).disk=s.disk ∧
    Normalization.transferCost (leafInstruction (R:=R) (v:=v) (H:=H) (b:=b) (d:=d) hw).operation=0 :=
  ⟨rfl,rfl,rfl⟩

/-- Public machine parameters; live file sizes remain counted input words.
All reserve constants are independent of payloads and input length. -/
structure Configuration where
  inventory : Inventory
  N : ℕ
  M : ℕ
  B : ℕ
  w : ℕ
  c : ℕ
  exponent : ℕ
  input_large : 2 ≤ N
  memory_input : M ≤ N
  block_pos : 0 < B
  block_memory : 2*B ≤ M
  exponent_pos : 1 ≤ exponent
  word_convention : WordConvention.Covers N w c
  memory_large : (reserve inventory c (digits c exponent))^2 ≤ M

def Configuration.digits (q : Configuration) := SortingResourceBudget.digits q.c q.exponent
def Configuration.height (q : Configuration) := SortingResourceBudget.H q.inventory q.c q.digits q.M
def Configuration.block (q : Configuration) := SortingResourceBudget.block q.inventory q.c q.digits q.B
def Configuration.ramWords (q : Configuration) := sourceCells q.inventory q.height q.block q.digits

abbrev SourcePolicy (q : Configuration) :=
  ControlledNormalization.Policy q.ramWords q.block (q.N^q.exponent) (Word q.w)

theorem Configuration.word_width (q : Configuration) : 3 ≤ q.w :=
  large_instance_width q.inventory q.c q.digits q.M q.N q.w q.input_large
    q.memory_input q.memory_large q.word_convention

def program (q : Configuration) (policy : SourcePolicy q) :
    CommonNormalizationController.Program q.ramWords (q.N^q.exponent)
      q.B q.block q.digits q.w where
  positive_region := pow_pos (by have := q.input_large; omega) _
  positive_block := q.block_pos
  block_ratio := Normalization.logical_block_le_physical q.B _ q.block_pos
  counter_capacity := Nat.lt_of_succ_le
    (WordConvention.polynomial_capacity q.N q.w q.c q.exponent q.input_large q.word_convention)
  phase_capacity := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) q.word_width
    norm_num at h
    exact h
  padding := 0
  policy := policy

abbrev MachineState (q : Configuration) :=
  CommonNormalizationController.State q.ramWords (q.N^q.exponent) q.B q.block q.digits q.w

/-- These are the actual fields of MachineState, plus its separately
reserved address port. The source RAM is the injective pack above. -/
abbrev ResidentIndex (q : Configuration) :=
  (Fin q.ramWords ⊕ Fin q.B) ⊕
    ((Fin q.block ⊕ Fin q.digits) ⊕
      ((Fin q.digits ⊕ Fin q.digits) ⊕ (Fin 2 ⊕ Fin (q.digits+1))))

def resident (q : Configuration) (s : MachineState q) (port : Words (q.digits+1) q.w) :
    ResidentIndex q → Word q.w
  | .inl (.inl i) => s.ram i
  | .inl (.inr i) => s.buffer i
  | .inr (.inl (.inl i)) => s.scratch i
  | .inr (.inl (.inr i)) => s.counter i
  | .inr (.inr (.inl (.inl i))) => s.inputCount i
  | .inr (.inr (.inl (.inr i))) => s.outputCount i
  | .inr (.inr (.inr (.inl i))) => if i.val=0 then s.phase else s.stage
  | .inr (.inr (.inr (.inr i))) => port i

theorem resident_memory (q : Configuration) : Fintype.card (ResidentIndex q) ≤ q.M := by
  have h := (resident_bound q.inventory q.c q.digits q.M q.B q.memory_large q.block_memory).1
  simp only [ResidentIndex,Fintype.card_sum,Fintype.card_fin]
  change sourceCells q.inventory q.height q.block q.digits+q.B+
    (q.block+q.digits+(q.digits+q.digits+(2+(q.digits+1)))) ≤ q.M
  rw [sourceCells_eq]
  change sourceWords q.inventory q.height q.block q.digits+q.B+q.block+4*q.digits+3 ≤ q.M at h
  omega

theorem source_memory (q : Configuration) : q.ramWords ≤ q.M/4 := by
  unfold Configuration.ramWords
  rw [sourceCells_eq]
  exact (resident_bound q.inventory q.c q.digits q.M q.B q.memory_large q.block_memory).2

theorem normalized_ratio (q : Configuration) : q.inventory.ratio*q.block ≤ q.height :=
  (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
    (by have := q.block_memory; omega)).2.2

theorem disk_polynomial (q : Configuration) :
    Fintype.card (CommonNormalizationController.Address (q.N^q.exponent)) ≤ q.N^(q.exponent+2) := by
  simpa only [CommonNormalizationController.Address,Fintype.card_sum,Fintype.card_fin] using
    common_disk_polynomial q.N q.exponent q.input_large

/-- The already allocated full address, including its bank selector, is
encoded by the actual controller's address codec in the original word type. -/
theorem address_decodes (q : Configuration) (policy : SourcePolicy q)
    (a : CommonNormalizationController.Address (q.N^q.exponent)) :
    decodeWords (CommonNormalizationController.addressWords (d:=q.digits) (w:=q.w) a)=
      (CommonNormalizationController.physicalAddress a).val :=
  CommonNormalizationController.addressWords_decode (program q policy) a

/-- Initialization consumes counted WordConvention encodings for both live
lengths. The parameter is no longer a free runtime natural in the program. -/
def initialState (q : Configuration) (policy : SourcePolicy q)
    (s : SourceState q.inventory q.height q.block q.digits q.w)
    (nIn : Fin (q.N^q.exponent+1)) (nOut : Fin (q.N^q.exponent))
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  CommonNormalizationController.initial (program q policy) (pack s)
    (WordConvention.encode q.N q.w q.c q.exponent q.input_large q.word_convention nIn)
    (WordConvention.encode q.N q.w q.c q.exponent q.input_large q.word_convention nOut.castSucc)
    disk

theorem initialize_sizes (q : Configuration) (policy : SourcePolicy q)
    (s : SourceState q.inventory q.height q.block q.digits q.w)
    (nIn : Fin (q.N^q.exponent+1)) (nOut : Fin (q.N^q.exponent))
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) :
    CommonNormalizationController.inputSize (initialState q policy s nIn nOut disk)=nIn.val ∧
    CommonNormalizationController.outputSize (initialState q policy s nIn nOut disk)=nOut.val ∧
    unpack (initialState q policy s nIn nOut disk).ram=s := by
  simp only [initialState,CommonNormalizationController.initial,
    CommonNormalizationController.inputSize,CommonNormalizationController.outputSize,
    WordConvention.decode_encode,Fin.coe_castSucc,unpack_pack]
  exact ⟨Nat.min_eq_left (by have := nIn.isLt; omega),
    Nat.min_eq_left (by have := nOut.isLt; omega),True.intro⟩

theorem leaf_header_capacity (q : Configuration) : 512*q.height+1 ≤ (2^q.w)^q.digits := by
  have hC : 512 ≤ reserve q.inventory q.c q.digits := by
    have hh := (reserve_bounds q.inventory q.c q.digits).1
    unfold payloadCoefficient at hh
    omega
  have hmul := Nat.mul_le_mul_right q.height hC
  have hdiv : q.height*reserve q.inventory q.c q.digits ≤ q.M := Nat.div_mul_le_self _ _
  have hcap : 512*q.height ≤ q.N := by nlinarith [q.memory_input]
  have hpow : q.N ≤ q.N^q.exponent := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by have := q.input_large; omega : 0 < q.N)
      q.exponent_pos
  exact (Nat.add_le_add_right (hcap.trans hpow) 1).trans
    (WordConvention.polynomial_capacity q.N q.w q.c q.exponent q.input_large q.word_convention)

def initializeLeaf (q : Configuration) (n : Fin (512*q.height+1))
    (records : Fin (512*q.height) → KeyRecordWords.Record q.w) : ResidentLeafSort.RAM (512*q.height) q.digits q.w :=
  ResidentLeafSort.initializeBank (512*q.height) q.digits q.w (by have := q.word_width; omega)
    (leaf_header_capacity q) n records

theorem initializeLeaf_count (q : Configuration) (n : Fin (512*q.height+1))
    (records : Fin (512*q.height) → KeyRecordWords.Record q.w) :
    ResidentLeafSort.count (initializeLeaf q n records)=n.val :=
  ResidentLeafSort.count_initializeBank _ _ _ _ _ _ _

end CodedSorting.CommonSortingNormalization
end Normalization

section NormalizationFrames
/-! Actual handle-directory and saved-parent codecs in the source RAM
slots already charged by the common controller. All three frame banks are
resident concurrently; no extra frame is allocated by these local maps. -/
set_option autoImplicit false
namespace CodedSorting.CommonSortingNormalization
open WordControl SortingResourceBudget
noncomputable section

abbrev FileDirectory (q : Configuration) :=
  PhysicalFileHandles.Directory q.N q.exponent (Fin q.inventory.keys)

def directoryBank (q : Configuration) (dir : FileDirectory q) :
    Words ((2*q.inventory.keys)*q.digits) q.w :=
  (PhysicalFileHandles.directoryWords q.w q.c q.input_large q.word_convention dir) ∘
    (Fin.cast (by simp only [Fintype.card_fin]; rfl))

theorem directoryBank_injective (q : Configuration) : Function.Injective (directoryBank q) := by
  intro a b h
  apply PhysicalFileHandles.directoryWords_injective q.w q.c q.input_large q.word_convention
  funext i
  exact congrFun h (Fin.cast (by simp only [Fintype.card_fin]; rfl) i)

def installDirectory (q : Configuration)
    (s : SourceState q.inventory q.height q.block q.digits q.w)
    (slot : Fin 3) (dir : FileDirectory q) : SourceState q.inventory q.height q.block q.digits q.w :=
  {s with directories:=Function.update s.directories slot (directoryBank q dir)}

@[simp] theorem installed_directory (q : Configuration)
    (s : SourceState q.inventory q.height q.block q.digits q.w)
    (slot : Fin 3) (dir : FileDirectory q) :
    (unpack (pack (installDirectory q s slot dir))).directories slot=directoryBank q dir := by
  simp only [unpack_pack,installDirectory,Function.update_self]

/-- The source bank contains exactly the unchanged code used by the
real stack push/pop implementation, split over its shape/directory/PC slots. -/
theorem frame_size (q : Configuration) (length : ℕ)
    (hp : q.inventory.pc=Nat.clog 2 (PhysicalLevelFrame.states length+1)) :
    PhysicalLevelFrameGeneral.words (2*q.inventory.keys) q.exponent length q.c =
      (13*q.digits+(2*q.inventory.keys)*q.digits)+q.inventory.pc := by
  unfold PhysicalLevelFrameGeneral.words Configuration.digits SortingResourceBudget.digits
  rw [hp]
  ring

def frameWords (q : Configuration) (length : ℕ)
    (hp : q.inventory.pc=Nat.clog 2 (PhysicalLevelFrame.states length+1))
    (s : SourceState q.inventory q.height q.block q.digits q.w) (slot : Fin 3) :
    Words (PhysicalLevelFrameGeneral.words (2*q.inventory.keys) q.exponent length q.c) q.w :=
  fun i => Fin.append (Fin.append (s.shapes slot) (s.directories slot)) (s.pcs slot)
    (Fin.cast (frame_size q length hp) i)

def installFrame (q : Configuration) (length : ℕ)
    (hp : q.inventory.pc=Nat.clog 2 (PhysicalLevelFrame.states length+1))
    (s : SourceState q.inventory q.height q.block q.digits q.w) (slot : Fin 3)
    (frame : PhysicalLevelFrame.Saved (2*q.inventory.keys) q.N q.exponent length) :
    SourceState q.inventory q.height q.block q.digits q.w :=
  let encoded := PhysicalLevelFrameGeneral.encode q.input_large q.word_convention frame
  let joined : Words ((13*q.digits+(2*q.inventory.keys)*q.digits)+q.inventory.pc) q.w :=
    fun i => encoded (Fin.cast (frame_size q length hp).symm i)
  {s with
    shapes:=Function.update s.shapes slot (first (first joined))
    directories:=Function.update s.directories slot (rest (first joined))
    pcs:=Function.update s.pcs slot (rest joined)}

@[simp] theorem append_first_rest {a z w : ℕ} (ram : Words (a+z) w) :
    Fin.append (first ram) (rest ram)=ram := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left,first]
  · intro j
    simp only [Fin.append_right,rest]

@[simp] theorem frameWords_installFrame (q : Configuration) (length : ℕ)
    (hp : q.inventory.pc=Nat.clog 2 (PhysicalLevelFrame.states length+1))
    (s : SourceState q.inventory q.height q.block q.digits q.w) (slot : Fin 3)
    (frame : PhysicalLevelFrame.Saved (2*q.inventory.keys) q.N q.exponent length) :
    frameWords q length hp (installFrame q length hp s slot frame) slot =
      PhysicalLevelFrameGeneral.encode q.input_large q.word_convention frame := by
  unfold installFrame
  dsimp only
  unfold frameWords
  simp only [Function.update_self,append_first_rest]
  rfl

/-- Recovery uses the existing real stack decoder on the actual packed
source RAM, not a saved Lean value of the parent frame. -/
theorem frame_recovers (q : Configuration) (length : ℕ)
    (hp : q.inventory.pc=Nat.clog 2 (PhysicalLevelFrame.states length+1))
    (s : SourceState q.inventory q.height q.block q.digits q.w) (slot : Fin 3)
    (frame : PhysicalLevelFrame.Saved (2*q.inventory.keys) q.N q.exponent length) :
    PhysicalLevelFrameGeneral.decode (frameWords q length hp
      (unpack (pack (installFrame q length hp s slot frame))) slot)=frame := by
  rw [unpack_pack,frameWords_installFrame,PhysicalLevelFrameGeneral.decode_encode]

/-- Three exact stack frame word arrays, the top pointer, and a transfer bank
are already part of the same charged source state. -/
theorem three_frames_budget (q : Configuration) (length : ℕ)
    (hp : q.inventory.pc=Nat.clog 2 (PhysicalLevelFrame.states length+1)) :
    3*PhysicalLevelFrameGeneral.words (2*q.inventory.keys) q.exponent length q.c+
      q.digits+q.block ≤ q.ramWords := by
  rw [frame_size q length hp]
  unfold Configuration.ramWords sourceCells tailCells ResidentLeafSort.residentWords
  omega

/-- The actual normalized block and every polynomial descriptor fit the
multiword stream codec. No one-word block-length assumption is needed. -/
theorem stream_block_capacity (q : Configuration) : q.block < (2^q.w)^q.digits := by
  have hb : q.block ≤ q.height := (normalized_shape q.inventory q.c q.digits q.M q.B
    q.memory_large (by have := q.block_memory; omega)).2.1
  have hh := leaf_header_capacity q
  omega

theorem descriptor_capacity (q : Configuration) (n : ℕ) (hn : n ≤ q.N^q.exponent) :
    n < (2^q.w)^q.digits := by
  have hh := WordConvention.polynomial_capacity q.N q.w q.c q.exponent
    q.input_large q.word_convention
  change n < (2^q.w)^(q.c*(q.exponent+1))
  omega

end
end CodedSorting.CommonSortingNormalization
end NormalizationFrames
