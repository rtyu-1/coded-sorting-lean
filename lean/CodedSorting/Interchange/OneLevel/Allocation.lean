import CodedSorting.Interchange.Streams.StreamParentProgram
import CodedSorting.Circuit.NetworkModel.Adapter

section Assembly
/-! Assembly of one Construction exchange layer from actual distribution, literal
network, and gathering instructions.  The edge programs supplied here will
be constructed from rank-sized scalar children by the concrete frame
adapter.  This assembly is not itself the final edge-program constructor. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace CodedSorting.Construction.OneLevelAssembly

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open Address CoordinateScans CommonAddressLayout StreamSplitLayout StreamSplitMachine
open PartialSwapScan PhysicalStreamCursor
open ProgramNetwork TensorLiftProgram TensorThreeRound ThreeCopySchedule
open MachineNetworkAdapter

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  physicalInputs registerEnumeration originalEnumeration temporaryEnumeration

def localVolume (q : Configuration) (Q rows G S : Nat) : Nat :=
  Volume (Fin ambientDimension) rows Q G (S*q.w)

def parentVolume (q : Configuration) (Q rows G S : Nat) : Nat :=
  Volume (Fin ambientDimension) (rows*streamCount) Q G (S*q.w)

abbrev nodeCount := nodes TensorFrameNetwork.program (inputs := physicalInputs)
abbrev fileCount := physicalInputs + nodeCount

def exchangePermutation (m Q rows G S : Nat) :
    Equiv.Perm (Fin (Volume (Fin m) rows Q G S)) :=
  longLayout.symm.trans (exchangeEquiv.trans longLayout)

@[simp] theorem exchangePermutation_encoded (m Q rows G S : Nat)
    (a : Addr (Fin m) rows Q G S) :
    exchangePermutation m Q rows G S (longLayout a) = longLayout (exchange a) := by
  simp only [exchangePermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

structure Setup (q : Configuration) (Q rows G S source temporary : Nat) where
  network : MachineNetwork.Layout q physicalInputs (nodes TensorFrameNetwork.program (inputs := physicalInputs)) (localVolume q Q rows G S)
  source_separate : source + count q (parentVolume q Q rows G S) ≤ temporary
  temporary_separate : temporary + count q (parentVolume q Q rows G S) ≤ network.workspace

variable {q : Configuration} {Q rows G S source temporary : Nat}

theorem Setup.workspace_fits (a : Setup q Q rows G S source temporary) :
    a.network.workspace + (physicalInputs+(nodes TensorFrameNetwork.program (inputs := physicalInputs)))*a.network.stride ≤ q.N^q.exponent :=
  a.network.files_le_buffer.trans (a.network.buffer_le_limit.trans a.network.fit)

theorem Setup.temporary_fits (a : Setup q Q rows G S source temporary) :
    temporary + count q (parentVolume q Q rows G S) ≤ q.N^q.exponent :=
  a.temporary_separate.trans ((Nat.le_add_right _ _).trans a.workspace_fits)

theorem Setup.source_fits (a : Setup q Q rows G S source temporary) :
    source + count q (parentVolume q Q rows G S) ≤ q.N^q.exponent :=
  a.source_separate.trans ((Nat.le_add_right _ _).trans a.temporary_fits)

/-- Reuse the verified concrete file enumeration without normalizing the
astronomically large literal network again at the assembly boundary. -/
abbrev inputSlot := MachineNetworkAdapter.inputSlot
abbrev outputSlot := MachineNetworkAdapter.outputSlot

theorem inputSlot_injective : Function.Injective inputSlot :=
  MachineNetworkAdapter.inputSlot_injective

theorem outputSlot_injective : Function.Injective outputSlot :=
  MachineNetworkAdapter.outputSlot_injective

def slabs (a : Setup q Q rows G S source temporary)
    (slot : Fin streamCount → Fin (physicalInputs+(nodes TensorFrameNetwork.program (inputs := physicalInputs)))) (hinj : Function.Injective slot) :
    Slabs q streamCount (Volume (Fin ambientDimension) rows Q G S) :=
  allocatedSlabs q _ a.network.workspace a.network.stride slot hinj
    (by simpa only [←local_count, localVolume] using a.network.count_le_stride) a.workspace_fits

theorem slabs_live (a : Setup q Q rows G S source temporary)
    (slot : Fin streamCount → Fin (physicalInputs+(nodes TensorFrameNetwork.program (inputs := physicalInputs)))) (hinj : Function.Injective slot)
    (k : Nat) (hk : k < streamCount*blockCount q.block
      (Volume (Fin ambientDimension) rows Q G S)) :
    a.network.workspace ≤ ((slabs a slot hinj).address k).val ∧
      ((slabs a slot hinj).address k).val < a.network.limit := by
  have h := slotMap_live q a.network.workspace a.network.stride
    (blockCount q.block (Volume (Fin ambientDimension) rows Q G S)) slot
    (by simpa only [←local_count, localVolume] using a.network.count_le_stride)
    a.workspace_fits k hk
  exact ⟨h.1, h.2.trans_le (a.network.files_le_buffer.trans a.network.buffer_le_limit)⟩

theorem slabs_separate (a : Setup q Q rows G S source temporary)
    (slot : Fin streamCount → Fin (physicalInputs+(nodes TensorFrameNetwork.program (inputs := physicalInputs)))) (hinj : Function.Injective slot) :
    ∀ b < blockCount q.block (streamCount*Volume (Fin ambientDimension) rows Q G S),
      ∀ k < streamCount*blockCount q.block (Volume (Fin ambientDimension) rows Q G S),
        CommonColumnSplit.address q temporary b ≠ (slabs a slot hinj).address k := by
  intro b hb k hk h
  have hb' : b < count q (parentVolume q Q rows G S) := by
    simpa only [parentVolume, parent_count] using hb
  have hfit := a.temporary_fits
  have hv := congrArg Fin.val h
  rw [CommonColumnSplit.address_val q _ _ (by omega)] at hv
  have := (slabs_live a slot hinj k hk).1
  have := a.temporary_separate
  omega

theorem slabs_after_temporary (a : Setup q Q rows G S source temporary)
    (slot : Fin streamCount → Fin (physicalInputs+(nodes TensorFrameNetwork.program (inputs := physicalInputs)))) (hinj : Function.Injective slot) :
    ∀ k < streamCount*blockCount q.block (Volume (Fin ambientDimension) rows Q G S),
      ((slabs a slot hinj).address k).val < temporary ∨
        temporary + blockCount q.block (streamCount*Volume (Fin ambientDimension) rows Q G S) ≤
          ((slabs a slot hinj).address k).val := by
  intro k hk
  right
  have h := a.temporary_separate.trans (slabs_live a slot hinj k hk).1
  simpa only [parentVolume, parent_count] using h

def scatter (reader : Fin q.inventory.readers) (a : Setup q Q rows G S source temporary) :=
  scatterCode q reader ambientDimension Q rows streamCount G S source temporary
    (slabs a inputSlot inputSlot_injective)

def gather (reader : Fin q.inventory.readers) (a : Setup q Q rows G S source temporary) :=
  gatherCode q reader ambientDimension Q rows streamCount G S source temporary
    (slabs a outputSlot outputSlot_injective)

variable (location : Vertex GlobalReg TensorFrameNetwork.program.length →
  Equiv.Perm (Fin (localVolume q Q rows G S)))

def code (reader : Fin q.inventory.readers) (a : Setup q Q rows G S source temporary)
    (ep : MachineNetwork.Programs (actualCircuit location) a.network) : List (Instruction q) :=
  scatter reader a ++ MachineNetwork.code reader (actualCircuit location) a.network ep ++ gather reader a

def charge (a : Setup q Q rows G S source temporary)
    (ep : MachineNetwork.Programs (actualCircuit location) a.network) : Nat :=
  distributionCharge q ambientDimension Q rows streamCount G S +
    MachineNetwork.charge (actualCircuit location) a.network ep +
    distributionCharge q ambientDimension Q rows streamCount G S

theorem raw_correct (reader : Fin q.inventory.readers)
    (hframe : ∀ r : IndependentStream,
      (location (.sink (.inl (originalSwap r)))).symm.trans (location (.source (.inl r))) =
        exchangePermutation ambientDimension Q rows G (S*q.w))
    (a : Setup q Q rows G S source temporary)
    (ep : MachineNetwork.Programs (actualCircuit location) a.network) (s : Machine q)
    (c : Fin streamCount) (x : Addr (Fin ambientDimension) rows Q G (S*q.w)) :
    readBit q (executeRaw q (code location reader a ep) s).1.disk source
      (longLayout (parentAddress c x)).val =
    readBit q s.disk source (longLayout (parentAddress c (exchange x))).val := by
  let middle := (executeRaw q (scatter reader a) s).1
  have hn := (actual_selected_raw reader location
    (exchangePermutation ambientDimension Q rows G (S*q.w)) hframe
    a.network ep middle).1 (originalEnumeration.symm c) (longLayout x)
  have hn' : readBit q (executeRaw q
      (MachineNetwork.code reader (actualCircuit location) a.network ep) middle).1.disk
      (a.network.base (outputSlot c)) (longLayout x).val =
      readBit q middle.disk (a.network.base (inputSlot c)) (longLayout (exchange x)).val :=
    hn.trans (congrArg (fun n : Nat => readBit q middle.disk (a.network.base (inputSlot c)) n)
      (congrArg Fin.val (exchangePermutation_encoded ambientDimension Q rows G (S*q.w) x)))
  unfold code gather
  rw [raw_append, raw_append]
  rw [gather_raw q reader ambientDimension Q rows streamCount G S source temporary
    (slabs a outputSlot outputSlot_injective) _ a.source_fits a.temporary_fits a.source_separate
    (slabs_after_temporary a outputSlot outputSlot_injective) c x]
  change readBit q (executeRaw q (MachineNetwork.code reader (actualCircuit location)
    a.network ep) middle).1.disk (a.network.base (outputSlot c)) (longLayout x).val = _
  exact hn'.trans (scatter_raw q reader ambientDimension Q rows streamCount G S source temporary
    (slabs a inputSlot inputSlot_injective) s a.source_fits a.temporary_fits a.source_separate
    (slabs_separate a inputSlot inputSlot_injective) c (exchange x))

theorem raw_frame (reader : Fin q.inventory.readers)
    (a : Setup q Q rows G S source temporary)
    (ep : MachineNetwork.Programs (actualCircuit location) a.network) (s : Machine q)
    (i : Fin (q.N^q.exponent))
    (hi : i.val < source ∨ source + count q (parentVolume q Q rows G S) ≤ i.val)
    (hw : i.val < temporary ∨ a.network.limit ≤ i.val) :
    (executeRaw q (code location reader a ep) s).1.disk i = s.disk i := by
  have htw : temporary + count q (parentVolume q Q rows G S) ≤ a.network.limit :=
    a.temporary_separate.trans ((Nat.le_add_right _ _).trans
      (a.network.files_le_buffer.trans a.network.buffer_le_limit))
  have ht : i.val < temporary ∨ temporary + count q (parentVolume q Q rows G S) ≤ i.val := by
    omega
  have hn : i.val < a.network.workspace ∨ a.network.limit ≤ i.val := by
    have := a.temporary_separate
    omega
  have hslots : ∀ k < streamCount*blockCount q.block
      (Volume (Fin ambientDimension) rows Q G S),
      i ≠ (slabs a inputSlot inputSlot_injective).address k := by
    intro k hk he
    have h := slabs_live a inputSlot inputSlot_injective k hk
    have hv := congrArg Fin.val he
    have := a.temporary_separate
    omega
  unfold code gather
  rw [raw_append, raw_append]
  rw [gather_outside q reader ambientDimension Q rows streamCount G S source temporary
    (slabs a outputSlot outputSlot_injective) _ a.source_fits a.temporary_fits a.source_separate
    (slabs_after_temporary a outputSlot outputSlot_injective) i ht hi]
  rw [MachineNetwork.code_frame reader (actualCircuit location) a.network ep _ i hn]
  exact scatter_outside q reader ambientDimension Q rows streamCount G S source temporary
    (slabs a inputSlot inputSlot_injective) s a.source_fits a.temporary_fits a.source_separate
    i ht hslots

theorem resources (reader : Fin q.inventory.readers)
    (a : Setup q Q rows G S source temporary)
    (ep : MachineNetwork.Programs (actualCircuit location) a.network) :
    cost q (code location reader a ep) ≤ charge location a ep ∧
    (code location reader a ep).length ≤ charge location a ep ∧
    ∀ i ∈ code location reader a ep, RespectsPC q i := by
  obtain ⟨hc, hl, hs⟩ := MachineNetwork.code_resources reader (actualCircuit location) a.network ep
  refine ⟨?_, ?_, ?_⟩
  · unfold code charge
    rw [cost_append, cost_append]
    exact Nat.add_le_add (Nat.add_le_add
      (scatter_cost q reader ambientDimension Q rows streamCount G S source temporary _) hc)
      (gather_cost q reader ambientDimension Q rows streamCount G S source temporary _)
  · unfold code charge
    rw [List.length_append, List.length_append]
    exact Nat.add_le_add (Nat.add_le_add
      (scatter_length q reader ambientDimension Q rows streamCount G S source temporary _) hl)
      (gather_length q reader ambientDimension Q rows streamCount G S source temporary _)
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact scatter_safe q reader ambientDimension Q rows streamCount G S source temporary _ i hi
      · exact hs i hi
    · exact gather_safe q reader ambientDimension Q rows streamCount G S source temporary _ i hi

/-- One actual program, with its semantic, frame, control, and resource
proofs referring to precisely the same chronological instruction list. -/
def program (reader : Fin q.inventory.readers)
    (hframe : ∀ r : IndependentStream,
      (location (.sink (.inl (originalSwap r)))).symm.trans (location (.source (.inl r))) =
        exchangePermutation ambientDimension Q rows G (S*q.w))
    (a : Setup q Q rows G S source temporary)
    (ep : MachineNetwork.Programs (actualCircuit location) a.network) :
    CommonFinitePermutation.Program q (parentVolume q Q rows G S) source temporary a.network.limit
      (exchangePermutation ambientDimension Q (rows*streamCount) G (S*q.w)) where
  instructions := code location reader a ep
  charge := charge location a ep
  correct := by
    intro s y
    obtain ⟨x, rfl⟩ := (longLayout (I := Fin ambientDimension)
      (P := rows*streamCount) (Q := Q) (G := G) (S := S*q.w)).surjective y
    obtain ⟨c, x, rfl⟩ := parentAddress_surjective x
    have he := (exchangePermutation_encoded ambientDimension Q (rows*streamCount) G
      (S*q.w) (parentAddress c x)).trans
        (congrArg longLayout (parentAddress_exchange c x).symm)
    exact (raw_correct location reader hframe a ep s c x).trans
      (congrArg (fun n : Nat => readBit q s.disk source n) (congrArg Fin.val he.symm))
  frame := raw_frame location reader a ep
  safe := (resources location reader a ep).2.2
  cost_le := (resources location reader a ep).1
  length_le := (resources location reader a ep).2.1

theorem charge_bound (a : Setup q Q rows G S source temporary)
    (ep : MachineNetwork.Programs (actualCircuit location) a.network) :
    charge location a ep ≤
      (24*streamCount+36)*count q (parentVolume q Q rows G S) +
      MachineNetwork.charge (actualCircuit location) a.network ep := by
  have h := distributionCharge_le q ambientDimension Q rows streamCount G S
    (by decide : 0 < streamCount)
  unfold charge parentVolume
  nlinarith

#print axioms raw_correct
#print axioms program
#print axioms charge_bound

end
end CodedSorting.Construction.OneLevelAssembly
end Assembly

section Allocation
/-! A constructible allocation for one actual Construction exchange layer. The
temporary parent file, all network files, and one shared local buffer are
consecutive. `extra` reserves additional child workspace after that buffer.
All premises below are numerical separation or disk-capacity conditions;
none assumes that a program executes correctly. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.OneLevelAllocation

open CommonSortingNormalization CommonPermutationPairs
open CommonAddressLayout OneLevelAssembly MachineNetworkAdapter

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program physicalInputs

def localBlocks (q : Configuration) (Q rows G S : Nat) : Nat :=
  count q (localVolume q Q rows G S)

def parentBlocks (q : Configuration) (Q rows G S : Nat) : Nat :=
  count q (parentVolume q Q rows G S)

theorem parentVolume_eq_streams (q : Configuration) (Q rows G S : Nat) :
    parentVolume q Q rows G S = streamCount * localVolume q Q rows G S :=
  (StreamSplitLayout.streamVolume ambientDimension Q rows streamCount G (S*q.w)).symm

theorem localVolume_le_parent (q : Configuration) (Q rows G S : Nat) :
    localVolume q Q rows G S ≤ parentVolume q Q rows G S := by
  rw [parentVolume_eq_streams]
  have hW : 1 ≤ streamCount := by rw [streamCount_eq]; omega
  simpa only [one_mul] using
    Nat.mul_le_mul_right (localVolume q Q rows G S) hW

/-- Rounding to machine blocks preserves the local-to-parent size bound. -/
theorem localBlocks_le_parent (q : Configuration) (Q rows G S : Nat) :
    localBlocks q Q rows G S ≤ parentBlocks q Q rows G S := by
  apply LayoutConversion.blockCount_minimal _ _ _ (width_pos q)
  exact (localVolume_le_parent q Q rows G S).trans
    (LayoutConversion.blockCount_covers (parentVolume q Q rows G S)
      (width q) (width_pos q))

def canonicalWorkspace (q : Configuration) (Q rows G S temporary : Nat) : Nat :=
  temporary + parentBlocks q Q rows G S

/-- Keep the file count in the same syntactic form as `Setup.network`.
Aliases at this dependent boundary would force reduction of the huge word. -/
def canonicalBuffer (q : Configuration) (Q rows G S temporary : Nat) : Nat :=
  canonicalWorkspace q Q rows G S temporary + (physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs)) * localBlocks q Q rows G S

def canonicalLimit (q : Configuration) (Q rows G S temporary extra : Nat) : Nat :=
  canonicalBuffer q Q rows G S temporary + localBlocks q Q rows G S + extra

/-- Every physical input and physical edge receives one local file slab.
All edge programs reuse the same buffer and the same additional workspace. -/
def canonicalNetwork (q : Configuration) (Q rows G S temporary extra : Nat)
    (hfit : canonicalLimit q Q rows G S temporary extra ≤ q.N^q.exponent) :
    MachineNetwork.Layout q physicalInputs
      (nodes TensorFrameNetwork.program (inputs := physicalInputs)) (localVolume q Q rows G S) where
  workspace := canonicalWorkspace q Q rows G S temporary
  stride := localBlocks q Q rows G S
  buffer := canonicalBuffer q Q rows G S temporary
  limit := canonicalLimit q Q rows G S temporary extra
  count_le_stride := le_rfl
  files_le_buffer := le_rfl
  buffer_le_limit := by
    change canonicalBuffer q Q rows G S temporary ≤
      canonicalBuffer q Q rows G S temporary + localBlocks q Q rows G S + extra
    omega
  fit := hfit

/-- The node allocation is built from its source separation and one explicit
disk-fit inequality. No abstract allocation package remains to be supplied. -/
def canonicalSetup (q : Configuration) (Q rows G S source temporary extra : Nat)
    (hsource : source + parentBlocks q Q rows G S ≤ temporary)
    (hfit : canonicalLimit q Q rows G S temporary extra ≤ q.N^q.exponent) :
    Setup q Q rows G S source temporary where
  network := canonicalNetwork q Q rows G S temporary extra hfit
  source_separate := hsource
  temporary_separate := le_rfl

theorem canonicalSetup_room (q : Configuration) (Q rows G S source temporary extra : Nat)
    (hsource : source + parentBlocks q Q rows G S ≤ temporary)
    (hfit : canonicalLimit q Q rows G S temporary extra ≤ q.N^q.exponent) :
    (canonicalSetup q Q rows G S source temporary extra hsource hfit).network.buffer +
      count q (localVolume q Q rows G S) ≤
        (canonicalSetup q Q rows G S source temporary extra hsource hfit).network.limit := by
  change canonicalBuffer q Q rows G S temporary + localBlocks q Q rows G S ≤
    canonicalBuffer q Q rows G S temporary + localBlocks q Q rows G S + extra
  exact Nat.le_add_right _ _

theorem canonicalSetup_extra (q : Configuration) (Q rows G S source temporary extra : Nat)
    (hsource : source + parentBlocks q Q rows G S ≤ temporary)
    (hfit : canonicalLimit q Q rows G S temporary extra ≤ q.N^q.exponent) :
    (canonicalSetup q Q rows G S source temporary extra hsource hfit).network.buffer +
      count q (localVolume q Q rows G S) + extra =
        (canonicalSetup q Q rows G S source temporary extra hsource hfit).network.limit := rfl

/-- Exact occupied interval beginning at the temporary parent file. -/
def reservedBlocks (q : Configuration) (Q rows G S temporary extra : Nat) : Nat :=
  canonicalLimit q Q rows G S temporary extra - temporary

theorem canonicalLimit_eq (q : Configuration) (Q rows G S temporary extra : Nat) :
    canonicalLimit q Q rows G S temporary extra = temporary +
      (parentBlocks q Q rows G S + ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+1)*localBlocks q Q rows G S + extra) := by
  unfold canonicalLimit canonicalBuffer canonicalWorkspace
  ring

theorem reservedBlocks_eq (q : Configuration) (Q rows G S temporary extra : Nat) :
    reservedBlocks q Q rows G S temporary extra =
      parentBlocks q Q rows G S + ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+1)*localBlocks q Q rows G S + extra := by
  unfold reservedBlocks
  rw [canonicalLimit_eq]
  omega

/-- A fixed finite multiple of the actual parent-block count bounds the
whole local allocation; the child's extra scratch is stated separately. -/
theorem reservedBlocks_le (q : Configuration) (Q rows G S temporary extra : Nat) :
    reservedBlocks q Q rows G S temporary extra ≤
      ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+2)*parentBlocks q Q rows G S + extra := by
  rw [reservedBlocks_eq]
  have hm := Nat.mul_le_mul_left ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+1) (localBlocks_le_parent q Q rows G S)
  calc
    parentBlocks q Q rows G S + ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+1)*localBlocks q Q rows G S + extra ≤
        parentBlocks q Q rows G S + ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+1)*parentBlocks q Q rows G S + extra := by
      omega
    _ = ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+2)*parentBlocks q Q rows G S + extra := by ring

theorem canonicalLimit_le (q : Configuration) (Q rows G S temporary extra : Nat) :
    canonicalLimit q Q rows G S temporary extra ≤
      temporary + ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+2)*parentBlocks q Q rows G S + extra := by
  rw [canonicalLimit_eq]
  have h := reservedBlocks_le q Q rows G S temporary extra
  rw [reservedBlocks_eq] at h
  omega

/-- A conservative parent-size inequality suffices to construct the actual
network layout, even without calculating the smaller local-block count. -/
def boundedSetup (q : Configuration) (Q rows G S source temporary extra : Nat)
    (hsource : source + parentBlocks q Q rows G S ≤ temporary)
    (hfit : temporary + ((physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs))+2)*parentBlocks q Q rows G S + extra ≤
      q.N^q.exponent) : Setup q Q rows G S source temporary :=
  canonicalSetup q Q rows G S source temporary extra hsource
    ((canonicalLimit_le q Q rows G S temporary extra).trans hfit)

#print axioms canonicalSetup
#print axioms canonicalSetup_room
#print axioms reservedBlocks_le
#print axioms boundedSetup

end
end CodedSorting.Construction.OneLevelAllocation
end Allocation
