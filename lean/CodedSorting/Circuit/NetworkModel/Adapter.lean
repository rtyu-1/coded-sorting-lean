import CodedSorting.Interchange.Local.RankPartialSwapMachine
import CodedSorting.Interchange.Bounds.ExchangeSpecializationEndpoints
import CodedSorting.Circuit.NetworkModel.Definitions
import CodedSorting.Interchange.Bounds.ExchangeSimulation

section RankEdge
/-! Exact interface between the rank-many scan compiler and the numerical
frame permutations consumed by the real machine network. Relabeling does
not change one instruction or its charge. -/
set_option autoImplicit false
namespace CodedSorting.Construction.MachineNetworkRankEdge
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonAddressLayout MatrixFactorization
open PartialSwapScan PartialSwapExecution RankPartialSwapExecution
open ProjectionRankDecomposition PartialSwapMachine ExchangeFramePermutation
open scoped BigOperators
noncomputable section

variable {m : Nat}
local instance doubledDecEq : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq
variable {P : Matrix (Fin m) (Fin m) ℚ} (d : RankDecomposition P)
variable (F : SpecializedFamily (family d)) (f : Nat)
local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩
variable (Pref G S : Nat) (hG : 0 < G) (hS : 0 < S)

def permutation : Equiv.Perm (Fin (Volume (Fin m) Pref (F.prime^f) G S)) :=
  numericPerm (fullFinMatrix F f none) (finite_target_square d F f) Pref G S

theorem forward_eq : RankPartialSwapMachine.forward d F f Pref G S hG hS =
    permutation d F f Pref G S := by
  apply Equiv.ext
  intro y
  obtain ⟨a, rfl⟩ := longLayout.surjective y
  exact (RankPartialSwapMachine.forward_encoded d F f Pref G S hG hS a).trans
    (numericPerm_encoded _ _ _ _ _ a).symm

theorem inverse_forward_eq : (RankPartialSwapMachine.forward d F f Pref G S hG hS).symm =
    permutation d F f Pref G S := by
  rw [RankPartialSwapMachine.forward_symm, forward_eq]

variable (q : Configuration) {source buffer limit : Nat}
variable (reader : Fin q.inventory.readers)
variable (alloc : ScanAllocation q (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit)
variable (children : (i : Fin P.rank) → CommonFinitePermutation.Program q
  (Volume (Fin m) Pref (F.prime^f) G S) source buffer limit
  (RankPartialSwapMachine.childPermutation d F f Pref G S i))

/-- The actual edge program, with the exact numeric frame specification. -/
def program : CommonFinitePermutation.Program q (Volume (Fin m) Pref (F.prime^f) G S)
    source buffer limit (permutation d F f Pref G S) :=
  RankPartialSwapMachine.relabel
    (RankPartialSwapMachine.program d F f Pref G S hG hS q reader alloc children)
    (inverse_forward_eq d F f Pref G S hG hS)

@[simp] theorem program_instructions :
    (program d F f Pref G S hG hS q reader alloc children).instructions =
      (RankPartialSwapMachine.program d F f Pref G S hG hS q reader alloc children).instructions := rfl

@[simp] theorem program_charge :
    (program d F f Pref G S hG hS q reader alloc children).charge =
      (RankPartialSwapMachine.program d F f Pref G S hG hS q reader alloc children).charge := rfl

theorem program_charge_le :
    (program d F f Pref G S hG hS q reader alloc children).charge ≤
      3*(fixedConstant d+16*P.rank)*count q (Volume (Fin m) Pref (F.prime^f) G S) +
        ∑ i, (children i).charge :=
  RankPartialSwapMachine.program_charge_le d F f Pref G S hG hS q reader alloc children

#print axioms forward_eq
#print axioms program
#print axioms program_charge_le
end
end CodedSorting.Construction.MachineNetworkRankEdge
end RankEdge

section Adapter
/-!
# Stage-major compilation data for the literal Construction program

Every physical wire has one fresh file.  Its sources are exactly the input
ports used by the literal XOR gate (including repeated ports in overwrite
instructions).  The ordering proof is derived from the actual graph ranks.
No graph-execution or payload-correctness assumption is introduced here.

This first layer is independent of the machine executor; the accompanying
binding module instantiates its circuit and consumes these local equations.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.MachineNetworkAdapter

open CodedSorting.Circuit CodedSorting.ProgramNetwork CodedSorting.CircuitProgram
open CodedSorting.CommonNetworkInputs

noncomputable section

variable {Reg : Type*} [DecidableEq Reg] {inputs V : ℕ}
variable (p : List (XorGate Reg)) (enumeration : Reg ≃ Fin inputs)

def nodes : ℕ := (p.length + 1) * inputs

def edgeEnumeration : Wire Reg p.length ≃ Fin (nodes p (inputs := inputs)) :=
  (Equiv.prodCongr (Equiv.refl _) enumeration).trans finProdFinEquiv

@[simp] theorem edgeEnumeration_val (e : Wire Reg p.length) :
    (edgeEnumeration p enumeration e).val = (enumeration e.2).val + inputs * e.1.val := rfl

theorem edgeEnumeration_prior (a b : Wire Reg p.length) (h : a.1.val < b.1.val) :
    (edgeEnumeration p enumeration a).val < (edgeEnumeration p enumeration b).val := by
  have ha := (enumeration a.2).isLt
  simp only [edgeEnumeration_val]
  nlinarith

abbrev File := Reg ⊕ Wire Reg p.length

def fileEnumeration : File p ≃ Fin (inputs + nodes p (inputs := inputs)) :=
  (Equiv.sumCongr enumeration (edgeEnumeration p enumeration)).trans finSumFinEquiv

def inputIndex (r : Reg) : Fin (inputs + nodes p (inputs := inputs)) :=
  fileEnumeration p enumeration (.inl r)

def edgeIndex (e : Wire Reg p.length) : Fin (inputs + nodes p (inputs := inputs)) :=
  fileEnumeration p enumeration (.inr e)

@[simp] theorem inputIndex_val (r : Reg) :
    (inputIndex p enumeration r).val = (enumeration r).val := rfl

@[simp] theorem edgeIndex_val (e : Wire Reg p.length) :
    (edgeIndex p enumeration e).val = inputs + (edgeEnumeration p enumeration e).val := rfl

def portIndex {v : Vertex Reg p.length} (port : InputPort p v) :
    Fin (inputs + nodes p (inputs := inputs)) :=
  match port with
  | .inl r => inputIndex p enumeration r.val
  | .inr e => edgeIndex p enumeration e.val

def edgePorts (e : Wire Reg p.length) : List (InputPort p (wireTail p e)) :=
  inputList p (wireTail p e) ⟨e, rfl⟩

def ports (e : Wire Reg p.length) : List (Fin (inputs + nodes p (inputs := inputs))) :=
  (edgePorts p e).map (portIndex p enumeration)

/-- The literal incoming ports always refer to input files or an earlier
stage.  This is independent of register ordering within a stage. -/
theorem portIndex_prior (e : Wire Reg p.length) (port : InputPort p (wireTail p e)) :
    (portIndex p enumeration port).val < inputs + (edgeEnumeration p enumeration e).val := by
  cases port with
  | inl r =>
    change (enumeration r.val).val < inputs + _
    exact (enumeration r.val).isLt.trans_le (Nat.le_add_right _ _)
  | inr a =>
    have h := congrArg (vertexRank p) a.property
    rw [rank_wireHead, rank_wireTail] at h
    have ha : a.val.1.val < e.1.val := by omega
    exact Nat.add_lt_add_left (edgeEnumeration_prior p enumeration a.val e ha) inputs

theorem ports_prior (e : Wire Reg p.length) (i : Fin (inputs + nodes p (inputs := inputs)))
    (hi : i ∈ ports p enumeration e) :
    i.val < inputs + (edgeEnumeration p enumeration e).val := by
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp hi
  exact portIndex_prior p enumeration e port

variable (frame : Vertex Reg p.length → Equiv.Perm (Fin V))

/-- Output-to-input address map.  The head coordinate is first decoded,
then encoded at the tail, where all inputs of the XOR meet. -/
def edgePermutation (e : Wire Reg p.length) : Equiv.Perm (Fin V) :=
  (frame (wireHead p e)).symm.trans (frame (wireTail p e))

def fileValue (input : Reg → Fin V → Bit) : File p → Fin V → Bit
  | .inl r, y => input r ((frame (.source r)).symm y)
  | .inr e, y => wireValue p
      (fun r => input r ((frame (wireHead p e)).symm y)) e

def values (input : Reg → Fin V → Bit) :
    Fin (inputs + nodes p (inputs := inputs)) → Fin V → Bit :=
  fun i => fileValue p frame input ((fileEnumeration p enumeration).symm i)

@[simp] theorem values_input (input : Reg → Fin V → Bit) (r : Reg) (y : Fin V) :
    values p enumeration frame input (inputIndex p enumeration r) y =
      input r ((frame (.source r)).symm y) := by
  simp only [values, inputIndex, Equiv.symm_apply_apply, fileValue]

@[simp] theorem values_edge (input : Reg → Fin V → Bit) (e : Wire Reg p.length)
    (y : Fin V) :
    values p enumeration frame input (edgeIndex p enumeration e) y =
      wireValue p (fun r => input r ((frame (wireHead p e)).symm y)) e := by
  simp only [values, edgeIndex, Equiv.symm_apply_apply, fileValue]

theorem portValue (input : Reg → Fin V → Bit) (e : Wire Reg p.length)
    (port : InputPort p (wireTail p e)) (y : Fin V) :
    values p enumeration frame input (portIndex p enumeration port)
      (edgePermutation p frame e y) =
      localInputs p (fun r => input r ((frame (wireHead p e)).symm y))
        (wireTail p e) port := by
  cases port with
  | inl r =>
    simp only [portIndex, values_input, localInputs, edgePermutation, Equiv.trans_apply]
    rw [r.property]
    simp only [Equiv.symm_apply_apply]
  | inr a =>
    simp only [portIndex, values_edge, localInputs, edgePermutation, Equiv.trans_apply]
    rw [a.property]
    simp only [Equiv.symm_apply_apply]

/-- The concrete XOR sources and frame conversion satisfy the exact local
equation consumed by the fresh-file machine executor. -/
theorem local_equation (input : Reg → Fin V → Bit) (e : Wire Reg p.length) (y : Fin V) :
    values p enumeration frame input (edgeIndex p enumeration e) y =
      ((ports p enumeration e).map (fun i => values p enumeration frame input i
        (edgePermutation p frame e y))).sum := by
  rw [values_edge]
  rw [← localMap_wireValues p
    (fun r => input r ((frame (wireHead p e)).symm y)) (wireTail p e) ⟨e, rfl⟩]
  rw [localMap_eq_sum]
  simp only [ports, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro port _
  exact (portValue p enumeration frame input e port y).symm

end
end CodedSorting.Construction.MachineNetworkAdapter
end Adapter

section ActualEdgePrograms
/-! Actual edge programs for the certified Construction frame family. The only
recursive arguments are executable smaller coordinate exchanges. The rank
index bijection accounts for every physical child exactly once. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
namespace CodedSorting.Construction.MachineNetworkActualEdges
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonAddressLayout PartialSwapMachine PartialSwapExecution
open RankPartialSwapExecution ExchangeSpecialization OneLevelChildren
open scoped BigOperators
noncomputable section
attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  ExchangeSpecialization.uniform

local instance doubledDecEq : DecidableEq (Fin 512 ⊕ₗ Fin 512) :=
  (inferInstance : LinearOrder (Fin 512 ⊕ₗ Fin 512)).toDecidableEq

variable (f Pref G S : Nat)
local instance : NeZero (radix^f) := ⟨pow_ne_zero _ radix_prime.ne_zero⟩

abbrev FileVolume := Volume (Fin 512) Pref (radix^f) G S

def childPermutation (e : Edge) (i : Fin (edgeRank e)) :
    Equiv.Perm (Fin (FileVolume f Pref G S)) :=
  RankPartialSwapMachine.childPermutation (decomposition e) (edgeFamily e) f Pref G S
    ((childIndex e).symm i)

abbrev Children (q : Configuration) (e : Edge) (source buffer limit : Nat) :=
  (i : Fin (edgeRank e)) → CommonFinitePermutation.Program q (FileVolume f Pref G S)
    source buffer limit (childPermutation f Pref G S e i)

variable (hG : 0 < G) (hS : 0 < S) (q : Configuration) (e : Edge)
variable {source buffer limit : Nat}
variable (reader : Fin q.inventory.readers)
variable (alloc : ScanAllocation q (FileVolume f Pref G S) source buffer limit)
variable (children : Children f Pref G S q e source buffer limit)

def rankChildren (i : Fin (edgeProjection e).rank) :
    CommonFinitePermutation.Program q (FileVolume f Pref G S) source buffer limit
      (RankPartialSwapMachine.childPermutation (decomposition e) (edgeFamily e) f Pref G S i) :=
  RankPartialSwapMachine.relabel (children (childIndex e i))
    (by simp only [childPermutation, Equiv.symm_apply_apply])

def program : CommonFinitePermutation.Program q (FileVolume f Pref G S) source buffer limit
    (ExchangeSpecialization.edgePermutation f Pref G S e) :=
  RankPartialSwapMachine.relabel
    (MachineNetworkRankEdge.program (decomposition e) (edgeFamily e) f Pref G S hG hS
      q reader alloc (rankChildren f Pref G S q e children)) rfl

/-- Fixed rational construction overhead, independent of the file width. -/
def coefficient (e : Edge) : Nat :=
  3*(fixedConstant (decomposition e)+16*edgeRank e)

@[simp] theorem program_instructions :
    (program f Pref G S hG hS q e reader alloc children).instructions =
      (RankPartialSwapMachine.program (decomposition e) (edgeFamily e) f Pref G S hG hS
        q reader alloc (rankChildren f Pref G S q e children)).instructions := rfl

theorem program_charge_le :
    (program f Pref G S hG hS q e reader alloc children).charge ≤
      coefficient e*count q (FileVolume f Pref G S) + ∑ i, (children i).charge := by
  have h := MachineNetworkRankEdge.program_charge_le (decomposition e) (edgeFamily e)
    f Pref G S hG hS q reader alloc (rankChildren f Pref G S q e children)
  have hs : (∑ i : Fin (edgeProjection e).rank, (children (childIndex e i)).charge) =
      ∑ i : Fin (edgeRank e), (children i).charge :=
    (childIndex e).sum_comp (fun i => (children i).charge)
  change (program f Pref G S hG hS q e reader alloc children).charge ≤ _ at h
  simp only [rankChildren, RankPartialSwapMachine.relabel] at h
  rw [hs, edgeProjection_rank] at h
  exact h


#print axioms program
#print axioms program_charge_le
end
end CodedSorting.Construction.MachineNetworkActualEdges
end ActualEdgePrograms

section Slots
/-! Concrete original-session and physical temporary file enumeration. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace CodedSorting.Construction.MachineNetworkAdapter
open CodedSorting.ProgramNetwork TensorLiftProgram ThreeCopySchedule TensorThreeRound
noncomputable section

theorem sumEnumeration_left {A B : Type*} {m n : ℕ}
    (ea : A ≃ Fin m) (eb : B ≃ Fin n) (a : A) :
    (((Equiv.sumCongr ea eb).trans (finSumFinEquiv (m := m) (n := n))) (.inl a)).val =
      (ea a).val := rfl

/-- The selected original streams occupy the first input slots.  The
physical temporary registers follow them and add no independent session. -/
def originalEnumeration : IndependentStream ≃ Fin streamCount :=
  (Fintype.equivFin IndependentStream).trans (finCongr independent_stream_count)

def temporaryEnumeration : TemporaryStream ≃ Fin 998001 :=
  (Fintype.equivFin TemporaryStream).trans (finCongr TensorFrameNetwork.temporary_stream_count)

attribute [local irreducible] originalEnumeration temporaryEnumeration

def physicalInputs : ℕ := streamCount + 998001

def registerEnumeration : GlobalReg ≃ Fin physicalInputs :=
  (Equiv.sumCongr originalEnumeration temporaryEnumeration).trans
    (finSumFinEquiv (m := streamCount) (n := 998001))

@[simp] theorem registerEnumeration_original (r : IndependentStream) :
    (registerEnumeration (.inl r)).val = (originalEnumeration r).val :=
  sumEnumeration_left originalEnumeration temporaryEnumeration r

attribute [local irreducible] TensorFrameNetwork.program

def inputSlot (c : Fin streamCount) :
    Fin (physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs)) :=
  inputIndex TensorFrameNetwork.program registerEnumeration
    (.inl (originalEnumeration.symm c))

def outputSlot (c : Fin streamCount) :
    Fin (physicalInputs + nodes TensorFrameNetwork.program (inputs := physicalInputs)) :=
  edgeIndex TensorFrameNetwork.program registerEnumeration
    (sinkWire TensorFrameNetwork.program (.inl (originalSwap (originalEnumeration.symm c))))

@[simp] theorem inputSlot_val (c : Fin streamCount) : (inputSlot c).val = c.val := by
  rw [inputSlot, inputIndex_val, registerEnumeration_original]
  rw [Equiv.apply_symm_apply]

theorem inputSlot_injective : Function.Injective inputSlot := by
  intro c d h
  apply Fin.ext
  simpa only [inputSlot_val] using congrArg Fin.val h

theorem outputSlot_injective : Function.Injective outputSlot := by
  intro c d h
  have he := (fileEnumeration TensorFrameNetwork.program registerEnumeration).injective h
  have hw := Sum.inr.inj he
  have hr := Sum.inl.inj (congrArg Prod.snd hw)
  have ho := TensorNetwork.originalSwap_involutive.injective hr
  exact originalEnumeration.symm.injective ho

#print axioms inputSlot_injective
#print axioms outputSlot_injective

end
end CodedSorting.Construction.MachineNetworkAdapter
end Slots

section Binding
/-! Binding of the literal Construction program graph to actual machine instructions.
The initial physical files are read directly from the starting disk.  In
particular no separate successful-run or temporary-initialization premise
is part of the machine theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.MachineNetworkAdapter

open CodedSorting.Circuit CodedSorting.CircuitProgram CodedSorting.ProgramNetwork
open CodedSorting.CommonSortingNormalization CodedSorting.CommonStaticSchedule
open CodedSorting.CommonPermutationPairs
open CodedSorting.CommonLeafProgram (Machine)
open TensorLiftProgram ThreeCopySchedule TensorThreeRound

noncomputable section

attribute [local irreducible] originalEnumeration temporaryEnumeration registerEnumeration
  physicalInputs

variable {Reg : Type*} [DecidableEq Reg] {inputs V : ℕ}
variable (p : List (XorGate Reg)) (enumeration : Reg ≃ Fin inputs)
variable (frame : Vertex Reg p.length → Equiv.Perm (Fin V))

def circuit : MachineNetwork.Circuit inputs (nodes p (inputs := inputs)) V where
  ports e := ports p enumeration ((edgeEnumeration p enumeration).symm e)
  prior e i hi := by
    simpa only [Equiv.apply_symm_apply] using
      ports_prior p enumeration ((edgeEnumeration p enumeration).symm e) i hi
  permutation e := edgePermutation p frame ((edgeEnumeration p enumeration).symm e)

@[simp] theorem nodeFile_edge (e : Wire Reg p.length) :
    MachineNetwork.nodeFile (edgeEnumeration p enumeration e) = edgeIndex p enumeration e := by
  apply Fin.ext
  rfl

theorem localEq (input : Reg → Fin V → Bit) :
    MachineNetwork.LocalEq (circuit p enumeration frame) (values p enumeration frame input) := by
  intro e y
  obtain ⟨a, rfl⟩ := (edgeEnumeration p enumeration).surjective e
  simpa only [circuit, Equiv.symm_apply_apply, nodeFile_edge] using
    local_equation p enumeration frame input a y

variable {q : Configuration}

def physicalInput (layout : MachineNetwork.Layout q inputs (nodes p (inputs := inputs)) V)
    (s : Machine q) (r : Reg) (y : Fin V) : Bit :=
  readBit q s.disk (layout.base (inputIndex p enumeration r)) y.val

def decodedInput (layout : MachineNetwork.Layout q inputs (nodes p (inputs := inputs)) V)
    (s : Machine q) (r : Reg) (y : Fin V) : Bit :=
  physicalInput p enumeration layout s r (frame (.source r) y)

theorem initial_view
    (layout : MachineNetwork.Layout q inputs (nodes p (inputs := inputs)) V)
    (s : Machine q) :
    MachineNetwork.View layout 0 s.disk
      (values p enumeration frame (decodedInput p enumeration frame layout s)) := by
  intro file hfile y
  have hi : file.val < inputs := by simpa only [Nat.add_zero] using hfile
  let r := enumeration.symm ⟨file.val, hi⟩
  have he : inputIndex p enumeration r = file := by
    apply Fin.ext
    change (enumeration (enumeration.symm ⟨file.val, hi⟩)).val = file.val
    rw [Equiv.apply_symm_apply]
  rw [← he, values_input]
  simp only [decodedInput, Equiv.apply_symm_apply]
  rfl

/-- Exact physical value of every actual wire after the real disk program,
starting from arbitrary source-file contents, including temporary files. -/
theorem raw_physical (reader : Fin q.inventory.readers)
    (layout : MachineNetwork.Layout q inputs (nodes p (inputs := inputs)) V)
    (ep : MachineNetwork.Programs (circuit p enumeration frame) layout) (s : Machine q) :
    let result := executeRaw q (MachineNetwork.code reader (circuit p enumeration frame) layout ep) s
    (∀ e y, readBit q result.1.disk (layout.base (edgeIndex p enumeration e)) y.val =
      ExchangeSimulation.physicalWire p frame (physicalInput p enumeration layout s) e y) ∧
    (∀ a : Fin (q.N^q.exponent), a.val < layout.workspace ∨ layout.limit ≤ a.val →
      result.1.disk a = s.disk a) := by
  obtain ⟨hv, hf⟩ := MachineNetwork.raw_correct reader (circuit p enumeration frame)
    layout ep s (values p enumeration frame (decodedInput p enumeration frame layout s))
    (localEq p enumeration frame _) (initial_view p enumeration frame layout s)
  refine ⟨?_, hf⟩
  intro e y
  rw [hv, values_edge]
  rfl

/-- A selected payload permutation becomes an actual disk-file permutation
after the endpoint frame maps are composed. -/
theorem raw_selected {Session : Type*} (reader : Fin q.inventory.readers)
    (sourceReg sinkReg : Session → Reg)
    (hprogram : ∀ input r, runProgram p input (sinkReg r) = input (sourceReg r))
    (exchange : Equiv.Perm (Fin V))
    (hframe : ∀ r, (frame (.sink (sinkReg r))).symm.trans
      (frame (.source (sourceReg r))) = exchange)
    (layout : MachineNetwork.Layout q inputs (nodes p (inputs := inputs)) V)
    (ep : MachineNetwork.Programs (circuit p enumeration frame) layout) (s : Machine q) :
    let result := executeRaw q (MachineNetwork.code reader (circuit p enumeration frame) layout ep) s
    (∀ r y, readBit q result.1.disk (layout.base (edgeIndex p enumeration
      (sinkWire p (sinkReg r)))) y.val =
      readBit q s.disk (layout.base (inputIndex p enumeration (sourceReg r))) (exchange y).val) ∧
    (∀ a : Fin (q.N^q.exponent), a.val < layout.workspace ∨ layout.limit ≤ a.val →
      result.1.disk a = s.disk a) := by
  obtain ⟨hv, hf⟩ := raw_physical p enumeration frame reader layout ep s
  refine ⟨?_, hf⟩
  intro r y
  rw [hv, ExchangeSimulation.physicalWire, sinkWire_head, wireValue_sink, hprogram]
  have he := congrArg (fun e : Equiv.Perm (Fin V) => e y) (hframe r)
  change frame (.source (sourceReg r)) ((frame (.sink (sinkReg r))).symm y) = exchange y at he
  change physicalInput p enumeration layout s (sourceReg r)
    (frame (.source (sourceReg r)) ((frame (.sink (sinkReg r))).symm y)) = _
  rw [he]
  rfl

attribute [local irreducible] TensorFrameNetwork.program

def actualCircuit (location : Vertex GlobalReg TensorFrameNetwork.program.length →
    Equiv.Perm (Fin V)) :
    MachineNetwork.Circuit physicalInputs (nodes TensorFrameNetwork.program
      (inputs := physicalInputs)) V :=
  circuit TensorFrameNetwork.program registerEnumeration location

/-- Every designated Construction output file contains the requested address exchange
of its actual input file.  The local code is the certified literal program;
only actual edge programs and the endpoint frame identity are supplied. -/
theorem actual_selected_raw (reader : Fin q.inventory.readers)
    (location : Vertex GlobalReg TensorFrameNetwork.program.length → Equiv.Perm (Fin V))
    (exchange : Equiv.Perm (Fin V))
    (hframe : ∀ r : IndependentStream,
      (location (.sink (.inl (originalSwap r)))).symm.trans
        (location (.source (.inl r))) = exchange)
    (layout : MachineNetwork.Layout q physicalInputs (nodes TensorFrameNetwork.program
      (inputs := physicalInputs)) V)
    (ep : MachineNetwork.Programs (actualCircuit location) layout) (s : Machine q) :
    let result := executeRaw q (MachineNetwork.code reader (actualCircuit location) layout ep) s
    (∀ r y, readBit q result.1.disk
      (layout.base (edgeIndex TensorFrameNetwork.program registerEnumeration
        (sinkWire TensorFrameNetwork.program (.inl (originalSwap r))))) y.val =
      readBit q s.disk
        (layout.base (inputIndex TensorFrameNetwork.program registerEnumeration (.inl r)))
        (exchange y).val) ∧
    (∀ a : Fin (q.N^q.exponent), a.val < layout.workspace ∨ layout.limit ≤ a.val →
      result.1.disk a = s.disk a) :=
  raw_selected TensorFrameNetwork.program registerEnumeration location reader
    Sum.inl (fun r => .inl (originalSwap r)) ExchangeSimulation.actual_selected_program
    exchange hframe layout ep s

#print axioms localEq
#print axioms raw_physical
#print axioms actual_selected_raw

end
end CodedSorting.Construction.MachineNetworkAdapter
end Binding

section ActualEdges
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
namespace CodedSorting.Construction.MachineNetworkActualEdges
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonAddressLayout PartialSwapMachine PartialSwapExecution
open RankPartialSwapExecution ExchangeSpecialization OneLevelChildren
open scoped BigOperators
noncomputable section
attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  ExchangeSpecialization.uniform MachineNetworkAdapter.physicalInputs
  MachineNetworkAdapter.registerEnumeration MachineNetworkAdapter.originalEnumeration
variable (f Pref G S : Nat) (q : Configuration)
local instance : NeZero (radix^f) := ⟨pow_ne_zero _ radix_prime.ne_zero⟩
section Network

abbrev NodeCount := MachineNetworkAdapter.nodes TensorFrameNetwork.program
  (inputs := MachineNetworkAdapter.physicalInputs)

abbrev NetworkLayout (q : Configuration) (f Pref G S : Nat) :=
  MachineNetwork.Layout q MachineNetworkAdapter.physicalInputs NodeCount
    (FileVolume f Pref G S)

abbrev actualEdge (i : Fin NodeCount) : Edge :=
  (MachineNetworkAdapter.edgeEnumeration TensorFrameNetwork.program
    MachineNetworkAdapter.registerEnumeration).symm i

def edgeFile (e : Edge) : Fin (MachineNetworkAdapter.physicalInputs+NodeCount) :=
  MachineNetwork.nodeFile (inputs := MachineNetworkAdapter.physicalInputs)
    (MachineNetworkAdapter.edgeEnumeration TensorFrameNetwork.program
      MachineNetworkAdapter.registerEnumeration e)

abbrev NetworkChildren (q : Configuration) (f Pref G S : Nat)
    (layout : NetworkLayout q f Pref G S) :=
  (e : Edge) → Children f Pref G S q e (layout.base (edgeFile e)) layout.buffer layout.limit

/-- Change only the name of an equal source address. Code and charge are
preserved literally, including when a dependent edge index is transported. -/
def atSource {q : Configuration} {V source source' buffer limit : Nat}
    {π : Equiv.Perm (Fin V)}
    (p : CommonFinitePermutation.Program q V source buffer limit π) (h : source=source') :
    CommonFinitePermutation.Program q V source' buffer limit π where
  instructions := p.instructions
  charge := p.charge
  correct := by simpa only [← h] using p.correct
  frame := by simpa only [← h] using p.frame
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

variable {f Pref G S q}

def edgeAllocation (layout : NetworkLayout q f Pref G S)
    (hroom : layout.buffer+count q (FileVolume f Pref G S) ≤ layout.limit) (e : Edge) :
    ScanAllocation q (FileVolume f Pref G S) (layout.base (edgeFile e))
      layout.buffer layout.limit where
  source_separate := (Nat.add_le_add_left layout.count_le_stride _).trans
    (layout.base_end_le (edgeFile e))
  buffer_fits := hroom
  limit_fits := layout.fit

variable (f Pref G S q)

def networkPrograms (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (layout : NetworkLayout q f Pref G S)
    (hroom : layout.buffer+count q (FileVolume f Pref G S) ≤ layout.limit)
    (children : NetworkChildren q f Pref G S layout) :
    MachineNetwork.Programs
      (MachineNetworkAdapter.actualCircuit (location f Pref G S)) layout := by
  intro i
  let e := actualEdge i
  let p := program f Pref G S hG hS q e reader (edgeAllocation layout hroom e) (children e)
  have hi : edgeFile e = MachineNetwork.nodeFile i := by
    simp only [edgeFile, e, actualEdge, Equiv.apply_symm_apply]
  exact RankPartialSwapMachine.relabel (atSource p (congrArg layout.base hi))
    (ExchangeSpecialization.edgePermutation_eq f Pref G S e).symm

theorem networkPrograms_charge (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (layout : NetworkLayout q f Pref G S)
    (hroom : layout.buffer+count q (FileVolume f Pref G S) ≤ layout.limit)
    (children : NetworkChildren q f Pref G S layout) (i : Fin NodeCount) :
    (networkPrograms f Pref G S q reader hG hS layout hroom children i).charge =
      (program f Pref G S hG hS q (actualEdge i) reader
        (edgeAllocation layout hroom (actualEdge i)) (children (actualEdge i))).charge := rfl

theorem networkPrograms_charge_le (reader : Fin q.inventory.readers)
    (hG : 0 < G) (hS : 0 < S) (layout : NetworkLayout q f Pref G S)
    (hroom : layout.buffer+count q (FileVolume f Pref G S) ≤ layout.limit)
    (children : NetworkChildren q f Pref G S layout) (i : Fin NodeCount) :
    (networkPrograms f Pref G S q reader hG hS layout hroom children i).charge ≤
      coefficient (actualEdge i)*count q (FileVolume f Pref G S) +
        ∑ j, (children (actualEdge i) j).charge := by
  rw [networkPrograms_charge]
  exact program_charge_le f Pref G S hG hS q (actualEdge i) reader _ _


def localCoefficient : Nat :=
  3*(∑ i : Fin NodeCount,
    ((MachineNetworkAdapter.ports TensorFrameNetwork.program
      MachineNetworkAdapter.registerEnumeration (actualEdge i)).length+1)) +
    ∑ e : Edge, coefficient e

/-- This coefficient is fixed by the rational Construction construction. The sum
below indexes the actual rank children, whose cardinality is rankBudget. -/
theorem network_charge_le (reader : Fin q.inventory.readers)
    (hG : 0 < G) (hS : 0 < S) (layout : NetworkLayout q f Pref G S)
    (hroom : layout.buffer+count q (FileVolume f Pref G S) ≤ layout.limit)
    (children : NetworkChildren q f Pref G S layout) :
    MachineNetwork.charge (MachineNetworkAdapter.actualCircuit (location f Pref G S))
      layout (networkPrograms f Pref G S q reader hG hS layout hroom children) ≤
      localCoefficient*count q (FileVolume f Pref G S) +
        ∑ c : OneLevelChildren.Child, (children c.1 c.2).charge := by
  have h := MachineNetwork.charge_le
    (MachineNetworkAdapter.actualCircuit (location f Pref G S)) layout
    (networkPrograms f Pref G S q reader hG hS layout hroom children)
    (fun i => coefficient (actualEdge i))
    (fun i => ∑ j, (children (actualEdge i) j).charge)
    (networkPrograms_charge_le f Pref G S q reader hG hS layout hroom children)
  have hc : (∑ i : Fin NodeCount, coefficient (actualEdge i)) =
      ∑ e : Edge, coefficient e :=
    (MachineNetworkAdapter.edgeEnumeration TensorFrameNetwork.program
      MachineNetworkAdapter.registerEnumeration).symm.sum_comp coefficient
  have hh : (∑ i : Fin NodeCount, ∑ j, (children (actualEdge i) j).charge) =
      ∑ c : OneLevelChildren.Child, (children c.1 c.2).charge := by
    calc
      _ = ∑ e : Edge, ∑ j, (children e j).charge :=
        (MachineNetworkAdapter.edgeEnumeration TensorFrameNetwork.program
          MachineNetworkAdapter.registerEnumeration).symm.sum_comp
          (fun e => ∑ j, (children e j).charge)
      _ = _ := OneLevelChildren.child_sum (fun c => (children c.1 c.2).charge)
  rw [hc, hh] at h
  exact h

end Network

#print axioms program
#print axioms program_charge_le
#print axioms networkPrograms
#print axioms networkPrograms_charge_le
#print axioms network_charge_le
end
end CodedSorting.Construction.MachineNetworkActualEdges
end ActualEdges
