import CodedSorting.Interchange.Recursion.Resources

section CostBounds
/-! The improved Construction rate attached to the actual recursively generated code.
The charge, static I/O fees, instruction length and controlled execution
below all use `RecursiveBuild.build`, not a supplied implementation kit.
The stronger cutoff condition absorbs child startup while preserving the
exact rank/stream multiplier. Public recurrence capacity and the initial
PC condition remain explicit at the controlled-run endpoint. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveCostBounds

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface ExchangeSpecialization RecursiveBuildConditions
open RecursiveCostRate (rateConstant)

noncomputable section

local notation "coefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs MachineNetworkActualEdges.localCoefficient

/-- The actual returned charge has the improved Construction exponent, with one
constant shared by all admissible machines, inputs, depths and cutoffs. -/
theorem build_charge_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c)
    (hcutoff : streamCount * width q ≤ cutoff) :
    ((RecursiveBuild.build q reader cutoff k c h).charge : ℝ) ≤
      rateConstant * (1 + (volume radix c : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  (Nat.cast_le.mpr (RecursiveCost.build_charge_le q reader cutoff k c h)).trans
    (RecursiveCostRate.costBound_le_rate (width q) cutoff k (volume radix c)
      (width_pos q) hcutoff)

/-- Every transfer fee of the same instruction list is included. -/
theorem build_cost_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c)
    (hcutoff : streamCount * width q ≤ cutoff) :
    (cost q (RecursiveBuild.build q reader cutoff k c h).instructions : ℝ) ≤
      rateConstant * (1 + (volume radix c : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  (Nat.cast_le.mpr (RecursiveCost.build_cost_le q reader cutoff k c h)).trans
    (RecursiveCostRate.costBound_le_rate (width q) cutoff k (volume radix c)
      (width_pos q) hcutoff)

/-- Compressed instruction length of exactly the same actual code. -/
theorem build_length_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c)
    (hcutoff : streamCount * width q ≤ cutoff) :
    ((RecursiveBuild.build q reader cutoff k c h).instructions.length : ℝ) ≤
      rateConstant * (1 + (volume radix c : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  (Nat.cast_le.mpr (RecursiveCost.build_length_le q reader cutoff k c h)).trans
    (RecursiveCostRate.costBound_le_rate (width q) cutoff k (volume radix c)
      (width_pos q) hcutoff)

/-- Correctness, disk frame, halt, improved I/O and resident RAM for one
controlled run of the actual recursively generated program. -/
theorem complete_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c)
    (hcutoff : streamCount * width q ≤ cutoff) (s : Machine q)
    (hsize : costBound coefficient (width q) cutoff k (volume radix c) ≤ q.N^q.exponent)
    (hpc : pc q s.ram = 0) :
    let p := RecursiveBuild.build q reader cutoff k c h
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q s.disk c.source (permutation radix c y).val) ∧
    (∀ z : Fin (q.N^q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) → result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧
    (result.2 : ℝ) ≤ rateConstant * (1 + (volume radix c : ℝ) / width q *
      (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  obtain ⟨hc, hf, hh, hcost, hram⟩ := RecursiveCost.complete q reader cutoff k c h s hsize hpc
  exact ⟨hc, hf, hh, (Nat.cast_le.mpr hcost).trans
    (RecursiveCostRate.costBound_le_rate (width q) cutoff k (volume radix c)
      (width_pos q) hcutoff), hram⟩

#print axioms build_charge_le_rate
#print axioms build_cost_le_rate
#print axioms build_length_le_rate
#print axioms complete_rate

end
end CodedSorting.Construction.RecursiveCostBounds
end CostBounds

section CostProgram
/-! Global fees and instruction counts for the same root-constructed program.
Workspace comes from the previously verified linear root reserve. The exact
integer fee recurrence controls the actual program counter; the improved
real bound uses Construction's fixed constant and epsilon with its stronger cutoff.
No child program, tree, Ready certificate or successful run is an input. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveCostProgram

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface ExchangeSpecialization
open RecursiveCallShape RecursiveWorkspaceBudget

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

local notation "coefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)

/-- The integer recurrence bounds the actual program's charge. -/
theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + RecursiveWorkspaceProgram.linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) :
    (RecursiveWorkspaceProgram.program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).charge ≤
      costBound coefficient (width q) cutoff k (volume radix c) :=
  RecursiveCost.build_charge_le q reader cutoff k c (RecursiveWorkspaceProgram.ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk)

/-- The integer recurrence bounds the actual program's cost. -/
theorem program_cost_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + RecursiveWorkspaceProgram.linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) :
    cost q (RecursiveWorkspaceProgram.program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).instructions ≤
      costBound coefficient (width q) cutoff k (volume radix c) :=
  RecursiveCost.build_cost_le q reader cutoff k c (RecursiveWorkspaceProgram.ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk)

/-- The integer recurrence bounds the actual program's length. -/
theorem program_length_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + RecursiveWorkspaceProgram.linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) :
    (RecursiveWorkspaceProgram.program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).instructions.length ≤
      costBound coefficient (width q) cutoff k (volume radix c) :=
  RecursiveCost.build_length_le q reader cutoff k c (RecursiveWorkspaceProgram.ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk)

/-- The same charge, with the fixed Construction exponent improvement. -/
theorem program_charge_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + RecursiveWorkspaceProgram.linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent)
    (hrate : streamCount * width q ≤ cutoff) :
    ((RecursiveWorkspaceProgram.program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).charge : ℝ) ≤
      RecursiveCostRate.rateConstant * (1 + (volume radix c : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  RecursiveCostBounds.build_charge_le_rate q reader cutoff k c (RecursiveWorkspaceProgram.ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk) hrate

/-- The same cost, with the fixed Construction exponent improvement. -/
theorem program_cost_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + RecursiveWorkspaceProgram.linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent)
    (hrate : streamCount * width q ≤ cutoff) :
    (cost q (RecursiveWorkspaceProgram.program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).instructions : ℝ) ≤
      RecursiveCostRate.rateConstant * (1 + (volume radix c : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  RecursiveCostBounds.build_cost_le_rate q reader cutoff k c (RecursiveWorkspaceProgram.ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk) hrate

/-- The same length, with the fixed Construction exponent improvement. -/
theorem program_length_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + RecursiveWorkspaceProgram.linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent)
    (hrate : streamCount * width q ≤ cutoff) :
    ((RecursiveWorkspaceProgram.program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk).instructions.length : ℝ) ≤
      RecursiveCostRate.rateConstant * (1 + (volume radix c : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  RecursiveCostBounds.build_length_le_rate q reader cutoff k c (RecursiveWorkspaceProgram.ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk) hrate

/-- Correctness, frame, halt, integer I/O bound and RAM for this program.
The displayed numerical recurrence replaces an opaque actual-charge premise. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + RecursiveWorkspaceProgram.linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) (s : Machine q)
    (hsize : costBound coefficient (width q) cutoff k (volume radix c) ≤ q.N^q.exponent)
    (hpc : pc q s.ram = 0) :
    let p := RecursiveWorkspaceProgram.program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q s.disk c.source (permutation radix c y).val) ∧
    (∀ z : Fin (q.N^q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) → result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧
    result.2 ≤ costBound coefficient (width q) cutoff k (volume radix c) ∧
    Fintype.card (ResidentIndex q) ≤ q.M :=
  RecursiveCost.complete q reader cutoff k c (RecursiveWorkspaceProgram.ready_of_linear q cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk) s hsize hpc

/-- The same controlled execution with the improved real I/O bound.
Parameter selection and the numerical PC-capacity inequality remain explicit. -/
theorem complete_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hcutoff : width q ≤ cutoff) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + RecursiveWorkspaceProgram.linearReserve q (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) (hrate : streamCount * width q ≤ cutoff)
    (s : Machine q)
    (hsize : costBound coefficient (width q) cutoff k (volume radix c) ≤ q.N^q.exponent)
    (hpc : pc q s.ram = 0) :
    let p := RecursiveWorkspaceProgram.program q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q s.disk c.source (permutation radix c y).val) ∧
    (∀ z : Fin (q.N^q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) → result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧
    (result.2 : ℝ) ≤
      RecursiveCostRate.rateConstant * (1 + (volume radix c : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  obtain ⟨hc, hf, hh, hcost, hram⟩ := complete q reader cutoff base k c hp hcutoff hshape hwidth hsource hspace hdisk s hsize hpc
  have hb := RecursiveCostRate.costBound_le_rate (width q) cutoff k (volume radix c)
    (width_pos q) hrate
  exact ⟨hc, hf, hh, (Nat.cast_le.mpr hcost).trans hb, hram⟩

end
end CodedSorting.Construction.RecursiveCostProgram
end CostProgram

section Endpoint
/-! The executable canonical Construction recursion with uniform resource choices.
A counted input, the fixed memory-normalization threshold and fixed address
exponent supply every leaf, descendant allocation and code-capacity proof.
The run explicitly initializes only the reserved PC; its input disk is
unchanged. This is a canonical equal-width exchange, not arbitrary-length
exchange or the full sorting theorem. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveEndpoint

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface ExchangeSpecialization
open RecursiveParameters RecursiveRootLayout RecursiveResources

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

/-- The same recursive builder, now with every resource certificate derived
from uniform machine choices and the counted canonical input. -/
def program (q : Configuration) (reader : Fin q.inventory.readers)
    (k lanes G S : Nat)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤ q.inventory.ratio)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) : Program q radix (root q k lanes G S) :=
  RecursiveBuild.build q reader (cutoff q) k (root q k lanes G S) (RecursiveResources.ready q k lanes G S (normalized_of_inventory q hthreshold) hG hS hwords hexponent)

/-- Resource selection changes no instruction of the previously verified
recursive builder. -/
theorem program_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (k lanes G S : Nat)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤ q.inventory.ratio)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    (program q reader k lanes G S hthreshold hG hS hwords hexponent).instructions =
      (RecursiveBuild.build q reader (cutoff q) k (root q k lanes G S) (RecursiveResources.ready q k lanes G S (normalized_of_inventory q hthreshold) hG hS hwords hexponent)).instructions := rfl

/-- The generated charge fits the fixed configured address space. -/
theorem program_charge_fits (q : Configuration) (reader : Fin q.inventory.readers)
    (k lanes G S : Nat)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤ q.inventory.ratio)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    (program q reader k lanes G S hthreshold hG hS hwords hexponent).charge ≤ q.N^q.exponent :=
  (RecursiveCost.build_charge_le q reader (cutoff q) k (root q k lanes G S) (RecursiveResources.ready q k lanes G S (normalized_of_inventory q hthreshold) hG hS hwords hexponent)).trans
    (root_code_fits q k lanes G S hG hS hwords hexponent)

/-- No program-length capacity assumption is supplied by the caller. -/
theorem program_length_fits (q : Configuration) (reader : Fin q.inventory.readers)
    (k lanes G S : Nat)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤ q.inventory.ratio)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    (program q reader k lanes G S hthreshold hG hS hwords hexponent).instructions.length ≤ q.N^q.exponent :=
  (program q reader k lanes G S hthreshold hG hS hwords hexponent).length_le.trans
    (program_charge_fits q reader k lanes G S hthreshold hG hS hwords hexponent)

/-- The improved Construction charge bound for this same concrete program. -/
theorem program_charge_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (k lanes G S : Nat)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤ q.inventory.ratio)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    ((program q reader k lanes G S hthreshold hG hS hwords hexponent).charge : ℝ) ≤
      RecursiveCostRate.rateConstant *
      (1 + (volume radix (root q k lanes G S) : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  RecursiveCostBounds.build_charge_le_rate q reader (cutoff q) k (root q k lanes G S)
    (RecursiveResources.ready q k lanes G S (normalized_of_inventory q hthreshold) hG hS hwords hexponent) (cutoff_child q (normalized_of_inventory q hthreshold))

/-- The improved Construction cost bound for this same concrete program. -/
theorem program_cost_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (k lanes G S : Nat)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤ q.inventory.ratio)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    (cost q (program q reader k lanes G S hthreshold hG hS hwords hexponent).instructions : ℝ) ≤
      RecursiveCostRate.rateConstant *
      (1 + (volume radix (root q k lanes G S) : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  RecursiveCostBounds.build_cost_le_rate q reader (cutoff q) k (root q k lanes G S)
    (RecursiveResources.ready q k lanes G S (normalized_of_inventory q hthreshold) hG hS hwords hexponent) (cutoff_child q (normalized_of_inventory q hthreshold))

/-- The improved Construction length bound for this same concrete program. -/
theorem program_length_le_rate (q : Configuration) (reader : Fin q.inventory.readers)
    (k lanes G S : Nat)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤ q.inventory.ratio)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) :
    ((program q reader k lanes G S hthreshold hG hS hwords hexponent).instructions.length : ℝ) ≤
      RecursiveCostRate.rateConstant *
      (1 + (volume radix (root q k lanes G S) : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) :=
  RecursiveCostBounds.build_length_le_rate q reader (cutoff q) k (root q k lanes G S)
    (RecursiveResources.ready q k lanes G S (normalized_of_inventory q hthreshold) hG hS hwords hexponent) (cutoff_child q (normalized_of_inventory q hthreshold))

/-- Explicit initialization of the reserved program counter. This is a
choice of starting RAM state, not a change to the input disk or a claim
that an arbitrary pre-existing PC starts the recursive code correctly. -/
def initialState (q : Configuration) (s : Machine q) : Machine q := erasePC q s

theorem initialState_disk (q : Configuration) (s : Machine q) :
    (initialState q s).disk = s.disk := rfl

theorem initialState_pc (q : Configuration) (s : Machine q) :
    pc q (initialState q s).ram = 0 :=
  pc_setPC q 0 s.ram (Nat.zero_le _)

/-- Correct output, protected outside disk, halt, improved I/O, improved
instruction length and resident RAM all refer to this same actual program.
There are no per-child proofs, scratch-fit, actual-charge, numerical
recurrence-capacity or initial-PC assumptions at this public endpoint. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (k lanes G S : Nat)
    (hthreshold : PhysicalLeafParameters.minimumRatio radix 1 streamCount ≤ q.inventory.ratio)
    (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords q (chosenBase q) k lanes G S ≤ q.N)
    (hexponent : RecursiveCapacity.addressExponent ≤ q.exponent) (s : Machine q) :
    let p := program q reader k lanes G S hthreshold hG hS hwords hexponent
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length (initialState q s)
    (∀ y : Fin (volume radix (root q k lanes G S)),
      readBit q result.1.disk (root q k lanes G S).source y.val =
        readBit q s.disk (root q k lanes G S).source (permutation radix (root q k lanes G S) y).val) ∧
    (∀ z : Fin (q.N^q.exponent), (root q k lanes G S).limit ≤ z.val →
      result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧
    (result.2 : ℝ) ≤ RecursiveCostRate.rateConstant *
      (1 + (volume radix (root q k lanes G S) : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) ∧
    (p.instructions.length : ℝ) ≤ RecursiveCostRate.rateConstant *
      (1 + (volume radix (root q k lanes G S) : ℝ) / width q *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  obtain ⟨hc, hf, hh, hcost, hram⟩ := RecursiveCostBounds.complete_rate
    q reader (cutoff q) k (root q k lanes G S) (RecursiveResources.ready q k lanes G S (normalized_of_inventory q hthreshold) hG hS hwords hexponent)
    (cutoff_child q (normalized_of_inventory q hthreshold)) (initialState q s)
    (root_code_fits q k lanes G S hG hS hwords hexponent)
    (initialState_pc q s)
  refine ⟨hc, ?_, hh, hcost, program_length_le_rate q reader k lanes G S hthreshold hG hS hwords hexponent, hram⟩
  intro z hz
  have hbuffer : (root q k lanes G S).buffer ≤ (root q k lanes G S).limit := Nat.le_add_right _ _
  exact hf z (Or.inr ((root_source_separate q (chosenBase q) k lanes G S).trans
    (hbuffer.trans hz))) (Or.inr hz)

end
end CodedSorting.Construction.RecursiveEndpoint
end Endpoint
