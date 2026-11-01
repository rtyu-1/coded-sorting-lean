import CodedSorting.Interchange.Recursion.Resources
import CodedSorting.Interchange.Recursion.Endpoint

/-! The canonical recursive Construction exchange on one fixed machine inventory.
Only the ordinary common-machine conditions and the counted canonical
input remain as hypotheses. The fixed inventory supplies reader zero and
the normalization threshold; the fixed exponent supplies disk and code
capacity. The executable program and its initialized-PC run are exactly
those of `RecursiveEndpoint`, with no new implementation or execution
assumption. This is an equal-width exchange endpoint, not full sorting. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveConfiguredEndpoint

open CommonSortingNormalization SortingResourceBudget
open CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface ExchangeSpecialization
open RecursiveParameters RecursiveRootLayout RecursiveResources

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

variable (N M B w c : Nat)
  (hinput : 2 ≤ N) (hmem : M ≤ N) (hB : 0 < B) (hblock : 2*B ≤ M)
  (hword : WordConvention.Covers N w c)
  (hlarge : (reserve RecursiveMachine.fixedInventory c
    (digits c RecursiveCapacity.addressExponent))^2 ≤ M)

local notation "cfg" =>
  RecursiveMachine.configuration N M B w c hinput hmem hB hblock hword hlarge
local notation "reader0" =>
  RecursiveMachine.reader N M B w c hinput hmem hB hblock hword hlarge
local notation "thresholdProof" =>
  RecursiveMachine.inventory_threshold N M B w c hinput hmem hB hblock hword hlarge
local notation "exponentProof" =>
  RecursiveMachine.exponent_sufficient N M B w c hinput hmem hB hblock hword hlarge

/-- The previously verified program with its machine choices fixed. -/
def program (k lanes G S : Nat) (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords cfg (chosenBase cfg) k lanes G S ≤ (cfg).N) :
    Program cfg radix (root cfg k lanes G S) :=
  RecursiveEndpoint.program cfg reader0 k lanes G S thresholdProof hG hS hwords exponentProof

/-- Fixing the machine choices adds no instructions to the actual builder. -/
theorem program_instructions (k lanes G S : Nat) (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords cfg (chosenBase cfg) k lanes G S ≤ (cfg).N) :
    (program N M B w c hinput hmem hB hblock hword hlarge k lanes G S hG hS hwords).instructions =
      (RecursiveBuild.build cfg reader0 (cutoff cfg) k (root cfg k lanes G S)
        (RecursiveResources.ready cfg k lanes G S
          (normalized_of_inventory cfg thresholdProof) hG hS hwords exponentProof)).instructions :=
  RecursiveEndpoint.program_instructions cfg reader0 k lanes G S
    thresholdProof hG hS hwords exponentProof

/-- The entire root disk interval fits without a caller-supplied reserve. -/
theorem diskFits (k lanes G S : Nat)
    (hwords : rootWords cfg (chosenBase cfg) k lanes G S ≤ (cfg).N) :
    (root cfg k lanes G S).limit ≤ (cfg).N^(cfg).exponent :=
  root_disk_fits cfg k lanes G S hwords exponentProof

/-- Both actual charge and instruction count fit the fixed address space. -/
theorem codeFits (k lanes G S : Nat) (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords cfg (chosenBase cfg) k lanes G S ≤ (cfg).N) :
    let p := program N M B w c hinput hmem hB hblock hword hlarge k lanes G S hG hS hwords
    p.charge ≤ (cfg).N^(cfg).exponent ∧ p.instructions.length ≤ (cfg).N^(cfg).exponent :=
  ⟨RecursiveEndpoint.program_charge_fits cfg reader0 k lanes G S
      thresholdProof hG hS hwords exponentProof,
    RecursiveEndpoint.program_length_fits cfg reader0 k lanes G S
      thresholdProof hG hS hwords exponentProof⟩

/-- One actual run has the claimed permutation, outside-disk frame, halt,
improved I/O and instruction bounds, and resident RAM bound. The reserved
PC is explicitly initialized while the input disk remains unchanged.
No reader, inventory threshold, address exponent, descendant resource,
charge-capacity or initial-PC proof is supplied by the caller. -/
theorem complete (k lanes G S : Nat) (hG : 0 < G) (hS : 0 < S)
    (hwords : rootWords cfg (chosenBase cfg) k lanes G S ≤ (cfg).N) (s : Machine cfg) :
    let p := program N M B w c hinput hmem hB hblock hword hlarge k lanes G S hG hS hwords
    let result := ControlledNormalization.runLogical (policy cfg p.instructions)
      p.instructions.length (RecursiveEndpoint.initialState cfg s)
    (∀ y : Fin (volume radix (root cfg k lanes G S)),
      readBit cfg result.1.disk (root cfg k lanes G S).source y.val =
        readBit cfg s.disk (root cfg k lanes G S).source
          (permutation radix (root cfg k lanes G S) y).val) ∧
    (∀ z : Fin ((cfg).N^(cfg).exponent), (root cfg k lanes G S).limit ≤ z.val →
      result.1.disk z = s.disk z) ∧
    policy cfg p.instructions result.1.ram = none ∧
    (result.2 : ℝ) ≤ RecursiveCostRate.rateConstant *
      (1 + (volume radix (root cfg k lanes G S) : ℝ) / width cfg *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) ∧
    (p.instructions.length : ℝ) ≤ RecursiveCostRate.rateConstant *
      (1 + (volume radix (root cfg k lanes G S) : ℝ) / width cfg *
        (ambientDimension : ℝ) ^ ((k : ℝ) * (1 - (Construction.epsilon : ℝ)))) ∧
    Fintype.card (ResidentIndex cfg) ≤ (cfg).M :=
  RecursiveEndpoint.complete cfg reader0 k lanes G S thresholdProof hG hS hwords exponentProof s

end
end CodedSorting.Construction.RecursiveConfiguredEndpoint
