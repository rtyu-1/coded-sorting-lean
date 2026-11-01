import CodedSorting.Interchange.OneLevel.Allocation
import CodedSorting.Circuit.NetworkModel.Adapter
import CodedSorting.Interchange.Streams.StreamParentProgram

/-! Concrete one-level Construction exchange.  All frame identities, finite-ring
specialization, edge programs and network semantics are instantiated here.
The remaining inputs are actual smaller scalar exchange programs and public
space bounds.  Full recursive tree construction is a separate next step. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace CodedSorting.Construction.OneLevelExchange

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonAddressLayout StreamSplitLayout ExchangeSpecialization
open OneLevelChildren
open scoped BigOperators

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  ExchangeSpecialization.uniform MachineNetworkAdapter.physicalInputs
  MachineNetworkAdapter.registerEnumeration MachineNetworkAdapter.originalEnumeration

abbrev Setup (q : Configuration) (f rows G S source temporary : Nat) :=
  OneLevelAssembly.Setup q (radix^f) rows G S source temporary

variable {q : Configuration} {f rows G S source temporary : Nat}

def parentCall (a : Setup q f rows G S source temporary) : ExchangeInterface.Call :=
  ⟨ambientDimension*f, rows*streamCount, G, S*q.w, source, temporary, a.network.limit⟩

def childRow (c : Child) : Fin 512 :=
  (RankPartialSwapExecution.supports (decomposition c.1) ((childIndex c.1).symm c.2)).first

def childCol (c : Child) : Fin 512 :=
  (RankPartialSwapExecution.supports (decomposition c.1) ((childIndex c.1).symm c.2)).last

/-- Keep the dependent file index within its already verified network-layout
interface, rather than normalizing the concrete network size at each call. -/
def edgeSource (layout : MachineNetworkActualEdges.NetworkLayout q f rows G (S*q.w))
    (e : Edge) : Nat :=
  layout.base (MachineNetworkActualEdges.edgeFile e)

def childCall (a : Setup q f rows G S source temporary) (c : Child) : ExchangeInterface.Call :=
  selectedCall radix 512 f rows G (S*q.w) (childRow c) (childCol c)
    (edgeSource a.network c.1) a.network.buffer a.network.limit

abbrev Children (a : Setup q f rows G S source temporary) :=
  (c : Child) → ExchangeInterface.Program q radix (childCall a c)

/-- The same scalar child code is interpreted at its identical packed
addresses; this conversion adds no instruction or fee. -/
def selectedChildren (a : Setup q f rows G S source temporary) (children : Children a) :
    MachineNetworkActualEdges.NetworkChildren q f rows G (S*q.w) a.network := by
  intro e i
  exact selectedChildProgram q radix 512 f rows G (S*q.w) (childRow ⟨e,i⟩) (childCol ⟨e,i⟩)
    (edgeSource a.network e) a.network.buffer a.network.limit
    (children ⟨e,i⟩)

theorem selectedChildren_charge (a : Setup q f rows G S source temporary)
    (children : Children a) (c : Child) :
    (selectedChildren a children c.1 c.2).charge = (children c).charge := rfl

def edgePrograms (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer + count q (OneLevelAssembly.localVolume q (radix^f) rows G S)
      ≤ a.network.limit) (children : Children a) :=
  MachineNetworkActualEdges.networkPrograms f rows G (S*q.w) q reader hG
    (Nat.mul_pos hS (by have := q.word_width; omega)) a.network hroom (selectedChildren a children)

def longProgram (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer + count q (OneLevelAssembly.localVolume q (radix^f) rows G S)
      ≤ a.network.limit) (children : Children a) :=
  OneLevelAssembly.program (location f rows G (S*q.w)) reader
    (selected_endpoint f rows G (S*q.w)) a (edgePrograms reader hG hS a hroom children)

/-- The concrete one-level scalar exchange program. -/
def program (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer + count q (OneLevelAssembly.localVolume q (radix^f) rows G S)
      ≤ a.network.limit) (children : Children a) :
    ExchangeInterface.Program q radix (parentCall a) :=
  StreamParentProgram.parentProgram q radix ambientDimension f (rows*streamCount) G (S*q.w)
    source temporary a.network.limit (longProgram reader hG hS a hroom children)

/-- Instantiate the allocation as well: only the displayed numerical disk
bounds and actual smaller scalar programs are supplied by the caller. -/
def canonicalProgram (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (extra : Nat)
    (hsource : source + OneLevelAllocation.parentBlocks q (radix^f) rows G S ≤ temporary)
    (hfit : OneLevelAllocation.canonicalLimit q (radix^f) rows G S temporary extra ≤ q.N^q.exponent)
    (children : Children (OneLevelAllocation.canonicalSetup q (radix^f) rows G S
      source temporary extra hsource hfit)) :
    ExchangeInterface.Program q radix
      (parentCall (OneLevelAllocation.canonicalSetup q (radix^f) rows G S
        source temporary extra hsource hfit)) :=
  program reader hG hS
    (OneLevelAllocation.canonicalSetup q (radix^f) rows G S source temporary extra hsource hfit)
    (OneLevelAllocation.canonicalSetup_room q (radix^f) rows G S source temporary extra hsource hfit)
    children

theorem child_width (a : Setup q f rows G S source temporary) (c : Child) :
    (childCall a c).fieldWidth = f := rfl

theorem child_smaller (hf : 0 < f) (a : Setup q f rows G S source temporary) (c : Child) :
    (childCall a c).fieldWidth < (parentCall a).fieldWidth := by
  change f < ambientDimension*f
  rw [ambientDimension_eq]
  omega

theorem child_volume (a : Setup q f rows G S source temporary) (c : Child) :
    streamCount * ExchangeInterface.volume radix (childCall a c) =
      ExchangeInterface.volume radix (parentCall a) := by
  rw [childCall, selectedCall_volume]
  change streamCount * Volume (Fin 512) rows (radix^f) G (S*q.w) =
    ScalarVolume radix (ambientDimension*f) (rows*streamCount) G (S*q.w)
  rw [ambientDimension_eq, parent_volume]

theorem child_volume_div (a : Setup q f rows G S source temporary) (c : Child) :
    ExchangeInterface.volume radix (childCall a c) =
      ExchangeInterface.volume radix (parentCall a) / streamCount := by
  rw [←child_volume a c]
  exact (Nat.mul_div_cancel_left _ (by decide : 0 < streamCount)).symm

def localCoefficient : Nat :=
  24*streamCount+36+MachineNetworkActualEdges.localCoefficient

theorem local_count_le_parent :
    count q (OneLevelAssembly.localVolume q (radix^f) rows G S) ≤
      count q (OneLevelAssembly.parentVolume q (radix^f) rows G S) :=
  OneLevelAllocation.localBlocks_le_parent q (radix^f) rows G S

private theorem combineCharges {a b l p s k c : Nat}
    (hlocal : a ≤ k*p+b) (hnetwork : b ≤ c*l+s) (hblocks : l ≤ p) :
    a ≤ (k+c)*p+s := by
  have hm := Nat.mul_le_mul_left c hblocks
  calc
    a ≤ k*p+b := hlocal
    _ ≤ k*p+(c*l+s) := Nat.add_le_add_left hnetwork _
    _ ≤ k*p+(c*p+s) := Nat.add_le_add_left (Nat.add_le_add_right hm _) _
    _ = (k+c)*p+s := by ring

theorem selectedChildren_sum_charge (a : Setup q f rows G S source temporary)
    (children : Children a) :
    (∑ c : Child, (selectedChildren a children c.1 c.2).charge) =
      ∑ c : Child, (children c).charge := by
  apply Finset.sum_congr rfl
  intro c _
  exact selectedChildren_charge a children c

theorem program_charge (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer + count q (OneLevelAssembly.localVolume q (radix^f) rows G S)
      ≤ a.network.limit) (children : Children a) :
    (program reader hG hS a hroom children).charge =
      OneLevelAssembly.charge (location f rows G (S*q.w)) a
        (edgePrograms reader hG hS a hroom children) := rfl

theorem edge_network_charge_le (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer + count q (OneLevelAssembly.localVolume q (radix^f) rows G S)
      ≤ a.network.limit) (children : Children a) :
    MachineNetwork.charge (MachineNetworkAdapter.actualCircuit
      (V := OneLevelAssembly.localVolume q (radix^f) rows G S) (location f rows G (S*q.w)))
      a.network (edgePrograms reader hG hS a hroom children) ≤
        MachineNetworkActualEdges.localCoefficient *
          count q (OneLevelAssembly.localVolume q (radix^f) rows G S) +
        ∑ c : Child, (children c).charge := by
  have hn := MachineNetworkActualEdges.network_charge_le f rows G (S*q.w) q reader hG
    (Nat.mul_pos hS (by have := q.word_width; omega)) a.network hroom (selectedChildren a children)
  rw [selectedChildren_sum_charge] at hn
  exact hn

theorem assembly_charge_combined (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer + count q (OneLevelAssembly.localVolume q (radix^f) rows G S)
      ≤ a.network.limit) (children : Children a) :
    OneLevelAssembly.charge (location f rows G (S*q.w)) a
      (edgePrograms reader hG hS a hroom children) ≤
      ((24*streamCount+36)+MachineNetworkActualEdges.localCoefficient) *
        count q (OneLevelAssembly.parentVolume q (radix^f) rows G S) +
        ∑ c : Child, (children c).charge := by
  exact combineCharges
    (OneLevelAssembly.charge_bound (location f rows G (S*q.w)) a
      (edgePrograms reader hG hS a hroom children))
    (edge_network_charge_le reader hG hS a hroom children)
    (local_count_le_parent (q := q) (f := f) (rows := rows) (G := G) (S := S))

theorem parent_volume (a : Setup q f rows G S source temporary) :
    ExchangeInterface.volume radix (parentCall a) =
      OneLevelAssembly.parentVolume q (radix^f) rows G S :=
  packedVolume radix ambientDimension f (rows*streamCount) G (S*q.w)

private theorem transportChargeBound {a a' k k' p p' s : Nat}
    (ha : a = a') (hk : k = k') (hp : p = p')
    (h : a' ≤ k'*p'+s) : a ≤ k*p+s := by
  rw [ha, hk, hp]
  exact h

theorem charge_le (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer + count q (OneLevelAssembly.localVolume q (radix^f) rows G S)
      ≤ a.network.limit) (children : Children a) :
    (program reader hG hS a hroom children).charge ≤
      (24*streamCount+36+MachineNetworkActualEdges.localCoefficient) *
        count q (ExchangeInterface.volume radix (parentCall a)) +
        ∑ c : Child, (children c).charge := by
  exact transportChargeBound
    (program_charge reader hG hS a hroom children) rfl
    (congrArg (count q) (parent_volume a))
    (assembly_charge_combined reader hG hS a hroom children)

/-- Actual controlled execution, including halting and physical RAM use.
No network-correctness, rank-budget, endpoint, or specialization assumptions
occur here: all are supplied by the concrete Construction construction. -/
theorem complete (reader : Fin q.inventory.readers) (hG : 0 < G) (hS : 0 < S)
    (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer + count q (OneLevelAssembly.localVolume q (radix^f) rows G S)
      ≤ a.network.limit) (children : Children a) (s : Machine q)
    (hsize : (program reader hG hS a hroom children).charge ≤ q.N^q.exponent)
    (hpc : pc q s.ram = 0) :
    let p := program reader hG hS a hroom children
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (ExchangeInterface.volume radix (parentCall a)),
      readBit q result.1.disk source y.val =
        readBit q s.disk source (ExchangeInterface.permutation radix (parentCall a) y).val) ∧
    (∀ i : Fin (q.N^q.exponent),
      (i.val < source ∨ source + count q (ExchangeInterface.volume radix (parentCall a)) ≤ i.val) →
      (i.val < temporary ∨ a.network.limit ≤ i.val) → result.1.disk i = s.disk i) ∧
    policy q p.instructions result.1.ram = none ∧
    result.2 ≤ p.charge ∧ Fintype.card (ResidentIndex q) ≤ q.M :=
  CommonFinitePermutation.complete q (program reader hG hS a hroom children) s hsize hpc

#print axioms program
#print axioms canonicalProgram
#print axioms child_volume
#print axioms charge_le
#print axioms complete

end
end CodedSorting.Construction.OneLevelExchange
