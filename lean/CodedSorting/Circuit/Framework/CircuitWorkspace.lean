import CodedSorting.Shared.Memory.ProgramWorkspace
import CodedSorting.Shared.Memory.PhysicalLayerCost

/-! Named file slots of the already implemented network layer. This list
covers banks, gate outputs, and all matrix/scalar address programs. Outer
partition/gather/initialization programs must be added before calling it a
complete invocation workspace. -/
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 250000
namespace CodedSorting.CircuitWorkspace
open RecursiveExchange RecursiveExchangeCost PhysicalLayerCost ProgramWorkspace
open scoped BigOperators
noncomputable section

/-- A fresh result file for each actual XOR scan, including intermediate
control sums; forwarded source/pass outputs do not allocate a new file. -/
def GateSlot := (e : Edge) × Fin (edgeGateScans e)

instance gateSlotFintype : Fintype GateSlot :=
  inferInstanceAs (Fintype ((e : Edge) × Fin (edgeGateScans e)))

theorem gate_slot_bound : Fintype.card GateSlot≤gateLocalConstant := by
  simp only [GateSlot,Fintype.card_sigma,Fintype.card_fin,gateLocalConstant]
  exact Finset.sum_le_sum (fun e _ => Nat.le_mul_of_pos_left (edgeGateScans e) (by decide : 0<3))

/-- Two boundary files, all source registers, all stored physical edges,
actual XOR-control results, and actual per-pass bucket/output files. -/
def KnownLayerSlot (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :=
  Fin 2 ⊕ Reg ⊕ Edge ⊕ GateSlot ⊕ AddressSlot f P G S hG hS

/-- Compose two finite file-name assignments without enumerating the enormous
combined network type. -/
def sumIndex {α β : Type*} {a b : ℕ} (left : α↪Fin a) (right : β↪Fin b) :
    α⊕β↪Fin (a+b) :=
  (left.sumMap right).trans finSumFinEquiv.toEmbedding

def gateSlotIndex : GateSlot↪Fin gateLocalConstant where
  toFun slot := ((Fintype.equivFin GateSlot) slot).castLE gate_slot_bound
  inj' x y h := by
    apply (Fintype.equivFin GateSlot).injective
    apply Fin.ext
    simpa only [Fin.coe_castLE] using congrArg (@Fin.val gateLocalConstant) h

/-- Tagged finite budgets avoid forcing evaluation of the enormous closed
network enumeration merely to flatten its file identifiers. -/
abbrev BudgetSlot := Fin 2 ⊕ Fin Parameters.W ⊕ Fin (Fintype.card Edge) ⊕
  Fin gateLocalConstant ⊕ Fin addressLocalConstant

/-- The budget is exactly the cardinality of the explicit tagged family,
so no unspecified large constant is used. -/
def knownLayerBudget := Fintype.card BudgetSlot

/-- Every actual known-layer file has a distinct tag within the explicit
fixed finite budgets. -/
def knownLayerTagIndex (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    KnownLayerSlot f P G S hG hS↪BudgetSlot :=
  (Function.Embedding.refl _).sumMap
    (roleEnumeration.toEmbedding.sumMap
      ((Fintype.equivFin Edge).toEmbedding.sumMap
        (gateSlotIndex.sumMap (addressSlotIndex f P G S hG hS))))

def knownLayerIndex (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    KnownLayerSlot f P G S hG hS↪Fin knownLayerBudget :=
  (knownLayerTagIndex f P G S hG hS).trans (Fintype.equivFin BudgetSlot).toEmbedding

theorem knownLayerIndex_injective (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    Function.Injective (knownLayerIndex f P G S hG hS) :=
  (knownLayerIndex f P G S hG hS).injective

/-- Uniform polynomial exponent for allocating all known-layer files of
all real recursive invocations simultaneously. -/
def knownExponent := Nat.clog 2 knownLayerBudget+2*Nat.clog radix (Parameters.S+1)+1

theorem known_layer_span_bound (base cutoff k rows : ℕ) (hb : 0<base)
    (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P ≃ Fin (rows*Parameters.W^k))
    (hV : 0<Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z))
    (file : WorkspaceAllocation.Span)
    (hf : file∈WorkspaceAllocation.Exchange.files knownLayerBudget
      (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls) :
    let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
    file.start≤V^knownExponent ∧ file.blocks≤V^knownExponent ∧ file.stop≤V^knownExponent :=
  WorkspaceAllocation.Exchange.actual_span_bound knownLayerBudget base cutoff k rows hb leaf charge layout hV file hf

end
end CodedSorting.CircuitWorkspace
