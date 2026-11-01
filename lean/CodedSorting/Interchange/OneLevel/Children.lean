import CodedSorting.Circuit.Composition.TensorFrameCertifiedBudget

/-! The children of a concrete Construction exchange node are indexed by actual
physical edges and their rank coordinates.  Temporary-register edges remain
in this type.  Its cardinality comes from the checked physical rank budget,
not from an independently supplied recursion-size assumption. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.OneLevelChildren

open ProgramNetwork TensorFrameNetwork TensorLiftProgram
open scoped BigOperators

noncomputable section

attribute [local irreducible] program actualLabel

abbrev Edge := Wire GlobalReg program.length

def edgeRank (e : Edge) : Nat :=
  (actualLabel (wireHead program e) - actualLabel (wireTail program e)).rank

abbrev Child := (e : Edge) × Fin (edgeRank e)

theorem sum_edgeRank : (∑ e : Edge, edgeRank e) = rankBudget :=
  actualRank_eq_budget

theorem child_count : Fintype.card Child = rankBudget := by
  simp only [Child, Fintype.card_sigma, Fintype.card_fin]
  exact sum_edgeRank

/-- A public bijective enumeration, with no missing or repeated rank calls. -/
def enumeration : Child ≃ Fin rankBudget :=
  (Fintype.equivFin Child).trans (finCongr child_count)

theorem child_sum (charge : Child → Nat) :
    (∑ e : Edge, ∑ i : Fin (edgeRank e), charge ⟨e, i⟩) = ∑ c : Child, charge c :=
  (Fintype.sum_sigma charge).symm

/-- A node's edge-local scans have a fixed finite total coefficient, while
every supplied smaller child program contributes its charge exactly once. -/
theorem edge_charge_bound (edgeCharge coefficient : Edge → Nat)
    (childCharge : Child → Nat) (blocks : Nat)
    (h : ∀ e, edgeCharge e ≤ coefficient e * blocks +
      ∑ i : Fin (edgeRank e), childCharge ⟨e, i⟩) :
    (∑ e, edgeCharge e) ≤ (∑ e, coefficient e) * blocks + ∑ c, childCharge c := by
  calc
    (∑ e, edgeCharge e) ≤ ∑ e, (coefficient e * blocks +
        ∑ i : Fin (edgeRank e), childCharge ⟨e, i⟩) :=
      Finset.sum_le_sum (fun e _ => h e)
    _ = (∑ e, coefficient e) * blocks + ∑ c, childCharge c := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, child_sum]

#print axioms child_count
#print axioms edge_charge_bound

end
end CodedSorting.Construction.OneLevelChildren
