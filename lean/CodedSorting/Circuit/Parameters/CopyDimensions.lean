import CodedSorting.Generated.FiniteCircuit.ArrayLookup

namespace CodedSorting.Construction
open FiniteCertificate

theorem actualCopyDimensions (t : Fin 9) : projections[510+t.val]!.dimension = 7 := by
  have ht := t.isLt
  rcases (show t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨
    t.val = 4 ∨ t.val = 5 ∨ t.val = 6 ∨ t.val = 7 ∨ t.val = 8 by omega) with
    h | h | h | h | h | h | h | h | h <;>
    rw [h, projections_lookup] <;> rfl

#print axioms actualCopyDimensions
end CodedSorting.Construction
