import CodedSorting.Circuit.MemoryAccess.PhysicalFramePaths
import CodedSorting.Generated.FiniteCircuit.ProjectionAlgebraChecks

section ProjectionAlgebraInterpretation
/-! Interpret exactly the finite algebra needed by the physical network.
Line membership in a separately listed frame is not required by this result. -/

namespace CodedSorting.Construction.FiniteProjectionInterpretation

open scoped BigOperators Matrix
open FiniteCertificate IntegerProjection

theorem projection_equations_of_algebraCheck (p : Projection)
    (hf : projectionAlgebraCheck p = true) : ProjectionEquations p := by
  unfold projectionAlgebraCheck at hf
  simp only [Id.run, Bind.bind, Pure.pure] at hf
  split at hf
  · cases hf
  · rename_i hp
    split at hf
    · cases hf
    · rename_i hm
      split at hf
      · cases hf
      · rename_i ht
        have hp' : (0 < p.denominator ∧ p.numerator.size = 64) ∧ p.dimension ≤ 8 := by
          simpa using hp
        simp at hm
        refine ⟨hp'.1.1, hp'.1.2, ?_, ?_, ?_⟩
        · intro i j
          have hij := hm i.val i.isLt j.val j.isLt
          simpa [certificateNumerator, matrixEntry] using hij.1
        · intro i j
          have hij := hm i.val i.isLt j.val j.isLt
          simpa [PhysicalFramePaths.eight_fold_sum, certificateNumerator, matrixEntry] using hij.2
        · simpa [PhysicalFramePaths.eight_fold_sum, certificateNumerator, matrixEntry] using ht

theorem projection_equations_of_algebra_valid (f : Nat)
    (hf : projectionAlgebraValid f = true) : ProjectionEquations projections[f]! :=
  projection_equations_of_algebraCheck _ hf

end CodedSorting.Construction.FiniteProjectionInterpretation
end ProjectionAlgebraInterpretation

section FiniteProjectionEquations
/-! All 636 concrete rational projectors satisfy their integer equations.
This checks projector algebra; it does not assert the separately listed
frame-membership classification of the 111 lines. -/

namespace CodedSorting.Construction
open FiniteCertificate IntegerProjection

theorem allProjectionEquations (f : Nat) (hf : f < 636) :
    ProjectionEquations projections[f]! :=
  FiniteProjectionInterpretation.projection_equations_of_algebra_valid f
    (allProjectionAlgebraValid f hf)

#print axioms allProjectionEquations

end CodedSorting.Construction
end FiniteProjectionEquations
