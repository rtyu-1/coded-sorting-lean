import CodedSorting.Circuit.Composition.TensorFrameNetwork
import CodedSorting.Circuit.Composition.TensorFrameFiniteBounds
import CodedSorting.Circuit.Labels.FiniteInterpretation
import CodedSorting.Circuit.Parameters.CopyDimensions
import CodedSorting.Circuit.MemoryAccess.FinitePhysicalFramePaths
import CodedSorting.Generated.FiniteCircuit.RegisterTrace.Composition

/-! The concrete geometry checks instantiate every premise of the physical
wire-cost proof. No rank budget or local correctness premise remains. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.TensorFrameNetwork

open PhysicalFramePaths FiniteCertificate

attribute [local irreducible] gates projections startFrames finalFrames

theorem actualGeometryChecks : GeometryChecks where
  operands := concreteOperandsBound
  frames := actual_path_projection_equations
  paths := actualForwardPathValid
  endpoints := actualEndpointEquations
  copies := fun t => allProjectionEquations (510+t.val) (by omega)
  copyDimensions := actualCopyDimensions

theorem actualRank_eq_budget :
    CodedSorting.StageLabels.physicalRank program actualLabel =
      rankBudget :=
  actualRank_eq_budget_of_checks actualGeometryChecks

#print axioms actualRank_eq_budget

end CodedSorting.Construction.TensorFrameNetwork
