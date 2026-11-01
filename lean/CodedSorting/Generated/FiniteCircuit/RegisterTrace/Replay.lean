import CodedSorting.Generated.FiniteCircuit.RegisterTrace.Composition
import CodedSorting.Generated.FiniteCircuit.RegisterTrace.FinalSnapshot
import CodedSorting.Generated.FiniteCircuit.RegisterTrace.InitialSnapshot

namespace CodedSorting.Construction.FiniteCertificate
open CodedSorting.Construction.FiniteSSA CodedSorting.Construction.FiniteSSA.Verified
  CodedSorting.Construction.SSAFunctionCertificate

/-- The complete 5583-gate word, checked by composition of independent
ordinary Lean kernel certificates and literal endpoint snapshots. -/
theorem scalarCoefficientReplay : runCoefficients gates = coefficientExpected :=
  runCoefficients_of_blocks rows gates allSteps Block000.before Block174.after
    program_eq initial_represents allSteps_sound finalRows

end CodedSorting.Construction.FiniteCertificate

#print axioms CodedSorting.Construction.FiniteCertificate.scalarCoefficientReplay
