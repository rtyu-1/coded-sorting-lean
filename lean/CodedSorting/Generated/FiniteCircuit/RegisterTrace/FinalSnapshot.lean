import CodedSorting.Generated.FiniteCircuit.RegisterTrace.Steps5376To5582
import CodedSorting.Generated.FiniteCircuit.SSARows

namespace CodedSorting.Construction.FiniteSSA.Verified
open CodedSorting.Construction.FiniteCertificate CodedSorting.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem finalScalarRows : ∀ r : Fin 661,
    rows (Block174.after r.val) =
      if 111 ≤ r.val && r.val < 222 then
        Nat.xor (2 ^ r.val) (2 ^ (r.val - 111)) else 2 ^ r.val := by
  decide +kernel

theorem finalRows : ∀ r : Fin 661,
    rows (Block174.after r.val) = coefficientExpected[r.val]! := by
  intro r
  simpa [coefficientExpected, registerCount, portCount, getElem!_pos, r.isLt]
    using finalScalarRows r

#print axioms finalScalarRows
#print axioms finalRows
end
end CodedSorting.Construction.FiniteSSA.Verified
