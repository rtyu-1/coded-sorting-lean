import CodedSorting.Generated.FiniteCircuit.RegisterTrace.Steps0000To0255
import CodedSorting.Generated.FiniteCircuit.SSARows

namespace CodedSorting.Construction.FiniteSSA.Verified
open CodedSorting.Construction.FiniteCertificate CodedSorting.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem initialRows : ∀ r : Fin 661, rows (Block000.before r.val) = 2 ^ r.val := by
  decide +kernel

theorem initial_represents : Represents rows Block000.before coefficientStart := by
  intro r hr
  have hr' : r < 661 := by simpa [coefficientStart, registerCount] using hr
  rw [initialRows ⟨r, hr'⟩]
  simp [coefficientStart, registerCount, getElem!_pos, hr']

#print axioms initialRows
#print axioms initial_represents
end
end CodedSorting.Construction.FiniteSSA.Verified
