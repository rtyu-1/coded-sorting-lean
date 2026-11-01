import CodedSorting.Circuit.MemoryAccess.PhysicalFrameWordData
import CodedSorting.Generated.FiniteCircuit.ArrayLookup
import CodedSorting.Circuit.Local.SSAArrayConcat

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CodedSorting.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def nestedCheck (p q : Projection) : Bool :=
  (List.range 8).all fun i => (List.range 8).all fun j =>
    (List.range 8).foldl
      (fun s k => s + matrixEntry q i k * matrixEntry p k j) 0 ==
      q.denominator * matrixEntry p i j

theorem frameNested_eq (a b : Nat) :
    frameNested a b = nestedCheck projections[a]! projections[b]! := rfl

@[simp] theorem canClimb_self (a : Nat) : canClimb a a = true := by
  simp [canClimb]

end CodedSorting.Construction.PhysicalFramePaths
