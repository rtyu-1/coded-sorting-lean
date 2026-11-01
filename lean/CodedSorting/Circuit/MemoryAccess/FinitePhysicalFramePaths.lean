import CodedSorting.Generated.FiniteCircuit.FramePathChecks
import CodedSorting.Circuit.Local.LocalPhysicalSemantics

namespace CodedSorting.Construction

theorem actualForwardPathValid (r : LocalPhysicalSemantics.OriginalReg) :
    PhysicalFramePaths.forwardPathValid r.val = true :=
  PhysicalFramePaths.allForwardPathValid r.val r.isLt

#print axioms actualForwardPathValid
end CodedSorting.Construction
