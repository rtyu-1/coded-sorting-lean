import CodedSorting.Circuit.MemoryAccess.PhysicalFrameFastVisits
import CodedSorting.Generated.FiniteCircuit.FramePathChecks.VisitNumbers.Base

namespace CodedSorting.Construction.PhysicalFramePaths

theorem forward_visits_computed (r : Nat) :
    eventVisits r forwardEvents = computedForwardVisits r :=
  forward_visits_fast r

end CodedSorting.Construction.PhysicalFramePaths
