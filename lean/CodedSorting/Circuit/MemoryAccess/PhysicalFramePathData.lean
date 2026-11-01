import CodedSorting.Generated.FiniteCircuit.Data

namespace CodedSorting.Construction.PhysicalFramePaths
open FiniteCertificate

/-- The ordinary-frame visit contributed by one literal scalar gate. -/
def ordinaryFrameVisit (r : Nat) (g : Gate) : Option Nat :=
  if g.frame = scatterFrame then none
  else if r ∈ g.destination :: g.sources then some g.frame else none

/-- Chronological gate visits, including repeated visits to the same frame. -/
def ordinaryFrameVisits (r : Nat) (word : List Gate) : List Nat :=
  word.filterMap (ordinaryFrameVisit r)

/-- A small Boolean checker for a literal list of successive frame IDs. -/
def climbPath (start : Nat) : List Nat → Bool
  | [] => true
  | next :: rest => canClimb start next && climbPath next rest

/-- The entire original-register path, including the prescribed terminal. -/
def originalFramePath (r : Nat) : List Nat :=
  ordinaryFrameVisits r gates.toList ++ [finalFrames[r]!]

def originalFramePathValid (r : Nat) : Bool :=
  climbPath startFrames[r]! (originalFramePath r)


end CodedSorting.Construction.PhysicalFramePaths
