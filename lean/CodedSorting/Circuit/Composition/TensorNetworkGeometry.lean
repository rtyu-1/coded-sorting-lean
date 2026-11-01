import CodedSorting.Circuit.Labels.FiniteInterpretation
import CodedSorting.Circuit.MemoryAccess.HelperFrameChain
import CodedSorting.Circuit.Composition.TensorThreeRound
import CodedSorting.Circuit.Labels.ProjectionRankDecomposition
import CodedSorting.Circuit.Local.ReverseLocalProgram

section TensorFrameGeometry
/-!
# Geometry of the concrete 111-line tensor construction

The local vectors and orthogonal partner are read from the actual finite data.
The register indices are those used by `TensorLiftProgram`, rather than a
separate collection with merely the same cardinality.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.TensorFrameGeometry

open scoped BigOperators Matrix Kronecker
open ThreeCopySchedule
open CodedSorting.TensorLabels (tensor3 tensor3_mul tensor3_one Label H Nested)
open TriangularConjugacy (normSq lineProjection)
open ProjectionRankDecomposition

def integerLine (a : Line) : Fin 8 → Int :=
  fun k => (FiniteCertificate.lines[a.val]!)[k.val]!

/-- This is a small kernel computation on the actual 111 by 8 integer table. -/
theorem integerLine_norm : ∀ a : Line, ∑ k, integerLine a k * integerLine a k = 4 := by
  decide +kernel

theorem partner_bound : ∀ a : Line,
    FiniteCertificate.orthogonalPartner[a.val]! < 111 := by
  decide +kernel

def partnerFunction (a : Line) : Line :=
  ⟨FiniteCertificate.orthogonalPartner[a.val]!, partner_bound a⟩

theorem partner_bijective : Function.Bijective partnerFunction := by
  decide +kernel

noncomputable def partner : Equiv.Perm Line := Equiv.ofBijective partnerFunction partner_bijective

theorem integerLine_partner_orthogonal : ∀ a : Line,
    ∑ k, integerLine a k * integerLine (partnerFunction a) k = 0 := by
  decide +kernel

def lineVector (a : Line) : Fin 8 → ℚ :=
  IntegerProjection.vectorOfInts (integerLine a)

theorem lineVector_norm (a : Line) : normSq (lineVector a) = 4 := by
  unfold normSq dotProduct lineVector IntegerProjection.vectorOfInts
  exact_mod_cast integerLine_norm a

theorem lineVector_nonzero (a : Line) : lineVector a ≠ 0 := by
  intro h
  have hn := lineVector_norm a
  rw [h] at hn
  norm_num [normSq, dotProduct] at hn

theorem lineVector_partner_orthogonal (a : Line) :
    lineVector a ⬝ᵥ lineVector (partner a) = 0 := by
  change (∑ k, (integerLine a k : ℚ) * (integerLine (partnerFunction a) k : ℚ)) = 0
  exact_mod_cast integerLine_partner_orthogonal a

def lineProjector (a : Line) : Matrix (Fin 8) (Fin 8) ℚ :=
  lineProjection (lineVector a)

theorem lineProjector_symmetric (a : Line) : (lineProjector a)ᵀ = lineProjector a :=
  lineProjection_symmetric _

theorem lineProjector_idempotent (a : Line) :
    lineProjector a * lineProjector a = lineProjector a :=
  lineProjection_idempotent _ (by rw [lineVector_norm]; norm_num)

theorem lineProjector_rank (a : Line) : (lineProjector a).rank = 1 :=
  lineProjection_rank _ (by rw [lineVector_norm]; norm_num)

theorem lineProjector_partner_orthogonal (a : Line) :
    lineProjector a * lineProjector (partner a) = 0 :=
  lineProjection_mul_zero _ _ (lineVector_partner_orthogonal a)

theorem partner_lineProjector_orthogonal (a : Line) :
    lineProjector (partner a) * lineProjector a = 0 :=
  lineProjection_mul_zero _ _ (by rw [dotProduct_comm]; exact lineVector_partner_orthogonal a)

abbrev Coordinates := TensorLiftProgram.Coordinates
abbrev GlobalMatrix := Label 8

def tensorLine (a : Coordinates) : GlobalMatrix :=
  tensor3 (lineProjector a.1) (lineProjector a.2.1) (lineProjector a.2.2)

theorem lineProjector_trace (a : Line) : Matrix.trace (lineProjector a) = 1 := by
  rw [IntegerProjection.trace_eq_rank _ (lineProjector_idempotent a), lineProjector_rank]
  rfl

theorem tensorLine_idempotent (a : Coordinates) : tensorLine a * tensorLine a = tensorLine a := by
  simp only [tensorLine, tensor3_mul, lineProjector_idempotent]

theorem tensorLine_rank (a : Coordinates) : (tensorLine a).rank = 1 := by
  have h := IntegerProjection.trace_eq_rank _ (tensorLine_idempotent a)
  simp only [tensorLine, tensor3, Matrix.trace_kronecker, lineProjector_trace, mul_one] at h
  exact_mod_cast h.symm

theorem tensorLine_symmetric (a : Coordinates) : (tensorLine a)ᵀ = tensorLine a := by
  ext r c
  change lineProjector a.1 c.1 r.1 *
    (lineProjector a.2.1 c.2.1 r.2.1 * lineProjector a.2.2 c.2.2 r.2.2) = _
  have hs (t : Line) (i j : Fin 8) : lineProjector t i j = lineProjector t j i :=
    congrFun (congrFun (lineProjector_symmetric t) j) i
  rw [hs a.1, hs a.2.1, hs a.2.2]
  rfl

/-- Express an ambient tensor coordinate in the cyclic order of a data copy. -/
def copyView (i : Copy) : H 8 ≃ H 8 :=
  if i.val = 0 then Equiv.refl _
  else if i.val = 1 then
    { toFun := fun p => (p.2.1, p.2.2, p.1)
      invFun := fun p => (p.2.2, p.1, p.2.1)
      left_inv := by rintro ⟨a,b,c⟩; rfl
      right_inv := by rintro ⟨a,b,c⟩; rfl }
  else
    { toFun := fun p => (p.2.2, p.1, p.2.1)
      invFun := fun p => (p.2.1, p.2.2, p.1)
      left_inv := by rintro ⟨a,b,c⟩; rfl
      right_inv := by rintro ⟨a,b,c⟩; rfl }

def globalize (i : Copy) (P : GlobalMatrix) : GlobalMatrix :=
  P.submatrix (copyView i) (copyView i)

theorem globalize_mul (i : Copy) (P Q : GlobalMatrix) :
    globalize i P * globalize i Q = globalize i (P * Q) := by
  exact Matrix.submatrix_mul_equiv P Q _ (copyView i) _

theorem globalize_rank (i : Copy) (P : GlobalMatrix) : (globalize i P).rank = P.rank :=
  Matrix.rank_submatrix P (copyView i) (copyView i)

def dataProjector (a : DataStream) : GlobalMatrix := globalize a.1 (tensorLine a.2.2)

theorem dataProjector_idempotent (a : DataStream) :
    dataProjector a * dataProjector a = dataProjector a := by
  rw [dataProjector, globalize_mul, tensorLine_idempotent]

theorem dataProjector_rank (a : DataStream) : (dataProjector a).rank = 1 := by
  rw [dataProjector, globalize_rank, tensorLine_rank]

theorem dataProjector_symmetric (a : DataStream) : (dataProjector a)ᵀ = dataProjector a := by
  ext r c
  exact congrFun (congrFun (tensorLine_symmetric a.2.2) (copyView a.1 r)) (copyView a.1 c)

/-- Physical data wires: X begins at its line and Y begins at zero. -/
def dataSource (a : DataStream) : GlobalMatrix :=
  if a.2.1 = 0 then dataProjector a else 0

/-- Physical data wires: X ends at full space and Y at the line complement. -/
def dataTerminal (a : DataStream) : GlobalMatrix :=
  if a.2.1 = 0 then 1 else 1 - dataProjector a

def dataPartner (a : DataStream) : DataStream :=
  (a.1, Equiv.swap 0 1 a.2.1, a.2.2)

theorem dataProjector_partner (a : DataStream) : dataProjector (dataPartner a) = dataProjector a := rfl

theorem reflection_involution (P : GlobalMatrix) (hp : P * P = P) :
    ((1 - P) - P) * ((1 - P) - P) = 1 := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, hp]
  abel_nf
  simp

theorem reflection_rank (P : GlobalMatrix) (hp : P * P = P) :
    ((1 - P) - P).rank = 512 := by
  have hi := reflection_involution P hp
  have hu : IsUnit ((1 - P) - P) := ⟨⟨_, _, hi, hi⟩, rfl⟩
  simpa [H] using Matrix.rank_of_isUnit _ hu

theorem data_endpoint_rank (a : DataStream) :
    (dataTerminal (dataPartner a) - dataSource a).rank = 512 := by
  have hb : a.2.1 = 0 ∨ a.2.1 = 1 := by omega
  rcases hb with hb | hb
  · simpa [dataTerminal, dataSource, dataPartner, hb, dataProjector] using
      reflection_rank (dataProjector a) (dataProjector_idempotent a)
  · simp [dataTerminal, dataSource, dataPartner, hb, Matrix.rank_one, H]

def sourceLabel : IndependentStream → GlobalMatrix
  | .inl a => dataSource a
  | .inr _ => 0

def terminalLabel : IndependentStream → GlobalMatrix
  | .inl a => dataTerminal a
  | .inr _ => 1

/-- The session permutation is exactly the proved scalar program's
`TensorThreeRound.originalSwap`, including every persistent helper. -/
theorem all_endpoint_ranks (r : IndependentStream) :
    (terminalLabel (TensorThreeRound.originalSwap r) - sourceLabel r).rank = 512 := by
  rcases r with a | h
  · exact data_endpoint_rank a
  · simp [TensorThreeRound.originalSwap, sourceLabel, terminalLabel, Matrix.rank_one, H]

end CodedSorting.Construction.TensorFrameGeometry
end TensorFrameGeometry

section TensorNetwork
/-!
# The expanded tensor program network with only original sessions

The network is built from the actual lifted three-round physical gate list.
Every physical temporary remains in that graph, but it contributes no
independent session. Payload correctness is conditional on the local-word
contracts, or equivalently on the explicitly listed finite-certificate inputs.
No matrix-label or routing-budget assertion is made here.
-/

set_option autoImplicit false

namespace CodedSorting.Construction.TensorNetwork

open CodedSorting.Circuit CodedSorting.CircuitProgram
open CodedSorting.NetworkProtocol CodedSorting.ProgramNetwork
open CodedSorting.Construction.NetworkAdapter CodedSorting.Construction.TensorLiftProgram
open CodedSorting.Construction.TensorThreeRound CodedSorting.Construction.ThreeCopySchedule
open CodedSorting.Construction.FiniteCertificate CodedSorting.Construction.SymbolicXor
open CodedSorting.Construction.FiniteSemantics CodedSorting.Construction.ExplicitCopies
open CodedSorting.Construction.ScatterCopies CodedSorting.Construction.LocalPhysicalSemantics
open CodedSorting.Construction.LocalPhysicalContract CodedSorting.Construction.ReverseLocalProgram

def OriginalActive : GlobalReg → Prop
  | .inl _ => True
  | .inr _ => False

instance originalActiveDecidable : DecidablePred OriginalActive := by
  intro r
  cases r <;> dsimp [OriginalActive] <;> infer_instance

abbrev Session := {r : GlobalReg // OriginalActive r}

/-- Sessions are exactly the original independent streams, not all physical
registers. This equivalence is also the interface for endpoint labels. -/
def sessionEquiv : Session ≃ IndependentStream where
  toFun r := match r with
    | ⟨.inl s, _⟩ => s
    | ⟨.inr _, h⟩ => False.elim h
  invFun r := ⟨.inl r, trivial⟩
  left_inv := by
    rintro ⟨r,hr⟩
    cases r with
    | inl r => rfl
    | inr r => exact False.elim hr
  right_inv := by intro r; rfl

noncomputable instance sessionFintype : Fintype Session :=
  Fintype.ofEquiv IndependentStream sessionEquiv.symm

theorem session_count : Fintype.card Session = CodedSorting.Construction.streamCount := by
  rw [Fintype.card_congr sessionEquiv]
  exact independent_stream_count

theorem session_value (r : Session) : r.val = .inl (sessionEquiv r) := by
  rcases r with ⟨s,hs⟩
  cases s with
  | inl s => rfl
  | inr s => exact False.elim hs

theorem originalSwap_involutive : Function.Involutive originalSwap := by
  rintro (⟨i,bank,coordinates⟩ | helper) <;> simp [originalSwap]

noncomputable def actualNetwork (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (pi : Equiv.Perm Line) :=
  network (threeRoundProgram wordOne wordTwo wordThree pi)

noncomputable def actualCode (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (pi : Equiv.Perm Line) : LinearCode (actualNetwork wordOne wordTwo wordThree pi) Session :=
  restrictCode (actualNetwork wordOne wordTwo wordThree pi)
    (code (threeRoundProgram wordOne wordTwo wordThree pi) physicalSwap) OriginalActive

theorem actualCode_source (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (pi : Equiv.Perm Line) (r : Session) :
    (actualCode wordOne wordTwo wordThree pi).source r =
      Vertex.source (.inl (sessionEquiv r)) := by
  change Vertex.source r.val = _
  rw [session_value]

theorem actualCode_sink (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (pi : Equiv.Perm Line) (r : Session) :
    (actualCode wordOne wordTwo wordThree pi).sink r =
      Vertex.sink (.inl (originalSwap (sessionEquiv r))) := by
  change Vertex.sink (physicalSwap r.val) = _
  rw [session_value]
  rfl

/-- Correct coding on the literal expanded global program network. The proof
uses only original selected sinks and imposes no temporary restoration. -/
theorem actualCode_correct (wordOne wordTwo wordThree : List (XorGate LocalReg))
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree)
    (pi : Equiv.Perm Line) :
    Correct (actualNetwork wordOne wordTwo wordThree pi) (actualCode wordOne wordTwo wordThree pi) := by
  apply selected_program_correct
  intro input r
  have hr := session_value r
  have h := threeRound_original wordOne wordTwo wordThree hOne hTwo hThree pi
    (extendMessages OriginalActive input) (originalSwap (sessionEquiv r))
  rw [originalSwap_involutive] at h
  change runProgram (threeRoundProgram wordOne wordTwo wordThree pi)
    (extendMessages OriginalActive input) (physicalSwap r.val) = input r
  rw [hr]
  change runProgram (threeRoundProgram wordOne wordTwo wordThree pi)
    (extendMessages OriginalActive input) (.inl (originalSwap (sessionEquiv r))) = _
  rw [h, ← hr]
  exact extendMessages_active OriginalActive input r

/-- Concrete program recipe: forward physical word, freshly copied reversed
word, forward physical word. The finite decomposition remains an input. -/
noncomputable def certificateForward (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg)) : List (XorGate LocalReg) :=
  structuredProgram (localPhysicalProgram before after rows)

noncomputable def certificateMiddle (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg)) : List (XorGate LocalReg) :=
  structuredProgram (reverseLocalPhysicalProgram before after rows)

/-- All payload premises for the actual graph are exposed at the finite
certificate boundary. No abstract correct function is used as a gate. -/
theorem certificateNetwork_correct (word : Array Gate)
    (hreplay : runCoefficients word = coefficientExpected)
    (hnodup : ∀ g ∈ word.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ word.toList, ∀ s ∈ g.sources, s < registerCount)
    (hnot : ∀ g ∈ word.toList, g.destination ∉ g.sources)
    (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg))
    (hdecompose : compileProgram registerCount word =
      reducedProgram retainedHelper before after rows)
    (hsafe : ∀ row ∈ rows, ∀ t, retainedHelper t ≠ row.destination)
    (pi : Equiv.Perm Line) :
    Correct
      (actualNetwork (certificateForward before after rows) (certificateMiddle before after rows)
        (certificateForward before after rows) pi)
      (actualCode (certificateForward before after rows) (certificateMiddle before after rows)
        (certificateForward before after rows) pi) := by
  have hforward : LocalCorrect (certificateForward before after rows) :=
    localCorrect_of_physical _
      (localPhysical_correct_of_certificate word hreplay hnodup hbound
        before after rows hdecompose hsafe)
  have hmiddle : LocalCorrect (certificateMiddle before after rows) :=
    localCorrect_of_physical _
      (reverseLocalPhysical_correct_of_certificate word hreplay hnodup hbound hnot
        before after rows hdecompose hsafe)
  exact actualCode_correct _ _ _ hforward hmiddle hforward pi

end CodedSorting.Construction.TensorNetwork
end TensorNetwork

section TensorNetworkGeometry
/-!
# Endpoint-rank interface for the actual selected-session network

The source and sink belong to the actual expanded program network. A full
vertex labeling must satisfy the two boundary equations below. Its internal
wire labels and total rank budget are intentionally not fabricated here.
-/

set_option autoImplicit false

namespace CodedSorting.Construction.TensorNetworkGeometry

open CodedSorting.Circuit CodedSorting.CircuitProgram
open CodedSorting.ProgramNetwork
open CodedSorting.Construction.TensorLiftProgram CodedSorting.Construction.TensorThreeRound
open CodedSorting.Construction.ThreeCopySchedule CodedSorting.Construction.TensorNetwork
open CodedSorting.Construction.TensorFrameGeometry

/-- Geometry's rank-512 endpoint theorem transported to the actual code's
source and sink functions. The graph is the expanded physical program graph. -/
theorem actualCode_endpoint_rank
    (wordOne wordTwo wordThree : List (XorGate LocalReg)) (pi : Equiv.Perm Line)
    (label : Vertex GlobalReg (threeRoundProgram wordOne wordTwo wordThree pi).length → GlobalMatrix)
    (hsource : ∀ r : IndependentStream, label (.source (.inl r)) = sourceLabel r)
    (hterminal : ∀ r : IndependentStream, label (.sink (.inl r)) = terminalLabel r)
    (r : Session) :
    (label ((actualCode wordOne wordTwo wordThree pi).sink r) -
      label ((actualCode wordOne wordTwo wordThree pi).source r)).rank = 512 := by
  rw [actualCode_sink, actualCode_source, hsource, hterminal]
  exact all_endpoint_ranks (sessionEquiv r)

end CodedSorting.Construction.TensorNetworkGeometry
end TensorNetworkGeometry
