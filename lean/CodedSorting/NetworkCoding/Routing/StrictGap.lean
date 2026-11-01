import CodedSorting.Circuit.Composition.TensorNetworkGeometry
import CodedSorting.NetworkCoding.Model.PipelineBlockCode

/-!
# Operational theorem-2.2 endpoint for the Construction program

The graph, messages, local code, block code and routing upper bound below all
refer to the same expanded three-round physical program. Temporary registers
are physical storage only; the session type is exactly the original streams.

This module exposes the remaining concrete proof inputs: correctness of the
three local words, the source/terminal equations of a complete vertex label,
and its actual edge-rank budget. The final concrete certificate must supply
these inputs; the theorem here does not claim they have already been supplied.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace CodedSorting.Construction.SimpleNetworkSeparation

open CodedSorting.Circuit CodedSorting.CircuitProgram
open CodedSorting.NetworkProtocol CodedSorting.ProgramNetwork CodedSorting.GraphRouting
open CodedSorting.Construction.TensorLiftProgram CodedSorting.Construction.TensorThreeRound
open CodedSorting.Construction.ThreeCopySchedule CodedSorting.Construction.TensorNetwork
open CodedSorting.Construction.TensorFrameGeometry CodedSorting.Construction.TensorNetworkGeometry
open CodedSorting.Construction.NetworkAdapter
open scoped BigOperators

noncomputable section

variable (wordOne wordTwo wordThree : List (XorGate LocalReg)) (pi : Equiv.Perm Line)

abbrev program := threeRoundProgram wordOne wordTwo wordThree pi
abbrev baseNetwork := TensorNetwork.actualNetwork wordOne wordTwo wordThree pi
abbrev baseCode := TensorNetwork.actualCode wordOne wordTwo wordThree pi

def simpleNetwork := NetworkSubdivision.network (baseNetwork wordOne wordTwo wordThree pi)

def simpleCode : LinearCode (simpleNetwork wordOne wordTwo wordThree pi) Session :=
  NetworkSubdivision.codeOnSubdivision
    (baseNetwork wordOne wordTwo wordThree pi) (baseCode wordOne wordTwo wordThree pi)

def simpleSource := (simpleCode wordOne wordTwo wordThree pi).source
def simpleSink := (simpleCode wordOne wordTwo wordThree pi).sink
def simpleGraph := NetworkSubdivision.simpleGraph (baseNetwork wordOne wordTwo wordThree pi)
def simpleDepth : ℕ := 2 * (program wordOne wordTwo wordThree pi).length + 1

def simplePhysicalEdgeEquiv :
    NetworkSubdivision.HalfEdge (Wire GlobalReg (program wordOne wordTwo wordThree pi).length) ≃
      (simpleGraph wordOne wordTwo wordThree pi).edgeSet :=
  NetworkSubdivision.physicalEdgeEquiv (baseNetwork wordOne wordTwo wordThree pi)

theorem simpleCode_correct
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree) :
    Correct (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleCode wordOne wordTwo wordThree pi) :=
  NetworkSubdivision.correctness_preserved _ _
    (TensorNetwork.actualCode_correct _ _ _ hOne hTwo hThree pi)

theorem simple_depth_bound :
    ∀ e, (simpleNetwork wordOne wordTwo wordThree pi).rank
      ((simpleNetwork wordOne wordTwo wordThree pi).tail e) ≤
        simpleDepth wordOne wordTwo wordThree pi :=
  NetworkSubdivision.depth_bound _ (ProgramNetwork.depth_bound (program wordOne wordTwo wordThree pi))

/-- Actual finite causal block code on the simple undirected network. -/
def simpleBlockCode
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree)
    (k : ℕ) : NetworkRates.BlockCode (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi)
      k (k + simpleDepth wordOne wordTwo wordThree pi) :=
  PipelineBlockCode.blockCode _ (simpleCode wordOne wordTwo wordThree pi) k
    (simpleCode_correct _ _ _ _ hOne hTwo hThree) (simple_depth_bound _ _ _ _)

theorem simple_achievable_le_one (i₀ : Session)
    {rate : ℝ} (hr : NetworkRates.Achievable (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) rate) :
    rate ≤ 1 := by
  let p := program wordOne wordTwo wordThree pi
  let e₀ := sourceWire p i₀.val
  have ht : (simpleNetwork wordOne wordTwo wordThree pi).tail (.inl e₀) =
      simpleSource wordOne wordTwo wordThree pi i₀ :=
    congrArg Sum.inl (sourceWire_tail p i₀.val)
  have hh : (simpleNetwork wordOne wordTwo wordThree pi).head (.inl e₀) ≠
      simpleSource wordOne wordTwo wordThree pi i₀ := by
    intro h
    exact NetworkSubdivision.tail_ne_head (simpleNetwork wordOne wordTwo wordThree pi)
      (.inl e₀) (ht.trans h.symm)
  have hl : ∀ e, NetworkCut.Incident (simpleNetwork wordOne wordTwo wordThree pi) e
      (simpleSource wordOne wordTwo wordThree pi i₀) ↔ e = .inl e₀ :=
    NetworkSubdivision.source_leaf_preserved (baseNetwork wordOne wordTwo wordThree pi)
      (.source i₀.val) e₀ (sourceWire_tail p i₀.val) (source_is_leaf p i₀.val)
  have hs : simpleSink wordOne wordTwo wordThree pi i₀ ≠
      simpleSource wordOne wordTwo wordThree pi i₀ := by
    intro h
    change (Sum.inl (Vertex.sink (physicalSwap i₀.val)) :
      NetworkSubdivision.Vertex _ _) = Sum.inl (Vertex.source i₀.val) at h
    cases h
  exact NetworkRates.achievable_le_one _ _ _ i₀ (.inl e₀) ht hh hl hs hr

theorem sessions_positive : 0 < Fintype.card Session := by
  rw [session_count, streamCount_eq]
  norm_num

/-- The exact operational coding capacity, conditional only on the local
word correctness supplied by the finite replay proof. -/
theorem simple_coding_capacity
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree) :
    NetworkRates.capacity (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) = 1 := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp sessions_positive
  apply NetworkRates.capacity_eq_one_of_pipeline _ _ _ (simpleDepth wordOne wordTwo wordThree pi)
  · intro k
    exact ⟨simpleBlockCode _ _ _ _ hOne hTwo hThree k⟩
  · intro r hr
    exact simple_achievable_le_one _ _ _ _ i₀ hr

variable
  (label : Vertex GlobalReg (program wordOne wordTwo wordThree pi).length → GlobalMatrix)
  (hsource : ∀ r : IndependentStream, label (.source (.inl r)) = sourceLabel r)
  (hterminal : ∀ r : IndependentStream, label (.sink (.inl r)) = terminalLabel r)

def simpleLabel := NetworkSubdivision.label (baseNetwork wordOne wordTwo wordThree pi) label

include hsource hterminal in
theorem simple_endpoint_rank (r : Session) :
    (simpleLabel wordOne wordTwo wordThree pi label (simpleSink wordOne wordTwo wordThree pi r) -
      simpleLabel wordOne wordTwo wordThree pi label (simpleSource wordOne wordTwo wordThree pi r)).rank =
        512 :=
  actualCode_endpoint_rank _ _ _ _ label hsource hterminal r

theorem rank_ratio :
    (rankBudget : ℝ) / ((streamCount : ℝ) * (512 : ℝ)) = 1 - (33 : ℝ) / 338432 := by
  norm_num [rankBudget_eq, streamCount_eq]

include hsource hterminal in
/-- All undirected path flows are bounded on the actual simple graph. -/
theorem simple_routable_bound
    (hbudget : (∑ e, edgeLength (baseNetwork wordOne wordTwo wordThree pi) label e) ≤ rankBudget)
    (rate : ℝ) (hr : NetworkRates.Routable (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) rate) :
    rate ≤ 1 - (33 : ℝ) / 338432 := by
  obtain ⟨n, owner, walk, flow, hflow, hcapacity, hsessions⟩ := hr
  have hend (r : Session) :
      (simpleLabel wordOne wordTwo wordThree pi label (simpleSink wordOne wordTwo wordThree pi r) -
        simpleLabel wordOne wordTwo wordThree pi label (simpleSource wordOne wordTwo wordThree pi r)).rank =
          Fintype.card (CodedSorting.TensorLabels.H 8) := by
    simpa [CodedSorting.TensorLabels.H] using simple_endpoint_rank _ _ _ _ label hsource hterminal r
  have hb := common_routing_bound_of_full_rank (simpleNetwork wordOne wordTwo wordThree pi)
    (simpleLabel wordOne wordTwo wordThree pi label)
    (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi)
    hend owner walk flow rate (by norm_num [CodedSorting.TensorLabels.H])
    sessions_positive hflow hcapacity hsessions
  have hsum : (∑ e, (edgeLength (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleLabel wordOne wordTwo wordThree pi label) e : ℝ)) ≤ (rankBudget : ℝ) := by
    have hn := NetworkSubdivision.total_length_preserved
      (baseNetwork wordOne wordTwo wordThree pi) label
    have hn' : (∑ e, edgeLength (simpleNetwork wordOne wordTwo wordThree pi)
        (simpleLabel wordOne wordTwo wordThree pi label) e) ≤ rankBudget := by
      simpa only [simpleNetwork, simpleLabel] using hn.le.trans hbudget
    exact_mod_cast hn'
  rw [session_count] at hb
  have hcard : (Fintype.card (CodedSorting.TensorLabels.H 8) : ℝ) = 512 := by
    norm_num [CodedSorting.TensorLabels.H]
  rw [hcard] at hb
  have hden : (0 : ℝ) ≤ (streamCount : ℝ) * 512 := by positivity
  exact hb.trans ((div_le_div_of_nonneg_right hsum hden).trans_eq rank_ratio)

include hsource hterminal in
theorem simple_routing_capacity_le
    (hbudget : (∑ e, edgeLength (baseNetwork wordOne wordTwo wordThree pi) label e) ≤ rankBudget) :
    NetworkRates.routingCapacity (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) ≤
        1 - (33 : ℝ) / 338432 :=
  NetworkRates.routing_capacity_bound _ _ _ _
    (simple_routable_bound _ _ _ _ label hsource hterminal hbudget)

include hsource hterminal in
/-- The theorem-2.2 conclusion with all unfinished concrete inputs explicit. -/
theorem simple_network_separation
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree)
    (hbudget : (∑ e, edgeLength (baseNetwork wordOne wordTwo wordThree pi) label e) ≤ rankBudget) :
    NetworkRates.capacity (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) = 1 ∧
    NetworkRates.routingCapacity (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) ≤
        1 - (33 : ℝ) / 338432 ∧
    NetworkRates.routingCapacity (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) <
        NetworkRates.capacity (simpleNetwork wordOne wordTwo wordThree pi)
          (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) := by
  have hc := simple_coding_capacity _ _ _ pi hOne hTwo hThree
  have hr := simple_routing_capacity_le _ _ _ pi label hsource hterminal hbudget
  refine ⟨hc, hr, ?_⟩
  rw [hc]
  exact lt_of_le_of_lt hr (by norm_num)

include hsource hterminal in
theorem simple_finite_strict_block
    (hOne : LocalCorrect wordOne) (hTwo : LocalCorrect wordTwo) (hThree : LocalCorrect wordThree)
    (hbudget : (∑ e, edgeLength (baseNetwork wordOne wordTwo wordThree pi) label e) ≤ rankBudget) :
    ∃ k : ℕ, 0 < k ∧ Nonempty (NetworkRates.BlockCode (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi)
      k (k + simpleDepth wordOne wordTwo wordThree pi)) ∧
    NetworkRates.routingCapacity (simpleNetwork wordOne wordTwo wordThree pi)
      (simpleSource wordOne wordTwo wordThree pi) (simpleSink wordOne wordTwo wordThree pi) <
        (k : ℝ) / (k + simpleDepth wordOne wordTwo wordThree pi) := by
  obtain ⟨k, hk, hrate⟩ := NetworkRates.exists_pipeline_rate_gt
    (simpleDepth wordOne wordTwo wordThree pi) (1 - (33 : ℝ) / 338432) (by norm_num)
  exact ⟨k, hk, ⟨simpleBlockCode _ _ _ _ hOne hTwo hThree k⟩,
    lt_of_le_of_lt (simple_routing_capacity_le _ _ _ pi label hsource hterminal hbudget) hrate⟩

end
end CodedSorting.Construction.SimpleNetworkSeparation
