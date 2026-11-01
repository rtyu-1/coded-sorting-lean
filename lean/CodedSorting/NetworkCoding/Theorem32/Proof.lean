import CodedSorting.NetworkCoding.Theorem32.FiniteCode
import CodedSorting.Circuit.Composition.TensorFrameCertifiedBudget

/-!
# Concrete theorem 3.2

The concrete scalar replay, physical edge budget, and finite binary linear
pipeline are joined on one simple network. The final statement has no extra
correctness assumptions. Source-bound build and axiom-audit records are kept
separately from this theorem source.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace CodedSorting.Construction.NetworkCodingResult

open CodedSorting.NetworkProtocol CodedSorting.ProgramNetwork CodedSorting.GraphRouting
open ConcreteLocalProgram TensorFrameGeometry TensorNetwork TensorLiftProgram
open scoped BigOperators

noncomputable section

theorem physical_rank_budget :
    (∑ e, edgeLength (TensorNetwork.actualNetwork forward middle forward partner)
      TensorFrameNetwork.actualLabel e) ≤ rankBudget := by
  change CodedSorting.StageLabels.physicalRank
    TensorFrameNetwork.program TensorFrameNetwork.actualLabel ≤ rankBudget
  exact le_of_eq TensorFrameNetwork.actualRank_eq_budget

theorem routing_capacity_le :
    NetworkRates.routingCapacity network source sink ≤ 1 - (33 : ℝ) / 338432 :=
  SimpleNetworkSeparation.simple_routing_capacity_le forward middle forward partner
    TensorFrameNetwork.actualLabel TensorFrameNetwork.actualLabel_source
    TensorFrameNetwork.actualLabel_terminal physical_rank_budget

theorem routing_strictly_below_coding :
    NetworkRates.routingCapacity network source sink < NetworkRates.capacity network source sink := by
  rw [coding_capacity_eq_one]
  exact lt_of_le_of_lt routing_capacity_le (by norm_num)

/-- The concrete packet count is `338432 * (depth + 1)`. -/
theorem strictBlock_beats_routing :
    NetworkRates.routingCapacity network source sink <
      (strictPackets : ℝ) / (strictPackets + depth) :=
  lt_of_le_of_lt routing_capacity_le strictBlock_rate_gt_gap

/-- A finite strict witness, with `finiteLinearBlock k` as its actual code. -/
theorem finite_binary_linear_strict_block :
    ∃ k : ℕ, 0 < k ∧
      BinaryLinearPipeline.BinaryLinearBlock network source sink (finiteLinearBlock k) ∧
      Nonempty (NetworkRates.BlockCode network source sink k (k + depth)) ∧
      NetworkRates.routingCapacity network source sink < (k : ℝ) / (k + depth) := by
  exact ⟨strictPackets, strictPackets_pos, strictBlock_linear, ⟨strictBlock⟩,
    strictBlock_beats_routing⟩

/-- No extra local-correctness, label, replay or budget assumptions occur in
this statement. All facts must come from its checked concrete dependencies. -/
theorem network_coding_result :
    Correct network linearCode ∧
    NetworkRates.capacity network source sink = 1 ∧
    (∀ rate : ℝ, rate < 1 →
      ∃ k : ℕ, 0 < k ∧
        BinaryLinearPipeline.BinaryLinearBlock network source sink (finiteLinearBlock k) ∧
        rate < (k : ℝ) / (k + depth)) ∧
    NetworkRates.routingCapacity network source sink ≤ 1 - (33 : ℝ) / 338432 ∧
    NetworkRates.routingCapacity network source sink < NetworkRates.capacity network source sink ∧
    ∃ k : ℕ, 0 < k ∧
      BinaryLinearPipeline.BinaryLinearBlock network source sink (finiteLinearBlock k) ∧
      Nonempty (NetworkRates.BlockCode network source sink k (k + depth)) ∧
      NetworkRates.routingCapacity network source sink < (k : ℝ) / (k + depth) :=
  ⟨linearCode_correct, coding_capacity_eq_one, binary_linear_rates_approach_one, routing_capacity_le,
    routing_strictly_below_coding, finite_binary_linear_strict_block⟩

end
end CodedSorting.Construction.NetworkCodingResult
