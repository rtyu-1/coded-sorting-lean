import CodedSorting.NetworkCoding.Routing.StrictGap
import CodedSorting.Circuit.Local.ConcreteLocalProgram
import CodedSorting.NetworkCoding.FiniteCodes.BinaryLinearPipeline
import CodedSorting.Generated.FiniteCircuit.RegisterTrace.Replay

/-!
# Concrete coding half of theorem 3.2

This file requires the complete literal scalar replay and binds it to the
expanded three-round physical program. The network has exactly the original
independent streams as its sessions. The finite witness is certified linear
in all four operational functions by `BinaryLinearBlock`.

No routing or rank-budget conclusion is claimed in this module.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace CodedSorting.Construction.NetworkCodingResult

open CodedSorting.NetworkProtocol CodedSorting.ProgramNetwork CodedSorting.GraphRouting
open ConcreteLocalProgram TensorFrameGeometry TensorNetwork TensorLiftProgram

noncomputable section

abbrev network := SimpleNetworkSeparation.simpleNetwork forward middle forward partner
abbrev linearCode : LinearCode network Session :=
  SimpleNetworkSeparation.simpleCode forward middle forward partner
abbrev source := SimpleNetworkSeparation.simpleSource forward middle forward partner
abbrev sink := SimpleNetworkSeparation.simpleSink forward middle forward partner
abbrev graph := SimpleNetworkSeparation.simpleGraph forward middle forward partner
abbrev depth := SimpleNetworkSeparation.simpleDepth forward middle forward partner

/-- Each physical unit-capacity edge is one ordinary undirected graph edge. -/
def physicalEdgeEquiv :
    NetworkSubdivision.HalfEdge
      (Wire GlobalReg (TensorThreeRound.threeRoundProgram forward middle forward partner).length) ≃ graph.edgeSet :=
  SimpleNetworkSeparation.simplePhysicalEdgeEquiv forward middle forward partner

theorem forward_verified : LocalCorrect forward :=
  ConcreteLocalProgram.forward_correct
    FiniteCertificate.scalarCoefficientReplay FiniteCertificate.concreteSourcesNodup
    (fun g hg => (FiniteCertificate.concreteOperandsBound g hg).2)

theorem middle_verified : LocalCorrect middle :=
  ConcreteLocalProgram.middle_correct
    FiniteCertificate.scalarCoefficientReplay FiniteCertificate.concreteSourcesNodup
    (fun g hg => (FiniteCertificate.concreteOperandsBound g hg).2)
    FiniteCertificate.concreteNoSelf

theorem linearCode_correct : Correct network linearCode :=
  SimpleNetworkSeparation.simpleCode_correct forward middle forward partner
    forward_verified middle_verified forward_verified

/-- The named witness is built by the binary linear pipeline constructor. -/
abbrev finiteLinearBlock (k : ℕ) :
    NetworkRates.BlockCode network source sink k (k + depth) :=
  PipelineBlockCode.blockCode network linearCode k linearCode_correct
    (SimpleNetworkSeparation.simple_depth_bound forward middle forward partner)

/-- Linearity is a proposition about the actual operational witness, including
its emission, updates, initialization and decoding functions. -/
theorem finiteLinearBlock_linear (k : ℕ) :
    BinaryLinearPipeline.BinaryLinearBlock network source sink (finiteLinearBlock k) :=
  BinaryLinearPipeline.binaryLinear_blockCode network linearCode k linearCode_correct
    (SimpleNetworkSeparation.simple_depth_bound forward middle forward partner)

theorem finiteLinearBlock_direction (k t : ℕ)
    (e : NetworkSubdivision.HalfEdge (Wire GlobalReg (TensorThreeRound.threeRoundProgram forward middle forward partner).length)) :
    (finiteLinearBlock k).protocol.forward t e = true :=
  BinaryLinearPipeline.pipeline_direction network linearCode k t e

theorem coding_capacity_eq_one : NetworkRates.capacity network source sink = 1 :=
  SimpleNetworkSeparation.simple_coding_capacity forward middle forward partner
    forward_verified middle_verified forward_verified

/-- Binary linear witnesses themselves approach rate one. Thus the matching
upper bound for arbitrary operational codes also applies to the paper's
restricted binary linear coding class, with no nonlinear witness needed. -/
theorem binary_linear_rates_approach_one (rate : ℝ) (hrate : rate < 1) :
    ∃ k : ℕ, 0 < k ∧
      BinaryLinearPipeline.BinaryLinearBlock network source sink (finiteLinearBlock k) ∧
      rate < (k : ℝ) / (k + depth) := by
  obtain ⟨k, hk, h⟩ := NetworkRates.exists_pipeline_rate_gt depth rate hrate
  exact ⟨k, hk, finiteLinearBlock_linear k, h⟩

end
end CodedSorting.Construction.NetworkCodingResult
