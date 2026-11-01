import CodedSorting.NetworkCoding.Theorem32.Proof

/-! Paper Theorem 3.2 (`thm:network`).
The concrete network, coding class, routing bound and finite witness are unchanged.
-/
set_option autoImplicit false
namespace CodedSorting.NetworkCoding.Theorem32
open CodedSorting Construction NetworkCodingResult

theorem theorem_3_2 :
    NetworkProtocol.Correct network linearCode ∧
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
  network_coding_result

end CodedSorting.NetworkCoding.Theorem32
