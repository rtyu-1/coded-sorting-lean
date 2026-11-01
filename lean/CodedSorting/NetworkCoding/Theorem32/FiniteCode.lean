import CodedSorting.NetworkCoding.Theorem32.Coding
import Mathlib.Algebra.Order.Floor.Ring

/-!
An explicit finite packet count for the theorem 3.2 pipeline. The arithmetic
depends only on the finite network depth; no existence choice is needed to
select the block that will beat the routing upper bound.
-/

set_option autoImplicit false

namespace CodedSorting.Construction.NetworkCodingResult

noncomputable section

def strictPackets : ℕ := 338432 * (depth + 1)

theorem strictPackets_pos : 0 < strictPackets :=
  Nat.mul_pos (by decide) (Nat.succ_pos depth)

abbrev strictBlock := finiteLinearBlock strictPackets

theorem strictBlock_linear :
    BinaryLinearPipeline.BinaryLinearBlock network source sink strictBlock :=
  finiteLinearBlock_linear strictPackets

private theorem explicit_pipeline_rate (d : ℕ) :
    1 - (33 : ℝ) / 338432 <
      ((338432 * (d + 1) : ℕ) : ℝ) / ((338432 * (d + 1) : ℕ) + d) := by
  push_cast
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  apply (lt_div_iff₀ (by positivity)).2
  norm_num
  nlinarith

theorem strictBlock_rate_gt_gap :
    1 - (33 : ℝ) / 338432 < (strictPackets : ℝ) / (strictPackets + depth) :=
  explicit_pipeline_rate depth

def ceilingPackets (d : ℕ) (eta : ℝ) : ℕ :=
  ⌈(d : ℝ) * (1 - eta) / eta⌉₊ + 1

theorem ceiling_pipeline_rate (d : ℕ) (eta : ℝ) (heta : 0 < eta) :
    1 - eta < (ceilingPackets d eta : ℝ) / (ceilingPackets d eta + d) := by
  have hk : 0 < ceilingPackets d eta := Nat.succ_pos _
  have hkR : (0 : ℝ) < ceilingPackets d eta := by exact_mod_cast hk
  have hc := Nat.le_ceil ((d : ℝ) * (1 - eta) / eta)
  have hstrict : (d : ℝ) * (1 - eta) / eta < (ceilingPackets d eta : ℝ) := by
    unfold ceilingPackets
    push_cast
    linarith
  have hm := (div_lt_iff₀ heta).1 hstrict
  apply (lt_div_iff₀ (by positivity)).2
  nlinarith

theorem ceilingPackets_eq_int (d : ℕ) (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    (ceilingPackets d eta : ℤ) = ⌈(d : ℝ) * (1 - eta) / eta⌉ + 1 := by
  unfold ceilingPackets
  push_cast
  rw [Int.natCast_ceil_eq_ceil
    (div_nonneg (mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr heta1)) heta.le)]

/-- Appendix B.2's exact ceiling formula, with eta = 33/338432.
The argument of the natural ceiling is nonnegative, so this is the same
integer ceiling used in the paper. The proof also permits zero startup delay. -/
def paperPackets : ℕ := ceilingPackets depth ((33 : ℝ) / 338432)

theorem paperPackets_eq : paperPackets =
    ⌈(depth : ℝ) * (1 - (33 : ℝ) / 338432) / ((33 : ℝ) / 338432)⌉₊ + 1 := rfl

theorem paperPackets_eq_integer : (paperPackets : ℤ) =
    ⌈(depth : ℝ) * (1 - (33 : ℝ) / 338432) / ((33 : ℝ) / 338432)⌉ + 1 :=
  ceilingPackets_eq_int depth ((33 : ℝ) / 338432) (by norm_num) (by norm_num)

theorem paperPackets_pos : 0 < paperPackets := Nat.succ_pos _

abbrev paperBlock := finiteLinearBlock paperPackets

/-- The actual finite binary linear pipeline at the paper's specified length.
This proves the strict NUMERIC inequality, not merely a comparison with the
possibly smaller actual routing capacity. -/
theorem paper_finite_block :
    (paperPackets : ℤ) =
      ⌈(depth : ℝ) * (1 - (33 : ℝ) / 338432) / ((33 : ℝ) / 338432)⌉ + 1 ∧
    0 < paperPackets ∧
    BinaryLinearPipeline.BinaryLinearBlock network source sink paperBlock ∧
    Nonempty (NetworkRates.BlockCode network source sink paperPackets (paperPackets + depth)) ∧
    1 - (33 : ℝ) / 338432 < (paperPackets : ℝ) / (paperPackets + depth) :=
  ⟨paperPackets_eq_integer, paperPackets_pos, finiteLinearBlock_linear paperPackets, ⟨paperBlock⟩,
    ceiling_pipeline_rate depth ((33 : ℝ) / 338432) (by norm_num)⟩

end
end CodedSorting.Construction.NetworkCodingResult
