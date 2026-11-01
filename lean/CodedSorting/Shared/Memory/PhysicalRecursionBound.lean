import CodedSorting.Interchange.Framework.Memory.PhysicalExchangeRecursion

/-! Sharp I/O bound for the actual canonical-file recursive interpreter.
The tree below is only an exact arithmetic representation of its already
proved costBound; all final statements concern the same Option execution.
The cutoff retains every startup charge and makes each genuine child at
least one block, preserving the S/W rather than S growth multiplier. -/
namespace CodedSorting.PhysicalRecursionBound
open Circuit Address RecursiveExchange RecursiveExchangeCost
open PhysicalRecursiveExchange PhysicalFieldPacking PhysicalExchangeRecursion
open PhysicalWholeLevel
noncomputable section

def localCoefficient : ℕ := max 12 levelCoefficient

def boundConstant : ℝ := CallTree.uniformConstant (2*(localCoefficient : ℝ)) (2*12)

theorem boundConstant_nonneg : 0 ≤ boundConstant :=
  CallTree.uniformConstant_nonneg _ _ (by positivity) (by norm_num)

/-- Exact identification of the bound proved from actual recursive calls;
no hypothesized global recurrence or independently charged tree is used. -/
theorem costBound_eq_tree (B cutoff k V : ℕ) :
    costBound B cutoff k V = CallTree.cost (CallTree.prunedBuild 1 cutoff
      (fun V => 12*(V/B+1)) (fun _ V => localCoefficient*(V/B+1)) k V) := by
  induction k generalizing V with
  | zero => rfl
  | succ k ih =>
    rw [costBound,CallTree.prunedBuild]
    split_ifs with hfit
    · rfl
    · simp only [CallTree.cost,Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul]
      rw [← ih]
      rfl

/-- Every startup and scan in the explicit recurrence is absorbed with
constants independent of recursion depth, base width and data volume. -/
theorem costBound_scaled (B cutoff k V : ℕ) (hcut : Parameters.W*B ≤ cutoff) :
    (costBound B cutoff k V : ℝ)*B ≤ boundConstant*
      (B+(V : ℝ)*(Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  rw [costBound_eq_tree]
  apply CallTree.pruned_cost_with_startup 1 cutoff B
    (fun V => 12*(V/B+1)) (fun _ V => localCoefficient*(V/B+1))
    (2*(localCoefficient : ℝ)) 12 hcut (by positivity) (by norm_num)
  · intro v
    have hd := Nat.div_mul_le_self v B
    have hb : (12*(v/B+1))*B ≤ 12*(B+v) := by nlinarith
    exact_mod_cast hb
  · intro j v hlarge
    have hW : 1 ≤ Parameters.W := by rw [Parameters.W_value]; omega
    have hWB : B ≤ Parameters.W*B := by
      simpa only [one_mul] using Nat.mul_le_mul_right B hW
    have hv : B ≤ v := hWB.trans (hcut.trans hlarge.le)
    have hd := Nat.div_mul_le_self v B
    have hs : (v/B+1)*B ≤ 2*v := by nlinarith
    have hb := Nat.mul_le_mul_left localCoefficient hs
    have hb' : (localCoefficient*(v/B+1))*B ≤ (2*localCoefficient)*v := by nlinarith
    exact_mod_cast hb'

/-- The initial sub-block call keeps an additive startup. The geometric
factor multiplies data volume alone, not every empty descendant. -/
theorem costBound_transfers (B cutoff k V : ℕ) (hB : 0 < B)
    (hcut : Parameters.W*B ≤ cutoff) :
    (costBound B cutoff k V : ℝ) ≤ boundConstant*
      (1+(V : ℝ)/B*(Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  have hb : (0 : ℝ)<B := by exact_mod_cast hB
  apply (mul_le_mul_right hb).mp
  calc
    _ ≤ boundConstant*(B+(V : ℝ)*(Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) :=
      costBound_scaled B cutoff k V hcut
    _ = _ := by field_simp

/-- Functional correctness and the improved asymptotic exponent hold for
one and the same successful execution of the actual recursive file runner.
Only numerical startup/cutoff premises remain, not child-call contracts. -/
theorem actual_recursive_exchange_bound (base cutoff B : ℕ) (hB : 0 < B)
    (hbase : (radix^base*radix^base)*B ≤ cutoff+B)
    (hcut : Parameters.W*B ≤ cutoff)
    (k rows G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (F : ScalarData (base*Parameters.m^k) (rows*Parameters.W^k) G S)
    (source : File)
    (hs : source=represented (scalarLayout (base*Parameters.m^k) (rows*Parameters.W^k) G S) B hB F) :
    ∃ result,
      run base cutoff B hB k rows G S source=some result ∧
      result.1=represented (scalarLayout (base*Parameters.m^k) (rows*Parameters.W^k) G S)
        B hB (transport exchangeEquiv F) ∧
      (result.2 : ℝ) ≤ boundConstant*
        (1+(volume base k rows G S : ℝ)/B*
          (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  obtain ⟨result,hr,ho,hc⟩ := run_correct_cost base cutoff B hB hbase k rows G S hG hS F source hs
  refine ⟨result,hr,ho,?_⟩
  exact (Nat.cast_le.mpr hc).trans (costBound_transfers B cutoff k _ hB hcut)

end
end CodedSorting.PhysicalRecursionBound
