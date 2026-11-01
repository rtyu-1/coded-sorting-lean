import CodedSorting.Shared.Programs.LocalToMSD
import CodedSorting.Sorting.Local.Framework.LocalSortingComplete
import Mathlib.Data.Nat.Log
import CodedSorting.Sorting.Local.Framework.PhysicalLocalSortTranspose

section GlobalSortingBound
/-! The integer radix depth and the final logarithmic algebra for the actual
Columnsort/MSD composition. The address-exchange implementation retains its
explicit primitive contract in this trace-cost composition. -/
set_option autoImplicit false
namespace CodedSorting.GlobalSortingBound
open LocalShape LocalSortingCost GroupedNearMemory

/-- Minimum number of base-H digits covering the complete w-bit universe. -/
def depth (H w : ℕ) : ℕ := Nat.clog H (2 ^ w)

theorem depth_covers (H w : ℕ) (hH : 2 ≤ H) : 2 ^ w ≤ H ^ depth H w :=
  Nat.le_pow_clog (by omega) _

/-- Exact integer ceiling-log depth versus its real logarithm. -/
theorem clog_log_bound (H U : ℕ) (hH : 2 ≤ H) (hU : 1 ≤ U) :
    (Nat.clog H U : ℝ) ≤ Real.log (U : ℝ) / Real.log (H : ℝ) + 1 := by
  have hHR : (1 : ℝ) < H := by exact_mod_cast (show 1 < H by omega)
  have hh : 0 < Real.log (H : ℝ) := Real.log_pos hHR
  by_cases hsmall : U ≤ 1
  · have hu : U = 1 := by omega
    simp [hu, Nat.clog_one_right]
  · have hlarge : 1 < U := by omega
    have hp := Nat.pow_pred_clog_lt_self (by omega : 1 < H) hlarge
    have hpow : (H : ℝ) ^ (Nat.clog H U).pred < U := by exact_mod_cast hp
    have hlog := Real.log_lt_log (pow_pos (by linarith : (0 : ℝ) < H) _) hpow
    rw [Real.log_pow] at hlog
    have hc := Nat.clog_pos (by omega : 1 < H) (by omega : 2 ≤ U)
    have hcast : ((Nat.clog H U).pred : ℝ) = (Nat.clog H U : ℝ) - 1 := by
      rw [Nat.pred_eq_sub_one, Nat.cast_sub (by omega : 1 ≤ Nat.clog H U)]
      simp
    rw [hcast] at hlog
    have hdiv := (lt_div_iff₀ hh).2 hlog
    linarith

theorem depth_log_bound (H w : ℕ) (hH : 2 ≤ H) :
    (depth H w : ℝ) ≤ (w : ℝ) * Real.log 2 / Real.log (H : ℝ) + 1 := by
  have h := clog_log_bound H (2 ^ w) hH (Nat.one_le_pow _ _ (by decide))
  simpa only [depth, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

/-- All actual local Columnsort fields fit within this one fixed width for H. -/
theorem local_width_bound (H n : ℕ) (hn : n ≤ H ^ 2) :
    sizeExponent n ≤ Nat.clog 2 H := by
  apply (Nat.le_pow_iff_clog_le (by decide : 1 < 16)).1
  have hpow : H ≤ 2 ^ Nat.clog 2 H := Nat.le_pow_clog (by decide) H
  calc
    n ≤ H ^ 2 := hn
    _ ≤ (2 ^ Nat.clog 2 H) ^ 2 := Nat.pow_le_pow_left hpow 2
    _ = 4 ^ Nat.clog 2 H := by rw [← pow_mul, Nat.mul_comm (Nat.clog 2 H) 2, pow_mul]; norm_num
    _ ≤ 16 ^ Nat.clog 2 H := Nat.pow_le_pow_left (by decide : 4 ≤ 16) _

noncomputable def localRate (H : ℕ) (K a τ : ℝ) : ℕ := roundedRate K a τ (Nat.clog 2 H)

theorem local_exchange_contract (B H : ℕ) (K a τ : ℝ) (hK : 0 ≤ K)
    (ha : 0 < a) (hτ : 0 ≤ τ) (exchangeCost : InterchangeCost)
    (hx : ∀ t V, ((exchangeCost t V * B : ℕ) : ℝ) ≤
      K * (1 + ((t : ℝ) / a) ^ τ) * ((V + B : ℕ) : ℝ)) :
    ∀ n, 512 * H < n → n ≤ H ^ 2 →
      exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B ≤
        localRate H K a τ * (sizeChoice n ^ 4 + B) := by
  intro n _ hn
  have hr := rounded_exchange_contract B K a τ exchangeCost hx (sizeExponent n) (sizeChoice n ^ 4)
  exact hr.trans (Nat.mul_le_mul_right _
    (roundedRate_monotone K a τ hK ha hτ (local_width_bound H n hn)))

noncomputable def rateConstant (K τ : ℝ) : ℝ := K * (1 + (1 / Real.log 2 + 3) ^ τ) + 3

theorem localRate_power_bound (H : ℕ) (hH : 2 ≤ H) (K a τ : ℝ)
    (hK : 0 ≤ K) (ha : 1 ≤ a) (hτ : 0 ≤ τ) :
    (localRate H K a τ : ℝ) + 2 ≤
      rateConstant K τ * (1 + (Real.log (H : ℝ) / a) ^ τ) := by
  have ha0 : 0 < a := by linarith
  have hHlog : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ H by omega))
  have hclog := clog_log_bound 2 H (by decide) (by omega)
  norm_num only [Nat.cast_ofNat] at hclog
  have ht := div_le_div_of_nonneg_right hclog (le_of_lt ha0)
  have h1 : (1 : ℝ) / a ≤ 1 := (div_le_iff₀ ha0).2 (by linarith)
  apply rounded_rate_bound K a τ (Real.log (H : ℝ) / a) (Nat.clog 2 H)
    hK ha0 hτ (div_nonneg hHlog (le_of_lt ha0))
  have he : (Real.log (H : ℝ) / Real.log 2 + 1) / a =
      (Real.log (H : ℝ) / a) / Real.log 2 + 1 / a := by ring
  rw [he] at ht
  linarith

def sort (H : ℕ) (hH : 0 < H) (w : ℕ) (xs : List ℕ) : List ℕ :=
  LocalToMSD.sort H hH H hH (depth H w) xs

def cost (B H : ℕ) (hB : 0 < B) (hH : 0 < H)
    (exchangeCost : InterchangeCost) (w : ℕ) (xs : List ℕ) : ℕ :=
  LocalToMSD.cost H hH B hB H hH exchangeCost (depth H w) xs

theorem sort_correct (H w : ℕ) (hH : 2 ≤ H) (xs : List ℕ)
    (hkeys : ∀ x ∈ xs, x < 2 ^ w) :
    (sort H (by omega) w xs).Perm xs ∧ (sort H (by omega) w xs).Pairwise (· ≤ ·) := by
  apply LocalToMSD.sort_correct
  exact fun x hx => (hkeys x hx).trans_le (depth_covers H w hH)

/-- Coarse finite-depth cost for the same actual sorter, after inserting the
proved local trace bound and the explicit exchange primitive's rate. -/
theorem conditional_integer_cost (B H : ℕ) (hB : 0 < B) (hH : 2 ≤ H) (hBH : B ≤ H)
    (K a τ : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hτ : 0 ≤ τ)
    (exchangeCost : InterchangeCost)
    (hx : ∀ t V, ((exchangeCost t V * B : ℕ) : ℝ) ≤
      K * (1 + ((t : ℝ) / a) ^ τ) * ((V + B : ℕ) : ℝ))
    (w : ℕ) (xs : List ℕ) (hBN : B ≤ xs.length) :
    cost B H hB (by omega) exchangeCost w xs * B ≤
      135000000 * (localRate H K a τ + 2) * (depth H w + 1) * xs.length := by
  have hc := LocalToMSD.cost_bound H (by omega) B hB H (localRate H K a τ) (by omega) hBH le_rfl
    exchangeCost (local_exchange_contract B H K a τ hK ha hτ exchangeCost hx) (depth H w) xs
  change cost B H hB (by omega) exchangeCost w xs * B ≤ _ at hc
  have hL : 15 ≤ 27000000 * (localRate H K a τ + 2) := by omega
  have hb := Nat.mul_le_mul_left (27000000 * (localRate H K a τ + 2)) hBN
  nlinarith only [hc, hb, Nat.mul_le_mul_right (depth H w * xs.length) hL]

/-- Exact cancellation of the local exchange exponent with the radix depth. -/
theorem power_ratio_identity (h a z τ : ℝ) (hh : 0 < h) (ha : 0 < a) :
    (h / a) ^ τ * (z / h) = z / (a ^ τ * h ^ (1 - τ)) := by
  rw [Real.div_rpow (le_of_lt hh) (le_of_lt ha), Real.rpow_sub hh, Real.rpow_one]
  have hap : a ^ τ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha τ)
  have hhp : h ^ τ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh τ)
  field_simp
  ring

/-- Pure algebra: logarithmically many digits and the sublinear local
exchange rate give exactly the denominator in the paper's simple bound. -/
theorem depth_times_rate (h a z τ κ : ℝ) (hh : 0 < h) (ha : 0 < a)
    (hah : a ≤ h) (hzh : h ≤ z) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ) :
    (1 + (h / a) ^ τ) * (2 + κ * z / h) ≤
      2 * (κ + 2) * (z / (a ^ τ * h ^ (1 - τ))) := by
  have hz : 0 ≤ z := le_trans (le_of_lt hh) hzh
  have hratio : 1 ≤ h / a := (le_div_iff₀ ha).2 (by simpa)
  have hp : 1 ≤ (h / a) ^ τ := Real.one_le_rpow hratio hτ
  have hdepth : 2 + κ * z / h ≤ (κ + 2) * (z / h) := by
    have hzratio : 1 ≤ z / h := (le_div_iff₀ hh).2 (by simpa)
    rw [mul_div_assoc]
    nlinarith only [hzratio]
  calc
    (1 + (h / a) ^ τ) * (2 + κ * z / h) ≤
        (2 * (h / a) ^ τ) * ((κ + 2) * (z / h)) :=
      mul_le_mul (by linarith) hdepth (by positivity) (by positivity)
    _ = 2 * (κ + 2) * ((h / a) ^ τ * (z / h)) := by ring
    _ = _ := by rw [power_ratio_identity h a z τ hh ha]

noncomputable def boundConstant (K τ κ : ℝ) : ℝ :=
  270000000 * rateConstant K τ * (κ + 2)

/-- Final simple logarithmic expression for the real cost of the actual
MSD/Columnsort composition. The only algorithmic cost hypothesis is the
separately named address-exchange primitive; no sorting bound is assumed.
H denotes reserved usable memory, before the physical M-normalization. -/
theorem conditional_sorting_power (B H : ℕ) (hB : 0 < B) (hH : 2 ≤ H) (hBH : B ≤ H)
    (K a τ κ : ℝ) (hK : 0 ≤ K) (ha : 1 ≤ a) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (hah : a ≤ Real.log (H : ℝ)) (exchangeCost : InterchangeCost)
    (hx : ∀ t V, ((exchangeCost t V * B : ℕ) : ℝ) ≤
      K * (1 + ((t : ℝ) / a) ^ τ) * ((V + B : ℕ) : ℝ))
    (w : ℕ) (xs : List ℕ) (hHN : H ≤ xs.length)
    (hword : (w : ℝ) * Real.log 2 ≤ κ * Real.log (xs.length : ℝ)) :
    (cost B H hB (by omega) exchangeCost w xs : ℝ) ≤
      boundConstant K τ κ * ((xs.length : ℝ) / B) *
        (1 + Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ))) := by
  have ha0 : 0 < a := by linarith
  have hHR : (1 : ℝ) < H := by exact_mod_cast (show 1 < H by omega)
  have hH0 : (0 : ℝ) < H := by linarith
  have hh : 0 < Real.log (H : ℝ) := Real.log_pos hHR
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hlogN := Real.log_le_log hH0 (show (H : ℝ) ≤ xs.length by exact_mod_cast hHN)
  have hR : 0 ≤ rateConstant K τ := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    unfold rateConstant
    positivity
  have hpow : 0 ≤ (Real.log (H : ℝ) / a) ^ τ := Real.rpow_nonneg (by positivity) τ
  have hdepth := depth_log_bound H w hH
  have hworddiv := div_le_div_of_nonneg_right hword (le_of_lt hh)
  have hd : (depth H w : ℝ) + 1 ≤ 2 + κ * Real.log (xs.length : ℝ) / Real.log (H : ℝ) := by
    linarith
  have hcoeff := depth_times_rate (Real.log (H : ℝ)) a (Real.log (xs.length : ℝ)) τ κ
    hh ha0 hah hlogN hτ hκ
  have hi := conditional_integer_cost B H hB hH hBH K a τ hK ha0 hτ exchangeCost hx
    w xs (le_trans hBH hHN)
  have hiR : (cost B H hB (by omega) exchangeCost w xs : ℝ) * B ≤
      135000000 * ((localRate H K a τ : ℝ) + 2) * ((depth H w : ℝ) + 1) * xs.length := by
    exact_mod_cast hi
  have hr := localRate_power_bound H hH K a τ hK ha hτ
  have hproduct := mul_le_mul hr hd (by positivity : (0 : ℝ) ≤ (depth H w : ℝ) + 1)
    (mul_nonneg hR (by linarith))
  have hproduct' : ((localRate H K a τ : ℝ) + 2) * ((depth H w : ℝ) + 1) ≤
      rateConstant K τ * (2 * (κ + 2) * (Real.log (xs.length : ℝ) /
        (a ^ τ * Real.log (H : ℝ) ^ (1 - τ)))) := by
    calc
      _ ≤ (rateConstant K τ * (1 + (Real.log (H : ℝ) / a) ^ τ)) *
          (2 + κ * Real.log (xs.length : ℝ) / Real.log (H : ℝ)) := hproduct
      _ = rateConstant K τ * ((1 + (Real.log (H : ℝ) / a) ^ τ) *
          (2 + κ * Real.log (xs.length : ℝ) / Real.log (H : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff hR
  have hscaled := mul_le_mul_of_nonneg_left hproduct'
    (show (0 : ℝ) ≤ 135000000 * (xs.length : ℝ) by positivity)
  have hCB : (cost B H hB (by omega) exchangeCost w xs : ℝ) * B ≤
      boundConstant K τ κ * (xs.length : ℝ) *
        (Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ))) := by
    unfold boundConstant
    nlinarith only [hiR, hscaled]
  apply (le_div_iff₀ hBR).2 at hCB
  have hnonneg : 0 ≤ boundConstant K τ κ * ((xs.length : ℝ) / B) := by
    unfold boundConstant
    positivity
  calc
    _ ≤ (boundConstant K τ κ * (xs.length : ℝ) *
        (Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ)))) / B := hCB
    _ ≤ _ := by
      have he : (boundConstant K τ κ * (xs.length : ℝ) *
          (Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ)))) / B =
          (boundConstant K τ κ * ((xs.length : ℝ) / B)) *
            (Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ))) := by ring
      rw [he, mul_add, mul_one]
      linarith

/-- Substituting the paper's fixed positive epsilon gives the advertised
simple denominator. This remains explicitly conditional on the address
primitive and on the usable-memory normalization (here log(H/B)>=1). -/
theorem conditional_main_power (B H : ℕ) (hB : 0 < B) (hH : 2 ≤ H) (hBH : B ≤ H)
    (K κ : ℝ) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (ha : 1 ≤ Real.log ((H : ℝ) / B)) (exchangeCost : InterchangeCost)
    (hx : ∀ t V, ((exchangeCost t V * B : ℕ) : ℝ) ≤
      K * (1 + ((t : ℝ) / Real.log ((H : ℝ) / B)) ^ (1 - (Parameters.epsilon : ℝ))) *
        ((V + B : ℕ) : ℝ))
    (w : ℕ) (xs : List ℕ) (hHN : H ≤ xs.length)
    (hword : (w : ℝ) * Real.log 2 ≤ κ * Real.log (xs.length : ℝ))
    (hkeys : ∀ x ∈ xs, x < 2 ^ w) :
    (sort H (by omega) w xs).Perm xs ∧ (sort H (by omega) w xs).Pairwise (· ≤ ·) ∧
      (cost B H hB (by omega) exchangeCost w xs : ℝ) ≤
        boundConstant K (1 - (Parameters.epsilon : ℝ)) κ * ((xs.length : ℝ) / B) *
          (1 + Real.log (xs.length : ℝ) /
            (Real.log ((H : ℝ) / B) ^ (1 - (Parameters.epsilon : ℝ)) *
              Real.log (H : ℝ) ^ (Parameters.epsilon : ℝ))) := by
  have he : (Parameters.epsilon : ℝ) < 1 := by exact_mod_cast Parameters.epsilon_lt_one
  have hτ : (0 : ℝ) ≤ 1 - (Parameters.epsilon : ℝ) := by linarith
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hah : Real.log ((H : ℝ) / B) ≤ Real.log (H : ℝ) := by
    rw [Real.log_div (ne_of_gt hHR) (ne_of_gt hBR)]
    linarith
  have hc := conditional_sorting_power B H hB hH hBH K (Real.log ((H : ℝ) / B))
    (1 - (Parameters.epsilon : ℝ)) κ hK ha hτ hκ hah exchangeCost hx w xs hHN hword
  refine ⟨(sort_correct H w hH xs hkeys).1, (sort_correct H w hH xs hkeys).2, ?_⟩
  simpa only [sub_sub_cancel] using hc

end CodedSorting.GlobalSortingBound
end GlobalSortingBound

section MainSortingParameters
/-! The integer base chosen by the actual exchange program is comparable
to the real logarithm used in the main sorting bound.  These lemmas do not
change the memory parameter or the word width. -/
set_option autoImplicit false
namespace CodedSorting.MainSortingParameters
open Circuit RecursiveExchange PhysicalRecursiveExchange
open NormalizedPhysicalExchange PhysicalLeafParameters
noncomputable section

def baseLogConstant : ℝ := (8 * (Parameters.m : ℝ) + 2) * Real.log (radix : ℝ)

theorem baseLogConstant_nonneg : 0 ≤ baseLogConstant := by
  have hq : (1 : ℝ) ≤ radix := by exact_mod_cast radix_prime.one_lt.le
  unfold baseLogConstant
  exact mul_nonneg (by positivity) (Real.log_nonneg hq)

theorem ratio_pos (reserve H B : ℕ)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ H / B) : 0 < H / B := by
  have hp : 0 < radix ^ (8 * (Nat.log radix reserve + 1)) :=
    pow_pos radix_prime.pos _
  exact hp.trans_le ((Nat.le_max_left _ _).trans hnormal)

theorem quotient_lt_succ (H B : ℕ) (hB : 0 < B) :
    (H : ℝ) / B < (H / B : ℕ) + 1 := by
  apply (div_lt_iff₀ (show (0 : ℝ) < B by exact_mod_cast hB)).2
  have hh : H < (H / B + 1) * B := by
    have := Nat.mod_lt H hB
    have := Nat.div_add_mod H B
    nlinarith
  exact_mod_cast hh

theorem log_ratio_le_base (reserve H B : ℕ) (hB : 0 < B)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ H / B) :
    Real.log ((H : ℝ) / B) ≤ baseLogConstant * chosenBase H B := by
  have hb := (chosenBase_bounds reserve H B hnormal).1
  have hr := ratio_pos reserve H B hnormal
  have hH : 0 < H := by exact Nat.pos_of_div_pos hr
  have hq : (1 : ℝ) < radix := by exact_mod_cast radix_prime.one_lt
  have hq0 : (0 : ℝ) < radix := by linarith
  have hp := Nat.lt_pow_succ_log_self radix_prime.one_lt (H / B)
  have hpn : H / B + 1 ≤ radix ^ (Nat.log radix (H / B) + 1) := hp
  have hpr : ((H / B : ℕ) : ℝ) + 1 ≤
      (radix : ℝ) ^ (Nat.log radix (H / B) + 1) := by exact_mod_cast hpn
  have hquot := (quotient_lt_succ H B hB).trans_le hpr
  have hlog := Real.log_le_log
    (show 0 < (H : ℝ) / B by positivity) hquot.le
  rw [Real.log_pow] at hlog
  have he := (chosenBase_log reserve H B hnormal).2
  have he' : (Nat.log radix (H / B) : ℝ) + 1 ≤
      (8 * (Parameters.m : ℝ) + 2) * chosenBase H B := by
    have heR : (Nat.log radix (H / B) : ℝ) <
        8 * (Parameters.m : ℝ) * chosenBase H B := by exact_mod_cast he
    have hbR : (1 : ℝ) ≤ chosenBase H B := by exact_mod_cast hb
    nlinarith
  have hm := mul_le_mul_of_nonneg_right he' (Real.log_nonneg hq.le)
  push_cast at hlog
  unfold baseLogConstant
  nlinarith only [hlog, hm]

theorem normalized_log_one (reserve H B : ℕ) (hB : 0 < B)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ H / B) :
    1 ≤ Real.log ((H : ℝ) / B) := by
  have hb := (chosenBase_bounds reserve H B hnormal).1
  have he := (chosenBase_log reserve H B hnormal).1
  have hr := ratio_pos reserve H B hnormal
  have hpow : radix ^ 8 ≤ H / B := Nat.pow_le_of_le_log (Nat.ne_of_gt hr) (by omega)
  have hfour : 4 ≤ H / B := by
    have hp := Nat.pow_le_pow_left (show 2 ≤ radix by exact radix_prime.one_lt) 8
    norm_num at hp
    omega
  have hcast : (4 : ℝ) ≤ (H / B : ℕ) := by exact_mod_cast hfour
  have hquot : (4 : ℝ) ≤ (H : ℝ) / B := hcast.trans (Nat.cast_div_le)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hquot
  have hlogfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlogfour] at hl
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh
  linarith

theorem normalized_memory (reserve H B : ℕ) (hB : 0 < B)
    (hnormal : minimumRatio radix reserve Parameters.W ≤ H / B) :
    2 ≤ H ∧ B ≤ H := by
  have hb := (chosenBase_bounds reserve H B hnormal).1
  have he := (chosenBase_log reserve H B hnormal).1
  have hr := ratio_pos reserve H B hnormal
  have hpow : radix ^ 8 ≤ H / B := Nat.pow_le_of_le_log (Nat.ne_of_gt hr) (by omega)
  have htwo : 2 ≤ H / B := by
    have hp := Nat.pow_le_pow_left (show 2 ≤ radix by exact radix_prime.one_lt) 8
    norm_num at hp
    omega
  have hd := Nat.div_mul_le_self H B
  constructor <;> nlinarith

end
end CodedSorting.MainSortingParameters
end MainSortingParameters

section ActualShapeSortingBound
/-! The existing scalar Columnsort/MSD sorter needs exchange estimates only
at its actual nonterminal local shapes.  This module narrows that interface
without changing either the sorting function or its trace cost.

This is the coarse trace-cost composition through `LocalToMSD`. The grouped
near-memory implementation uses exchange volume `sizeChoice n ^ 4 * g`
and its corresponding scaled-shape contract. Finite-RAM and common-disk
realization are handled by the physical implementation modules. -/

set_option autoImplicit false
namespace CodedSorting.ActualShapeSortingBound
open LocalShape LocalSortingCost GroupedNearMemory GlobalSortingBound

/-- Exactly the nonterminal shapes occurring in the scalar local trace. -/
def ActualShapeRate (B H : ℕ) (K a τ : ℝ)
    (exchangeCost : InterchangeCost) : Prop :=
  ∀ n, 512 * H < n → n ≤ H ^ 2 →
    ((exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B : ℕ) : ℝ) ≤
      K * (1 + ((sizeExponent n : ℝ) / a) ^ τ) *
        ((sizeChoice n ^ 4 + B : ℕ) : ℝ)

/-- Round the rate only at a shape requested by the local sorter. -/
theorem rounded_shape_contract (B H : ℕ) (K a τ : ℝ)
    (exchangeCost : InterchangeCost)
    (hx : ActualShapeRate B H K a τ exchangeCost) :
    ∀ n, 512 * H < n → n ≤ H ^ 2 →
      exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B ≤
        roundedRate K a τ (sizeExponent n) * (sizeChoice n ^ 4 + B) := by
  intro n hlarge hn
  have hr := Nat.le_ceil (K * (1 + ((sizeExponent n : ℝ) / a) ^ τ))
  have hm := mul_le_mul_of_nonneg_right hr
    (Nat.cast_nonneg (sizeChoice n ^ 4 + B))
  have h := le_trans (hx n hlarge hn) hm
  exact_mod_cast h

/-- One width bound serves all actual local exchange calls. -/
theorem local_exchange_contract (B H : ℕ) (K a τ : ℝ) (hK : 0 ≤ K)
    (ha : 0 < a) (hτ : 0 ≤ τ) (exchangeCost : InterchangeCost)
    (hx : ActualShapeRate B H K a τ exchangeCost) :
    ∀ n, 512 * H < n → n ≤ H ^ 2 →
      exchangeCost (sizeExponent n) (sizeChoice n ^ 4) * B ≤
        localRate H K a τ * (sizeChoice n ^ 4 + B) := by
  intro n hlarge hn
  have hr := rounded_shape_contract B H K a τ exchangeCost hx n hlarge hn
  exact hr.trans (Nat.mul_le_mul_right _
    (roundedRate_monotone K a τ hK ha hτ (local_width_bound H n hn)))

/-- Coarse finite-depth cost for the same actual sorter, after inserting the
proved local trace bound and the explicit exchange primitive's rate. -/
theorem conditional_integer_cost (B H : ℕ) (hB : 0 < B) (hH : 2 ≤ H) (hBH : B ≤ H)
    (K a τ : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hτ : 0 ≤ τ)
    (exchangeCost : InterchangeCost)
    (hx : ActualShapeRate B H K a τ exchangeCost)
    (w : ℕ) (xs : List ℕ) (hBN : B ≤ xs.length) :
    cost B H hB (by omega) exchangeCost w xs * B ≤
      135000000 * (localRate H K a τ + 2) * (depth H w + 1) * xs.length := by
  have hc := LocalToMSD.cost_bound H (by omega) B hB H (localRate H K a τ) (by omega) hBH le_rfl
    exchangeCost (local_exchange_contract B H K a τ hK ha hτ exchangeCost hx) (depth H w) xs
  change cost B H hB (by omega) exchangeCost w xs * B ≤ _ at hc
  have hL : 15 ≤ 27000000 * (localRate H K a τ + 2) := by omega
  have hb := Nat.mul_le_mul_left (27000000 * (localRate H K a τ + 2)) hBN
  nlinarith only [hc, hb, Nat.mul_le_mul_right (depth H w * xs.length) hL]

/-- Final logarithmic expression for the unchanged MSD/Columnsort trace
cost. Only its actual local exchange shapes need satisfy a rate estimate;
no sorting bound is assumed. Physical realization remains a separate
obligation, and H is reserved usable memory before M-normalization. -/
theorem conditional_sorting_power (B H : ℕ) (hB : 0 < B) (hH : 2 ≤ H) (hBH : B ≤ H)
    (K a τ κ : ℝ) (hK : 0 ≤ K) (ha : 1 ≤ a) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (hah : a ≤ Real.log (H : ℝ)) (exchangeCost : InterchangeCost)
    (hx : ActualShapeRate B H K a τ exchangeCost)
    (w : ℕ) (xs : List ℕ) (hHN : H ≤ xs.length)
    (hword : (w : ℝ) * Real.log 2 ≤ κ * Real.log (xs.length : ℝ)) :
    (cost B H hB (by omega) exchangeCost w xs : ℝ) ≤
      boundConstant K τ κ * ((xs.length : ℝ) / B) *
        (1 + Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ))) := by
  have ha0 : 0 < a := by linarith
  have hHR : (1 : ℝ) < H := by exact_mod_cast (show 1 < H by omega)
  have hH0 : (0 : ℝ) < H := by linarith
  have hh : 0 < Real.log (H : ℝ) := Real.log_pos hHR
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hlogN := Real.log_le_log hH0 (show (H : ℝ) ≤ xs.length by exact_mod_cast hHN)
  have hR : 0 ≤ rateConstant K τ := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    unfold rateConstant
    positivity
  have hpow : 0 ≤ (Real.log (H : ℝ) / a) ^ τ := Real.rpow_nonneg (by positivity) τ
  have hdepth := depth_log_bound H w hH
  have hworddiv := div_le_div_of_nonneg_right hword (le_of_lt hh)
  have hd : (depth H w : ℝ) + 1 ≤ 2 + κ * Real.log (xs.length : ℝ) / Real.log (H : ℝ) := by
    linarith
  have hcoeff := depth_times_rate (Real.log (H : ℝ)) a (Real.log (xs.length : ℝ)) τ κ
    hh ha0 hah hlogN hτ hκ
  have hi := conditional_integer_cost B H hB hH hBH K a τ hK ha0 hτ exchangeCost hx
    w xs (le_trans hBH hHN)
  have hiR : (cost B H hB (by omega) exchangeCost w xs : ℝ) * B ≤
      135000000 * ((localRate H K a τ : ℝ) + 2) * ((depth H w : ℝ) + 1) * xs.length := by
    exact_mod_cast hi
  have hr := localRate_power_bound H hH K a τ hK ha hτ
  have hproduct := mul_le_mul hr hd (by positivity : (0 : ℝ) ≤ (depth H w : ℝ) + 1)
    (mul_nonneg hR (by linarith))
  have hproduct' : ((localRate H K a τ : ℝ) + 2) * ((depth H w : ℝ) + 1) ≤
      rateConstant K τ * (2 * (κ + 2) * (Real.log (xs.length : ℝ) /
        (a ^ τ * Real.log (H : ℝ) ^ (1 - τ)))) := by
    calc
      _ ≤ (rateConstant K τ * (1 + (Real.log (H : ℝ) / a) ^ τ)) *
          (2 + κ * Real.log (xs.length : ℝ) / Real.log (H : ℝ)) := hproduct
      _ = rateConstant K τ * ((1 + (Real.log (H : ℝ) / a) ^ τ) *
          (2 + κ * Real.log (xs.length : ℝ) / Real.log (H : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff hR
  have hscaled := mul_le_mul_of_nonneg_left hproduct'
    (show (0 : ℝ) ≤ 135000000 * (xs.length : ℝ) by positivity)
  have hCB : (cost B H hB (by omega) exchangeCost w xs : ℝ) * B ≤
      boundConstant K τ κ * (xs.length : ℝ) *
        (Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ))) := by
    unfold boundConstant
    nlinarith only [hiR, hscaled]
  apply (le_div_iff₀ hBR).2 at hCB
  have hnonneg : 0 ≤ boundConstant K τ κ * ((xs.length : ℝ) / B) := by
    unfold boundConstant
    positivity
  calc
    _ ≤ (boundConstant K τ κ * (xs.length : ℝ) *
        (Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ)))) / B := hCB
    _ ≤ _ := by
      have he : (boundConstant K τ κ * (xs.length : ℝ) *
          (Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ)))) / B =
          (boundConstant K τ κ * ((xs.length : ℝ) / B)) *
            (Real.log (xs.length : ℝ) / (a ^ τ * Real.log (H : ℝ) ^ (1 - τ))) := by ring
      rw [he, mul_add, mul_one]
      linarith

/-- Substituting the paper's fixed positive epsilon gives the advertised
simple denominator. This remains explicitly conditional on the address
primitive and on the usable-memory normalization (here log(H/B)>=1). -/
theorem conditional_main_power (B H : ℕ) (hB : 0 < B) (hH : 2 ≤ H) (hBH : B ≤ H)
    (K κ : ℝ) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (ha : 1 ≤ Real.log ((H : ℝ) / B)) (exchangeCost : InterchangeCost)
    (hx : ActualShapeRate B H K (Real.log ((H : ℝ) / B))
      (1 - (Parameters.epsilon : ℝ)) exchangeCost)
    (w : ℕ) (xs : List ℕ) (hHN : H ≤ xs.length)
    (hword : (w : ℝ) * Real.log 2 ≤ κ * Real.log (xs.length : ℝ))
    (hkeys : ∀ x ∈ xs, x < 2 ^ w) :
    (sort H (by omega) w xs).Perm xs ∧ (sort H (by omega) w xs).Pairwise (· ≤ ·) ∧
      (cost B H hB (by omega) exchangeCost w xs : ℝ) ≤
        boundConstant K (1 - (Parameters.epsilon : ℝ)) κ * ((xs.length : ℝ) / B) *
          (1 + Real.log (xs.length : ℝ) /
            (Real.log ((H : ℝ) / B) ^ (1 - (Parameters.epsilon : ℝ)) *
              Real.log (H : ℝ) ^ (Parameters.epsilon : ℝ))) := by
  have he : (Parameters.epsilon : ℝ) < 1 := by exact_mod_cast Parameters.epsilon_lt_one
  have hτ : (0 : ℝ) ≤ 1 - (Parameters.epsilon : ℝ) := by linarith
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hah : Real.log ((H : ℝ) / B) ≤ Real.log (H : ℝ) := by
    rw [Real.log_div (ne_of_gt hHR) (ne_of_gt hBR)]
    linarith
  have hc := conditional_sorting_power B H hB hH hBH K (Real.log ((H : ℝ) / B))
    (1 - (Parameters.epsilon : ℝ)) κ hK ha hτ hκ hah exchangeCost hx w xs hHN hword
  refine ⟨(sort_correct H w hH xs hkeys).1, (sort_correct H w hH xs hkeys).2, ?_⟩
  simpa only [sub_sub_cancel] using hc

end CodedSorting.ActualShapeSortingBound
end ActualShapeSortingBound

section MainSortingParametersNormalized
/-! Normalization reaches the concrete exchange program's fixed startup
ratio for every sufficiently large M, including M=2B.  The threshold and
block-rescaling factor depend only on the fixed reservation parameter. -/
set_option autoImplicit false
namespace CodedSorting.MainSortingParametersNormalized
open Circuit RecursiveExchange PhysicalRecursiveExchange PhysicalLeafParameters
open Normalization NormalizationLogs
noncomputable section

def scale (reserve : ℕ) : ℕ := 8 * minimumRatio radix reserve Parameters.W

theorem scale_ge_eight (reserve : ℕ) : 8 ≤ scale reserve := by
  have hp : 0 < radix ^ (8 * (Nat.log radix reserve + 1)) := pow_pos radix_prime.pos _
  have hr : 1 ≤ minimumRatio radix reserve Parameters.W :=
    hp.trans_le (Nat.le_max_left _ _)
  unfold scale
  omega

theorem normalized_startup (reserve M B : ℕ) (hM : scale reserve ≤ M) (hBM : B ≤ M) :
    minimumRatio radix reserve Parameters.W ≤ (M/4) / logicalBlockSize B (scale reserve) := by
  apply (Nat.le_div_iff_mul_le (logical_block_positive _ _)).2
  apply normalized_ratio M B _ _
  · unfold scale
    omega
  · unfold scale at hM
    omega
  · exact hBM

theorem normalized_scan (M B K N : ℕ) (hB : 0 < B) (hK : 0 < K) :
    (N : ℝ) / logicalBlockSize B K ≤ (2*K : ℝ) * ((N : ℝ)/B) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hb : (0 : ℝ) < logicalBlockSize B K := by exact_mod_cast logical_block_positive B K
  apply (div_le_iff₀ hb).2
  rw [show (2*K : ℝ)*((N : ℝ)/B)*(logicalBlockSize B K : ℝ) =
    ((N : ℝ)*(2*K*(logicalBlockSize B K : ℝ)))/B by ring]
  apply (le_div_iff₀ hBr).2
  have he : (B : ℝ) ≤ (2*K : ℝ)*(logicalBlockSize B K : ℝ) := by
    exact_mod_cast block_expansion_bound B K hK
  exact mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)

theorem power_scaled (x y τ : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≤ 4*y) (ht : 0 ≤ τ) (ht1 : τ ≤ 1) : x^τ ≤ 4*y^τ := by
  have hp := Real.rpow_le_rpow hx hxy ht
  rw [Real.mul_rpow (by norm_num) hy] at hp
  have hfour : (4 : ℝ)^τ ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤4) ht1
    simpa using h
  exact hp.trans (mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hy _))

theorem denominator_transfer (M B K : ℕ) (hM : 8 ≤ M) (hK : 8 ≤ K)
    (hB : 0 < B) (hMB : 2*B ≤ M) :
    Real.log ((M : ℝ)/B)^(1-(Parameters.epsilon : ℝ)) *
        Real.log (M : ℝ)^(Parameters.epsilon : ℝ) ≤
      16*(Real.log (((M/4 : ℕ) : ℝ)/logicalBlockSize B K)^(1-(Parameters.epsilon : ℝ)) *
        Real.log ((M/4 : ℕ) : ℝ)^(Parameters.epsilon : ℝ)) := by
  have he0 : 0 ≤ (Parameters.epsilon : ℝ) := by exact_mod_cast Parameters.epsilon_pos.le
  have he1 : (Parameters.epsilon : ℝ) ≤ 1 := by exact_mod_cast Parameters.epsilon_lt_one.le
  have hratio := (normalized_log_ratio M B K hM hK hB hMB).1
  have hmem := (normalized_log_memory M hM).1
  have hmem0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤M by omega))
  have hnormmem0 : 0 ≤ Real.log ((M/4 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤M/4 by omega))
  have hBr : (0 : ℝ)<B := by exact_mod_cast hB
  have hratio2 : (2 : ℝ)≤(M : ℝ)/B := by
    apply (le_div_iff₀ hBr).2
    exact_mod_cast hMB
  have hratio0 := Real.log_nonneg (show (1 : ℝ)≤(M : ℝ)/B by linarith)
  have hnormratio0 := Real.log_nonneg
    ((show (1 : ℝ)≤2 by norm_num).trans (normalized_ratio_ge_two M B K hM hK (by omega)))
  have h1 := power_scaled _ _ (1-(Parameters.epsilon : ℝ)) hratio0 hnormratio0
    (by linarith) (by linarith) (by linarith)
  have h2 := power_scaled _ _ (Parameters.epsilon : ℝ) hmem0 hnormmem0
    (by linarith) he0 he1
  have hm := mul_le_mul h1 h2 (Real.rpow_nonneg hmem0 _)
    (by positivity : 0≤4*Real.log (((M/4 : ℕ) : ℝ)/logicalBlockSize B K)^(1-(Parameters.epsilon : ℝ)))
  nlinarith only [hm]

theorem logarithmic_factor_transfer (M B K N : ℕ) (hM : 8 ≤ M) (hK : 8 ≤ K)
    (hB : 0 < B) (hMB : 2*B ≤ M) (hMN : M ≤ N) :
    1+Real.log (N : ℝ) /
        (Real.log (((M/4 : ℕ) : ℝ)/logicalBlockSize B K)^(1-(Parameters.epsilon : ℝ)) *
          Real.log ((M/4 : ℕ) : ℝ)^(Parameters.epsilon : ℝ)) ≤
      16*(1+Real.log (N : ℝ) /
        (Real.log ((M : ℝ)/B)^(1-(Parameters.epsilon : ℝ)) *
          Real.log (M : ℝ)^(Parameters.epsilon : ℝ))) := by
  let D := Real.log ((M : ℝ)/B)^(1-(Parameters.epsilon : ℝ)) *
    Real.log (M : ℝ)^(Parameters.epsilon : ℝ)
  let d := Real.log (((M/4 : ℕ) : ℝ)/logicalBlockSize B K)^(1-(Parameters.epsilon : ℝ)) *
    Real.log ((M/4 : ℕ) : ℝ)^(Parameters.epsilon : ℝ)
  have hBr : (0 : ℝ)<B := by exact_mod_cast hB
  have hratio2 : (2 : ℝ)≤(M : ℝ)/B := by
    apply (le_div_iff₀ hBr).2
    exact_mod_cast hMB
  have hratio := Real.log_pos (show (1 : ℝ)<(M : ℝ)/B by linarith)
  have hmem := Real.log_pos (by exact_mod_cast (show 1<M by omega) : (1 : ℝ)<M)
  have hnormratio := Real.log_pos (lt_of_lt_of_le (by norm_num)
    (normalized_ratio_ge_two M B K hM hK (by omega)))
  have hnormmem := Real.log_pos
    (by exact_mod_cast (show 1<M/4 by omega) : (1 : ℝ)<((M/4 : ℕ) : ℝ))
  have hD : 0<D := by dsimp [D]; positivity
  have hd : 0<d := by dsimp [d]; positivity
  have hz : 0≤Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hDd : D≤16*d := denominator_transfer M B K hM hK hB hMB
  have hdiv : Real.log (N : ℝ)/d ≤ 16*(Real.log (N : ℝ)/D) := by
    rw [show 16*(Real.log (N : ℝ)/D) = (16*Real.log (N : ℝ))/D by ring]
    apply (div_le_div_iff₀ hd hD).2
    have hm := mul_le_mul_of_nonneg_left hDd hz
    nlinarith only [hm]
  change 1+Real.log (N : ℝ)/d ≤ 16*(1+Real.log (N : ℝ)/D)
  linarith

end
end CodedSorting.MainSortingParametersNormalized
end MainSortingParametersNormalized

section SortingExchangeBound
/-! A numerical bridge from the structural charge of the actual binary
file interpreter to the scalar Columnsort/MSD trace.  A record occupies
`recordWords` words, each of width `w`.  The trace charge is a maximum of
the three concrete adjacent-field calls, not a postulated asymptotic rate.
It is an upper bound on their returned I/O counts, not an assertion that
the input-sensitive physical cost equals this trace annotation. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CodedSorting.SortingExchangeBound
open Circuit Address RecursiveExchange PhysicalRecursiveExchange BinaryPadding
open NormalizedPhysicalExchange MainSortingParameters PhysicalArbitraryBound
open PhysicalBinaryBound LocalSortingCost LocalShape ActualShapeSortingBound
noncomputable section

def callBound (reserve H B w t P S : ℕ) : ℕ :=
  PhysicalBinaryExchange.bound (chosenBase H B) (cutoff reserve H w) (B*w) P t 1 S

/-- The scalar Columnsort trace uses adjacent swaps 34, 23, 12.
The second argument is retained because this is the original cost interface;
the theorem below uses it only at the actual shape `(2^t)^4`. -/
def exchangeCost (reserve H B w recordWords : ℕ) : InterchangeCost := fun t _ =>
  let s := 2^t
  max (callBound reserve H B w t (s^2) (recordWords*w))
    (max (callBound reserve H B w t s (s*(recordWords*w)))
      (callBound reserve H B w t 1 (s^2*(recordWords*w))))

def rateConstant (recordWords : ℕ) : ℝ :=
  binaryConstant * recordWords *
    (1 + baseLogConstant ^ (1 - (Parameters.epsilon : ℝ)))

theorem rateConstant_nonneg (recordWords : ℕ) : 0 ≤ rateConstant recordWords := by
  unfold rateConstant
  have := binaryConstant_nonneg
  have := baseLogConstant_nonneg
  positivity

theorem scalar_volume_34 (t r w : ℕ) :
    Volume ((2^t)^2) (2^t) 1 (r*w) = (2^t)^4*(r*w) := by
  unfold Volume
  ring

theorem scalar_volume_23 (t r w : ℕ) :
    Volume (2^t) (2^t) 1 (2^t*(r*w)) = (2^t)^4*(r*w) := by
  unfold Volume
  ring

theorem scalar_volume_12 (t r w : ℕ) :
    Volume 1 (2^t) 1 ((2^t)^2*(r*w)) = (2^t)^4*(r*w) := by
  unfold Volume
  ring

theorem exchange_cost_physical_bound (reserve H B w r t V : ℕ)
    (hreserve : 0 < reserve) (hB : 0 < B) (hw : 0 < w) (hr : 0 < r)
    (hnormal : PhysicalLeafParameters.minimumRatio radix reserve Parameters.W ≤ H/B) :
    (exchangeCost reserve H B w r t V : ℝ) ≤
      binaryConstant * scan (B*w) ((2^t)^4*(r*w)) *
        (1 + ((t : ℝ) / chosenBase H B) ^ (1 - (Parameters.epsilon : ℝ))) := by
  have hb := (chosenBase_bounds reserve H B hnormal).1
  have hc := cutoff_child_blocks reserve H B w hreserve hnormal
  have h34 := bound_improved (chosenBase H B) (cutoff reserve H w) (B*w)
    ((2^t)^2) t 1 (r*w) (Nat.mul_pos hB hw) hb (by positivity) (by omega) (by positivity) hc
  have h23 := bound_improved (chosenBase H B) (cutoff reserve H w) (B*w)
    (2^t) t 1 (2^t*(r*w)) (Nat.mul_pos hB hw) hb (by positivity) (by omega) (by positivity) hc
  have h12 := bound_improved (chosenBase H B) (cutoff reserve H w) (B*w)
    1 t 1 ((2^t)^2*(r*w)) (Nat.mul_pos hB hw) hb (by omega) (by omega) (by positivity) hc
  rw [scalar_volume_34] at h34
  rw [scalar_volume_23] at h23
  rw [scalar_volume_12] at h12
  simpa only [exchangeCost, callBound, Nat.cast_max, max_le_iff] using
    (show _ ∧ _ ∧ _ from ⟨h34,h23,h12⟩)

theorem scan_record_words (B w r V : ℕ) (hB : 0 < B) (hw : 0 < w) (hr : 0 < r) :
    scan (B*w) (V*(r*w)) * B ≤ (r : ℝ) * (V+B) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have he : scan (B*w) (V*(r*w)) * B = B + (V : ℝ)*r := by
    unfold scan
    push_cast
    field_simp
    <;> ring
  rw [he]
  nlinarith

theorem factor_log_bound (reserve H B t : ℕ) (hB : 0 < B)
    (hnormal : PhysicalLeafParameters.minimumRatio radix reserve Parameters.W ≤ H/B) :
    1 + ((t : ℝ) / chosenBase H B) ^ (1 - (Parameters.epsilon : ℝ)) ≤
      (1 + baseLogConstant ^ (1 - (Parameters.epsilon : ℝ))) *
        (1 + ((t : ℝ) / Real.log ((H : ℝ) / B)) ^ (1 - (Parameters.epsilon : ℝ))) := by
  let a := Real.log ((H : ℝ) / B)
  let b : ℝ := chosenBase H B
  let τ : ℝ := 1 - (Parameters.epsilon : ℝ)
  have ha : 0 < a := lt_of_lt_of_le (by norm_num) (normalized_log_one reserve H B hB hnormal)
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast (chosenBase_bounds reserve H B hnormal).1
  have ht : 0 ≤ τ := by
    have he : (Parameters.epsilon : ℝ) < 1 := by exact_mod_cast Parameters.epsilon_lt_one
    dsimp [τ]
    linarith
  have hab : a ≤ baseLogConstant*b := log_ratio_le_base reserve H B hB hnormal
  have hd : (t : ℝ)/b ≤ baseLogConstant*((t : ℝ)/a) := by
    apply (div_le_iff₀ hb).2
    rw [show baseLogConstant*((t : ℝ)/a)*b = (baseLogConstant*t*b)/a by ring]
    apply (le_div_iff₀ ha).2
    have hm := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg t : (0 : ℝ)≤t)
    nlinarith only [hm]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (t : ℝ)/b) hd ht
  rw [Real.mul_rpow baseLogConstant_nonneg (by positivity)] at hp
  have hx : 0 ≤ ((t : ℝ)/a)^τ := Real.rpow_nonneg (by positivity) _
  have hc : 0 ≤ baseLogConstant^τ := Real.rpow_nonneg baseLogConstant_nonneg _
  change 1+((t : ℝ)/b)^τ ≤ (1+baseLogConstant^τ)*(1+((t : ℝ)/a)^τ)
  nlinarith only [hp,hx,hc]

theorem exchange_cost_log_bound (reserve H B w r t : ℕ)
    (hreserve : 0 < reserve) (hB : 0 < B) (hw : 0 < w) (hr : 0 < r)
    (hnormal : PhysicalLeafParameters.minimumRatio radix reserve Parameters.W ≤ H/B) :
    ((exchangeCost reserve H B w r t ((2^t)^4) * B : ℕ) : ℝ) ≤
      rateConstant r *
        (1 + ((t : ℝ) / Real.log ((H : ℝ) / B)) ^ (1 - (Parameters.epsilon : ℝ))) *
          (((2^t)^4+B : ℕ) : ℝ) := by
  have hp := exchange_cost_physical_bound reserve H B w r t ((2^t)^4)
    hreserve hB hw hr hnormal
  have hs := scan_record_words B w r ((2^t)^4) hB hw hr
  have hf := factor_log_bound reserve H B t hB hnormal
  have hfac : 0 ≤ 1+((t : ℝ)/chosenBase H B)^(1-(Parameters.epsilon : ℝ)) := by positivity
  have hsR : 0 ≤ (r : ℝ)*(((2^t)^4 : ℕ)+B) := by positivity
  have hm := mul_le_mul hs hf hfac hsR
  have hm' := mul_le_mul_of_nonneg_left hm binaryConstant_nonneg
  have hp' := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg B : (0 : ℝ)≤B)
  push_cast at hp' hm' ⊢
  unfold rateConstant
  nlinarith only [hp',hm']

theorem actual_shape_rate (reserve H B w r : ℕ)
    (hreserve : 0 < reserve) (hB : 0 < B) (hw : 0 < w) (hr : 0 < r)
    (hnormal : PhysicalLeafParameters.minimumRatio radix reserve Parameters.W ≤ H/B) :
    ActualShapeRate B H (rateConstant r) (Real.log ((H : ℝ)/B))
      (1-(Parameters.epsilon : ℝ)) (exchangeCost reserve H B w r) := by
  intro n _ _
  simpa only [sizeChoice] using exchange_cost_log_bound reserve H B w r (sizeExponent n)
    hreserve hB hw hr hnormal

end
end CodedSorting.SortingExchangeBound
end SortingExchangeBound

section PhysicalSortingExchangeCost
/-! The six executed scalar swaps consume the same concrete charge that
the local Columnsort trace uses. This connects an actual returned cost to
the trace annotation; it does not identify a worst-case charge with an
input's exact I/O count. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalSortingExchangeCost
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalExchangeRecursion
open PhysicalSortingExchangeLayout PhysicalSortingExchange PhysicalLocalSortTranspose
open ColumnsortExchange SortingExchangeBound NormalizedPhysicalExchange
noncomputable section

theorem stageBound_le_exchangeCost (reserve H B w r t V : ℕ) (j : Swap) :
    stageBound (chosenBase H B) (cutoff reserve H w) (B*w) t (r*w) j ≤
      exchangeCost reserve H B w r t V := by
  cases j
  · exact Nat.le_max_left _ _
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

theorem forward_charge_le (reserve H B w r t V : ℕ) :
    charge (chosenBase H B) (cutoff reserve H w) (B*w) t (r*w) forwardSwaps ≤
      3*exchangeCost reserve H B w r t V := by
  have h1 := stageBound_le_exchangeCost reserve H B w r t V .last
  have h2 := stageBound_le_exchangeCost reserve H B w r t V .middle
  have h3 := stageBound_le_exchangeCost reserve H B w r t V .first
  simp only [charge,forwardSwaps,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem backward_charge_le (reserve H B w r t V : ℕ) :
    charge (chosenBase H B) (cutoff reserve H w) (B*w) t (r*w) backwardSwaps ≤
      3*exchangeCost reserve H B w r t V := by
  have h1 := stageBound_le_exchangeCost reserve H B w r t V .last
  have h2 := stageBound_le_exchangeCost reserve H B w r t V .middle
  have h3 := stageBound_le_exchangeCost reserve H B w r t V .first
  simp only [charge,backwardSwaps,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- One actual forward/batch/backward run, including all six exchanges,
is covered by exactly the six-exchange term in `LocalSortingCost.traceCost`.
`r=3` represents complete key/payload/tag records of word width `w`. -/
theorem six_swaps_actual_cost (reserve H B w r t : ℕ)
    (hreserve : 0 < reserve) (hB : 0 < B) (hw : 0 < w) (hr : 0 < r)
    (hnormal : PhysicalLeafParameters.minimumRatio radix reserve Parameters.W ≤ H/B)
    (one : Fin (2^t) → Fin ((2^t)^2*(2^t)*1) → Fin (r*w) → Bit)
    (batch : File → Option Result) (mid : Result) (two : RecordAddress (2^t) (r*w) → Bit)
    (hbatch : batch (represented (recordLayout (2^t) (r*w)) (B*w) (Nat.mul_pos hB hw)
      (secondValues (2^t) (r*w) one))=some mid)
    (hmid : mid.1=represented (recordLayout (2^t) (r*w)) (B*w) (Nat.mul_pos hB hw) two) :
    ∃ out,
      aroundBatch (chosenBase H B) (cutoff reserve H w) (B*w) (Nat.mul_pos hB hw)
        t (r*w) batch (represented (recordLayout (2^t) (r*w)) (B*w) (Nat.mul_pos hB hw)
          (firstValues (2^t) (r*w) one))=some out ∧
      out.1=represented (recordLayout (2^t) (r*w)) (B*w) (Nat.mul_pos hB hw)
        (transport (forwardRecord (2^t) (Fin (r*w))).symm two) ∧
      out.2≤6*exchangeCost reserve H B w r t ((2^t)^4)+mid.2 := by
  have hb := (chosenBase_bounds reserve H B hnormal).1
  have hs := (chosenBase_startup reserve H B w hreserve hnormal).trans (Nat.le_add_right _ (B*w))
  obtain ⟨out,ho,hf,hc⟩ := aroundBatch_correct (chosenBase H B) (cutoff reserve H w)
    (B*w) (Nat.mul_pos hB hw) hb hs t (r*w) (Nat.mul_pos hr hw) one batch mid two hbatch hmid
  have h1 := forward_charge_le reserve H B w r t ((2^t)^4)
  have h2 := backward_charge_le reserve H B w r t ((2^t)^4)
  exact ⟨out,ho,hf,by omega⟩

end
end CodedSorting.PhysicalSortingExchangeCost
end PhysicalSortingExchangeCost
