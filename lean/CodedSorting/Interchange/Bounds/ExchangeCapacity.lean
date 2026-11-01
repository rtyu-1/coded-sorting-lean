import CodedSorting.Interchange.Binary.Machine
import CodedSorting.Interchange.Recursion.Resources
import Mathlib.Algebra.Order.Floor.Ring

/-! A fixed integer program-counter bound for binary Construction exchange.
The sharper real I/O estimate implies a coarse quadratic capacity bound.
The original machine size N is unchanged. The width premise is explicit;
it can be derived from a nonempty counted input, but never from an empty
prefix. Empty public inputs may instead use an identity program. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.ExchangeCapacity

open ExchangeSpecialization CommonChunkLayout

noncomputable section

attribute [local irreducible] ExchangeSpecialization.uniform TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs MachineNetworkActualEdges.localCoefficient

local notation "K" => BinaryCost.binaryConstant 24 27 (6*(2*radix+6))

/-- Four accounts for both rounded-scan and width-factor envelopes. -/
def pcCoefficient : Nat := 4*⌈K⌉₊

theorem scan_le (b V N : Nat) (hb : 0 < b) (hscan : V/b ≤ N) :
    ArbitraryCost.scan b V ≤ 2*((N : ℝ)+1) := by
  have hn : V < b*(N+1) := (Nat.lt_mul_div_succ V hb).trans_le
    (Nat.mul_le_mul_left b (Nat.add_le_add_right hscan 1))
  have hr : (V : ℝ) < (b : ℝ)*((N : ℝ)+1) := by exact_mod_cast hn
  have hd : (V : ℝ)/b < (N : ℝ)+1 :=
    (div_lt_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).2
      (by simpa only [mul_comm] using hr)
  unfold ArbitraryCost.scan
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

theorem width_factor_le (base u N : Nat) (hbase : 0 < base) (hu : u ≤ N) :
    1+((u : ℝ)/base)^(1-(Construction.epsilon : ℝ)) ≤ 2*((N : ℝ)+1) := by
  have ht0 : 0 ≤ 1-(Construction.epsilon : ℝ) := ArbitraryCost.tau_pos.le
  have ht1 : 1-(Construction.epsilon : ℝ) ≤ 1 := by
    have he : (0 : ℝ) < (Construction.epsilon : ℝ) := by exact_mod_cast Construction.epsilon_pos
    linarith
  have hx0 : (0 : ℝ) ≤ (u : ℝ)/base := by positivity
  have hx : (u : ℝ)/base ≤ u :=
    div_le_self (Nat.cast_nonneg u)
      (by exact_mod_cast (show 1 ≤ base by omega) : (1 : ℝ) ≤ base)
  have hp : ((u : ℝ)/base)^(1-(Construction.epsilon : ℝ)) ≤ (u : ℝ)+1 := by
    by_cases hsmall : (u : ℝ)/base ≤ 1
    · have h := Real.rpow_le_one hx0 hsmall ht0
      have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
      linarith
    · have h := Real.rpow_le_rpow_of_exponent_le (lt_of_not_ge hsmall).le ht1
      rw [Real.rpow_one] at h
      linarith
  have huR : (u : ℝ) ≤ N := by exact_mod_cast hu
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-- A fixed natural coefficient bounds the complete numerical binary charge. -/
theorem bound_le_polynomial (base cutoff b P u G S N : Nat)
    (hb : 0 < b) (hbase : 0 < base) (hP : 0 < P) (hG : 0 < G) (hS : 0 < S)
    (hcut : streamCount*b ≤ cutoff)
    (hu : u ≤ N) (hscan : Volume P (2^u) G S/b ≤ N) :
    BinaryCost.bound base cutoff b P u G S 24 27 (6*(2*radix+6)) ≤
      pcCoefficient*(N+1)^2 := by
  have hc := BinaryCost.bound_improved base cutoff b P u G S 24 27
    (6*(2*radix+6)) hb hbase hP hG hS hcut
  have hs := scan_le b (Volume P (2^u) G S) N hb hscan
  have hf := width_factor_le base u N hbase hu
  have hK := BinaryCost.binaryConstant_nonneg 24 27 (6*(2*radix+6))
  have hk : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
  have hm := mul_le_mul hs hf
    (by positivity : (0 : ℝ) ≤ 1+((u : ℝ)/base)^(1-(Construction.epsilon : ℝ)))
    (by positivity : (0 : ℝ) ≤ 2*((N : ℝ)+1))
  have hcost : (BinaryCost.bound base cutoff b P u G S 24 27 (6*(2*radix+6)) : ℝ) ≤
      (pcCoefficient : ℝ)*((N : ℝ)+1)^2 := by
    calc
      _ ≤ K*ArbitraryCost.scan b (Volume P (2^u) G S)*
          (1+((u : ℝ)/base)^(1-(Construction.epsilon : ℝ))) := hc
      _ ≤ K*((2*((N : ℝ)+1))*(2*((N : ℝ)+1))) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm hK
      _ ≤ (⌈K⌉₊ : ℝ)*((2*((N : ℝ)+1))*(2*((N : ℝ)+1))) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = _ := by unfold pcCoefficient; push_cast; ring
  exact_mod_cast hcost

def pcExponent : Nat := 2+Nat.clog 2 (pcCoefficient*2^2)

theorem pcExponent_ge_two : 2 ≤ pcExponent := by unfold pcExponent; omega

theorem bound_fits (base cutoff b P u G S N E : Nat)
    (hb : 0 < b) (hbase : 0 < base) (hP : 0 < P) (hG : 0 < G) (hS : 0 < S)
    (hcut : streamCount*b ≤ cutoff) (hN : 2 ≤ N)
    (hu : u ≤ N) (hscan : Volume P (2^u) G S/b ≤ N) (hE : pcExponent ≤ E) :
    BinaryCost.bound base cutoff b P u G S 24 27 (6*(2*radix+6)) ≤ N^E :=
  (bound_le_polynomial base cutoff b P u G S N hb hbase hP hG hS hcut hu hscan).trans
    (RecursiveCapacity.absorb N pcCoefficient 2 E hN hE)

private theorem nat_le_two_pow (u : Nat) : u ≤ 2^u := by
  induction u with
  | zero => exact Nat.zero_le _
  | succ u ih =>
    have hp : 0 < (2 : Nat)^u := pow_pos (by decide) _
    rw [pow_succ]
    omega

/-- The width bound follows from the original word count only for a
nonempty prefix and positive spectators. -/
theorem input_width_le (P u G S N : Nat) (hP : 0 < P) (hG : 0 < G) (hS : 0 < S)
    (hwords : Volume P (2^u) G S ≤ N) : u ≤ N := by
  have hu := nat_le_two_pow u
  have hQ : 0 < (2 : Nat)^u := pow_pos (by decide) _
  have hv : 2^u ≤ Volume P (2^u) G S :=
    (Nat.le_mul_of_pos_right _ hG).trans
      ((Nat.le_mul_of_pos_left _ hP).trans
        (Nat.le_mul_of_pos_right _ (Nat.mul_pos hQ hS)))
  exact hu.trans (hv.trans hwords)

end
end CodedSorting.Construction.ExchangeCapacity
