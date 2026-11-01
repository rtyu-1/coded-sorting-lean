import CodedSorting.Interchange.Binary.Machine
import CodedSorting.Interchange.Recursion.Resources

/-! Linear disk space for the actual arbitrary-width and binary wrappers.
Sequential chunks share one recursive reserve. Borrowing preserves volume,
prefix padding grows it by at most two (including an empty prefix), and
binary padding grows it by at most the square of the fixed Construction prime.
All capacities below use the original common-machine input parameter N. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.ExchangeSpace

open CommonSortingNormalization CommonPermutationPairs CommonChunkLayout
open ExchangeSpecialization ArbitraryCalls ArbitrarySchedule

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs ExchangeSpecialization.uniform

local notation "files" => (MachineNetworkAdapter.physicalInputs +
  MachineNetworkAdapter.nodes TensorFrameNetwork.program
    (inputs := MachineNetworkAdapter.physicalInputs))

/-- Scaling volume scales the rounded-up scan envelope without a depth term. -/
theorem scan_scale (b a V U : Nat) (hb : 0 < b) (ha : 0 < a) (hU : U ≤ a*V) :
    U/b+1 ≤ a*(V/b+1) := by
  apply Nat.succ_le_of_lt
  apply (Nat.div_lt_iff_lt_mul hb).2
  calc
    U ≤ a*V := hU
    _ < a*(b*(V/b+1)) := Nat.mul_lt_mul_of_pos_left (Nat.lt_mul_div_succ V hb) ha
    _ = (a*(V/b+1))*b := by ring

theorem prefix_volume_scale (a P P' Q G S : Nat) (hP : P' ≤ a*P) :
    Volume P' Q G S ≤ a*Volume P Q G S := by
  change P'*(Q*G)*(Q*S) ≤ a*(P*(Q*G)*(Q*S))
  calc
    _ ≤ (a*P)*(Q*G)*(Q*S) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hP)
    _ = _ := by ring

/-- The binary volume estimate also covers zero prefix or spectator counts. -/
theorem binary_volume (P u G S : Nat) :
    Volume P (radix^(BinaryPadding.exponent radix u)) G S ≤
      radix^2 * Volume P (2^u) G S := by
  have h := (BinaryPadding.binary_range_growth radix u radix_prime.one_lt).le
  have hm := Nat.mul_le_mul
    (Nat.mul_le_mul_left P (Nat.mul_le_mul_right G h))
    (Nat.mul_le_mul_right S h)
  change P*(radix^(BinaryPadding.exponent radix u)*G)*
      (radix^(BinaryPadding.exponent radix u)*S) ≤ _
  exact hm.trans_eq (by ring)

private theorem linear_arithmetic (F s : Nat) :
    (F+3)*(s+1)+3 ≤ (F+6)*(s+1) := by
  nlinarith

private theorem borrowed_arithmetic (F s t C C' : Nat)
    (hC : C ≤ s+1) (hC' : C' ≤ t+1) (hs : t+1 ≤ 2*(s+1)) :
    C+(C'+C'+((F+3)*(t+1)+3)) ≤ (2*F+14)*(s+1) := by
  have hm := Nat.mul_le_mul_left (F+3) hs
  nlinarith

private theorem binary_arithmetic (F a s t C A : Nat)
    (hA : A ≤ (2*F+14)*(t+1)) (hC : C ≤ t+1) (hs : t+1 ≤ a*(s+1)) :
    2*C+A ≤ (a*(2*F+16))*(s+1) := by
  have hm := Nat.mul_le_mul_left (2*F+16) hs
  nlinarith

theorem linear_reserve (q : Configuration) (V : Nat) :
    RecursiveWorkspaceProgram.linearReserve q V ≤ (files+6)*(V/width q+1) :=
  linear_arithmetic files (V/width q)

theorem borrowed (q : Configuration) (cutoff : Nat) (cs : List ArbitraryCalls.Call)
    (P ρ P' G S : Nat) (hG : 0 < G) (hS : 0 < S)
    (hc : ChunkExchange.Conditions q cutoff cs P')
    (hV : Volume P' (fieldCount cs) G (S*q.w) ≤
      2*Volume P (radix^ρ*fieldCount cs) G (S*q.w)) :
    BorrowedChunks.space q cutoff cs P ρ P' G S hG hS hc ≤
      (2*files+14)*(Volume P (radix^ρ*fieldCount cs) G (S*q.w)/width q+1) := by
  have hs := scan_scale (width q) 2
    (Volume P (radix^ρ*fieldCount cs) G (S*q.w))
    (Volume P' (fieldCount cs) G (S*q.w)) (width_pos q) (by decide) hV
  have hC : count q (Volume P (radix^ρ*fieldCount cs) G (S*q.w)) ≤
      Volume P (radix^ρ*fieldCount cs) G (S*q.w)/width q+1 :=
    CommonResidentBase.count_le_floor q _
  have hC' : count q (Volume P' (fieldCount cs) G (S*q.w)) ≤
      Volume P' (fieldCount cs) G (S*q.w)/width q+1 :=
    CommonResidentBase.count_le_floor q _
  exact borrowed_arithmetic files _ _ _ _ hC hC' hs

theorem arbitrary (q : Configuration) (base cutoff P e G S : Nat)
    (hb : 0 < base) (hG : 0 < G) (hS : 0 < S)
    (hresident : cutoff ≤ CommonExchangeLeaf.bankBits q) (hblock : width q ≤ cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block ≤ CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q ≤ cutoff+width q) :
    ArbitraryMachine.space q base cutoff P e G S hb hG hS hresident hblock hfit hstartup ≤
      (2*files+14)*(Volume P (radix^e) G (S*q.w)/width q+1) := by
  let k := depth ambientDimension base e
  let ρ := borrowedWidth radix streamCount k
  by_cases hborrow : ρ < e
  · let cs := calls base k (e-ρ)
    let P' := paddedRows (highRows P ρ) k
    let hc := ArbitraryConditions.paddedConditions q cutoff base k (e-ρ)
      (highRows P ρ) hb hresident hblock hfit hstartup
    have hfield : radix^ρ*fieldCount cs = radix^e := borrowed_fields base e k ρ hborrow.le
    have hvol : Volume P' (fieldCount cs) G (S*q.w) ≤
        2*Volume P (radix^ρ*fieldCount cs) G (S*q.w) := by
      have h := prefix_volume_scale 2 (highRows P ρ) P' (fieldCount cs) G (S*q.w)
        (generated_padding_le_twice P k)
      simpa only [highRows, ← BorrowedChunks.borrowed_volume] using h
    have h := borrowed q cutoff cs P ρ P' G S hG hS hc hvol
    rw [hfield] at h
    simpa only [ArbitraryMachine.space,
      show borrowedWidth radix streamCount (depth ambientDimension base e) < e from hborrow,
      if_pos, k, ρ, cs, P', hc, highRows] using h
  · have h := linear_reserve q (Volume P (radix^e) G (S*q.w))
    have hm : (files+6)*(Volume P (radix^e) G (S*q.w)/width q+1) ≤
        (2*files+14)*(Volume P (radix^e) G (S*q.w)/width q+1) :=
      Nat.mul_le_mul_right _ (by omega)
    simpa only [ArbitraryMachine.space,
      show ¬borrowedWidth radix streamCount (depth ambientDimension base e) < e from hborrow,
      if_neg, ChunkExchange.space, base_fields] using h.trans hm

/-- Preserve a fixed natural value without evaluating a closed network when
the kernel compares coefficient aliases. Its specification is an equality,
not an additional bound or assumption. -/
private def fixedNat (n : Nat) : Nat :=
  Classical.choose (show ∃ m : Nat, m = n from ⟨n, rfl⟩)

private theorem fixedNat_eq (n : Nat) : fixedNat n = n :=
  Classical.choose_spec (show ∃ m : Nat, m = n from ⟨n, rfl⟩)

/-- One fixed natural coefficient, independent of width, depth and machine size. -/
def spaceCoefficient : Nat := fixedNat (radix^2*(2*files+16))

theorem spaceCoefficient_eq : spaceCoefficient = radix^2*(2*files+16) :=
  fixedNat_eq _

attribute [local irreducible] spaceCoefficient

theorem binary (q : Configuration) (base cutoff P u G S : Nat)
    (hb : 0 < base) (hG : 0 < G) (hS : 0 < S)
    (hresident : cutoff ≤ CommonExchangeLeaf.bankBits q) (hblock : width q ≤ cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block ≤ CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q ≤ cutoff+width q) :
    BinaryMachine.space q base cutoff P u G S hb hG hS hresident hblock hfit hstartup ≤
      spaceCoefficient*(Volume P (2^u) G (S*q.w)/width q+1) := by
  rw [spaceCoefficient_eq, BinaryMachine.space]
  have h := arbitrary q base cutoff P (BinaryPadding.exponent radix u) G S
    hb hG hS hresident hblock hfit hstartup
  have hC : count q (Volume P (radix^(BinaryPadding.exponent radix u)) G (S*q.w)) ≤
      Volume P (radix^(BinaryPadding.exponent radix u)) G (S*q.w)/width q+1 :=
    CommonResidentBase.count_le_floor q _
  have hs := scan_scale (width q) (radix^2)
    (Volume P (2^u) G (S*q.w))
    (Volume P (radix^(BinaryPadding.exponent radix u)) G (S*q.w))
    (width_pos q) (pow_pos radix_prime.pos _) (binary_volume P u G (S*q.w))
  exact binary_arithmetic files (radix^2) _ _ _ _ h hC hs

/-- Counting original words bounds their original-volume scan on this machine. -/
theorem word_scan_le (q : Configuration) (P Q G S : Nat)
    (hwords : Volume P Q G S ≤ q.N) : Volume P Q G (S*q.w)/width q ≤ q.N := by
  have hw : q.w ≤ width q := by
    have hb : 1 ≤ q.block := CommonLeafProgram.block_positive q
    exact (Nat.one_mul q.w).symm.trans_le (Nat.mul_le_mul_right q.w hb)
  have hv : Volume P Q G (S*q.w) = Volume P Q G S*q.w := by
    change P*(Q*G)*(Q*(S*q.w)) = (P*(Q*G)*(Q*S))*q.w
    ring
  apply Nat.div_le_of_le_mul
  rw [hv]
  simpa only [Nat.mul_comm q.N (width q)] using Nat.mul_le_mul hwords hw

theorem root_allocation (q : Configuration) (base cutoff P u G S : Nat)
    (hb : 0 < base) (hG : 0 < G) (hS : 0 < S)
    (hresident : cutoff ≤ CommonExchangeLeaf.bankBits q) (hblock : width q ≤ cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block ≤ CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q ≤ cutoff+width q)
    (hwords : Volume P (2^u) G S ≤ q.N) :
    count q (Volume P (2^u) G (S*q.w))+
      BinaryMachine.space q base cutoff P u G S hb hG hS hresident hblock hfit hstartup ≤
        (spaceCoefficient+1)*(q.N+1) := by
  have hs := word_scan_le q P (2^u) G S hwords
  have hC : count q (Volume P (2^u) G (S*q.w)) ≤
      Volume P (2^u) G (S*q.w)/width q+1 := CommonResidentBase.count_le_floor q _
  have h := binary q base cutoff P u G S hb hG hS hresident hblock hfit hstartup
  have hm := Nat.mul_le_mul_left spaceCoefficient (Nat.add_le_add_right hs 1)
  nlinarith only [h, hC, hs, hm]

def diskExponent : Nat := 1+Nat.clog 2 ((spaceCoefficient+1)*2)

theorem root_allocation_fits (q : Configuration) (base cutoff P u G S : Nat)
    (hb : 0 < base) (hG : 0 < G) (hS : 0 < S)
    (hresident : cutoff ≤ CommonExchangeLeaf.bankBits q) (hblock : width q ≤ cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block ≤ CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q ≤ cutoff+width q)
    (hwords : Volume P (2^u) G S ≤ q.N) (hexponent : diskExponent ≤ q.exponent) :
    count q (Volume P (2^u) G (S*q.w))+
      BinaryMachine.space q base cutoff P u G S hb hG hS hresident hblock hfit hstartup ≤
        q.N^q.exponent := by
  apply (root_allocation q base cutoff P u G S hb hG hS hresident hblock hfit hstartup hwords).trans
  simpa only [pow_one] using RecursiveCapacity.absorb q.N (spaceCoefficient+1) 1 q.exponent
    q.input_large (by simpa only [diskExponent, pow_one] using hexponent)

end
end CodedSorting.Construction.ExchangeSpace
