import CodedSorting.Interchange.Framework.Chunks.Exchange

/-! Uniform arithmetic envelope for arbitrary-width common-machine code.
Padding and borrowing are charged by explicit numerical coefficients;
the execution module must supply its actual instruction-cost inequality.
No execution or correctness assumption appears in these arithmetic results.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonArbitraryCost
open Circuit RecursiveExchange ArbitrarySchedule BinaryPadding
open PhysicalChunkExchange PhysicalChunkBound PhysicalArbitraryBound
noncomputable section

def overheadBound (cutoff b : ℕ) (cs : List ArbitraryRecursive.Call)
    (V V' ρ A D F : ℕ) : ℕ :=
  CommonChunkCost.totalBound cutoff b cs V'+A*(V/b+1)+D*(V'/b+1)+F*ρ*(V/b+1)

def borrowCoefficient (A D F : ℕ) : ℝ :=
  2*CommonRecursiveExchange.Pruned.boundConstant*Parameters.m+A+2*D+F*borrowing

theorem borrowCoefficient_nonneg (A D F : ℕ) : 0≤borrowCoefficient A D F := by
  unfold borrowCoefficient
  have := CommonRecursiveExchange.Pruned.boundConstant_nonneg
  have := borrowing_nonneg
  positivity

/-- Any fixed number of scans of the original and padded files, together
with linearly many borrowing scans, retains the geometric chunk bound. -/
theorem overhead_bound (cutoff b V V' base k e A D F : ℕ) (hb : 0<b)
    (hcut : Parameters.W*b≤cutoff) (he : e/base<Parameters.m^(k+1)) (hv : V'≤2*V) :
    (overheadBound cutoff b (ArbitraryRecursive.calls base k e) V V'
        (borrowedWidth radix Parameters.W k) A D F : ℝ)≤
      borrowCoefficient A D F*scan b V*geometric ratio k := by
  have hs := scan_double b V V' hv
  have hg := geometric_one k
  have hg0 : 0≤geometric ratio k := by linarith
  have hsc := scan_nonneg b V
  have hchunk := CommonChunkCost.calls_totalBound cutoff b V' base k e hb hcut he
  change (CommonChunkCost.totalBound cutoff b (ArbitraryRecursive.calls base k e) V' : ℝ)≤
    CommonRecursiveExchange.Pruned.boundConstant*scan b V'*Parameters.m*geometric ratio k at hchunk
  have hchunk' : (CommonChunkCost.totalBound cutoff b (ArbitraryRecursive.calls base k e) V' : ℝ)≤
      (2*CommonRecursiveExchange.Pruned.boundConstant*Parameters.m)*scan b V*geometric ratio k := by
    have hm := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (mul_nonneg CommonRecursiveExchange.Pruned.boundConstant_nonneg
        (Nat.cast_nonneg Parameters.m)) hg0)
    nlinarith only [hchunk,hm]
  have hvscan := nat_scan_le b V
  have hv'scan := (nat_scan_le b V').trans hs
  have hA : ((A*(V/b+1) : ℕ) : ℝ)≤A*scan b V*geometric ratio k := by
    have h1 := mul_le_mul_of_nonneg_left hvscan (Nat.cast_nonneg A : (0 : ℝ)≤A)
    have h2 := mul_le_mul_of_nonneg_left hg (mul_nonneg (Nat.cast_nonneg A) hsc)
    push_cast at h1 ⊢
    nlinarith only [h1,h2]
  have hD : ((D*(V'/b+1) : ℕ) : ℝ)≤(2*D)*scan b V*geometric ratio k := by
    have h1 := mul_le_mul_of_nonneg_left hv'scan (Nat.cast_nonneg D : (0 : ℝ)≤D)
    have h2 := mul_le_mul_of_nonneg_left hg
      (by positivity : (0 : ℝ)≤(2*D)*scan b V)
    push_cast at h1 ⊢
    nlinarith only [h1,h2]
  have hprod := mul_le_mul (rho_bound k) hvscan
    (by positivity : (0 : ℝ)≤(V/b+1 : ℕ)) (mul_nonneg borrowing_nonneg hg0)
  have hF : ((F*borrowedWidth radix Parameters.W k*(V/b+1) : ℕ) : ℝ)≤
      (F*borrowing)*scan b V*geometric ratio k := by
    have hm := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg F : (0 : ℝ)≤F)
    push_cast at hm ⊢
    nlinarith only [hm]
  unfold overheadBound borrowCoefficient
  push_cast at hA hD hF ⊢
  nlinarith only [hchunk',hA,hD,hF]

/-- The coefficients used by the actual wrapper: two borrowing programs,
and insertion/erasure with their charged reads, writes, and startup costs. -/
theorem assembled_overhead_le (q : CommonSortingNormalization.Configuration)
    (cutoff V V' ρ : ℕ) (cs : List ArbitraryRecursive.Call) :
    CommonChunkCost.totalBound cutoff (CommonPermutationPairs.width q) cs V'+
      2*((3*ρ*(2*radix+6)+6)*CommonPermutationPairs.count q V)+
      (12*CommonPermutationPairs.count q V+27*CommonPermutationPairs.count q V')≤
    overheadBound cutoff (CommonPermutationPairs.width q) cs V V' ρ 24 27 (6*(2*radix+6)) := by
  have hV := CommonRecursiveExchange.Pruned.count_le_scan q V
  have hV' := CommonRecursiveExchange.Pruned.count_le_scan q V'
  have h1 := Nat.mul_le_mul_left (24+6*(2*radix+6)*ρ) hV
  have h2 := Nat.mul_le_mul_left 27 hV'
  unfold overheadBound
  nlinarith only [h1,h2]

def borrowedBound (cutoff b : ℕ) (cs : List ArbitraryRecursive.Call)
    (P ρ P' G S A D F : ℕ) : ℕ :=
  overheadBound cutoff b cs (BorrowScan.volume P (radix^ρ) (fieldCount cs) G S)
    (Volume P' (fieldCount cs) G S) ρ A D F

theorem borrowed_bound (cutoff b P base k e G S A D F : ℕ) (hb : 0<b) (hP : 0<P)
    (hcut : Parameters.W*b≤cutoff) (he : e/base<Parameters.m^(k+1)) :
    let ρ := borrowedWidth radix Parameters.W k
    let cs := ArbitraryRecursive.calls base k e
    let V := BorrowScan.volume P (radix^ρ) (fieldCount cs) G S
    let P' := ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k
    (borrowedBound cutoff b cs P ρ P' G S A D F : ℝ)≤
      borrowCoefficient A D F*scan b V*geometric ratio k := by
  dsimp only [borrowedBound]
  apply overhead_bound cutoff b _ _ base k e A D F hb hcut he
  exact padded_volume P k _ G S hP

def bound (base cutoff b P e G S A D F : ℕ) : ℕ :=
  let k := depth Parameters.m base e
  let ρ := borrowedWidth radix Parameters.W k
  if ρ<e then
    let cs := ArbitraryRecursive.calls base k (e-ρ)
    borrowedBound cutoff b cs P ρ
      (ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k) G S A D F
  else CommonChunkCost.totalBound cutoff b (ArbitraryRecursive.baseCalls base e)
    (Volume P (radix^e) G S)

def coefficient (A D F : ℕ) : ℝ := borrowCoefficient A D F+20*(borrowing+1)

theorem coefficient_nonneg (A D F : ℕ) : 0≤coefficient A D F := by
  unfold coefficient
  have := borrowCoefficient_nonneg A D F
  have := borrowing_nonneg
  positivity

theorem bound_geometric (base cutoff b P e G S A D F : ℕ) (hb : 0<b) (hP : 0<P)
    (hcut : Parameters.W*b≤cutoff) :
    (bound base cutoff b P e G S A D F : ℝ)≤
      coefficient A D F*scan b (Volume P (radix^e) G S)*
        geometric ratio (depth Parameters.m base e) := by
  let k := depth Parameters.m base e
  let ρ := borrowedWidth radix Parameters.W k
  let V := Volume P (radix^e) G S
  have hg0 : 0≤geometric ratio k := by have := geometric_one k; linarith
  by_cases hborrow : ρ<e
  · let cs := ArbitraryRecursive.calls base k (e-ρ)
    have hquot : (e-ρ)/base<Parameters.m^(k+1) :=
      (Nat.div_le_div_right (Nat.sub_le e ρ)).trans_lt
        (quotient_depth_bound Parameters.m base e (by norm_num [Parameters.m_value]))
    have hv : BorrowScan.volume P (radix^ρ) (fieldCount cs) G S=V := by
      rw [← PhysicalBorrowLayout.original_volume,fieldCount_width,ArbitraryRecursive.calls_width]
      have hp : radix^ρ*radix^(e-ρ)=radix^e := by rw [← pow_add]; congr 1; omega
      rw [hp]
    have hh := borrowed_bound cutoff b P base k (e-ρ) G S A D F hb hP hcut hquot
    change (borrowedBound cutoff b cs P ρ
      (ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k) G S A D F : ℝ)≤
        borrowCoefficient A D F*scan b (BorrowScan.volume P (radix^ρ) (fieldCount cs) G S)*
          geometric ratio k at hh
    rw [hv] at hh
    have hc : borrowCoefficient A D F≤coefficient A D F := by
      unfold coefficient
      have := borrowing_nonneg
      linarith
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (scan_nonneg b V)) hg0
    have hh' := hh.trans hm
    simpa only [bound,show borrowedWidth radix Parameters.W (depth Parameters.m base e)<e
      from hborrow,↓reduceIte] using hh'
  · have he : e≤ρ := by omega
    have hh := CommonChunkCost.fallback_bound cutoff b V base e k he
    have hc : 20*(borrowing+1)≤coefficient A D F := by
      unfold coefficient
      exact le_add_of_nonneg_left (borrowCoefficient_nonneg A D F)
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (scan_nonneg b V)) hg0
    have hh' := hh.trans hm
    simpa only [bound,show ¬borrowedWidth radix Parameters.W (depth Parameters.m base e)<e
      from hborrow,↓reduceIte] using hh'

def finalConstant (A D F : ℕ) : ℝ := coefficient A D F*(ratio/(ratio-1))

theorem finalConstant_nonneg (A D F : ℕ) : 0≤finalConstant A D F := by
  unfold finalConstant
  apply mul_nonneg (coefficient_nonneg A D F)
  have := ratio_gt_one
  apply div_nonneg <;> linarith

theorem bound_improved (base cutoff b P e G S A D F : ℕ) (hb : 0<b)
    (hbase : 0<base) (hP : 0<P) (hcut : Parameters.W*b≤cutoff) :
    (bound base cutoff b P e G S A D F : ℝ)≤
      finalConstant A D F*scan b (Volume P (radix^e) G S)*
        (1+((e : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) := by
  let V := Volume P (radix^e) G S
  let k := depth Parameters.m base e
  have hgeo := mul_le_mul_of_nonneg_left (geometric_power_bound ratio ratio_gt_one k)
    (mul_nonneg (coefficient_nonneg A D F) (scan_nonneg b V))
  have hfirst := (bound_geometric base cutoff b P e G S A D F hb hP hcut).trans hgeo
  have htau : 0≤1-(Parameters.epsilon : ℝ) := by
    have h : (Parameters.epsilon : ℝ)<1 := by exact_mod_cast Parameters.epsilon_lt_one
    linarith
  have hwidth := depth_power_width_bound Parameters.m base e hbase
    (1-(Parameters.epsilon : ℝ)) htau
  change ratio^k≤_ at hwidth
  have hsecond := mul_le_mul_of_nonneg_left hwidth
    (mul_nonneg (finalConstant_nonneg A D F) (scan_nonneg b V))
  unfold finalConstant at hfirst hsecond ⊢
  dsimp only [V,k] at hfirst hsecond
  nlinarith only [hfirst,hsecond]

end
end CodedSorting.CommonArbitraryCost
