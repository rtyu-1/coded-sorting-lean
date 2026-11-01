import CodedSorting.Interchange.Framework.Chunks.One

section PhysicalArbitraryExchange
/-! Complete file-level arbitrary-width address exchange, including the
small-width branch where borrowing would consume all available digits.
The runner only manipulates files via the proven scans and recursive calls.
The exact natural-number cost expression is connected to this same output.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.PhysicalArbitraryExchange
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalExchangeRecursion
open PhysicalChunkExchange BinaryPadding CoordinateScans
noncomputable section

def CorrectCost (P Q G S B : ℕ) (hB : 0 < B) (runner : File → Option Result) (C : ℕ) : Prop :=
  ∀ F : Addr P Q G S → Bit,
    ∃ out, runner (represented lowLayout B hB F) = some out ∧
      out.1 = represented lowLayout B hB (transport exchangeEquiv F) ∧ out.2 ≤ C

def execute (base cutoff B : ℕ) (hB : 0 < B) (P e G S : ℕ) (source : File) : Option Result :=
  let k := ArbitrarySchedule.depth Parameters.m base e
  let ρ := ArbitrarySchedule.borrowedWidth radix Parameters.W k
  if ρ < e then PhysicalBorrowedChunks.automatic base cutoff B hB P e G S source
  else PhysicalChunkExchange.execute cutoff B hB (ArbitraryRecursive.baseCalls base e) P G S source

def bound (base cutoff B P e G S : ℕ) : ℕ :=
  let k := ArbitrarySchedule.depth Parameters.m base e
  let ρ := ArbitrarySchedule.borrowedWidth radix Parameters.W k
  if ρ < e then
    PhysicalBorrowedChunks.bound cutoff B (ArbitraryRecursive.calls base k (e-ρ)) P ρ
      (ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k) G S
  else totalBound cutoff B (ArbitraryRecursive.baseCalls base e) (Volume P (radix^e) G S)

theorem baseCalls_startup (base cutoff B e : ℕ) (hb : 0 < base)
    (hstartup : (radix^base*radix^base)*B ≤ cutoff+B) :
    ∀ c ∈ ArbitraryRecursive.baseCalls base e,
      (radix^c.baseWidth*radix^c.baseWidth)*B ≤ cutoff+B := by
  intro c hc
  have hwidth : c.baseWidth ≤ base := by
    rcases List.mem_append.mp hc with h | h
    · have he : c=⟨base,0⟩ := (List.mem_replicate.mp h).2
      rw [he]
    · have he : c=⟨e%base,0⟩ := by simpa using h
      rw [he]
      exact (Nat.mod_lt e hb).le
  have hpow := Nat.pow_le_pow_right radix_prime.pos hwidth
  exact (Nat.mul_le_mul_right B (Nat.mul_le_mul hpow hpow)).trans hstartup

theorem baseCalls_fit (P base e : ℕ) :
    ∀ c ∈ ArbitraryRecursive.baseCalls base e, Parameters.W^c.depth ∣ P := by
  intro c hc
  obtain ⟨i,hi⟩ := List.get_of_mem hc
  rw [← hi]
  exact ArbitraryRecursive.baseCalls_fit P base e i

/-- Uniform in every nonnegative field width, including width zero.
All logical exchange contracts have been replaced by the actual file runner;
the remaining premises are the fixed numerical memory cutoff conditions.
-/
theorem execute_correct_cost (base cutoff B : ℕ) (hB : 0 < B) (hb : 0 < base)
    (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (P e G S : ℕ) (hG : 0 < G) (hS : 0 < S) :
    CorrectCost P (radix^e) G S B hB (execute base cutoff B hB P e G S)
      (bound base cutoff B P e G S) := by
  let k := ArbitrarySchedule.depth Parameters.m base e
  let ρ := ArbitrarySchedule.borrowedWidth radix Parameters.W k
  by_cases hborrow : ρ<e
  · let cs := ArbitraryRecursive.calls base k (e-ρ)
    have hfields : radix^ρ*fieldCount cs=radix^e := by
      rw [fieldCount_width,ArbitraryRecursive.calls_width,← pow_add]
      congr 1
      omega
    have hall : CorrectCost P (radix^ρ*fieldCount cs) G S B hB
        (PhysicalBorrowedChunks.automatic base cutoff B hB P e G S)
        (PhysicalBorrowedChunks.bound cutoff B cs P ρ
          (ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k) G S) := by
      intro F
      obtain ⟨out,hr,ho,hc⟩ := PhysicalBorrowedChunks.automatic_correct_cost base cutoff B hB hb
        hstartup P e G S hG hS (F ∘ PhysicalChunkLayout.productShape P (radix^ρ) (fieldCount cs) G S)
      rw [PhysicalBorrowLayout.original_input] at hr
      rw [PhysicalBorrowLayout.original_output] at ho
      exact ⟨out,hr,ho,hc⟩
    rw [hfields] at hall
    intro F
    simpa only [execute,bound,show ArbitrarySchedule.borrowedWidth radix Parameters.W
      (ArbitrarySchedule.depth Parameters.m base e) < e from hborrow,↓reduceIte] using hall F
  · have hfields : fieldCount (ArbitraryRecursive.baseCalls base e)=radix^e := by
      rw [fieldCount_width,ArbitraryRecursive.baseCalls_width]
    have hall : CorrectCost P (fieldCount (ArbitraryRecursive.baseCalls base e)) G S B hB
        (PhysicalChunkExchange.execute cutoff B hB (ArbitraryRecursive.baseCalls base e) P G S)
        (totalBound cutoff B (ArbitraryRecursive.baseCalls base e)
          (Volume P (fieldCount (ArbitraryRecursive.baseCalls base e)) G S)) := by
      exact PhysicalChunkExchange.execute_correct_cost cutoff B hB _ P G S hG hS
        (baseCalls_fit P base e) (baseCalls_startup base cutoff B e hb hstartup)
    rw [hfields] at hall
    intro F
    simpa only [execute,bound,show ¬ ArbitrarySchedule.borrowedWidth radix Parameters.W
      (ArbitrarySchedule.depth Parameters.m base e) < e from hborrow,↓reduceIte] using hall F

end
end CodedSorting.PhysicalArbitraryExchange
end PhysicalArbitraryExchange

section Conditions
/-! Discharge every chunk's numerical memory and prefix obligations from
one base-width choice. These are arithmetic conditions, not execution oracles. -/
set_option autoImplicit false
namespace CodedSorting.CommonArbitraryConditions
open CommonSortingNormalization CommonPermutationPairs
open CommonRecursiveExchange CommonChunkExchange RecursiveExchange Circuit
noncomputable section

theorem buckets_mono {a b : ℕ} (h : a≤b) : Pruned.buckets a≤Pruned.buckets b := by
  have hp := Nat.pow_le_pow_right radix_prime.pos h
  exact Nat.mul_le_mul hp hp

theorem baseCalls_base (base e : ℕ) (hb : 0<base) :
    ∀ c∈ArbitraryRecursive.baseCalls base e,c.baseWidth≤base := by
  intro c hc
  rcases List.mem_append.mp hc with hc|hc
  · have he : c=⟨base,0⟩ := (List.mem_replicate.mp hc).2
    rw [he]
  · have he : c=⟨e%base,0⟩ := by simpa using hc
    rw [he]
    exact (Nat.mod_lt e hb).le

def baseConditions (q : Configuration) (cutoff base e P : ℕ) (hb : 0<base)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : Pruned.buckets base*width q≤cutoff+width q) :
    Conditions q cutoff (ArbitraryRecursive.baseCalls base e) P where
  resident := hresident
  divisible := PhysicalArbitraryExchange.baseCalls_fit P base e
  buffers := fun c hc => (Nat.mul_le_mul_right q.block
    (buckets_mono (baseCalls_base base e hb c hc))).trans hfit
  startup := fun c hc => (Nat.mul_le_mul_right (width q)
    (buckets_mono (baseCalls_base base e hb c hc))).trans hstartup

def paddedConditions (q : Configuration) (cutoff base k e P : ℕ) (hb : 0<base)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : Pruned.buckets base*width q≤cutoff+width q) :
    Conditions q cutoff (ArbitraryRecursive.calls base k e)
      (ArbitraryRecursive.paddedRows P k) where
  resident := hresident
  divisible := PhysicalPaddedChunks.calls_fit P base k e
  buffers := fun c hc => (Nat.mul_le_mul_right q.block
    (buckets_mono (PhysicalPaddedChunks.calls_base base k e hb c hc))).trans hfit
  startup := fun c hc => (Nat.mul_le_mul_right (width q)
    (buckets_mono (PhysicalPaddedChunks.calls_base base k e hb c hc))).trans hstartup

end
end CodedSorting.CommonArbitraryConditions
end Conditions

section PhysicalArbitraryBound
/-! The full arbitrary-width file program retains the coding exponent.
The bound below includes both borrow scans, both prefix-padding scans,
every actual recursive chunk, and the no-borrow fallback branch.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace CodedSorting.PhysicalArbitraryBound
open Circuit RecursiveExchange ArbitrarySchedule PhysicalRecursionBound
open PhysicalChunkExchange PhysicalChunkBound BinaryPadding
noncomputable section

def scan (B V : ℕ) : ℝ := 1+(V : ℝ)/B
def borrowing : ℝ := borrowConstant radix Parameters.W
def borrowCoefficient : ℝ := 2*boundConstant*Parameters.m+6+2*borrowing*(2*radix+6)
def coefficient : ℝ := borrowCoefficient+12*(borrowing+1)

theorem scan_nonneg (B V : ℕ) : 0 ≤ scan B V := by unfold scan; positivity
theorem borrowing_nonneg : 0 ≤ borrowing := Nat.cast_nonneg _
theorem borrowCoefficient_nonneg : 0 ≤ borrowCoefficient := by
  unfold borrowCoefficient
  have := boundConstant_nonneg
  have := borrowing_nonneg
  positivity
theorem coefficient_nonneg : 0 ≤ coefficient := by
  unfold coefficient
  have := borrowCoefficient_nonneg
  have := borrowing_nonneg
  positivity

theorem nat_scan_le (B V : ℕ) : ((V/B+1 : ℕ) : ℝ) ≤ scan B V := by
  have hd : ((V/B : ℕ) : ℝ) ≤ (V : ℝ)/B := Nat.cast_div_le
  simp only [Nat.cast_add,Nat.cast_one,scan]
  linarith

theorem ceil_scan_le (B V : ℕ) (hB : 0 < B) : ((V+B-1)/B : ℕ) ≤ scan B V := by
  have hn : ((V+B-1)/B)*B ≤ V+B :=
    (Nat.div_mul_le_self (V+B-1) B).trans (Nat.sub_le _ _)
  have hnR : (((V+B-1)/B : ℕ) : ℝ)*B ≤ (V : ℝ)+B := by exact_mod_cast hn
  have hbR : (0 : ℝ)<B := by exact_mod_cast hB
  have he := div_mul_cancel₀ (V : ℝ) (ne_of_gt hbR)
  unfold scan
  nlinarith

theorem scan_double (B V V' : ℕ) (hv : V' ≤ 2*V) : scan B V' ≤ 2*scan B V := by
  have hr : (V' : ℝ) ≤ 2*V := by exact_mod_cast hv
  have hd := div_le_div_of_nonneg_right hr (Nat.cast_nonneg B : (0 : ℝ)≤B)
  unfold scan
  rw [mul_div_assoc] at hd
  linarith

theorem geometric_one (k : ℕ) : 1 ≤ geometric ratio k :=
  (show (1 : ℝ) ≤ (k+1 : ℕ) by exact_mod_cast (by omega : 1 ≤ k+1)).trans
    (depth_le_geometric ratio ratio_gt_one.le k)

theorem rho_bound (k : ℕ) :
    (borrowedWidth radix Parameters.W k : ℝ) ≤ borrowing*geometric ratio k := by
  have h := mul_le_mul_of_nonneg_left (depth_le_geometric ratio ratio_gt_one.le k)
    borrowing_nonneg
  simpa [borrowedWidth,borrowing] using h

theorem padded_volume (P k L G S : ℕ) (hP : 0 < P) :
    Volume (ArbitraryRecursive.paddedRows
      (P*((radix^(borrowedWidth radix Parameters.W k))*(radix^(borrowedWidth radix Parameters.W k)))) k)
      L G S ≤
        2*BorrowScan.volume P (radix^(borrowedWidth radix Parameters.W k)) L G S := by
  have hp := (ArbitraryRecursive.generated_padding_bound P k hP).le
  change ArbitraryRecursive.paddedRows
    (P*((radix^(borrowedWidth radix Parameters.W k))*(radix^(borrowedWidth radix Parameters.W k)))) k ≤
    2*(P*((radix^(borrowedWidth radix Parameters.W k))*(radix^(borrowedWidth radix Parameters.W k)))) at hp
  have hm := Nat.mul_le_mul_right ((L*G)*(L*S)) hp
  unfold Volume BorrowScan.volume
  nlinarith only [hm]

theorem borrowed_bound (cutoff B P base k e G S : ℕ) (hB : 0 < B) (hP : 0 < P)
    (hcut : Parameters.W*B ≤ cutoff) (he : e/base < Parameters.m^(k+1)) :
    let ρ := borrowedWidth radix Parameters.W k
    let cs := ArbitraryRecursive.calls base k e
    let V := BorrowScan.volume P (radix^ρ) (fieldCount cs) G S
    let P' := ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k
    (PhysicalBorrowedChunks.bound cutoff B cs P ρ P' G S : ℝ) ≤
      borrowCoefficient*scan B V*geometric ratio k := by
  dsimp only
  let ρ := borrowedWidth radix Parameters.W k
  let cs := ArbitraryRecursive.calls base k e
  let V := BorrowScan.volume P (radix^ρ) (fieldCount cs) G S
  let P' := ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k
  let V' := Volume P' (fieldCount cs) G S
  have hv : V'≤2*V := padded_volume P k (fieldCount cs) G S hP
  have hs := scan_double B V V' hv
  have hgeo := geometric_one k
  have hgeo0 : 0 ≤ geometric ratio k := by linarith
  have hscan := scan_nonneg B V
  have hchunk := calls_totalBound cutoff B V' base k e hB hcut he
  change (totalBound cutoff B cs V' : ℝ) ≤
    boundConstant*scan B V'*Parameters.m*geometric ratio k at hchunk
  have hchunk' : (totalBound cutoff B cs V' : ℝ) ≤
      (2*boundConstant*Parameters.m)*scan B V*geometric ratio k := by
    have hm := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (mul_nonneg boundConstant_nonneg (Nat.cast_nonneg Parameters.m)) hgeo0)
    nlinarith only [hchunk,hm]
  have hc1 := ceil_scan_le B V hB
  have hc2 := (ceil_scan_le B V' hB).trans hs
  have hpads : (2*(((V+B-1)/B)+((V'+B-1)/B)) : ℕ) ≤
      (6 : ℝ)*scan B V*geometric ratio k := by
    have hm := mul_le_mul_of_nonneg_left hgeo (by positivity : 0 ≤ 6*scan B V)
    push_cast
    nlinarith only [hc1,hc2,hm]
  have hρ : (ρ : ℝ) ≤ borrowing*geometric ratio k := rho_bound k
  have hnat := nat_scan_le B V
  have hprod := mul_le_mul hρ hnat (by positivity : (0 : ℝ) ≤ (V/B+1 : ℕ))
    (mul_nonneg borrowing_nonneg hgeo0)
  have hborrows : (2*(ρ*(2*radix+6)*(V/B+1)) : ℕ) ≤
      (2*borrowing*(2*radix+6))*scan B V*geometric ratio k := by
    have hm := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ)≤2*(2*radix+6))
    push_cast at hm ⊢
    nlinarith only [hm]
  change ((PhysicalBorrowedChunks.bound cutoff B cs P ρ P' G S : ℕ) : ℝ) ≤
    borrowCoefficient*scan B V*geometric ratio k
  unfold PhysicalBorrowedChunks.bound
  change ((totalBound cutoff B cs V'+2*((V+B-1)/B+(V'+B-1)/B)+
    2*(ρ*(2*radix+6)*(V/B+1)) : ℕ) : ℝ) ≤ _
  push_cast at hpads hborrows ⊢
  unfold borrowCoefficient
  nlinarith only [hchunk',hpads,hborrows]

theorem base_totalBound (cutoff B V base e : ℕ) :
    totalBound cutoff B (ArbitraryRecursive.baseCalls base e) V =
      (e/base+1)*(12*(V/B+1)) := by
  simp [totalBound,ArbitraryRecursive.baseCalls,PhysicalExchangeRecursion.costBound,
    List.sum_replicate,smul_eq_mul]
  ring

theorem fallback_bound (cutoff B V base e k : ℕ) (he : e ≤ borrowedWidth radix Parameters.W k) :
    (totalBound cutoff B (ArbitraryRecursive.baseCalls base e) V : ℝ) ≤
      (12*(borrowing+1))*scan B V*geometric ratio k := by
  have hdiv : e/base ≤ borrowedWidth radix Parameters.W k := (Nat.div_le_self _ _).trans he
  have hr : ((e/base : ℕ) : ℝ) ≤ borrowedWidth radix Parameters.W k := by exact_mod_cast hdiv
  have hρ := rho_bound k
  have hg := geometric_one k
  have hn : ((e/base+1 : ℕ) : ℝ) ≤ (borrowing+1)*geometric ratio k := by
    push_cast
    nlinarith
  have hm := mul_le_mul hn (nat_scan_le B V) (by positivity : (0 : ℝ)≤(V/B+1 : ℕ))
    (by have := borrowing_nonneg; have := geometric_nonneg ratio (by have := ratio_gt_one; linarith) k; positivity)
  rw [base_totalBound]
  push_cast at hm ⊢
  nlinarith only [hm]

theorem bound_geometric (base cutoff B P e G S : ℕ) (hB : 0 < B) (hP : 0 < P)
    (hcut : Parameters.W*B ≤ cutoff) :
    (PhysicalArbitraryExchange.bound base cutoff B P e G S : ℝ) ≤
      coefficient*scan B (Volume P (radix^e) G S)*
        geometric ratio (depth Parameters.m base e) := by
  let k := depth Parameters.m base e
  let ρ := borrowedWidth radix Parameters.W k
  let V := Volume P (radix^e) G S
  have hgeo0 : 0 ≤ geometric ratio k := by have := geometric_one k; linarith
  by_cases hborrow : ρ<e
  · let cs := ArbitraryRecursive.calls base k (e-ρ)
    have hquot : (e-ρ)/base < Parameters.m^(k+1) :=
      (Nat.div_le_div_right (Nat.sub_le e ρ)).trans_lt
        (quotient_depth_bound Parameters.m base e (by norm_num [Parameters.m_value]))
    have hv : BorrowScan.volume P (radix^ρ) (fieldCount cs) G S = V := by
      rw [← PhysicalBorrowLayout.original_volume,fieldCount_width,ArbitraryRecursive.calls_width]
      have hp : radix^ρ*radix^(e-ρ)=radix^e := by rw [← pow_add]; congr 1; omega
      rw [hp]
    have hh := borrowed_bound cutoff B P base k (e-ρ) G S hB hP hcut hquot
    change (PhysicalBorrowedChunks.bound cutoff B cs P ρ
      (ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k) G S : ℝ) ≤
        borrowCoefficient*scan B (BorrowScan.volume P (radix^ρ) (fieldCount cs) G S)*
          geometric ratio k at hh
    rw [hv] at hh
    have hc : borrowCoefficient ≤ coefficient := by
      unfold coefficient
      have := borrowing_nonneg
      linarith
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (scan_nonneg B V)) hgeo0
    have hh' := hh.trans hm
    simpa only [PhysicalArbitraryExchange.bound,
      show borrowedWidth radix Parameters.W (depth Parameters.m base e)<e from hborrow,↓reduceIte] using hh'
  · have he : e≤ρ := by omega
    have hh := fallback_bound cutoff B V base e k he
    have hc : 12*(borrowing+1)≤coefficient := by
      unfold coefficient
      exact le_add_of_nonneg_left borrowCoefficient_nonneg
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (scan_nonneg B V)) hgeo0
    have hh' := hh.trans hm
    simpa only [PhysicalArbitraryExchange.bound,
      show ¬ borrowedWidth radix Parameters.W (depth Parameters.m base e)<e from hborrow,↓reduceIte] using hh'

def finalConstant : ℝ := coefficient*(ratio/(ratio-1))

theorem finalConstant_nonneg : 0 ≤ finalConstant := by
  unfold finalConstant
  apply mul_nonneg coefficient_nonneg
  have := ratio_gt_one
  apply div_nonneg <;> linarith

theorem bound_improved (base cutoff B P e G S : ℕ) (hB : 0 < B)
    (hb : 0 < base) (hP : 0 < P) (hcut : Parameters.W*B ≤ cutoff) :
    (PhysicalArbitraryExchange.bound base cutoff B P e G S : ℝ) ≤
      finalConstant*scan B (Volume P (radix^e) G S)*
        (1+((e : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) := by
  let V := Volume P (radix^e) G S
  let k := depth Parameters.m base e
  have hgeo := mul_le_mul_of_nonneg_left (geometric_power_bound ratio ratio_gt_one k)
    (mul_nonneg coefficient_nonneg (scan_nonneg B V))
  have hfirst := (bound_geometric base cutoff B P e G S hB hP hcut).trans hgeo
  have htau : 0 ≤ 1-(Parameters.epsilon : ℝ) := by
    have h : (Parameters.epsilon : ℝ)<1 := by exact_mod_cast Parameters.epsilon_lt_one
    linarith
  have hwidth := depth_power_width_bound Parameters.m base e hb
    (1-(Parameters.epsilon : ℝ)) htau
  change ratio^k ≤ _ at hwidth
  have hsecond := mul_le_mul_of_nonneg_left hwidth
    (mul_nonneg finalConstant_nonneg (scan_nonneg B V))
  unfold finalConstant at hfirst hsecond ⊢
  dsimp only [V,k] at hfirst hsecond
  nlinarith only [hfirst,hsecond]

/-- Correct output and the final improved exponent refer to the same
successful actual file execution, for every width e and every P,G,S>0. -/
theorem actual_arbitrary_exchange_bound (base cutoff B : ℕ) (hB : 0 < B)
    (hb : 0 < base) (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (hcut : Parameters.W*B ≤ cutoff) (P e G S : ℕ) (hP : 0 < P) (hG : 0 < G) (hS : 0 < S)
    (F : Addr P (radix^e) G S → Bit) :
    ∃ out, PhysicalArbitraryExchange.execute base cutoff B hB P e G S
        (PhysicalRecursiveExchange.represented CoordinateScans.lowLayout B hB F) = some out ∧
      out.1 = PhysicalRecursiveExchange.represented CoordinateScans.lowLayout B hB
        (Address.transport Address.exchangeEquiv F) ∧
      (out.2 : ℝ) ≤ finalConstant*scan B (Volume P (radix^e) G S)*
        (1+((e : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) := by
  obtain ⟨out,hr,ho,hc⟩ := PhysicalArbitraryExchange.execute_correct_cost base cutoff B hB hb
    hstartup P e G S hG hS F
  exact ⟨out,hr,ho,(Nat.cast_le.mpr hc).trans
    (bound_improved base cutoff B P e G S hB hb hP hcut)⟩

end
end CodedSorting.PhysicalArbitraryBound
end PhysicalArbitraryBound

section PhysicalBinaryExchange
/-! Binary address fields are expanded to the smallest fitting fixed-prime
power, exchanged by the genuine arbitrary-width file program, and compacted.
Every scan and recursive call contributes to the same returned cost. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalBinaryExchange
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalExchangeRecursion
open BinaryPadding CoordinateScans
noncomputable section

def execute (base cutoff B : ℕ) (hB : 0 < B) (P u G S : ℕ) (source : File) : Option Result :=
  PhysicalPaddingExchange.padded P (2^u) (radix^(exponent radix u)) G S B
    (PhysicalArbitraryExchange.execute base cutoff B hB P (exponent radix u) G S) source

def bound (base cutoff B P u G S : ℕ) : ℕ :=
  PhysicalArbitraryExchange.bound base cutoff B P (exponent radix u) G S+
    2*((Volume P (2^u) G S+B-1)/B+(Volume P (radix^(exponent radix u)) G S+B-1)/B)

theorem execute_correct_cost (base cutoff B : ℕ) (hB : 0 < B) (hb : 0 < base)
    (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (P u G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (F : Fin (Volume P (2^u) G S) → Bit) :
    ∃ out, execute base cutoff B hB P u G S (canonical B hB F) = some out ∧
      out.1 = canonical B hB (PhysicalPaddingExchange.exchanged F) ∧
      out.2 ≤ bound base cutoff B P u G S := by
  have hf := binary_range_fits radix u radix_prime.one_lt
  let E := BinaryPaddingScan.expanded hf (0 : Bit) F
  obtain ⟨out,hr,ho,hc⟩ := PhysicalArbitraryExchange.execute_correct_cost base cutoff B hB hb
    hstartup P (exponent radix u) G S hG hS (E ∘ lowLayout)
  rw [PhysicalPaddedChunks.represented_numeric] at hr
  rw [PhysicalPaddedChunks.represented_exchanged] at ho
  let scans := 2*((Volume P (2^u) G S+B-1)/B+
    (Volume P (radix^(exponent radix u)) G S+B-1)/B)
  refine ⟨(canonical B hB (PhysicalPaddingExchange.exchanged F),out.2+scans),?_,rfl,
    Nat.add_le_add_right hc scans⟩
  exact PhysicalPaddingExchange.padded_correct P (2^u) (radix^(exponent radix u)) G S B hB
    hf _ F out hr ho

/-- The enlarged file's volume is bounded by one absolute q² factor.
This bound concerns the actual prime-power file used by `execute`. -/
theorem enlarged_volume (P u G S : ℕ) (hP : 0 < P) (hG : 0 < G) (hS : 0 < S) :
    Volume P (radix^(exponent radix u)) G S < radix^2*Volume P (2^u) G S :=
  binary_volume_growth P G S radix u radix_prime.one_lt hP hG hS

end
end CodedSorting.PhysicalBinaryExchange
end PhysicalBinaryExchange

section PhysicalBinaryBound
/-! The actual binary-field program inherits the improved arbitrary-width
bound. Prime-power padding grows volume by a fixed q² factor and reduces
the field exponent. The last theorem instantiates every startup/cutoff
premise using the normalized choices already verified in the paper model.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CodedSorting.PhysicalBinaryBound
open Circuit Address RecursiveExchange PhysicalRecursiveExchange
open BinaryPadding PhysicalArbitraryBound
noncomputable section

def growth : ℝ := (radix : ℝ)^2
def binaryConstant : ℝ := finalConstant*growth+2*(1+growth)

theorem growth_one : 1 ≤ growth := by
  have h : (1 : ℝ) ≤ radix := by exact_mod_cast radix_prime.one_lt.le
  exact one_le_pow₀ h

theorem binaryConstant_nonneg : 0 ≤ binaryConstant := by
  unfold binaryConstant
  have := finalConstant_nonneg
  have := growth_one
  positivity

theorem expanded_scan (B P u G S : ℕ) (hP : 0 < P) (hG : 0 < G) (hS : 0 < S) :
    scan B (Volume P (radix^(exponent radix u)) G S) ≤
      growth*scan B (Volume P (2^u) G S) := by
  have hv := (binary_volume_growth P G S radix u radix_prime.one_lt hP hG hS).le
  have hvR : (Volume P (radix^(exponent radix u)) G S : ℝ) ≤
      growth*(Volume P (2^u) G S : ℝ) := by
    unfold growth
    exact_mod_cast hv
  have hd := div_le_div_of_nonneg_right hvR (Nat.cast_nonneg B : (0 : ℝ)≤B)
  have hg := growth_one
  unfold scan
  rw [mul_div_assoc] at hd
  nlinarith

theorem exponent_factor (base u : ℕ) :
    1+((exponent radix u : ℝ)/base)^(1-(Parameters.epsilon : ℝ)) ≤
      1+((u : ℝ)/base)^(1-(Parameters.epsilon : ℝ)) := by
  have he : (exponent radix u : ℝ) ≤ u := by exact_mod_cast binary_width_bound radix u radix_prime.one_lt
  have hd := div_le_div_of_nonneg_right he (Nat.cast_nonneg base : (0 : ℝ)≤base)
  have ht : 0 ≤ 1-(Parameters.epsilon : ℝ) := by
    have h : (Parameters.epsilon : ℝ)<1 := by exact_mod_cast Parameters.epsilon_lt_one
    linarith
  exact add_le_add_left (Real.rpow_le_rpow (by positivity) hd ht) 1

theorem bound_improved (base cutoff B P u G S : ℕ) (hB : 0 < B)
    (hb : 0 < base) (hP : 0 < P) (hG : 0 < G) (hS : 0 < S)
    (hcut : Parameters.W*B ≤ cutoff) :
    (PhysicalBinaryExchange.bound base cutoff B P u G S : ℝ) ≤
      binaryConstant*scan B (Volume P (2^u) G S)*
        (1+((u : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) := by
  let V := Volume P (2^u) G S
  let V' := Volume P (radix^(exponent radix u)) G S
  let factor : ℝ := 1+((u : ℝ)/base)^(1-(Parameters.epsilon : ℝ))
  have hs : scan B V'≤growth*scan B V := expanded_scan B P u G S hP hG hS
  have hf : 1≤factor := by
    unfold factor
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
  have hf0 : 0≤factor := by linarith
  have hgeo := exponent_factor base u
  have hc := PhysicalArbitraryBound.bound_improved base cutoff B P (exponent radix u) G S hB hb hP hcut
  have hm := mul_le_mul hs hgeo
    (by positivity : 0 ≤ 1+((exponent radix u : ℝ)/base)^(1-(Parameters.epsilon : ℝ)))
    (mul_nonneg (growth_one.trans' (by norm_num)) (scan_nonneg B V))
  have hm' := mul_le_mul_of_nonneg_left hm finalConstant_nonneg
  have hcost : (PhysicalArbitraryExchange.bound base cutoff B P (exponent radix u) G S : ℝ) ≤
      finalConstant*growth*scan B V*factor := by
    change _ ≤ finalConstant*scan B V'*(1+((exponent radix u : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) at hc
    change _ ≤ _*factor at hm
    change _ ≤ finalConstant*(_*factor) at hm'
    exact hc.trans (by simpa only [mul_assoc] using hm')
  have hp1 := ceil_scan_le B V hB
  have hp2 := (ceil_scan_le B V' hB).trans hs
  have hpad : ((2*((V+B-1)/B+(V'+B-1)/B) : ℕ) : ℝ) ≤
      (2*(1+growth))*scan B V*factor := by
    have hm := mul_le_mul_of_nonneg_left hf
      (by have := growth_one; have := scan_nonneg B V; positivity : 0≤2*(1+growth)*scan B V)
    push_cast
    calc
      _ ≤ 2*(scan B V+growth*scan B V) :=
        mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) (by norm_num)
      _ = (2*(1+growth))*scan B V := by ring
      _ ≤ _ := by simpa only [mul_one] using hm
  change ((PhysicalArbitraryExchange.bound base cutoff B P (exponent radix u) G S+
    2*((V+B-1)/B+(V'+B-1)/B) : ℕ) : ℝ) ≤ binaryConstant*scan B V*factor
  push_cast at hpad ⊢
  unfold binaryConstant
  calc
    _ ≤ finalConstant*growth*scan B V*factor+(2*(1+growth))*scan B V*factor := add_le_add hcost hpad
    _ = _ := by ring

/-- Final binary bound for the very file execution whose output is proved
correct; all padding costs are included in the absolute constant. -/
theorem actual_binary_exchange_bound (base cutoff B : ℕ) (hB : 0 < B)
    (hb : 0 < base) (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (hcut : Parameters.W*B ≤ cutoff) (P u G S : ℕ) (hP : 0 < P) (hG : 0 < G) (hS : 0 < S)
    (F : Fin (Volume P (2^u) G S) → Bit) :
    ∃ out, PhysicalBinaryExchange.execute base cutoff B hB P u G S (canonical B hB F) = some out ∧
      out.1 = canonical B hB (PhysicalPaddingExchange.exchanged F) ∧
      (out.2 : ℝ) ≤ binaryConstant*scan B (Volume P (2^u) G S)*
        (1+((u : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) := by
  obtain ⟨out,hr,ho,hc⟩ := PhysicalBinaryExchange.execute_correct_cost base cutoff B hB hb
    hstartup P u G S hG hS F
  exact ⟨out,hr,ho,(Nat.cast_le.mpr hc).trans
    (bound_improved base cutoff B P u G S hB hb hP hG hS hcut)⟩

theorem normalized_binary_exchange_bound (reserve M B w P u G S : ℕ)
    (hreserve : 0 < reserve) (hB : 0 < B) (hw : 0 < w)
    (hP : 0 < P) (hG : 0 < G) (hS : 0 < S)
    (hnormal : PhysicalLeafParameters.minimumRatio radix reserve Parameters.W ≤ M/B)
    (F : Fin (Volume P (2^u) G S) → Bit) :
    ∃ out, PhysicalBinaryExchange.execute (NormalizedPhysicalExchange.chosenBase M B)
        (NormalizedPhysicalExchange.cutoff reserve M w) (B*w) (Nat.mul_pos hB hw)
        P u G S (canonical (B*w) (Nat.mul_pos hB hw) F) = some out ∧
      out.1 = canonical (B*w) (Nat.mul_pos hB hw) (PhysicalPaddingExchange.exchanged F) ∧
      (out.2 : ℝ) ≤ binaryConstant*scan (B*w) (Volume P (2^u) G S)*
        (1+((u : ℝ)/(NormalizedPhysicalExchange.chosenBase M B : ℝ))^
          (1-(Parameters.epsilon : ℝ))) := by
  apply actual_binary_exchange_bound _ _ _ (Nat.mul_pos hB hw)
    (NormalizedPhysicalExchange.chosenBase_bounds reserve M B hnormal).1
    ((NormalizedPhysicalExchange.chosenBase_startup reserve M B w hreserve hnormal).trans
      (Nat.le_add_right _ _))
    (NormalizedPhysicalExchange.cutoff_child_blocks reserve M B w hreserve hnormal)
    P u G S hP hG hS F

end
end CodedSorting.PhysicalBinaryBound
end PhysicalBinaryBound
