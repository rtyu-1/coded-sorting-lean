import CodedSorting.Interchange.Framework.Fields.MachineBound
import CodedSorting.Interchange.Framework.Pruned.Parameters

section Cost
/-! Binary-field padding costs for the common machine. The two padding
programs retain their actual 12 and 27 scan coefficients; their volume
increase is fixed and therefore preserves the coding exponent.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonBinaryCost
open Circuit RecursiveExchange BinaryPadding PhysicalArbitraryBound
open PhysicalBinaryBound
noncomputable section

def bound (base cutoff b P u G S A D F : ℕ) : ℕ :=
  CommonArbitraryCost.bound base cutoff b P (exponent radix u) G S A D F+
    12*(Volume P (2^u) G S/b+1)+27*(Volume P (radix^(exponent radix u)) G S/b+1)

def binaryConstant (A D F : ℕ) : ℝ :=
  CommonArbitraryCost.finalConstant A D F*growth+12+27*growth

theorem binaryConstant_nonneg (A D F : ℕ) : 0≤binaryConstant A D F := by
  unfold binaryConstant
  have := CommonArbitraryCost.finalConstant_nonneg A D F
  have := growth_one
  positivity

theorem bound_improved (base cutoff b P u G S A D F : ℕ) (hb : 0<b)
    (hbase : 0<base) (hP : 0<P) (hG : 0<G) (hS : 0<S)
    (hcut : Parameters.W*b≤cutoff) :
    (bound base cutoff b P u G S A D F : ℝ)≤
      binaryConstant A D F*scan b (Volume P (2^u) G S)*
        (1+((u : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) := by
  let V := Volume P (2^u) G S
  let V' := Volume P (radix^(exponent radix u)) G S
  let factor : ℝ := 1+((u : ℝ)/base)^(1-(Parameters.epsilon : ℝ))
  have hs : scan b V'≤growth*scan b V := expanded_scan b P u G S hP hG hS
  have hf : 1≤factor := by
    unfold factor
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
  have hgeo := exponent_factor base u
  have hc := CommonArbitraryCost.bound_improved base cutoff b P (exponent radix u) G S
    A D F hb hbase hP hcut
  have hm := mul_le_mul hs hgeo
    (by positivity : 0≤1+((exponent radix u : ℝ)/base)^(1-(Parameters.epsilon : ℝ)))
    (mul_nonneg (growth_one.trans' (by norm_num)) (scan_nonneg b V))
  have hm' := mul_le_mul_of_nonneg_left hm (CommonArbitraryCost.finalConstant_nonneg A D F)
  have hcost : (CommonArbitraryCost.bound base cutoff b P (exponent radix u) G S A D F : ℝ)≤
      CommonArbitraryCost.finalConstant A D F*growth*scan b V*factor := by
    change _≤CommonArbitraryCost.finalConstant A D F*scan b V'*
      (1+((exponent radix u : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) at hc
    change _≤_*factor at hm
    change _≤CommonArbitraryCost.finalConstant A D F*(_*factor) at hm'
    exact hc.trans (by simpa only [mul_assoc] using hm')
  have hp1 := nat_scan_le b V
  have hp2 := (nat_scan_le b V').trans hs
  have hpad : ((12*(V/b+1)+27*(V'/b+1) : ℕ) : ℝ)≤
      (12+27*growth)*scan b V*factor := by
    have hm := mul_le_mul_of_nonneg_left hf
      (by have := growth_one; have := scan_nonneg b V
          positivity : 0≤(12+27*growth)*scan b V)
    push_cast at hp1 hp2 ⊢
    have h1 := mul_le_mul_of_nonneg_left hp1 (by norm_num : (0 : ℝ)≤12)
    have h2 := mul_le_mul_of_nonneg_left hp2 (by norm_num : (0 : ℝ)≤27)
    calc
      _≤12*scan b V+27*(growth*scan b V) := add_le_add h1 h2
      _=(12+27*growth)*scan b V := by ring
      _≤_ := by simpa only [mul_one] using hm
  change ((CommonArbitraryCost.bound base cutoff b P (exponent radix u) G S A D F+
    12*(V/b+1)+27*(V'/b+1) : ℕ) : ℝ)≤binaryConstant A D F*scan b V*factor
  rw [Nat.add_assoc]
  push_cast at hpad ⊢
  unfold binaryConstant
  calc
    _≤CommonArbitraryCost.finalConstant A D F*growth*scan b V*factor+
        (12+27*growth)*scan b V*factor := add_le_add hcost hpad
    _=_ := by ring

/-- Discharge the last arithmetic bridge from charged block counts to the
binary envelope. The child remains the same arbitrary-width program. -/
theorem assembled_padding_le (q : CommonSortingNormalization.Configuration)
    (base cutoff P u G S A D F : ℕ) :
    CommonArbitraryCost.bound base cutoff (CommonPermutationPairs.width q) P
      (exponent radix u) G S A D F+
      (12*CommonPermutationPairs.count q (Volume P (2^u) G S)+
       27*CommonPermutationPairs.count q (Volume P (radix^(exponent radix u)) G S))≤
    bound base cutoff (CommonPermutationPairs.width q) P u G S A D F := by
  have h1 := Nat.mul_le_mul_left 12
    (CommonRecursiveExchange.Pruned.count_le_scan q (Volume P (2^u) G S))
  have h2 := Nat.mul_le_mul_left 27
    (CommonRecursiveExchange.Pruned.count_le_scan q (Volume P (radix^(exponent radix u)) G S))
  unfold bound
  omega

end
end CodedSorting.CommonBinaryCost
end Cost

section Machine
/-! Binary-field exchange on the actual finite machine.  Both padding
passes surround the concrete arbitrary-width instruction list, and their
cost is included in the same execution bound. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonBinaryMachine
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonFinitePermutation CommonChunkLayout
open Circuit RecursiveExchange BinaryPadding
noncomputable section
attribute [local irreducible] CommonArbitraryMachine.program CommonArbitraryMachine.space

def space (q : Configuration) (base cutoff P u G S : ℕ)
    (hb : 0<base) (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q) : ℕ :=
  2*count q (CommonChunkLayout.Volume P (radix^(exponent radix u)) G (S*q.w))+
    CommonArbitraryMachine.space q base cutoff P (exponent radix u) G S
      hb hG hS hresident hfit hstartup

def bound (q : Configuration) (base cutoff P u G S : ℕ) : ℕ :=
  CommonBinaryCost.bound base cutoff (width q) P u G (S*q.w) 24 27 (6*(2*radix+6))

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P u G S source buffer limit : ℕ)
    (hb : 0<base) (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q)
    (hs : source+count q (CommonChunkLayout.Volume P (2^u) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P u G S hb hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (CommonChunkLayout.Volume P (2^u) G (S*q.w)) source buffer limit
      (swap P (2^u) G (S*q.w)) := by
  let C := count q (CommonChunkLayout.Volume P (radix^(exponent radix u)) G (S*q.w))
  have hw' : buffer+C+C+
      CommonArbitraryMachine.space q base cutoff P (exponent radix u) G S
        hb hG hS hresident hfit hstartup≤limit := by
    dsimp only [space] at hw
    dsimp only [C]
    omega
  let child := CommonArbitraryMachine.program q reader base cutoff P (exponent radix u) G S
    (buffer+C) (buffer+C+C) limit hb hG hS hresident hfit hstartup (le_refl _) hw' hl
  exact CommonPaddedPermutation.binaryProgram q reader P (2^u) (radix^(exponent radix u))
    G (S*q.w) (binary_range_fits radix u radix_prime.one_lt) source buffer limit child hs
      (by omega) hl

attribute [local irreducible] program

theorem charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P u G S source buffer limit : ℕ)
    (hb : 0<base) (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q)
    (hs : source+count q (CommonChunkLayout.Volume P (2^u) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P u G S hb hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) :
    (program q reader base cutoff P u G S source buffer limit hb hG hS
      hresident hfit hstartup hs hw hl).charge≤bound q base cutoff P u G S := by
  unfold program
  dsimp only [CommonPaddedPermutation.binaryProgram,CommonPaddedPermutation.wrap]
  have hchild := CommonArbitraryMachine.charge_le q reader base cutoff P (exponent radix u) G S
    (buffer+count q (CommonChunkLayout.Volume P (radix^(exponent radix u)) G (S*q.w)))
    (buffer+count q (CommonChunkLayout.Volume P (radix^(exponent radix u)) G (S*q.w))+
      count q (CommonChunkLayout.Volume P (radix^(exponent radix u)) G (S*q.w)))
    limit hb hG hS hresident hfit hstartup (le_refl _)
    (by dsimp only [space] at hw; omega) hl
  have hpad := CommonBinaryCost.assembled_padding_le q base cutoff P u G (S*q.w)
    24 27 (6*(2*radix+6))
  exact (Nat.add_le_add_right (Nat.add_le_add_right hchild _) _).trans
    (by simpa only [Nat.add_assoc,bound,CommonArbitraryMachine.bound] using hpad)

/-- Correctness, preservation, halt, transfer count and RAM refer to one
fixed-policy run of the concrete binary exchange. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P u G S source buffer limit : ℕ)
    (hb : 0<base) (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q)
    (hs : source+count q (CommonChunkLayout.Volume P (2^u) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P u G S hb hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : bound q base cutoff P u G S≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader base cutoff P u G S source buffer limit hb hG hS
      hresident hfit hstartup hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ y : Fin (CommonChunkLayout.Volume P (2^u) G (S*q.w)),
      readBit q result.1.disk source y.val=
        readBit q s.disk source (swap P (2^u) G (S*q.w) y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (CommonChunkLayout.Volume P (2^u) G (S*q.w))≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    result.2≤bound q base cutoff P u G S ∧ Fintype.card (ResidentIndex q)≤q.M := by
  let p := program q reader base cutoff P u G S source buffer limit hb hG hS
    hresident hfit hstartup hs hw hl
  have hc := charge_le q reader base cutoff P u G S source buffer limit hb hG hS
    hresident hfit hstartup hs hw hl
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ := CommonFinitePermutation.complete q p s (hc.trans hsize) hpc
  exact ⟨hout,hframe,hhalt,hcost.trans hc,hram⟩

theorem complete_improved (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P u G S source buffer limit : ℕ)
    (hb : 0<base) (hP : 0<P) (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q)
    (hcut : Parameters.W*width q≤cutoff)
    (hs : source+count q (CommonChunkLayout.Volume P (2^u) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P u G S hb hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : bound q base cutoff P u G S≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader base cutoff P u G S source buffer limit hb hG hS
      hresident hfit hstartup hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ y : Fin (CommonChunkLayout.Volume P (2^u) G (S*q.w)),
      readBit q result.1.disk source y.val=
        readBit q s.disk source (swap P (2^u) G (S*q.w) y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (CommonChunkLayout.Volume P (2^u) G (S*q.w))≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    (result.2 : ℝ)≤CommonBinaryCost.binaryConstant 24 27 (6*(2*radix+6))*
      PhysicalArbitraryBound.scan (width q) (CommonChunkLayout.Volume P (2^u) G (S*q.w))*
        (1+((u : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ := complete q reader base cutoff P u G S
    source buffer limit hb hG hS hresident hfit hstartup hs hw hl s hsize hpc
  refine ⟨hout,hframe,hhalt,?_,hram⟩
  exact (Nat.cast_le.mpr hcost).trans
    (CommonBinaryCost.bound_improved base cutoff (width q) P u G (S*q.w)
      24 27 (6*(2*radix+6)) (width_pos q) hb hP hG
        (Nat.mul_pos hS (by have := q.word_width; omega)) hcut)

end
end CodedSorting.CommonBinaryMachine
end Machine

section Normalized
/-! One normalization ratio supplies every base/cutoff condition for the
actual binary-field exchange.  Source separation, finite disk allocation,
and instruction capacity remain explicit.  The suffix consists of whole
machine words throughout the padding and arbitrary-width calls. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonBinaryNormalized
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonPrunedParameters (chosenBase cutoff Normalized)
open CommonChunkLayout CommonFinitePermutation RecursiveExchange Circuit
noncomputable section
attribute [local irreducible] CommonBinaryMachine.program CommonBinaryMachine.space
  ControlledNormalization.runLogical Parameters.W Parameters.m radix

def space (q : Configuration) (P u G S : ℕ) (hG : 0<G) (hS : 0<S)
    (hnormal : Normalized q) : ℕ :=
  CommonBinaryMachine.space q (chosenBase q) (cutoff q) P u G S
    (CommonPrunedParameters.chosenBase_pos q hnormal) hG hS (le_refl _)
    (CommonPrunedParameters.chosenBase_fit q hnormal)
    (CommonPrunedParameters.chosenBase_startup q hnormal)

def normalizedProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (P u G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (hnormal : Normalized q)
    (hs : source+count q (Volume P (2^u) G (S*q.w))≤buffer)
    (hw : buffer+space q P u G S hG hS hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (2^u) G (S*q.w)) source buffer limit
      (swap P (2^u) G (S*q.w)) :=
  CommonBinaryMachine.program q reader (chosenBase q) (cutoff q) P u G S
    source buffer limit (CommonPrunedParameters.chosenBase_pos q hnormal) hG hS
    (le_refl _) (CommonPrunedParameters.chosenBase_fit q hnormal)
    (CommonPrunedParameters.chosenBase_startup q hnormal) hs hw hl

/-- This single actual run exchanges both binary fields, preserves the
external frame, halts, stays within resident RAM, and has the improved cost.
The base width is selected from the machine, not supplied by the caller. -/
theorem normalized_bound (q : Configuration) (reader : Fin q.inventory.readers)
    (P u G S source buffer limit : ℕ) (hP : 0<P) (hG : 0<G) (hS : 0<S)
    (hnormal : Normalized q)
    (hs : source+count q (Volume P (2^u) G (S*q.w))≤buffer)
    (hw : buffer+space q P u G S hG hS hnormal≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : CommonBinaryMachine.bound q (chosenBase q) (cutoff q) P u G S≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := normalizedProgram q reader P u G S source buffer limit hG hS hnormal hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ y : Fin (Volume P (2^u) G (S*q.w)),
      readBit q result.1.disk source y.val=
        readBit q s.disk source (swap P (2^u) G (S*q.w) y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (Volume P (2^u) G (S*q.w))≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    (result.2 : ℝ)≤CommonBinaryCost.binaryConstant 24 27 (6*(2*radix+6))*
      PhysicalArbitraryBound.scan (width q) (Volume P (2^u) G (S*q.w))*
        (1+((u : ℝ)/(chosenBase q))^(1-(Parameters.epsilon : ℝ))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  exact CommonBinaryMachine.complete_improved q reader (chosenBase q) (cutoff q) P u G S
    source buffer limit (CommonPrunedParameters.chosenBase_pos q hnormal) hP hG hS
    (le_refl _) (CommonPrunedParameters.chosenBase_fit q hnormal)
    (CommonPrunedParameters.chosenBase_startup q hnormal)
    (CommonPrunedParameters.cutoff_child q hnormal) hs hw hl s hsize hpc

/-- The same automatically chosen base is logarithmic in the available
payload-bank/block ratio. -/
theorem normalized_base_scale (q : Configuration) (hnormal : Normalized q) :
    0<chosenBase q ∧
      8*chosenBase q≤Nat.log radix (CommonPrunedParameters.ratio q) ∧
      Nat.log radix (CommonPrunedParameters.ratio q)<8*Parameters.m*chosenBase q :=
  ⟨CommonPrunedParameters.chosenBase_pos q hnormal,
    CommonPrunedParameters.chosenBase_log_sandwich q hnormal⟩

end
end CodedSorting.CommonBinaryNormalized
end Normalized
