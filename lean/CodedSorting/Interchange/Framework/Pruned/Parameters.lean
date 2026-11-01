import CodedSorting.Shared.Memory.Buffered.GatherProgram
import CodedSorting.Interchange.Framework.Memory.Reflection
import CodedSorting.Interchange.Framework.Memory.PhysicalPaddingExchange

/-! Integer parameter choices for the actual common machine.  The cutoff
uses the existing leaf payload bank, while stream/control buffers remain in
their separately counted slots.  One public ratio condition supplies the
bucket-buffer, startup, and minimum-child-block premises. -/
set_option autoImplicit false
namespace CodedSorting.CommonPrunedParameters
open CommonSortingNormalization CommonPermutationPairs RecursiveExchange
open PhysicalLeafParameters
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m radix

def ratio (q : Configuration) : ℕ := CommonExchangeLeaf.bankWords q/q.block

def cutoff (q : Configuration) : ℕ := CommonExchangeLeaf.bankBits q

def chosenBase (q : Configuration) : ℕ :=
  NormalizedPhysicalExchange.chosenBase (CommonExchangeLeaf.bankWords q) q.block

def Normalized (q : Configuration) : Prop :=
  minimumRatio radix 1 Parameters.W≤ratio q

/-- A supplied word-buffer bound immediately gives the stronger startup
bound without its optional extra block. -/
theorem bucket_fit_bits (q : Configuration) (base : ℕ)
    (hfit : ((radix^base)*(radix^base))*q.block≤CommonExchangeLeaf.bankWords q) :
    ((radix^base)*(radix^base))*width q≤cutoff q := by
  simpa only [width,cutoff,CommonExchangeLeaf.bankBits,Nat.mul_assoc] using
    Nat.mul_le_mul_right q.w hfit

theorem bucket_fit_startup (q : Configuration) (base : ℕ)
    (hfit : ((radix^base)*(radix^base))*q.block≤CommonExchangeLeaf.bankWords q) :
    ((radix^base)*(radix^base))*width q≤cutoff q+width q :=
  (bucket_fit_bits q base hfit).trans (Nat.le_add_right _ _)

theorem cutoff_child_of_fit (q : Configuration)
    (hfit : Parameters.W*q.block≤CommonExchangeLeaf.bankWords q) :
    Parameters.W*width q≤cutoff q := by
  simpa only [width,cutoff,CommonExchangeLeaf.bankBits,Nat.mul_assoc] using
    Nat.mul_le_mul_right q.w hfit

theorem chosenBase_bounds (q : Configuration) (hnormal : Normalized q) :
    0<chosenBase q ∧ chosenBase q≤widthLimit radix (ratio q) ∧
      widthLimit radix (ratio q)<Parameters.m*chosenBase q :=
  NormalizedPhysicalExchange.chosenBase_bounds 1 (CommonExchangeLeaf.bankWords q)
    q.block hnormal

theorem chosenBase_pos (q : Configuration) (hnormal : Normalized q) :
    0<chosenBase q := (chosenBase_bounds q hnormal).1

theorem chosenBase_log_sandwich (q : Configuration) (hnormal : Normalized q) :
    8*chosenBase q≤Nat.log radix (ratio q) ∧
      Nat.log radix (ratio q)<8*Parameters.m*chosenBase q :=
  NormalizedPhysicalExchange.chosenBase_log 1 (CommonExchangeLeaf.bankWords q)
    q.block hnormal

theorem width_fit (q : Configuration) (hnormal : Normalized q) (e : ℕ)
    (he : e≤widthLimit radix (ratio q)) :
    ((radix^e)*(radix^e))*q.block≤CommonExchangeLeaf.bankWords q := by
  simpa only [Nat.div_one] using
    bucket_words radix 1 Parameters.W (CommonExchangeLeaf.bankWords q) q.block e
      radix_prime.one_lt (by decide) hnormal he

theorem chosenBase_fit (q : Configuration) (hnormal : Normalized q) :
    ((radix^(chosenBase q))*(radix^(chosenBase q)))*q.block≤
      CommonExchangeLeaf.bankWords q :=
  width_fit q hnormal (chosenBase q) (chosenBase_bounds q hnormal).2.1

theorem chosenBase_bits (q : Configuration) (hnormal : Normalized q) :
    ((radix^(chosenBase q))*(radix^(chosenBase q)))*width q≤cutoff q :=
  bucket_fit_bits q (chosenBase q) (chosenBase_fit q hnormal)

theorem chosenBase_startup (q : Configuration) (hnormal : Normalized q) :
    ((radix^(chosenBase q))*(radix^(chosenBase q)))*width q≤cutoff q+width q :=
  bucket_fit_startup q (chosenBase q) (chosenBase_fit q hnormal)

theorem child_buffer_fit (q : Configuration) (hnormal : Normalized q) :
    Parameters.W*q.block≤CommonExchangeLeaf.bankWords q := by
  simpa only [Nat.div_one] using
    reserved_child_words radix 1 Parameters.W (CommonExchangeLeaf.bankWords q)
      q.block (by decide) hnormal

theorem cutoff_child (q : Configuration) (hnormal : Normalized q) :
    Parameters.W*width q≤cutoff q :=
  cutoff_child_of_fit q (child_buffer_fit q hnormal)

/-- The machine's existing normalization also supplies the ratio whenever
the fixed inventory threshold was chosen large enough. -/
theorem normalized_of_inventory (q : Configuration)
    (hthreshold : minimumRatio radix 1 Parameters.W≤q.inventory.ratio) : Normalized q := by
  apply (Nat.le_div_iff_mul_le (CommonLeafProgram.block_positive q)).2
  have h := Nat.mul_le_mul_right q.block hthreshold
  have hr := CommonSortingNormalization.normalized_ratio q
  have hb : q.height≤CommonExchangeLeaf.bankWords q := by
    unfold CommonExchangeLeaf.bankWords
    omega
  exact h.trans (hr.trans hb)

end
end CodedSorting.CommonPrunedParameters
