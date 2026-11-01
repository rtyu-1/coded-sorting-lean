import CodedSorting.Sorting.Bounds.PhysicalSortingExchange

/-! The actual forward transpose produces the exact finite `secondInput`
used by Columnsort. A second batch may be placed between the two transposes:
the inverse consumes that batch's returned file, not its abstract input or
a newly synthesized replacement. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalLocalSortTranspose
open Circuit Address RecursiveExchange PhysicalRecursiveExchange PhysicalExchangeRecursion
open PhysicalSortingExchangeLayout PhysicalSortingExchange ColumnsortExchange RecursiveColumnsort
noncomputable section

def firstRow (s : ℕ) (x : Fields s) : Fin (s^2*s*1) :=
  finCongr (by ring) (finProdFinEquiv (pair s (x.2.1,x.2.2.1),x.2.2.2))

def secondRow (s : ℕ) (x : Fields s) : Fin (s*(s^2*1)) :=
  finProdFinEquiv (x.2.1,finCongr (by ring) (pair s (x.2.2.1,x.2.2.2)))

def firstValues (s w : ℕ) (one : Fin s → Fin (s^2*s*1) → Fin w → Bit)
    (a : RecordAddress s w) : Bit := one a.1.1 (firstRow s a.1) a.2

def secondValues (s w : ℕ) (one : Fin s → Fin (s^2*s*1) → Fin w → Bit)
    (a : RecordAddress s w) : Bit :=
  secondInput (s^2) s one a.1.1 (secondRow s a.1) a.2

/-- This is the existing Columnsort second-batch input, down to the same
source column and source row, with each record's bit offset unchanged. -/
theorem forward_is_secondInput (s w : ℕ)
    (one : Fin s → Fin (s^2*s*1) → Fin w → Bit) :
    transport (forwardRecord s (Fin w)) (firstValues s w one)=secondValues s w one := by
  funext a
  unfold secondValues secondRow
  rw [secondInput_source]
  change one a.1.2.1 (firstRow s (a.1.2.1,a.1.2.2.1,a.1.2.2.2,a.1.1)) a.2 = _
  congr 2
  apply Fin.ext
  change a.1.1.val+s*(a.1.2.2.2.val+s*a.1.2.2.1.val)=
    (a.1.2.2.2.val+s*a.1.2.2.1.val)*s+a.1.1.val
  ring

theorem forward_correct (base cutoff B : ℕ) (hB : 0 < B) (hb : 0 < base)
    (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (t w : ℕ) (hw : 0 < w)
    (one : Fin (2^t) → Fin ((2^t)^2*(2^t)*1) → Fin w → Bit) :
    ∃ out,
      execute base cutoff B hB t w forwardSwaps
        (represented (recordLayout (2^t) w) B hB (firstValues (2^t) w one))=some out ∧
      out.1=represented (recordLayout (2^t) w) B hB (secondValues (2^t) w one) ∧
      out.2≤charge base cutoff B t w forwardSwaps := by
  obtain ⟨out,hr,ho,hc⟩ := execute_correct base cutoff B hB hb hstartup t w hw forwardSwaps
    (firstValues (2^t) w one)
  rw [forward_permute,forward_is_secondInput] at ho
  exact ⟨out,hr,ho,hc⟩

/-- Six physical exchanges with an actual file-producing batch between
them. The middle result's own cost is included in the returned total. -/
def aroundBatch (base cutoff B : ℕ) (hB : 0 < B) (t w : ℕ)
    (batch : File → Option Result) (source : File) : Option Result := do
  let fwd ← execute base cutoff B hB t w forwardSwaps source
  let mid ← batch fwd.1
  let bwd ← execute base cutoff B hB t w backwardSwaps mid.1
  return (bwd.1,fwd.2+mid.2+bwd.2)

/-- The hypothesis is one successful execution of the actual middle batch
on its specified input file, not an oracle asserting a sorted output. -/
theorem aroundBatch_correct (base cutoff B : ℕ) (hB : 0 < B) (hb : 0 < base)
    (hstartup : (radix^base*radix^base)*B ≤ cutoff+B)
    (t w : ℕ) (hw : 0 < w)
    (one : Fin (2^t) → Fin ((2^t)^2*(2^t)*1) → Fin w → Bit)
    (batch : File → Option Result) (mid : Result) (two : RecordAddress (2^t) w → Bit)
    (hbatch : batch (represented (recordLayout (2^t) w) B hB
      (secondValues (2^t) w one))=some mid)
    (hmid : mid.1=represented (recordLayout (2^t) w) B hB two) :
    ∃ out,
      aroundBatch base cutoff B hB t w batch
        (represented (recordLayout (2^t) w) B hB (firstValues (2^t) w one))=some out ∧
      out.1=represented (recordLayout (2^t) w) B hB
        (transport (forwardRecord (2^t) (Fin w)).symm two) ∧
      out.2≤charge base cutoff B t w forwardSwaps+mid.2+
        charge base cutoff B t w backwardSwaps := by
  obtain ⟨fwd,hf,ho,hc⟩ := forward_correct base cutoff B hB hb hstartup t w hw one
  obtain ⟨bwd,hbwd,ho',hc'⟩ := execute_correct base cutoff B hB hb hstartup t w hw backwardSwaps two
  refine ⟨(bwd.1,fwd.2+mid.2+bwd.2),?_,?_,?_⟩
  · simp [aroundBatch,hf,ho,hbatch,hmid,hbwd]
  · simpa only [backward_permute] using ho'
  · exact Nat.add_le_add (Nat.add_le_add_right hc mid.2) hc'

end
end CodedSorting.PhysicalLocalSortTranspose
