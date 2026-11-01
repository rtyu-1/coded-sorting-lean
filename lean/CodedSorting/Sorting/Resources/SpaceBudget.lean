import CodedSorting.Interchange.Bounds.ExchangeSpace
import CodedSorting.Sorting.Resources.Swaps
import CodedSorting.Sorting.Local.Program

/-! Actual Construction workspace for Columnsort's three adjacent exchanges.
The stages run sequentially and reuse the same arena. Their maximum is
bounded directly by the volume scan proved for BinaryMachine.space;
no old network file count or transfer-to-space assumption is used. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace CodedSorting.Construction.Sorting.CommonSortingSpaceBudget
open CommonSortingNormalization CommonPermutationPairs RecursiveParameters
open CommonSortingSwaps PhysicalSortingExchange
noncomputable section
attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs ExchangeSpecialization.uniform

theorem stage (q : Configuration) (t r : ℕ) (hr : 0<r)
    (normal : Normalized q) (j : Swap) :
    stageSpace q t r hr normal j≤ExchangeSpace.spaceCoefficient*
      (((2^t)^4*(r*q.w))/width q+1) := by
  have h := ExchangeSpace.binary q (chosenBase q) (cutoff q)
    (prefixSize (2^t) j) t 1 (suffix (2^t) r j)
    (chosenBase_pos q normal) (by omega) (suffix_pos t r hr j)
    (le_refl _) (RecursiveCostRate.block_le_cutoff (width q) (cutoff q)
      (cutoff_child q normal)) (chosenBase_fit q normal)
    (chosenBase_startup q normal)
  simpa only [stageSpace, BinaryNormalized.space, stage_volume] using h

theorem space (q : Configuration) (t r : ℕ) (hr : 0<r)
    (normal : Normalized q) :
    CommonSortingSwaps.space q t r hr normal≤ExchangeSpace.spaceCoefficient*
      (((2^t)^4*(r*q.w))/width q+1) := by
  unfold CommonSortingSwaps.space
  exact max_le (stage q t r hr normal .last)
    (max_le (stage q t r hr normal .middle) (stage q t r hr normal .first))

private theorem coefficient_exists (C : ℕ) : ∃ K : ℕ, K=C := ⟨C,rfl⟩

/-- The same fixed padding coefficient, sealed behind a generic proved
witness so kernel reduction need not evaluate the closed Construction network. -/
def coefficient : ℕ :=
  Classical.choose (coefficient_exists (49*ExchangeSpace.spaceCoefficient))

theorem coefficient_eq : coefficient=49*ExchangeSpace.spaceCoefficient :=
  Classical.choose_spec (coefficient_exists (49*ExchangeSpace.spaceCoefficient))

/-- The padded array has fewer than sixteen times the input records;
each record has three words. This is an actual allocation bound. -/
theorem local_space (q : Configuration) (normal : Normalized q) (n : ℕ)
    (hn : 512*q.height<n) :
    CommonSortingSwaps.space q (LocalShape.sizeExponent n) 3 (by omega) normal≤
      coefficient*(n+1) := by
  let t := LocalShape.sizeExponent n
  have hn1 : 1<n := by
    have := CommonLocalRecursion.height_pos q
    nlinarith only [this, hn]
  have hV : (2^t)^4<16*n := LocalShape.padding_lt n hn1
  have hb : 1≤q.block := CommonLeafProgram.block_positive q
  have hscan : (2^t)^4*(3*q.w)/width q≤3*(2^t)^4 := by
    apply Nat.div_le_of_le_mul
    change (2^t)^4*(3*q.w)≤(q.block*q.w)*(3*(2^t)^4)
    calc
      (2^t)^4*(3*q.w) = (1*(3*(2^t)^4))*q.w := by ring
      _ ≤ (q.block*(3*(2^t)^4))*q.w :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb)
      _ = _ := by ring
  have hscalar : (2^t)^4*(3*q.w)/width q+1≤49*(n+1) := by omega
  have h := (space q t 3 (by omega) normal).trans
    (Nat.mul_le_mul_left ExchangeSpace.spaceCoefficient hscalar)
  calc
    _ ≤ ExchangeSpace.spaceCoefficient*(49*(n+1)) := h
    _ = coefficient*(n+1) := by rw [coefficient_eq]; ring

end
end CodedSorting.Construction.Sorting.CommonSortingSpaceBudget
