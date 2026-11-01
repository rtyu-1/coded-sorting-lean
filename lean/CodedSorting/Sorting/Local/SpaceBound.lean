import CodedSorting.Sorting.Radix.Program.Execution

/-! Scalar workspace bounds for the actual three-level local program.
The exchange bound is isolated here and discharged by the concrete
polynomial exchange estimate in the global workspace endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.Construction.Sorting.CommonLocalSpaceBounds
open CommonSortingNormalization CommonRecordProgram CodedSorting.Construction.RecursiveParameters
open CommonLocalNode CodedSorting.Construction.Sorting.CommonLocalRecursion
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension

theorem blocks_le (q : Configuration) (n : ℕ) : recordBlocks q n≤3*n := by
  rw [CommonGroupedLeafCost.recordBlocks_eq]
  exact CommonLeafGrouping.blockCount_le_of_fits (CommonLeafProgram.block_positive q)
    (Nat.le_mul_of_pos_right _ (CommonLeafProgram.block_positive q))

theorem grouped_le (q : Configuration) (c r : ℕ) (hr : r≤512*q.height) :
    CommonGroupedLeafBatch.space q c r≤11*recordBlocks q (c*r) := by
  unfold CommonGroupedLeafBatch.space
  split
  · omega
  · rename_i hlarge
    have hcr : 512*q.height<c*r := by omega
    have hp : recordBlocks q (CommonGroupedLeafBatch.paddedSize q c r)≤
        2*recordBlocks q (c*r) := by
      simp only [CommonGroupedLeafCost.recordBlocks_eq]
      exact CommonLeafGrouping.padded_blocks_le (CommonLeafProgram.block_positive q)
        (CommonLeafGrouping.rows_pos hcr) hr hcr.le
    have hg : CommonGroupedLeafBatch.ng q c r*
        recordBlocks q (CommonGroupedLeafBatch.groupSize q r)≤8*recordBlocks q (c*r) := by
      simp only [CommonGroupedLeafCost.recordBlocks_eq]
      exact CommonLeafGrouping.grouped_blocks_le (CommonLeafProgram.block_positive q)
        (CommonLeafGrouping.rows_pos hcr) hr
        (by have:=block_le_height q;omega) hcr.le
    have hsize : CommonGroupedLeafBatch.groupSize q r≤c*r :=
      (CommonLeafGrouping.group_fits _ _).trans hcr.le
    have hs := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.recordBlocks_mono q hsize
    omega

theorem batch_le (q : Configuration) (c r childSpace : ℕ) :
    batchSpace q c r childSpace≤33*(c*r)+childSpace := by
  unfold batchSpace
  split
  · rename_i hr
    have hg := grouped_le q c r hr
    have hb := blocks_le q (c*r)
    omega
  · have hb := Nat.mul_le_mul_left c (blocks_le q r)
    nlinarith only [hb]

/-- All recursive children stay below the original size. The only
nonlinear workspace contribution is the actual exchange workspace. -/
theorem local_le (q : Configuration) (normal : Normalized q) (U E : ℕ)
    (hex : ∀ n,n≤U → 512*q.height<n →
      CodedSorting.Construction.Sorting.CommonSortingSwaps.space q (LocalShape.sizeExponent n) 3 (by omega) normal≤E)
    (fuel n : ℕ) (hn : n≤U) :
    space q normal fuel n≤(fuel+1)*(1250*(U+1)+E) := by
  induction fuel generalizing n with
  | zero =>
    change recordBlocks q n≤_
    have hb := blocks_le q n
    omega
  | succ fuel ih =>
    by_cases hsmall : n≤512*q.height
    · simp only [space,if_pos hsmall]
      have hb := blocks_le q n
      nlinarith only [hb,hn]
    · have hlarge : 512*q.height<n := by omega
      have h512 : 512<n := by have:=height_pos q;nlinarith only [this,hlarge]
      have hr := CommonLocalDescriptorBounds.child_lt n h512
      have hv := CommonLocalDescriptorBounds.large_words_lt n (by omega)
      have hsl : small n≤large n := by unfold small large;nlinarith
      have hs := blocks_le q (small n)
      have hl := blocks_le q (large n)
      have hm1 : max 1 (recordBlocks q (small n))≤96*n+1 := by omega
      have hm2 : max 1 (recordBlocks q (large n))≤96*n+1 := by omega
      have hi := ih (rowCount n) (hr.le.trans hn)
      have hb1 := batch_le q (side n) (rowCount n) (space q normal fuel (rowCount n))
      have hb2 := batch_le q (side n+1) (rowCount n) (space q normal fuel (rowCount n))
      have he := hex n hn hlarge
      have hm : max
          (batchSpace q (side n) (rowCount n) (space q normal fuel (rowCount n)))
          (max (batchSpace q (side n+1) (rowCount n) (space q normal fuel (rowCount n)))
            (CodedSorting.Construction.Sorting.CommonSortingSwaps.space q (LocalShape.sizeExponent n) 3 (by omega) normal))≤
          1056*n+space q normal fuel (rowCount n)+E := by
        apply max_le
        · change batchSpace q (side n) (rowCount n) _≤_
          change _≤33*small n+_ at hb1
          omega
        · apply max_le
          · change _≤33*large n+_ at hb2
            omega
          · omega
      simp only [space,if_neg hsmall]
      nlinarith only [hm1,hm2,hm,hi,hn]

end
end CodedSorting.Construction.Sorting.CommonLocalSpaceBounds
