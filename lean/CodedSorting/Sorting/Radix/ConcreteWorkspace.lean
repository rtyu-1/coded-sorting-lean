import CodedSorting.Sorting.Local.SpaceBound
import CodedSorting.Sorting.Resources.SpaceBudget

section WorkspaceEnvelope
/-! Propagate one uniform bound on the actual exchange workspaces through
all local calls, padded chunks, directories, and the global arena maximum.
The concrete exchange polynomial discharges the single scalar premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.Construction.Sorting.CommonMSDWorkspaceEnvelope
open CommonSortingNormalization CommonRecordProgram CodedSorting.Construction.RecursiveParameters
open CodedSorting.Construction.Sorting.CommonLocalSpaceBounds CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation
noncomputable section

def ExchangeBound (q : Configuration) (normal : Normalized q) (E : ℕ) : Prop :=
  ∀ n,n≤q.N^2 → 512*q.height<n →
    CodedSorting.Construction.Sorting.CommonSortingSwaps.space q (LocalShape.sizeExponent n) 3 (by omega) normal≤E

theorem height_le (q : Configuration) : q.height≤q.N := by
  have h := CommonLocalDescriptorBounds.height_scaled_le_input q
  omega

theorem input_le_square (q : Configuration) : q.N≤q.N^2 := by
  have h := q.input_large
  nlinarith

theorem local_le (q : Configuration) (normal : Normalized q) (E : ℕ)
    (hex : ExchangeBound q normal E) (n : ℕ) (hn : n≤q.N^2) :
    CodedSorting.Construction.Sorting.CommonLocalRecursion.space q normal 3 n≤5000*(q.N^2+1)+4*E := by
  have h := CodedSorting.Construction.Sorting.CommonLocalSpaceBounds.local_le q normal (q.N^2) E hex 3 n hn
  nlinarith only [h]

theorem interval_le (q : Configuration) (normal : Normalized q) (E : ℕ)
    (hex : ExchangeBound q normal E) (n : ℕ) (hn : n≤q.N) :
    CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q normal n≤5020*(q.N^2+1)+4*E := by
  have hn2 := hn.trans (input_le_square q)
  have hl := local_le q normal E hex n hn2
  have hb := blocks_le q n
  unfold CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space
  nlinarith only [hl,hb,hn2]

theorem chunks_le (q : Configuration) (normal : Normalized q) (E : ℕ)
    (hex : ExchangeBound q normal E) (n : ℕ) (hn : n≤q.N) :
    CodedSorting.Construction.Sorting.CommonMSDChunks.space q normal n≤5020*(q.N^2+1)+4*E := by
  have hh : CodedSorting.CommonMSDChunks.chunkSize q≤q.N^2 :=
    Nat.pow_le_pow_left (height_le q) 2
  have hn2 := hn.trans (input_le_square q)
  have hl := local_le q normal E hex (CodedSorting.CommonMSDChunks.chunkSize q) hh
  have hp := CodedSorting.CommonMSDChunks.padded_size_le q n
  have hb := blocks_le q (CodedSorting.CommonMSDChunks.paddedSize q n)
  have hm : max 1 (recordBlocks q (CodedSorting.CommonMSDChunks.paddedSize q n))≤
      3*CodedSorting.CommonMSDChunks.paddedSize q n+1 := by omega
  have hbatch := Nat.mul_le_mul_left (CodedSorting.CommonMSDChunks.chunkCount q n)
    (blocks_le q (CodedSorting.CommonMSDChunks.chunkSize q))
  have hbatch' : CodedSorting.CommonMSDChunks.chunkCount q n*recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)≤
      3*CodedSorting.CommonMSDChunks.paddedSize q n := by
    simpa only [CodedSorting.CommonMSDChunks.paddedSize,Nat.mul_left_comm,Nat.mul_assoc] using hbatch
  unfold CodedSorting.Construction.Sorting.CommonMSDChunks.space
  change max 1 (recordBlocks q (CodedSorting.CommonMSDChunks.paddedSize q n))+
    CodedSorting.CommonMSDChunks.chunkCount q n*recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)+
    CodedSorting.Construction.Sorting.CommonLocalRecursion.space q normal 3 (CodedSorting.CommonMSDChunks.chunkSize q)≤_
  nlinarith only [hl,hp,hm,hbatch',hh,hn2]

theorem directory_le (q : Configuration) (n : ℕ) (hn : n≤q.N) :
    recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)+CodedSorting.CommonMSDChunks.chunkCount q n*
      CommonMSDDirectory.blocks q (CommonMSDParameters.radix q)≤4*q.N^2 := by
  have hc : CodedSorting.CommonMSDChunks.chunkCount q n≤n :=
    CommonLeafGrouping.blockCount_le_of_fits (CodedSorting.CommonMSDChunks.chunk_positive q)
      (Nat.le_mul_of_pos_right n (CodedSorting.CommonMSDChunks.chunk_positive q))
  have hd : CommonMSDDirectory.blocks q (CommonMSDParameters.radix q)≤q.height :=
    CommonLeafGrouping.blockCount_le_of_fits (CommonLeafProgram.block_positive q)
      ((CommonMSDParameters.radix_fields q).trans
        (Nat.le_mul_of_pos_right _ (CommonLeafProgram.block_positive q)))
  have hh := Nat.pow_le_pow_left (height_le q) 2
  have hb := blocks_le q (CodedSorting.CommonMSDChunks.chunkSize q)
  have hm := Nat.mul_le_mul (hc.trans hn) (hd.trans (height_le q))
  change recordBlocks q (q.height^2)≤3*q.height^2 at hb
  unfold CodedSorting.CommonMSDChunks.chunkSize
  nlinarith only [hb,hm,hh]

theorem work_le (q : Configuration) (normal : Normalized q) (E : ℕ)
    (hex : ExchangeBound q normal E) :
    workSize q normal q.N (CommonMSDParameters.radix q)≤5020*(q.N^2+1)+4*E := by
  apply Finset.sup_le
  intro n hn
  have hn' : n≤q.N := by have := Finset.mem_range.mp hn;omega
  apply max_le
  · apply max_le (chunks_le q normal E hex n hn')
    exact (directory_le q n hn').trans (by omega)
  · exact interval_le q normal E hex n hn'

end
end CodedSorting.Construction.Sorting.CommonMSDWorkspaceEnvelope
end WorkspaceEnvelope

section ConcreteWorkspace
/-! A fixed polynomial bounds the actual complete workspace allocation.
The exchange coefficient comes from the Construction machine's proved volume-scan
workspace bound. The deliberately coarse degree five is only a disk
capacity envelope; it is not used in the improved I/O estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace
open CommonSortingNormalization RecursiveParameters CommonMSDGlobalAllocation
noncomputable section
attribute [local irreducible] CommonSortingSpaceBudget.coefficient

def exchangeCoefficient : ℕ := CommonSortingSpaceBudget.coefficient
def coefficient : ℕ := 5020+4*exchangeCoefficient
def degree : ℕ := 5

theorem coefficient_pos : 0<coefficient := by unfold coefficient;omega
theorem degree_two : 2≤degree := by decide

private theorem square_margin (N : ℕ) : N^2+1≤(N+1)^2 := by
  calc
    N^2+1 ≤ N^2+1+2*N := Nat.le_add_right _ _
    _ = (N+1)^2 := by ring

theorem exchange_le (q : Configuration) (normal : Normalized q) :
    CommonMSDWorkspaceEnvelope.ExchangeBound q normal (exchangeCoefficient*(q.N+1)^5) := by
  intro n hn hlarge
  have hs := CommonSortingSpaceBudget.local_space q normal n hlarge
  have hbase : n+1≤(q.N+1)^2 :=
    (Nat.add_le_add_right hn 1).trans (square_margin q.N)
  have hp : (q.N+1)^2≤(q.N+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  exact hs.trans (Nat.mul_le_mul_left exchangeCoefficient (hbase.trans hp))

/-- The finite maximum over every public job size is bounded using the
actual local allocation, including resident leaves and directories. -/
theorem work_le (q : Configuration) (normal : Normalized q) :
    workSize q normal q.N (CommonMSDParameters.radix q)≤coefficient*(q.N+1)^degree := by
  have hw := CommonMSDWorkspaceEnvelope.work_le q normal _ (exchange_le q normal)
  have hbase : q.N^2+1≤(q.N+1)^2 := square_margin q.N
  have hp : (q.N+1)^2≤(q.N+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm := Nat.mul_le_mul_left 5020 (hbase.trans hp)
  unfold coefficient degree
  nlinarith only [hw,hm]

end
end CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace
end ConcreteWorkspace
