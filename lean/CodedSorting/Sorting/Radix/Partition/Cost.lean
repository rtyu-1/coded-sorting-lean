import CodedSorting.Sorting.Radix.Partition.Complete
import CodedSorting.Sorting.Radix.LocalGroups.Local

namespace CodedSorting.Construction.Sorting.CommonMSDNodeChargeTrace
export CodedSorting.RadixNode.ChargeTrace (
  gatherCharge compose innerCharge complete)
end CodedSorting.Construction.Sorting.CommonMSDNodeChargeTrace

section PassCost
/-! The actual preparation and persisted metadata scans retain the
local sorting rate at every nonleaf MSD node. -/
set_option autoImplicit false
namespace CodedSorting.Construction.Sorting.CommonMSDNodePass
open CommonSortingNormalization CodedSorting.Construction.Sorting.CommonMSDChunks CodedSorting.Construction.Sorting.CommonLocalBudgetRate
noncomputable section

theorem directory_charge_scaled (q : Configuration) (n : ℕ) (hn : q.height^2≤n) :
    directoryCharge q n (CommonMSDParameters.radix q)*q.block≤39*n := by
  have hv := CommonMSDChunkRows.volume_eq q n
  change ((List.finRange (CodedSorting.CommonMSDChunks.chunkCount q n)).map (fun c => (CommonMSDChunkRows.row q n c).length)).sum=n at hv
  rw [←List.ofFn_eq_map,List.sum_ofFn] at hv
  have h := CommonMSDDirectoryCost.scan_bound q n hn
    (fun c => (CommonMSDChunkRows.row q n c).length) le_rfl hv.le
  have he : directoryCharge q n (CommonMSDParameters.radix q)=
      ∑ c : Fin (CodedSorting.CommonMSDChunks.chunkCount q n),CommonMSDDirectoryCost.rowCharge q
        (CommonMSDParameters.radix q) (CommonMSDChunkRows.row q n c).length := by
    unfold directoryCharge CommonMSDRowDirectoryBatch.rowBlocks CommonMSDDirectoryCost.rowCharge
    rw [←List.ofFn_eq_map,List.sum_ofFn,Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  rw [he]
  exact h

theorem integer_charge_bound (q : Configuration) (n : ℕ) (hn : q.height^2≤n)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block) :
    charge q n (CommonMSDParameters.radix q)*q.block≤
      (4*(22194000000*(GlobalSortingBound.localRate q.height K
        (Real.log ((q.height : ℝ)/q.block)) tau+2))+168)*n := by
  have hp := CodedSorting.Construction.Sorting.CommonMSDChunks.integer_charge_bound q n hn hnormal
  have hd := directory_charge_scaled q n hn
  unfold charge
  nlinarith only [hp,hd]

end
end CodedSorting.Construction.Sorting.CommonMSDNodePass
end PassCost

section Rate
/-! A size-only budget for the actual MSD node. It includes local row
sorting, persisted directories, the complete gather, and both interval
copies. The radix accounts for directory fields as well as data blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.Construction.Sorting.CommonMSDNodeRate
open CommonSortingNormalization CommonRecordProgram WordControl
open CodedSorting.Construction.Sorting.CommonMSDSemanticCost
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension 

def nodeBudget (q : Configuration) (n : ℕ) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDNodePass.charge q n (CommonMSDParameters.radix q)+48*n/q.block+
    12*(recordBlocks q n+1)

/-- The actual fragment enumeration has total payload exactly three words
per record; all its metadata reads are included in this bound. -/
theorem gather_scaled (q : Configuration) {n : ℕ}
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (f : Records q n) (source directory target D : ℕ) (hn : q.height^2≤n) :
    (CommonMSDGatherComparison.directoryCharge q
      (CommonMSDNodeLayout.layout q n (CommonMSDParameters.radix q) source directory target)
      (List.finRange (CommonMSDParameters.radix q*CodedSorting.CommonMSDChunks.chunkCount q n))+
    CommonMSDGatherSequence.charge q (CommonMSDNodeLayout.count q key f) D
      (List.finRange (CommonMSDParameters.radix q*CodedSorting.CommonMSDChunks.chunkCount q n)))*q.block≤48*n := by
  apply CommonMSDGatherEstimate.scan_bound q _ _ D _ n hn
  · simp only [List.length_finRange,CodedSorting.CommonMSDChunks.chunkCount,CodedSorting.CommonMSDChunks.chunkSize]
    exact Nat.le_of_eq (Nat.mul_comm _ _)
  · exact (CommonMSDNodeLayout.total_count q key f).le

theorem gather_le (q : Configuration) {n : ℕ}
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (f : Records q n) (source directory target D : ℕ) (hn : q.height^2≤n) :
    CommonMSDGatherComparison.directoryCharge q
      (CommonMSDNodeLayout.layout q n (CommonMSDParameters.radix q) source directory target)
      (List.finRange (CommonMSDParameters.radix q*CodedSorting.CommonMSDChunks.chunkCount q n))+
    CommonMSDGatherSequence.charge q (CommonMSDNodeLayout.count q key f) D
      (List.finRange (CommonMSDParameters.radix q*CodedSorting.CommonMSDChunks.chunkCount q n))≤48*n/q.block :=
  (Nat.le_div_iff_mul_le (CommonLeafProgram.block_positive q)).2
    (gather_scaled q key f source directory target D hn)

theorem prepare_scaled (q : Configuration) (n : ℕ) (hn : q.height^2≤n)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block) :
    CodedSorting.Construction.Sorting.CommonMSDNodePass.charge q n (CommonMSDParameters.radix q)*q.block≤
      (4*localRate q+168)*n :=
  CodedSorting.Construction.Sorting.CommonMSDNodePass.integer_charge_bound q n hn hnormal

theorem nodeBudget_scaled (q : Configuration) (n : ℕ) (hn : q.height^2≤n)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block) :
    nodeBudget q n*q.block≤(4*localRate q+288)*n := by
  have hp := prepare_scaled q n hn hnormal
  have hg := Nat.div_mul_le_self (48*n) q.block
  have ht := CodedSorting.Construction.Sorting.CommonMSDIntervalLocalRate.transport_scaled q n
  have hb : q.block≤n := (CodedSorting.Construction.Sorting.CommonMSDChunks.block_le_chunk q).trans hn
  unfold nodeBudget
  nlinarith only [hp,hg,ht,hb]

/-- The same coefficient works for every leaf, including the empty one. -/
theorem local_scaled (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (n : ℕ) (hn : n≤q.height^2) :
    CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n*q.block≤(localRate q+36)*(n+q.block) := by
  have hl := actual_local_charge q hnormal n hn
  have ht := CodedSorting.Construction.Sorting.CommonMSDIntervalLocalRate.transport_scaled q n
  unfold CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge
  nlinarith only [hl,ht]

/-- Any actual inner charge below the preparation and gather budgets
retains the public node budget after extraction and reinsertion. -/
theorem interval_le (q : Configuration) (n O inner : ℕ)
    (hi : inner≤CodedSorting.Construction.Sorting.CommonMSDNodePass.charge q n (CommonMSDParameters.radix q)+48*n/q.block) :
    CommonIntervalAdapter.charge q n O inner≤nodeBudget q n :=
  (CommonIntervalAdapter.charge_le q n O inner).trans
    (Nat.add_le_add_right hi _)

end
end CodedSorting.Construction.Sorting.CommonMSDNodeRate
end Rate

section ChargeRate
/-! The exact charge of the constructed node trace is bounded by the
size-only budget used in the full recursion. No histogram or successful
execution is an input to these bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.Construction.Sorting.CommonMSDNodeChargeRate
open CommonSortingNormalization CommonRecordProgram WordControl CodedSorting.Construction.RecursiveParameters
open CodedSorting.Construction.Sorting.CommonMSDNodeChargeTrace CodedSorting.Construction.Sorting.CommonMSDNodeRate
noncomputable section
attribute [local irreducible] CodedSorting.Construction.RecursiveParameters.Normalized
  CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension 
  CodedSorting.Construction.Sorting.CommonMSDNodePass.code CodedSorting.CommonMSDChunks.operation

theorem gather_le (q : Configuration) {n : ℕ}
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (source directory target : ℕ) (f : Records q n) (hn : q.height^2≤n) :
    gatherCharge q key source directory target f≤48*n/q.block :=
  CodedSorting.Construction.Sorting.CommonMSDNodeRate.gather_le q key f source directory target 0 hn

theorem inner_le (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normalized q} {n : ℕ}
    (r : CodedSorting.Construction.Sorting.CommonMSDNodePass.Resources q hnormal n (CommonMSDParameters.radix q))
    (hfit : (CommonMSDParameters.radix q*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (target : ℕ) (f : Records q n) (hn : q.height^2≤n) :
    innerCharge q reader r hfit key target f≤
      CodedSorting.Construction.Sorting.CommonMSDNodePass.charge q n (CommonMSDParameters.radix q)+48*n/q.block :=
  Nat.add_le_add (CodedSorting.Construction.Sorting.CommonMSDNodePass.code_cost_le q reader r hfit key)
    (gather_le q key r.source (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q r.buffer) target
      (CodedSorting.CommonMSDChunks.operation q n f) hn)

theorem interval_le (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normalized q} {n : ℕ}
    (r : CodedSorting.Construction.Sorting.CommonMSDNodePass.Resources q hnormal n (CommonMSDParameters.radix q))
    (hfit : (CommonMSDParameters.radix q*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (O target : ℕ) (f : Records q n) (hn : q.height^2≤n) :
    CommonIntervalAdapter.charge q n O (innerCharge q reader r hfit key target f)≤nodeBudget q n :=
  CodedSorting.Construction.Sorting.CommonMSDNodeRate.interval_le q n O _ (inner_le q reader r hfit key target f hn)

end
end CodedSorting.Construction.Sorting.CommonMSDNodeChargeRate
end ChargeRate
