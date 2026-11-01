import CodedSorting.Sorting.Radix.Partition.Framework.Pass
import CodedSorting.Sorting.Radix.SemanticCost

/-! Concrete chunk sorter instance and names for the shared MSD node proof. -/
namespace CodedSorting.Construction.Sorting.CommonMSDNodePass
noncomputable instance : CodedSorting.RadixNode.ChunkSorter
    CodedSorting.Construction.RecursiveParameters.Normalized where
  space := CodedSorting.Construction.Sorting.CommonMSDChunks.space
  charge := CodedSorting.Construction.Sorting.CommonMSDChunks.charge
  program := CodedSorting.Construction.Sorting.CommonMSDChunks.program
  program_charge_le := CodedSorting.Construction.Sorting.CommonMSDChunks.program_charge_le
end CodedSorting.Construction.Sorting.CommonMSDNodePass

namespace CodedSorting.Construction.Sorting.CommonMSDNodePass
open CodedSorting.CommonSortingNormalization
export CodedSorting.RadixNode.Pass (
  directory Resources chunks withChunks code directoryCharge
  Ready directories_raw raw_with_chunks raw_complete code_safe code_cost_le
  code_length_le complete)
noncomputable def charge (q : Configuration) (n K : ℕ) : ℕ := CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n+directoryCharge q n K
noncomputable def lengthBound (q : Configuration) (n K : ℕ) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n+
    7*CommonMSDRowDirectoryBatch.rowBlocks q (CommonMSDChunkRows.row q n)
      (List.finRange (CodedSorting.CommonMSDChunks.chunkCount q n))+
    (2*CommonMSDDirectory.blocks q K+2)*CodedSorting.CommonMSDChunks.chunkCount q n
end CodedSorting.Construction.Sorting.CommonMSDNodePass

namespace CodedSorting.Construction.Sorting.CommonMSDNodeController
open CodedSorting.CommonSortingNormalization
export CodedSorting.RadixNode.Controller (
  Tag tagCount tagEquiv body terminal advance
  code done next body_safe code_safe code_at
  done_at next_at code_length_lt)
noncomputable def chosenStride (q : Configuration) (n K C : ℕ) :=
  max (CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q n K+1) (CommonMSDGatherCapacity.chosenStride q C)
end CodedSorting.Construction.Sorting.CommonMSDNodeController

namespace CodedSorting.Construction.Sorting.CommonMSDNodeController
export CodedSorting.RadixNode.Controller (
  routine routine_fits)
end CodedSorting.Construction.Sorting.CommonMSDNodeController

namespace CodedSorting.Construction.Sorting.CommonMSDNodeTrace
export CodedSorting.RadixNode.Trace (
  nextTag_setPC raw_some next_some read_payload copy_payload read_next
  copy_next gather_trace_from)
namespace G
export CodedSorting.RadixNode.Trace.G (Tag ready copying)
end G
end CodedSorting.Construction.Sorting.CommonMSDNodeTrace

namespace CodedSorting.Construction.Sorting.CommonMSDNodeHead
export CodedSorting.RadixNode.Head (
  prepend trace)
end CodedSorting.Construction.Sorting.CommonMSDNodeHead

