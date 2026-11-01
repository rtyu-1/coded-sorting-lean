import CodedSorting.Sorting.Radix.Partition.Pass
import CodedSorting.Sorting.Radix.Partition.Framework.Cost

/-! Correctness of the concrete MSD node, instantiated from the shared proof. -/
namespace CodedSorting.Construction.Sorting.CommonMSDNodeComplete
export CodedSorting.RadixNode.Complete (
  ready_of_before observed_correct gather_correct gather_data encoded_erase ready_erase
  package_result compose complete_from_prepared complete)
end CodedSorting.Construction.Sorting.CommonMSDNodeComplete

