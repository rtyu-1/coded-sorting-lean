import CodedSorting.Interchange.Recursion.Endpoint
import CodedSorting.Interchange.Recursion.Workspace

/-! Checks the logical axioms used by the recursive program's cost and instruction-count theorems. These theorems connect child-call costs to the integer recurrence and improved exponent, and then apply them to the program constructed from the initial workspace parameters. 



-/

namespace CodedSorting.Construction.RecursiveCostAudit

#print axioms RecursiveCostNode.nextProgram_charge_le
#print axioms RecursiveCostNode.build_node_charge_le
#print axioms RecursiveCostNode.child_sum_le
#print axioms RecursiveCostNode.build_node_uniform_charge_le

#print axioms RecursiveCostRate.exists_rate
#print axioms RecursiveCostRate.rateConstant_nonneg
#print axioms RecursiveCostRate.costBound_le_rate
#print axioms RecursiveCostRate.costBound_scaled
#print axioms RecursiveCostRate.block_le_cutoff

#print axioms RecursiveCost.leaf_charge_le
#print axioms RecursiveCost.build_charge_le
#print axioms RecursiveCost.build_cost_le
#print axioms RecursiveCost.build_length_le
#print axioms RecursiveCost.complete

#print axioms RecursiveCostBounds.build_charge_le_rate
#print axioms RecursiveCostBounds.build_cost_le_rate
#print axioms RecursiveCostBounds.build_length_le_rate
#print axioms RecursiveCostBounds.complete_rate

#print axioms RecursiveCostProgram.program_charge_le
#print axioms RecursiveCostProgram.program_cost_le
#print axioms RecursiveCostProgram.program_length_le
#print axioms RecursiveCostProgram.program_charge_le_rate
#print axioms RecursiveCostProgram.program_cost_le_rate
#print axioms RecursiveCostProgram.program_length_le_rate
#print axioms RecursiveCostProgram.complete
#print axioms RecursiveCostProgram.complete_rate

end CodedSorting.Construction.RecursiveCostAudit
