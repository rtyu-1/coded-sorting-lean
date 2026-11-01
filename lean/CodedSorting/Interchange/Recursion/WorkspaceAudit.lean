import CodedSorting.Interchange.Recursion.Resources
import CodedSorting.Interchange.Recursion.Workspace

/-! Checks the logical axioms used by the recursive workspace construction: temporary space, child addresses, reuse between successive children, bounds independent of recursion depth, and allocation for every recursive call. 



-/

namespace CodedSorting.Construction.RecursiveWorkspaceAudit

#print axioms RecursiveWorkspaceBudget.space_zero
#print axioms RecursiveWorkspaceBudget.space_small
#print axioms RecursiveWorkspaceBudget.space_node
#print axioms RecursiveWorkspaceBudget.space_ge_count
#print axioms RecursiveWorkspaceBudget.space_ge_node_reserve

#print axioms RecursiveWorkspaceAddress.requiredLimit_eq
#print axioms RecursiveWorkspaceAddress.next_child_buffer
#print axioms RecursiveWorkspaceAddress.next_child_limit
#print axioms RecursiveWorkspaceAddress.next_child_volume
#print axioms RecursiveWorkspaceAddress.next_child_source_separate
#print axioms RecursiveWorkspaceAddress.next_child_allocation
#print axioms RecursiveWorkspaceAddress.sibling_buffer_eq
#print axioms RecursiveWorkspaceAddress.sibling_limit_eq

#print axioms RecursiveWorkspaceBounds.space_le_scan_padding
#print axioms RecursiveWorkspaceBounds.space_le_scan

#print axioms RecursiveWorkspace.shortWidth_family
#print axioms RecursiveWorkspace.ready_of_space
#print axioms RecursiveWorkspace.program
#print axioms RecursiveWorkspace.complete

#print axioms RecursiveWorkspaceProgram.room_of_linear
#print axioms RecursiveWorkspaceProgram.ready_of_linear
#print axioms RecursiveWorkspaceProgram.program
#print axioms RecursiveWorkspaceProgram.program_instructions
#print axioms RecursiveWorkspaceProgram.program_charge
#print axioms RecursiveWorkspaceProgram.complete

end CodedSorting.Construction.RecursiveWorkspaceAudit
