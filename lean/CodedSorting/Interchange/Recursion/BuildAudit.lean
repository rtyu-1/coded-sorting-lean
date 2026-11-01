import CodedSorting.Interchange.Recursion.Build
import CodedSorting.Interchange.Recursion.Workspace

/-! Axiom endpoint for the actual recursive Construction builder and its terminating
paths. The audit includes numerical-condition projections, actual-child
descent, concrete branch code/charge provenance, and controlled execution.
It does not assert uniform workspace or the final asymptotic cost bound. -/

namespace CodedSorting.Construction.RecursiveBuildAudit

#print axioms RecursiveBuildConditions.zero_leaf
#print axioms RecursiveBuildConditions.small_leaf
#print axioms RecursiveBuildConditions.large_node

#print axioms RecursiveDescent.next_child_depth
#print axioms RecursiveDescent.next_child_width_eq
#print axioms RecursiveDescent.next_child_width_lt
#print axioms RecursiveDescent.next_child_volume

#print axioms RecursiveBuild.leaf
#print axioms RecursiveBuild.build
#print axioms RecursiveBuild.children
#print axioms RecursiveBuild.build_zero
#print axioms RecursiveBuild.build_small
#print axioms RecursiveBuild.build_node
#print axioms RecursiveBuild.build_zero_instructions
#print axioms RecursiveBuild.build_small_instructions
#print axioms RecursiveBuild.build_node_instructions
#print axioms RecursiveBuild.build_node_charge
#print axioms RecursiveBuild.build_proof_independent
#print axioms RecursiveBuild.complete

#print axioms RecursiveBuildPath.nextCall_width_lt
#print axioms RecursiveBuildPath.path_depth
#print axioms RecursiveBuildPath.path_length_le
#print axioms RecursiveBuildPath.path_width_le
#print axioms RecursiveBuildPath.path_width_lt_of_nonempty
#print axioms RecursiveBuildPath.path_length_eq_of_zero

end CodedSorting.Construction.RecursiveBuildAudit
