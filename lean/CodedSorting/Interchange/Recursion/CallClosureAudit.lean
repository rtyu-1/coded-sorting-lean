import CodedSorting.Interchange.Recursion.CallBridge

/-! Final axiom audit for stage 2, step 1: admissible actual-call closure,
explicit allocation conditions, and an instruction-preserving adapter.
This does not assert a complete recursive tree or its global space bound. -/

#print axioms CodedSorting.Construction.RecursiveCallShape.depthCall_shape
#print axioms CodedSorting.Construction.RecursiveCallShape.parentForm_eq
#print axioms CodedSorting.Construction.RecursiveCallShape.actual_child_depth
#print axioms CodedSorting.Construction.RecursiveCallShape.next_parent_eq
#print axioms CodedSorting.Construction.RecursiveCallShape.no_depth_one_of_width_lt
#print axioms CodedSorting.Construction.RecursiveCallAddress.child_source_end_le
#print axioms CodedSorting.Construction.RecursiveCallAddress.child_source_after_parent_buffer
#print axioms CodedSorting.Construction.RecursiveCallAddress.childAllocation
#print axioms CodedSorting.Construction.RecursiveCallAddress.canonical_reserve_iff
#print axioms CodedSorting.Construction.RecursiveCallAddress.atLimitSetup
#print axioms CodedSorting.Construction.RecursiveCallAddress.atLimitSetup_room
#print axioms CodedSorting.Construction.RecursiveCallBridge.actualSplit
#print axioms CodedSorting.Construction.RecursiveCallBridge.nextSetup
#print axioms CodedSorting.Construction.RecursiveCallBridge.nextSetup_parent_eq
#print axioms CodedSorting.Construction.RecursiveCallBridge.nextSetup_room
#print axioms CodedSorting.Construction.RecursiveCallBridge.nextProgram
#print axioms CodedSorting.Construction.RecursiveCallBridge.nextProgram_instructions
#print axioms CodedSorting.Construction.RecursiveCallBridge.nextProgram_charge
#print axioms CodedSorting.Construction.RecursiveCallBridge.actualNextProgram
