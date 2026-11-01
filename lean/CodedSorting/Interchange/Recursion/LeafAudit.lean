import CodedSorting.Interchange.Recursion.Build

/-! Final axiom audit for stage 2, step 2: actual resident and buffered
Construction leaves, the public numeric selector, and its selected-child adapter.
The premises include resident-bank fit, disk workspace, and PC capacity.
This does not construct a recursive tree or prove its global space bound. -/

#print axioms CodedSorting.Construction.RecursiveResidentLeaf.program
#print axioms CodedSorting.Construction.RecursiveResidentLeaf.raw_correct
#print axioms CodedSorting.Construction.RecursiveResidentLeaf.code_cost
#print axioms CodedSorting.Construction.RecursiveResidentLeaf.code_length
#print axioms CodedSorting.Construction.RecursiveResidentLeaf.program_instructions
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.program
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.code_correct
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.code_cost
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.charge_le
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.program_instructions
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.leafFits_conditions
#print axioms CodedSorting.Construction.RecursiveLeafProgram.resident_fit
#print axioms CodedSorting.Construction.RecursiveLeafProgram.buffered_fit
#print axioms CodedSorting.Construction.RecursiveLeafProgram.program
#print axioms CodedSorting.Construction.RecursiveLeafProgram.program_resident_instructions
#print axioms CodedSorting.Construction.RecursiveLeafProgram.program_buffered_instructions
#print axioms CodedSorting.Construction.RecursiveLeafProgram.program_charge_le
#print axioms CodedSorting.Construction.RecursiveLeafProgram.complete
#print axioms CodedSorting.Construction.RecursiveLeafProgram.actualChildProgram
#print axioms CodedSorting.Construction.RecursiveLeafProgram.actualChildProgram_charge_le
