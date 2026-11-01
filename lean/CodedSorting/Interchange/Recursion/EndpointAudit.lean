import CodedSorting.Interchange.Recursion.ConfiguredEndpoint

/-! Axiom endpoint for the canonical Construction recursive exchange with concrete
machine parameters. This audit covers selected leaf parameters, exact root
layout, fixed disk and program-counter capacity, descendant readiness,
explicit PC initialization, and the same controlled run with the improved
fee bound. It does not assert arbitrary-shape exchange or full sorting. -/

namespace CodedSorting.Construction.RecursiveEndpointAudit

#print axioms RecursiveParameters.chosenBase_bounds
#print axioms RecursiveParameters.chosenBase_log_sandwich
#print axioms RecursiveParameters.chosenBase_fit
#print axioms RecursiveParameters.chosenBase_startup
#print axioms RecursiveParameters.cutoff_child
#print axioms RecursiveParameters.leafParameters
#print axioms RecursiveParameters.normalized_of_inventory

#print axioms RecursiveRootLayout.root_volume
#print axioms RecursiveRootLayout.root_shape
#print axioms RecursiveRootLayout.root_source_separate
#print axioms RecursiveRootLayout.root_space
#print axioms RecursiveRootLayout.root_scan_le
#print axioms RecursiveRootLayout.root_count_le
#print axioms RecursiveRootLayout.stream_power_le_words
#print axioms RecursiveRootLayout.root_limit_bound

#print axioms RecursiveCapacity.costBound_le_coarse
#print axioms RecursiveCapacity.costBound_le_polynomial_or_empty
#print axioms RecursiveCapacity.absorb
#print axioms RecursiveCapacity.addressExponent_ge_three
#print axioms RecursiveCapacity.capacity_fits
#print axioms RecursiveCapacity.costBound_fits

#print axioms RecursiveResources.root_disk_fits
#print axioms RecursiveResources.root_code_fits
#print axioms RecursiveResources.ready

#print axioms RecursiveEndpoint.program_instructions
#print axioms RecursiveEndpoint.program_charge_fits
#print axioms RecursiveEndpoint.program_length_fits
#print axioms RecursiveEndpoint.program_charge_le_rate
#print axioms RecursiveEndpoint.program_cost_le_rate
#print axioms RecursiveEndpoint.program_length_le_rate
#print axioms RecursiveEndpoint.initialState_disk
#print axioms RecursiveEndpoint.initialState_pc
#print axioms RecursiveEndpoint.complete

#print axioms RecursiveMachine.configuration
#print axioms RecursiveMachine.reader
#print axioms RecursiveMachine.normalized
#print axioms RecursiveMachine.exponent_sufficient

#print axioms RecursiveConfiguredEndpoint.complete

end CodedSorting.Construction.RecursiveEndpointAudit
