import CodedSorting.Interchange.OneLevel.Exchange
import CodedSorting.Interchange.OneLevel.Allocation

/-! Axiom audit of the concrete one-level machine program and the actual
child, space and charge interfaces used by the subsequent recursion. -/

#print axioms CodedSorting.Construction.OneLevelChildren.child_count
#print axioms CodedSorting.Construction.ExchangeSpecialization.radix_prime
#print axioms CodedSorting.Construction.ExchangeSpecialization.selected_endpoint
#print axioms CodedSorting.Construction.MachineNetworkActualEdges.networkPrograms
#print axioms CodedSorting.Construction.MachineNetworkActualEdges.network_charge_le
#print axioms CodedSorting.Construction.StreamParentProgram.parentProgram
#print axioms CodedSorting.Construction.OneLevelAssembly.program
#print axioms CodedSorting.Construction.OneLevelExchange.program
#print axioms CodedSorting.Construction.OneLevelExchange.canonicalProgram
#print axioms CodedSorting.Construction.OneLevelExchange.child_smaller
#print axioms CodedSorting.Construction.OneLevelExchange.child_volume
#print axioms CodedSorting.Construction.OneLevelExchange.child_volume_div
#print axioms CodedSorting.Construction.OneLevelExchange.charge_le
#print axioms CodedSorting.Construction.OneLevelExchange.complete
#print axioms CodedSorting.Construction.OneLevelAllocation.canonicalSetup
#print axioms CodedSorting.Construction.OneLevelAllocation.canonicalSetup_room
#print axioms CodedSorting.Construction.OneLevelAllocation.reservedBlocks_le
#print axioms CodedSorting.Construction.OneLevelAllocation.boundedSetup
