import CodedSorting.NetworkCoding.Routing.StrictGap
import CodedSorting.Circuit.Local.ConcreteLocalProgram

/-! Audits only the conditional endpoint and the concrete physical binding.
The final theorem-2.2 audit must additionally import its discharged inputs. -/

#print axioms CodedSorting.Construction.ConcreteLocalProgram.scatterShape
#print axioms CodedSorting.Construction.ConcreteLocalProgram.scatter_frames
#print axioms CodedSorting.Construction.ConcreteLocalProgram.prefix_frames
#print axioms CodedSorting.Construction.ConcreteLocalProgram.suffix_frames
#print axioms CodedSorting.Construction.ConcreteLocalProgram.concrete_decomposition
#print axioms CodedSorting.Construction.ConcreteLocalProgram.scatter_safe
#print axioms CodedSorting.Construction.ConcreteLocalProgram.forward_correct
#print axioms CodedSorting.Construction.ConcreteLocalProgram.middle_correct
#print axioms CodedSorting.Construction.SimpleNetworkSeparation.simplePhysicalEdgeEquiv
#print axioms CodedSorting.Construction.SimpleNetworkSeparation.simple_coding_capacity
#print axioms CodedSorting.Construction.SimpleNetworkSeparation.simple_routing_capacity_le
#print axioms CodedSorting.Construction.SimpleNetworkSeparation.simple_network_separation
#print axioms CodedSorting.Construction.SimpleNetworkSeparation.simple_finite_strict_block
