import CodedSorting.Interchange.Fields.ExchangeAudit
import CodedSorting.Sorting.Theorem31.Proof

/-! Final sorting audit in the explicitly stated public-program/public-index
I/O semantics. The imported exchange audit checks the actual Construction exchange;
the declarations below connect it to allocation, instruction capacity,
all-input physical execution, total cost, and all numerical memory ranges.

The normal-memory branch uses the atomic-resident controller. The small-memory
branches use the two-buffer Stage interpreter with immutable public programs
chosen before the arbitrary input and scratch state. In the narrow-word branch,
the public instruction-list position is not stored in the two payload buffers.
These theorems do not identify that public-index model with a fixed-control
machine charging every mutable control bit to the same resident memory bound.
The endpoint preserves this model scope rather than adding such an equivalence.
-/

namespace CodedSorting.Construction.Sorting.SortingImplementationAudit

#print axioms CommonSortingExchangeRate.actual_shape_rate
#print axioms CommonMSDConcreteWorkspace.work_le
#print axioms CommonMSDGlobalDiskCapacity.endAddress_polynomial
#print axioms CommonMSDGlobalControlCapacity.control_polynomial
#print axioms CommonIntegerAllInputCapacity.disk_capacity
#print axioms CommonIntegerAllInputCapacity.control
#print axioms CommonIntegerAllInputCapacity.fits

#print axioms CommonIntegerAllInputRun.complete
#print axioms CommonIntegerSortingRate.complete_cost
#print axioms CommonIntegerAllInputPhysical.algorithm
#print axioms CommonIntegerAllInputPhysical.complete

#print axioms GeneralWordNormalSorting.configuration
#print axioms GeneralWordNormalSorting.parameters
#print axioms GeneralWordNormalSorting.complete
#print axioms GeneralWordSorting.factor_eq
#print axioms GeneralWordSorting.coefficient_positive
#print axioms GeneralWordSorting.normal_complete
#print axioms GeneralWordSorting.small_complete
#print axioms GeneralWordSorting.complete

end CodedSorting.Construction.Sorting.SortingImplementationAudit
