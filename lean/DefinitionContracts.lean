import CodedSorting

/-! Direct checks of the mathematical meaning of the bottom-level operations
used by Theorem 3.1. These supplement the source-level correspondence guide. -/
set_option autoImplicit false
namespace CodedSorting.DefinitionContracts

open Normalization in
/-- A zero-transfer physical primitive preserves every disk block. -/
theorem zero_primitive_preserves_disk {L b B D : ℕ} {W : Type*}
    (h : b≤B) (padding : W) (cmd : PhysicalCommand L b D W)
    (s : PhysicalState L B D W) (hc : primitiveCost cmd=0) :
    (primitiveStep h padding cmd s).disk=s.disk := by
  cases cmd <;> simp_all [primitiveCost,primitiveStep]

open TwoWordBlockLift in
/-- A zero-transfer operation on the two-buffer machine preserves its disk. -/
theorem zero_two_buffer_preserves_disk {B : ℕ} {W : Type*} [DecidableEq W]
    (cmd : Command B W) (s : State B W) (hc : cost cmd=0) :
    (step cmd s).disk=s.disk := by
  cases cmd <;> simp_all [cost,step]

open CommonSortingNormalization in
/-- All normal-machine state fields and the address port appear in the count. -/
theorem resident_count (q : Configuration) :
    Fintype.card (ResidentIndex q)=q.ramWords+q.B+q.block+4*q.digits+3 := by
  simp only [ResidentIndex,Fintype.card_sum,Fintype.card_fin]
  omega

/-- The displayed complexity factor uses the current exponent and real division. -/
theorem sorting_factor (N M B : ℕ) :
    Construction.Sorting.GeneralWordSorting.factor N M B =
      1+Real.log (N : ℝ)/(Real.log ((M : ℝ)/B)^((1:ℝ)-(3:ℝ)/200000)*
        Real.log (M : ℝ)^((3:ℝ)/200000)) := by
  rw [Construction.Sorting.GeneralWordSorting.factor_eq]
  norm_num [Construction.Sorting.GeneralWordNormalSorting.factor,Construction.epsilon]

end CodedSorting.DefinitionContracts

#print axioms CodedSorting.DefinitionContracts.zero_primitive_preserves_disk
#print axioms CodedSorting.DefinitionContracts.zero_two_buffer_preserves_disk
#print axioms CodedSorting.DefinitionContracts.resident_count
#print axioms CodedSorting.DefinitionContracts.sorting_factor
