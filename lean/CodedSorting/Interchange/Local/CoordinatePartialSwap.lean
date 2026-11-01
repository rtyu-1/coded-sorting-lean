import Std

/-!
# Coordinate partial swaps

This module verifies the elementary permutation of two coordinate arrays that
exchanges exactly the coordinates selected by a Boolean mask.  It establishes
the algebraic involution and the behavior of selected/unselected coordinates.
It does not establish an I/O implementation, rank cost, or a change of basis.
-/

namespace CodedSorting.Construction

variable {ι α : Type}

def coordinatePartialSwap (mask : ι → Bool)
    (state : (ι → α) × (ι → α)) : (ι → α) × (ι → α) :=
  (fun i => if mask i then state.2 i else state.1 i,
   fun i => if mask i then state.1 i else state.2 i)

theorem coordinatePartialSwap_selected (mask : ι → Bool)
    (state : (ι → α) × (ι → α)) (i : ι) (h : mask i = true) :
    (coordinatePartialSwap mask state).1 i = state.2 i ∧
    (coordinatePartialSwap mask state).2 i = state.1 i := by
  simp [coordinatePartialSwap, h]

theorem coordinatePartialSwap_unselected (mask : ι → Bool)
    (state : (ι → α) × (ι → α)) (i : ι) (h : mask i = false) :
    (coordinatePartialSwap mask state).1 i = state.1 i ∧
    (coordinatePartialSwap mask state).2 i = state.2 i := by
  simp [coordinatePartialSwap, h]

theorem coordinatePartialSwap_involutive (mask : ι → Bool)
    (state : (ι → α) × (ι → α)) :
    coordinatePartialSwap mask (coordinatePartialSwap mask state) = state := by
  apply Prod.ext
  · funext i
    cases h : mask i <;> simp [coordinatePartialSwap, h]
  · funext i
    cases h : mask i <;> simp [coordinatePartialSwap, h]

theorem coordinatePartialSwap_empty (state : (ι → α) × (ι → α)) :
    coordinatePartialSwap (fun _ => false) state = state := by
  apply Prod.ext <;> funext i <;> simp [coordinatePartialSwap]

theorem coordinatePartialSwap_full (state : (ι → α) × (ι → α)) :
    coordinatePartialSwap (fun _ => true) state = (state.2, state.1) := by
  apply Prod.ext <;> funext i <;> simp [coordinatePartialSwap]

theorem coordinatePartialSwap_commute (first second : ι → Bool)
    (state : (ι → α) × (ι → α)) :
    coordinatePartialSwap first (coordinatePartialSwap second state) =
    coordinatePartialSwap second (coordinatePartialSwap first state) := by
  apply Prod.ext
  · funext i
    cases h₁ : first i <;> cases h₂ : second i <;>
      simp [coordinatePartialSwap, h₁, h₂]
  · funext i
    cases h₁ : first i <;> cases h₂ : second i <;>
      simp [coordinatePartialSwap, h₁, h₂]

end CodedSorting.Construction
