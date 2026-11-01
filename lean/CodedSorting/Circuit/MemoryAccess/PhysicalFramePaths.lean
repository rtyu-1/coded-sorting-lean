import CodedSorting.Circuit.Labels.FiniteInterpretation
import Mathlib.Algebra.BigOperators.Fin
import CodedSorting.Circuit.MemoryAccess.PhysicalFramePathData

section FiniteFrameNesting
/-! The small algebraic meaning of the frame-inclusion check. No enumeration
of line membership is needed for chronological projection nesting. -/

namespace CodedSorting.Construction.PhysicalFramePaths
open scoped BigOperators
open FiniteCertificate IntegerProjection

theorem eight_fold_sum (f : Nat → Int) :
    (List.range 8).foldl (fun s k => s + f k) 0 = ∑ i : Fin 8, f i.val := by
  simp [List.range_succ, Fin.sum_univ_succ, add_assoc]

theorem integerFrameNested_of_check (a b : Nat) (h : frameNested a b = true) :
    ∀ i j : Fin 8,
      ∑ k, certificateNumerator projections[b]! i k * certificateNumerator projections[a]! k j =
        projections[b]!.denominator * certificateNumerator projections[a]! i j := by
  simp only [frameNested, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  intro i j
  have hij := h i.val i.isLt j.val j.isLt
  simpa only [eight_fold_sum, certificateNumerator, matrixEntry] using hij

end CodedSorting.Construction.PhysicalFramePaths
end FiniteFrameNesting

section LocalFrameChain
namespace CodedSorting.Construction.TensorFrameGeometry

abbrev LocalMatrix := Matrix (Fin 8) (Fin 8) ℚ

/-- A chronological chain of actual eight-dimensional projection matrices. -/
def LocalChain (P : LocalMatrix) : List LocalMatrix → Prop
  | [] => P * P = P
  | Q :: qs => P * P = P ∧ (P * Q = P ∧ Q * P = P) ∧ LocalChain Q qs

end CodedSorting.Construction.TensorFrameGeometry
end LocalFrameChain

section PhysicalFramePaths
/-!
# Actual register visits and their projection histories

The finite check in this file reads the gate operands themselves. It does not
replace a physical gate history with its two endpoint frames. Scatter gates
are separated because their original helper controls are replaced by fresh
temporary copies in the physical word.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CodedSorting.Construction.PhysicalFramePaths

open FiniteCertificate IntegerProjection
open TensorFrameGeometry

def frameMatrix (f : Nat) : LocalMatrix := certificateMatrix projections[f]!

@[simp] theorem ordinaryFrameVisits_nil (r : Nat) : ordinaryFrameVisits r [] = [] := rfl

@[simp] theorem ordinaryFrameVisits_cons (r : Nat) (g : Gate) (gs : List Gate) :
    ordinaryFrameVisits r (g :: gs) =
      (ordinaryFrameVisit r g).toList ++ ordinaryFrameVisits r gs := by
  cases h : ordinaryFrameVisit r g <;> simp [ordinaryFrameVisits, h]

theorem ordinaryFrameVisits_append (r : Nat) (left right : List Gate) :
    ordinaryFrameVisits r (left ++ right) =
      ordinaryFrameVisits r left ++ ordinaryFrameVisits r right := by
  simp [ordinaryFrameVisits]

theorem ordinaryFrameVisits_reverse (r : Nat) (word : List Gate) :
    ordinaryFrameVisits r word.reverse = (ordinaryFrameVisits r word).reverse := by
  exact List.filterMap_reverse

theorem frameMatrix_idempotent (f : Nat) (hf : ProjectionEquations projections[f]!) :
    frameMatrix f * frameMatrix f = frameMatrix f :=
  certificate_idempotent _ hf

/-- The strict dimension comparison only speeds up the finite check. The
mathematical conclusion is actual two-sided nesting of rational matrices. -/
theorem canClimb_nested (a b : Nat)
    (ha : ProjectionEquations projections[a]!) (hb : ProjectionEquations projections[b]!)
    (h : canClimb a b = true) :
    frameMatrix a * frameMatrix b = frameMatrix a ∧
      frameMatrix b * frameMatrix a = frameMatrix a := by
  simp only [canClimb, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with hab | h
  · subst b
    exact ⟨frameMatrix_idempotent a ha, frameMatrix_idempotent a ha⟩
  · exact IntegerProjection.nested _ _ _ _ ha.denominator_pos hb.denominator_pos
      ha.numerator_symmetric hb.numerator_symmetric (integerFrameNested_of_check a b h.1)

/-- Interpret every chronological visit, not merely the first and last one. -/
theorem localChain_of_climbPath (start : Nat) (visits : List Nat)
    (hvalid : ∀ f ∈ start :: visits, ProjectionEquations projections[f]!)
    (hpath : climbPath start visits = true) :
    LocalChain (frameMatrix start) (visits.map frameMatrix) := by
  induction visits generalizing start with
  | nil => exact frameMatrix_idempotent start (hvalid start (by simp))
  | cons next rest ih =>
    simp only [climbPath, Bool.and_eq_true] at hpath
    refine ⟨frameMatrix_idempotent start (hvalid start (by simp)),
      canClimb_nested start next (hvalid start (by simp)) (hvalid next (by simp)) hpath.1,
      ih next ?_ hpath.2⟩
    intro f hf
    exact hvalid f (List.mem_cons_of_mem start hf)

theorem complement_idempotent (P : LocalMatrix) (hp : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  simp [sub_mul, mul_sub, hp]

theorem complement_nested (P Q : LocalMatrix)
    (h : P * Q = P ∧ Q * P = P) :
    (1 - Q) * (1 - P) = 1 - Q ∧ (1 - P) * (1 - Q) = 1 - Q := by
  constructor <;> simp only [sub_mul, mul_sub, one_mul, mul_one, h.1, h.2] <;> abel

theorem localChain_snoc (P Q R : LocalMatrix) (xs : List LocalMatrix)
    (h : LocalChain P (xs ++ [Q]))
    (hQR : Q * R = Q ∧ R * Q = Q) (hR : R * R = R) :
    LocalChain P (xs ++ [Q, R]) := by
  induction xs generalizing P with
  | nil => exact ⟨h.1, h.2.1, h.2.2, hQR, hR⟩
  | cons A xs ih => exact ⟨h.1, h.2.1, ih A h.2.2⟩

/-- Time reversal plus orthogonal complement turns an increasing path into
another increasing path, with the endpoints interchanged and complemented. -/
theorem localChain_reverse_complement (P Q : LocalMatrix) (xs : List LocalMatrix)
    (h : LocalChain P (xs ++ [Q])) :
    LocalChain (1 - Q) (xs.reverse.map (fun A => 1 - A) ++ [1 - P]) := by
  induction xs generalizing P with
  | nil =>
    exact ⟨complement_idempotent Q h.2.2,
      complement_nested P Q h.2.1, complement_idempotent P h.1⟩
  | cons A xs ih =>
    have hi := ih A h.2.2
    have hs := localChain_snoc (1-Q) (1-A) (1-P)
      (xs.reverse.map (fun B => 1-B)) hi
      (complement_nested P A h.2.1) (complement_idempotent P h.1)
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append] using hs

end CodedSorting.Construction.PhysicalFramePaths
end PhysicalFramePaths
