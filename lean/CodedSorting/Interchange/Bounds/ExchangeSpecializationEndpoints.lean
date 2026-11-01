import CodedSorting.Interchange.Local.ExchangeFramePaths
import CodedSorting.Interchange.Local.ExchangeFramePermutation
import CodedSorting.Interchange.OneLevel.Children

section ExchangeSpecialization
/-! One shared radix for all actual Construction frame transitions and all their
rank-one triangular scan factors.  No edge chooses its own prime. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.ExchangeSpecialization

open MatrixFactorization PartialSwapExecution ProjectionRankDecomposition
open TriangularConjugacy ExchangeFrameAlgebra ExchangeFramePaths ExchangeFramePermutation
open TensorFrameNetwork TensorFrameGeometry TensorLiftProgram TensorThreeRound
open ProgramNetwork OneLevelChildren
open scoped Matrix BigOperators

noncomputable section
attribute [local irreducible] program actualLabel
attribute [local instance] Classical.propDecidable

abbrev Node := Vertex GlobalReg program.length
abbrev Mat := Matrix (Fin 512) (Fin 512) ℚ
abbrev DoubleMat := Matrix (Fin 512 ⊕ₗ Fin 512) (Fin 512 ⊕ₗ Fin 512) ℚ

local instance doubledDecEq : DecidableEq (Fin 512 ⊕ₗ Fin 512) :=
  (inferInstance : LinearOrder (Fin 512 ⊕ₗ Fin 512)).toDecidableEq

def coordinateEquiv : Fin 512 ≃ CodedSorting.TensorLabels.H 8 :=
  (finCongr (by norm_num [CodedSorting.TensorLabels.H] :
    512 = Fintype.card (CodedSorting.TensorLabels.H 8))).trans
      (Fintype.equivFin _).symm

def label (v : Node) : Mat :=
  (actualLabel v).submatrix coordinateEquiv coordinateEquiv

theorem label_projection (v : Node) : Projection (label v) := by
  have h := actualLabel_projection v
  refine ⟨?_, ?_⟩
  · ext i j
    exact congrFun (congrFun h.1 (coordinateEquiv i)) (coordinateEquiv j)
  · exact (Matrix.submatrix_mul_equiv _ _ _ coordinateEquiv _).trans
      (congrArg (fun A : GlobalMatrix => A.submatrix coordinateEquiv coordinateEquiv) h.2)

theorem label_edge_nested (e : Edge) :
    ExchangeFrameAlgebra.Nested (label (wireTail program e)) (label (wireHead program e)) ∨
    ExchangeFrameAlgebra.Nested (label (wireHead program e)) (label (wireTail program e)) := by
  have hr := actual_edge_comparable e
  rcases hr with h | h | h
  · left
    have he : label (wireTail program e) = label (wireHead program e) :=
      congrArg (fun A : GlobalMatrix => A.submatrix coordinateEquiv coordinateEquiv) h
    rw [← he]
    exact ⟨(label_projection _).2, (label_projection _).2⟩
  · left
    constructor
    · exact (Matrix.submatrix_mul_equiv _ _ _ coordinateEquiv _).trans
        (congrArg (fun A : GlobalMatrix => A.submatrix coordinateEquiv coordinateEquiv) h.1)
    · exact (Matrix.submatrix_mul_equiv _ _ _ coordinateEquiv _).trans
        (congrArg (fun A : GlobalMatrix => A.submatrix coordinateEquiv coordinateEquiv) h.2)
  · right
    constructor
    · exact (Matrix.submatrix_mul_equiv _ _ _ coordinateEquiv _).trans
        (congrArg (fun A : GlobalMatrix => A.submatrix coordinateEquiv coordinateEquiv) h.1)
    · exact (Matrix.submatrix_mul_equiv _ _ _ coordinateEquiv _).trans
        (congrArg (fun A : GlobalMatrix => A.submatrix coordinateEquiv coordinateEquiv) h.2)

def edgeProjection (e : Edge) : Mat :=
  if ExchangeFrameAlgebra.Nested (label (wireTail program e)) (label (wireHead program e))
  then label (wireHead program e) - label (wireTail program e)
  else label (wireTail program e) - label (wireHead program e)

theorem edgeProjection_projection (e : Edge) : Projection (edgeProjection e) := by
  unfold edgeProjection
  split_ifs with h
  · exact projection_difference _ _ (label_projection _) (label_projection _) h
  · exact projection_difference _ _ (label_projection _) (label_projection _)
      ((label_edge_nested e).resolve_left h)

theorem edgeProjection_rank (e : Edge) : (edgeProjection e).rank = edgeRank e := by
  have h : (label (wireHead program e) - label (wireTail program e)).rank = edgeRank e := by
    change ((actualLabel (wireHead program e) - actualLabel (wireTail program e)).submatrix
      coordinateEquiv coordinateEquiv).rank =
        (actualLabel (wireHead program e) - actualLabel (wireTail program e)).rank
    exact Matrix.rank_submatrix
      (actualLabel (wireHead program e) - actualLabel (wireTail program e))
      coordinateEquiv coordinateEquiv
  unfold edgeProjection
  split_ifs
  · exact h
  · exact (CodedSorting.RankMetric.matrix_rank_sub_symm
      (label (wireTail program e)) (label (wireHead program e))).trans h

def decomposition (e : Edge) : RankDecomposition (edgeProjection e) :=
  Classical.choice (exists_rank_decomposition _
    (edgeProjection_projection e).1 (edgeProjection_projection e).2)

def childIndex (e : Edge) : Fin (edgeProjection e).rank ≃ Fin (edgeRank e) :=
  finCongr (edgeProjection_rank e)

theorem edgeFrame_product (e : Edge) :
    partialSwap (label (wireHead program e)) * partialSwap (label (wireTail program e)) =
      partialSwap (edgeProjection e) := by
  unfold edgeProjection
  split_ifs with h
  · exact partialSwap_nested _ _ h
  · exact partialSwap_reverse_nested _ _ ((label_edge_nested e).resolve_left h)

theorem edgeFrame_reverse_product (e : Edge) :
    partialSwap (label (wireTail program e)) * partialSwap (label (wireHead program e)) =
      partialSwap (edgeProjection e) := by
  unfold edgeProjection
  split_ifs with h
  · exact partialSwap_reverse_nested _ _ h
  · exact partialSwap_nested _ _ ((label_edge_nested e).resolve_left h)

abbrev FamilyIndex := Option (Node ⊕ ((e : Edge) × RankPartialSwapExecution.FamilyIndex (edgeProjection e)))

/-- The full bank swap, all actual vertex frames, and every triangular
rank-factor/inverse are included before a single prime is selected. -/
def family : FamilyIndex → DoubleMat
  | none => partialSwap 1
  | some (.inl v) => partialSwap (label v)
  | some (.inr ⟨e, k⟩) => RankPartialSwapExecution.family (decomposition e) k

def uniform : SpecializedFamily family := specializeFamily family

attribute [local irreducible] uniform

abbrev radix : Nat := uniform.prime

theorem radix_prime : radix.Prime := uniform.prime_is_prime
theorem radix_odd : Odd radix := uniform.prime_is_odd

abbrev edgeFamily (e : Edge) :
    SpecializedFamily (RankPartialSwapExecution.family (decomposition e)) :=
  restrictFamily uniform (fun k => some (.inr ⟨e, k⟩)) (fun _ => id) (fun _ => id)

theorem edgeFamily_prime (e : Edge) : (edgeFamily e).prime = radix := rfl

variable (f : Nat)
local instance : NeZero (radix^f) := ⟨pow_ne_zero _ radix_prime.ne_zero⟩

def frameMatrix (v : Node) := fullFinMatrix uniform f (some (.inl v))
def edgeMatrix (e : Edge) := fullFinMatrix (edgeFamily e) f none

theorem finite_product (i j k : FamilyIndex) (h : family i * family j = family k) :
    fullFinMatrix uniform f i * fullFinMatrix uniform f j = fullFinMatrix uniform f k := by
  have ht := uniform.preserves_product i j k h f
  have hf := congrArg ((ZMod.finEquiv (radix^f)).symm.toRingHom.mapMatrix) ht
  simpa only [map_mul, fullFinMatrix, RingHom.mapMatrix_apply, RingEquiv.coe_toRingHom] using hf

theorem finite_square (i : FamilyIndex) (h : family i * family i = 1) :
    fullFinMatrix uniform f i * fullFinMatrix uniform f i = 1 := by
  have ht := uniform.preserves_product_one i i h f
  have hf := congrArg ((ZMod.finEquiv (radix^f)).symm.toRingHom.mapMatrix) ht
  simpa only [map_mul, map_one, fullFinMatrix, RingHom.mapMatrix_apply,
    RingEquiv.coe_toRingHom] using hf

theorem frameMatrix_square (v : Node) : frameMatrix f v * frameMatrix f v = 1 :=
  finite_square f _ (partialSwap_involution _ (label_projection v).2)

theorem edgeMatrix_square (e : Edge) : edgeMatrix f e * edgeMatrix f e = 1 :=
  finite_square f _ (partialSwap_involution _ (edgeProjection_projection e).2)

theorem frameMatrix_edge_product (e : Edge) :
    frameMatrix f (wireTail program e) * frameMatrix f (wireHead program e) = edgeMatrix f e :=
  finite_product f _ _ _ (edgeFrame_reverse_product e)

#print axioms edgeProjection_rank
#print axioms frameMatrix_edge_product
#print axioms radix_prime

end
end CodedSorting.Construction.ExchangeSpecialization
end ExchangeSpecialization

section ExchangeSpecializationEndpoints
/-! Concrete finite endpoint and edge permutations for the actual Construction word. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.ExchangeSpecialization

open PartialSwapExecution TriangularConjugacy ExchangeFrameAlgebra ExchangeFramePermutation
open TensorFrameNetwork TensorFrameGeometry TensorLiftProgram TensorThreeRound
open ProgramNetwork OneLevelChildren
open scoped Matrix

noncomputable section
attribute [local irreducible] program actualLabel uniform
attribute [local instance] doubledDecEq
local instance endpointBaseDecEq : DecidableEq (Fin 512) :=
  (inferInstance : LinearOrder (Fin 512)).toDecidableEq

theorem label_endpoint_complement (r : ThreeCopySchedule.IndependentStream) :
    label (.sink (.inl (originalSwap r))) = 1 - label (.source (.inl r)) := by
  unfold label
  rw [actualLabel_source, actualLabel_terminal, actual_endpoint_complement]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
    coordinateEquiv.injective.eq_iff]

theorem rational_endpoint_product (r : ThreeCopySchedule.IndependentStream) :
    partialSwap (label (.source (.inl r))) *
      partialSwap (label (.sink (.inl (originalSwap r)))) = family none := by
  rw [label_endpoint_complement]
  have h := partialSwap_complement (1 - label (.source (.inl r)))
    (projection_complement _ (label_projection (.source (.inl r)))).2
  have hfull : partialSwap (1 : Mat) = family none := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      by_cases hij : i = j <;>
        simp [family, partialSwap, Matrix.fromBlocks, Matrix.one_apply, hij]
  rw [← hfull]
  simpa only [sub_sub_cancel] using h

variable (f : Nat)
local instance : NeZero (radix^f) := ⟨pow_ne_zero _ radix_prime.ne_zero⟩

theorem finite_entry_zero (k : FamilyIndex) (i j : Fin 512 ⊕ₗ Fin 512)
    (h : family k i j = 0) : fullFinMatrix uniform f k i j = 0 := by
  have hh := uniform.preserves_entry_zero k i j h f
  simp only [fullFinMatrix, Matrix.map_apply, hh, map_zero]

theorem finite_entry_one (k : FamilyIndex) (i j : Fin 512 ⊕ₗ Fin 512)
    (h : family k i j = 1) : fullFinMatrix uniform f k i j = 1 := by
  have hh := uniform.preserves_entry_one k i j h f
  simp only [fullFinMatrix, Matrix.map_apply, hh, map_one]

theorem finite_full_swap : fullFinMatrix uniform f none =
    (bankSwapMatrix : ExchangeFramePermutation.Mat 512 (radix^f)) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact finite_entry_zero f none (Sum.inl i) (Sum.inl j)
      (by by_cases hij : i = j <;>
        simp [family, partialSwap, Matrix.fromBlocks, Matrix.one_apply, hij])
  · by_cases hij : i = j
    · subst j
      simpa [bankSwapMatrix, Matrix.fromBlocks, Matrix.one_apply] using
        finite_entry_one f none (Sum.inl i) (Sum.inr i)
          (by simp [family, partialSwap, Matrix.fromBlocks])
    · simpa [bankSwapMatrix, Matrix.fromBlocks, Matrix.one_apply, hij] using
        finite_entry_zero f none (Sum.inl i) (Sum.inr j)
          (by simp [family, partialSwap, Matrix.fromBlocks, Matrix.one_apply, hij])
  · by_cases hij : i = j
    · subst j
      simpa [bankSwapMatrix, Matrix.fromBlocks, Matrix.one_apply] using
        finite_entry_one f none (Sum.inr i) (Sum.inl i)
          (by simp [family, partialSwap, Matrix.fromBlocks])
    · simpa [bankSwapMatrix, Matrix.fromBlocks, Matrix.one_apply, hij] using
        finite_entry_zero f none (Sum.inr i) (Sum.inl j)
          (by simp [family, partialSwap, Matrix.fromBlocks, Matrix.one_apply, hij])
  · exact finite_entry_zero f none (Sum.inr i) (Sum.inr j)
      (by by_cases hij : i = j <;>
        simp [family, partialSwap, Matrix.fromBlocks, Matrix.one_apply, hij])

theorem frameMatrix_endpoint_product (r : ThreeCopySchedule.IndependentStream) :
    frameMatrix f (.source (.inl r)) * frameMatrix f (.sink (.inl (originalSwap r))) =
      bankSwapMatrix := by
  rw [← finite_full_swap f]
  exact finite_product f _ _ _ (rational_endpoint_product r)

def location (Pref G S : Nat) (v : Node) :
    Equiv.Perm (Fin (CommonAddressLayout.Volume (Fin 512) Pref (radix^f) G S)) :=
  numericPerm (frameMatrix f v) (frameMatrix_square f v) Pref G S

def edgePermutation (Pref G S : Nat) (e : Edge) :
    Equiv.Perm (Fin (CommonAddressLayout.Volume (Fin 512) Pref (radix^f) G S)) :=
  numericPerm (edgeMatrix f e) (edgeMatrix_square f e) Pref G S

theorem edgePermutation_eq (Pref G S : Nat) (e : Edge) :
    (location f Pref G S (wireHead program e)).symm.trans
      (location f Pref G S (wireTail program e)) = edgePermutation f Pref G S e :=
  numericPerm_transition _ _ _ _ _ _ (frameMatrix_edge_product f e) Pref G S

/-- The exact output-to-input permutation required by the selected-session
network simulation is ordinary H/D exchange in the physical file layout. -/
theorem selected_endpoint (Pref G S : Nat) (r : ThreeCopySchedule.IndependentStream) :
    (location f Pref G S (.sink (.inl (originalSwap r)))).symm.trans
      (location f Pref G S (.source (.inl r))) =
        numericExchange Pref G S :=
  numericPerm_endpoint _ _ _ _ (frameMatrix_endpoint_product f r) Pref G S

#print axioms selected_endpoint
#print axioms edgePermutation_eq

end
end CodedSorting.Construction.ExchangeSpecialization
end ExchangeSpecializationEndpoints
