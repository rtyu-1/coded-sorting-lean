import CodedSorting.Circuit.Composition.TensorNetworkGeometry
import CodedSorting.Circuit.MemoryAccess.PhysicalFramePaths
import CodedSorting.Circuit.Labels.Framework.StageLabels

section TensorFrameChains
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.TensorFrameGeometry

noncomputable section
open scoped BigOperators Matrix Kronecker
open ThreeCopySchedule
open CodedSorting.TensorLabels

/-- The physical data frame after the first and second tensor rounds, in
copy-relative coordinates. The third exit is the full identity. -/
def firstAmbient (a : Coordinates) : GlobalMatrix :=
  tensor3 1 (lineProjector a.2.1) (lineProjector a.2.2)

def secondAmbient (a : Coordinates) : GlobalMatrix :=
  tensor3 1 1 (lineProjector a.2.2)

theorem firstAmbient_idempotent (a : Coordinates) : firstAmbient a * firstAmbient a = firstAmbient a := by
  simp [firstAmbient, tensor3_mul, lineProjector_idempotent]

theorem secondAmbient_idempotent (a : Coordinates) : secondAmbient a * secondAmbient a = secondAmbient a := by
  simp [secondAmbient, tensor3_mul, lineProjector_idempotent]

theorem line_first_nested (a : Coordinates) : Nested (tensorLine a) (firstAmbient a) := by
  constructor <;> simp [tensorLine, firstAmbient, tensor3_mul, lineProjector_idempotent]

theorem first_second_nested (a : Coordinates) : Nested (firstAmbient a) (secondAmbient a) := by
  constructor <;> simp [firstAmbient, secondAmbient, tensor3_mul, lineProjector_idempotent]

theorem difference_idempotent (P Q : GlobalMatrix)
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : Nested P Q) :
    (Q - P) * (Q - P) = Q - P := by
  simp only [sub_mul, mul_sub, hP, hQ, hPQ.1, hPQ.2]
  abel

theorem difference_nested (P Q R : GlobalMatrix)
    (hP : P * P = P) (hPQ : Nested P Q) (hPR : Nested P R) (hQR : Nested Q R) :
    Nested (Q - P) (R - P) := by
  constructor <;>
    simp only [sub_mul, mul_sub, hP, hPQ.1, hPQ.2, hPR.1, hPR.2, hQR.1, hQR.2] <;>
    abel

theorem x_boundary_chain (a : Coordinates) :
    IsNestedChain (tensorLine a) [firstAmbient a, secondAmbient a, 1] :=
  ⟨tensorLine_idempotent a, line_first_nested a,
    firstAmbient_idempotent a, first_second_nested a,
    secondAmbient_idempotent a, nested_one _, by simp [IsNestedChain]⟩

theorem y_boundary_chain (a : Coordinates) :
    IsNestedChain 0 [firstAmbient a - tensorLine a,
      secondAmbient a - tensorLine a, 1 - tensorLine a] := by
  have hPA := line_first_nested a
  have hAB := first_second_nested a
  have hPB := nested_trans hPA hAB
  have hP := tensorLine_idempotent a
  exact ⟨by simp, nested_zero _,
    difference_idempotent _ _ hP (firstAmbient_idempotent a) hPA,
    difference_nested _ _ _ hP hPA hPB hAB,
    difference_idempotent _ _ hP (secondAmbient_idempotent a) hPB,
    difference_nested _ _ _ hP hPB (nested_one _) (nested_one _),
    difference_idempotent _ _ hP (by simp) (nested_one _)⟩

@[simp] theorem globalize_zero (i : Copy) : globalize i 0 = 0 := rfl

@[simp] theorem globalize_one (i : Copy) : globalize i 1 = 1 := by
  ext r c
  simp [globalize, Matrix.one_apply]

@[simp] theorem globalize_sub (i : Copy) (P Q : GlobalMatrix) :
    globalize i (P - Q) = globalize i P - globalize i Q := rfl

theorem globalize_nested (i : Copy) {P Q : GlobalMatrix} (h : Nested P Q) :
    Nested (globalize i P) (globalize i Q) := by
  constructor <;> rw [globalize_mul]
  · rw [h.1]
  · rw [h.2]

theorem globalize_chain (i : Copy) (P : GlobalMatrix) (xs : List GlobalMatrix)
    (h : IsNestedChain P xs) :
    IsNestedChain (globalize i P) (xs.map (globalize i)) := by
  induction xs generalizing P with
  | nil => change globalize i P * globalize i P = globalize i P; rw [globalize_mul, h]
  | cons Q qs ih =>
    exact ⟨by rw [globalize_mul, h.1], globalize_nested i h.2.1, ih Q h.2.2⟩

/-- Drop a virtual entry frame while preserving the order on the literal
subsequent gate visits. -/
theorem nested_chain_weaken_start {P Q : GlobalMatrix} {xs : List GlobalMatrix}
    (hP : P * P = P) (hPQ : Nested P Q) (hxs : IsNestedChain Q xs) :
    IsNestedChain P xs := by
  cases xs with
  | nil => exact hP
  | cons R rs => exact ⟨hP, nested_trans hPQ hxs.2.1, hxs.2.2⟩

/-- Join literal visits across a verified exit-to-entry conversion. The exit
and entry may be strict inclusions and need not be actual program gates. -/
theorem join_paths_across_boundary {P T Q : GlobalMatrix}
    (xs ys : List GlobalMatrix)
    (hxs : IsNestedChain P (xs ++ [T])) (hTQ : Nested T Q)
    (hys : IsNestedChain Q ys) : IsNestedChain P (xs ++ ys) := by
  induction xs generalizing P with
  | nil =>
    exact nested_chain_weaken_start hxs.1 (nested_trans hxs.2.1 hTQ) hys
  | cons R rs ih =>
    exact ⟨hxs.1, hxs.2.1, ih hxs.2.2⟩

/-- These are the actual three round-exit frames of each physical data wire. -/
def dataBoundaryPath (a : DataStream) : List GlobalMatrix :=
  (if a.2.1 = 0 then [firstAmbient a.2.2, secondAmbient a.2.2, 1]
   else [firstAmbient a.2.2 - tensorLine a.2.2,
     secondAmbient a.2.2 - tensorLine a.2.2, 1 - tensorLine a.2.2]).map (globalize a.1)

theorem dataBoundaryPath_nested (a : DataStream) :
    IsNestedChain (dataSource a) (dataBoundaryPath a) := by
  by_cases h : a.2.1 = 0
  · simpa [dataBoundaryPath, dataSource, dataProjector, h] using
      globalize_chain a.1 _ _ (x_boundary_chain a.2.2)
  · simpa [dataBoundaryPath, dataSource, h] using
      globalize_chain a.1 _ _ (y_boundary_chain a.2.2)

theorem dataBoundaryPath_last (a : DataStream) :
    chainLast (dataSource a) (dataBoundaryPath a) = dataTerminal a := by
  by_cases h : a.2.1 = 0 <;>
    simp [dataBoundaryPath, dataTerminal, h, chainLast, dataProjector]

theorem dataComplement_rank (a : DataStream) : (1 - dataProjector a).rank = 511 := by
  have h := nested_rank_difference (dataProjector_idempotent a)
    (show (1 : GlobalMatrix) * 1 = 1 by simp) (nested_one (dataProjector a))
  simpa [dataProjector_rank, Matrix.rank_one, H] using h

/-- A full nested refinement of the actual endpoint labels has the same cost.
This will consume the lifted local register visits once those are assembled. -/
theorem data_path_rank_cost (a : DataStream) (xs : List GlobalMatrix)
    (hchain : IsNestedChain (dataSource a) xs)
    (hlast : chainLast (dataSource a) xs = dataTerminal a) :
    chainCost (dataSource a) xs = 511 := by
  rw [chainCost_telescope hchain, hlast]
  by_cases h : a.2.1 = 0
  · simp [dataSource, dataTerminal, h, Matrix.rank_one, H, dataProjector_rank]
  · simp [dataSource, dataTerminal, h, dataComplement_rank]

theorem dataBoundaryPath_cost (a : DataStream) :
    chainCost (dataSource a) (dataBoundaryPath a) = 511 :=
  data_path_rank_cost a _ (dataBoundaryPath_nested a) (dataBoundaryPath_last a)

/-- Keep the finite index type abstract while proving the summation identity.
This prevents kernel reduction from enumerating a large concrete register type. -/
theorem sum_uniform_rank_cost {J : Type*} [Fintype J]
    (f : J → Nat) (cost : Nat) (h : ∀ j, f j = cost) :
    (∑ j, f j) = Fintype.card J * cost := by
  calc
    (∑ j, f j) = ∑ _j : J, cost := Finset.sum_congr rfl (fun j _ => h j)
    _ = Fintype.card J * cost := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp

/-- This sum ranges over the exact scalar program's data registers. -/
theorem dataBoundary_total_rank_cost :
    (∑ a : DataStream, chainCost (dataSource a) (dataBoundaryPath a)) =
      6 * 111 ^ 3 * (512 - 1) := by
  calc
    _ = Fintype.card DataStream * 511 :=
      sum_uniform_rank_cost _ 511 dataBoundaryPath_cost
    _ = 6 * 111 ^ 3 * (512 - 1) := by
      rw [data_stream_count]
      norm_num

/-- The helper's actual paired labels use the concrete, kernel-checked
orthogonal permutation, not an arbitrary assumed matching. -/
def helperBoundaryPath (h : HelperStream) : List GlobalMatrix :=
  (HelperFrameChain.boundaries
    (lineProjector h.1.2.1) (lineProjector h.1.2.2)
    (lineProjector (partner h.1.2.1)) (lineProjector (partner h.1.2.2))).map
      (globalize h.1.1)

theorem helperBoundaryPath_nested (h : HelperStream) :
    IsNestedChain 0 (helperBoundaryPath h) := by
  have hc := HelperFrameChain.boundary_chain
    (lineProjector h.1.2.1) (lineProjector h.1.2.2)
    (lineProjector (partner h.1.2.1)) (lineProjector (partner h.1.2.2))
    (lineProjector_idempotent _) (lineProjector_idempotent _)
    (lineProjector_idempotent _) (lineProjector_idempotent _)
    (lineProjector_partner_orthogonal _) (partner_lineProjector_orthogonal _)
    (lineProjector_partner_orthogonal _) (partner_lineProjector_orthogonal _)
  simpa only [helperBoundaryPath, globalize_zero] using globalize_chain h.1.1 _ _ hc

theorem helperBoundaryPath_last (h : HelperStream) :
    chainLast 0 (helperBoundaryPath h) = 1 := by
  simp [helperBoundaryPath, HelperFrameChain.boundaries, chainLast]

theorem helper_path_rank_cost (xs : List GlobalMatrix)
    (hchain : IsNestedChain 0 xs) (hlast : chainLast 0 xs = 1) :
    chainCost 0 xs = 512 := by
  rw [chainCost_telescope hchain, hlast]
  norm_num [Matrix.rank_one, H]

theorem helperBoundaryPath_cost (h : HelperStream) :
    chainCost 0 (helperBoundaryPath h) = 512 :=
  helper_path_rank_cost _ (helperBoundaryPath_nested h) (helperBoundaryPath_last h)

/-- This sum uses the precise shared pools and local helper indices of
`TensorLiftProgram.GlobalReg`. Each helper is charged once over all three uses. -/
theorem helperBoundary_total_rank_cost :
    (∑ h : HelperStream, chainCost 0 (helperBoundaryPath h)) =
      3 * 111 ^ 2 * 439 * 512 := by
  calc
    _ = Fintype.card HelperStream * 512 :=
      sum_uniform_rank_cost _ 512 helperBoundaryPath_cost
    _ = 3 * 111 ^ 2 * 439 * 512 := by
      rw [helper_count]
      norm_num

end
end CodedSorting.Construction.TensorFrameGeometry
end TensorFrameChains

section TensorFrameLift
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.TensorFrameGeometry

noncomputable section
open scoped BigOperators Matrix Kronecker
open ThreeCopySchedule
open CodedSorting.TensorLabels (tensor3 tensor3_mul Label)

@[simp] theorem tensor3_zero_first (P Q : LocalMatrix) : tensor3 (0 : LocalMatrix) P Q = 0 := by
  simp [tensor3]

@[simp] theorem tensor3_zero_second (P Q : LocalMatrix) : tensor3 P (0 : LocalMatrix) Q = 0 := by
  simp [tensor3]

@[simp] theorem tensor3_zero_third (P Q : LocalMatrix) : tensor3 P Q (0 : LocalMatrix) = 0 := by
  simp [tensor3]

/-- Insert the processed coordinate in the exact cyclic `coordinateView` used
by the executable fiber embedding. The two arguments are the block's fixed
coordinates, in that view's order. -/
def liftLinear (r : TensorLiftProgram.Round) (b c : Line) (P : LocalMatrix) : GlobalMatrix :=
  match r with
  | .first => tensor3 P (lineProjector b) (lineProjector c)
  | .second => tensor3 (lineProjector c) P (lineProjector b)
  | .third => tensor3 (lineProjector b) (lineProjector c) P

def liftBase (r : TensorLiftProgram.Round) (b c : Line) : GlobalMatrix :=
  match r with
  | .first => 0
  | .second => tensor3 (1 - lineProjector c) 1 (lineProjector b)
  | .third => 1 - tensor3 (lineProjector b) (lineProjector c) 1

/-- The paper's orthogonal affine lift `K⊗E⊗Q + L⊗P⊗Q`. -/
def liftFrame (r : TensorLiftProgram.Round) (b c : Line) (P : LocalMatrix) : GlobalMatrix :=
  liftBase r b c + liftLinear r b c P

theorem liftLinear_mul (r : TensorLiftProgram.Round) (b c : Line) (P Q : LocalMatrix) :
    liftLinear r b c P * liftLinear r b c Q = liftLinear r b c (P * Q) := by
  cases r <;> simp [liftLinear, tensor3_mul, lineProjector_idempotent]

theorem liftLinear_idempotent (r : TensorLiftProgram.Round) (b c : Line)
    (P : LocalMatrix) (hp : P * P = P) :
    liftLinear r b c P * liftLinear r b c P = liftLinear r b c P := by
  rw [liftLinear_mul, hp]

theorem liftLinear_trace (r : TensorLiftProgram.Round) (b c : Line) (P : LocalMatrix) :
    Matrix.trace (liftLinear r b c P) = Matrix.trace P := by
  cases r <;> simp [liftLinear, tensor3, Matrix.trace_kronecker, lineProjector_trace]

/-- Actual Mathlib matrix ranks are preserved, not merely declared costs. -/
theorem liftLinear_rank (r : TensorLiftProgram.Round) (b c : Line)
    (P : LocalMatrix) (hp : P * P = P) : (liftLinear r b c P).rank = P.rank := by
  have ht := IntegerProjection.trace_eq_rank _ (liftLinear_idempotent r b c P hp)
  rw [liftLinear_trace, IntegerProjection.trace_eq_rank P hp] at ht
  exact_mod_cast ht.symm

theorem liftLinear_sub (r : TensorLiftProgram.Round) (b c : Line) (P Q : LocalMatrix) :
    liftLinear r b c (P - Q) = liftLinear r b c P - liftLinear r b c Q := by
  cases r <;> ext i j <;> simp [liftLinear, tensor3, Matrix.kroneckerMap_apply] <;> ring

theorem liftBase_idempotent (r : TensorLiftProgram.Round) (b c : Line) :
    liftBase r b c * liftBase r b c = liftBase r b c := by
  cases r <;>
    simp [liftBase, sub_mul, mul_sub, tensor3_mul, lineProjector_idempotent]

theorem liftBase_linear_zero (r : TensorLiftProgram.Round) (b c : Line) (P : LocalMatrix) :
    liftBase r b c * liftLinear r b c P = 0 := by
  cases r <;>
    simp [liftBase, liftLinear, sub_mul, mul_sub, tensor3_mul,
      lineProjector_idempotent]

theorem liftLinear_base_zero (r : TensorLiftProgram.Round) (b c : Line) (P : LocalMatrix) :
    liftLinear r b c P * liftBase r b c = 0 := by
  cases r <;>
    simp [liftBase, liftLinear, sub_mul, mul_sub, tensor3_mul,
      lineProjector_idempotent]

theorem liftFrame_idempotent (r : TensorLiftProgram.Round) (b c : Line)
    (P : LocalMatrix) (hp : P * P = P) :
    liftFrame r b c P * liftFrame r b c P = liftFrame r b c P := by
  simp [liftFrame, add_mul, mul_add, liftBase_idempotent,
    liftBase_linear_zero, liftLinear_base_zero, liftLinear_idempotent r b c P hp]

theorem liftFrame_nested (r : TensorLiftProgram.Round) (b c : Line)
    (P Q : LocalMatrix) (hpq : P * Q = P) (hqp : Q * P = P) :
    CodedSorting.TensorLabels.Nested (liftFrame r b c P) (liftFrame r b c Q) := by
  constructor <;>
    simp [liftFrame, add_mul, mul_add, liftBase_idempotent,
      liftBase_linear_zero, liftLinear_base_zero, liftLinear_mul, hpq, hqp]

theorem liftFrame_difference (r : TensorLiftProgram.Round) (b c : Line) (P Q : LocalMatrix) :
    liftFrame r b c Q - liftFrame r b c P = liftLinear r b c (Q - P) := by
  rw [liftLinear_sub]
  unfold liftFrame
  abel

theorem local_difference_idempotent (P Q : LocalMatrix)
    (hp : P * P = P) (hq : Q * Q = Q) (hpq : P * Q = P) (hqp : Q * P = P) :
    (Q - P) * (Q - P) = Q - P := by
  simp only [sub_mul, mul_sub, hp, hq, hpq, hqp]
  abel

theorem liftFrame_difference_rank (r : TensorLiftProgram.Round) (b c : Line)
    (P Q : LocalMatrix) (hp : P * P = P) (hq : Q * Q = Q)
    (hpq : P * Q = P) (hqp : Q * P = P) :
    (liftFrame r b c Q - liftFrame r b c P).rank = (Q - P).rank := by
  rw [liftFrame_difference]
  exact liftLinear_rank r b c _ (local_difference_idempotent P Q hp hq hpq hqp)

theorem liftFrame_chain (r : TensorLiftProgram.Round) (b c : Line)
    (P : LocalMatrix) (xs : List LocalMatrix) (h : LocalChain P xs) :
    CodedSorting.TensorLabels.IsNestedChain (liftFrame r b c P)
      (xs.map (liftFrame r b c)) := by
  induction xs generalizing P with
  | nil => exact liftFrame_idempotent r b c P h
  | cons Q qs ih =>
    exact ⟨liftFrame_idempotent r b c P h.1,
      liftFrame_nested r b c P Q h.2.1.1 h.2.1.2, ih Q h.2.2⟩

/-- The gate label for the exact round and block used by `fiberEmbedding`. -/
def globalFrame (r : TensorLiftProgram.Round) (block : Block) (P : LocalMatrix) : GlobalMatrix :=
  globalize block.1 (liftFrame r block.2.1 block.2.2 P)

theorem globalFrame_difference_rank (r : TensorLiftProgram.Round) (block : Block)
    (P Q : LocalMatrix) (hp : P * P = P) (hq : Q * Q = Q)
    (hpq : P * Q = P) (hqp : Q * P = P) :
    (globalFrame r block Q - globalFrame r block P).rank = (Q - P).rank := by
  change ((liftFrame r block.2.1 block.2.2 Q - liftFrame r block.2.1 block.2.2 P).submatrix
    (copyView block.1) (copyView block.1)).rank = _
  rw [Matrix.rank_submatrix]
  exact liftFrame_difference_rank r block.2.1 block.2.2 P Q hp hq hpq hqp

/-- A copied temporary may descend from its rank-seven retained frame to
zero. Reversing both endpoints leaves rank distance unchanged. -/
theorem globalFrame_reverse_difference_rank (r : TensorLiftProgram.Round) (block : Block)
    (P Q : LocalMatrix) (hp : P * P = P) (hq : Q * Q = Q)
    (hqp : Q * P = Q) (hpq : P * Q = Q) :
    (globalFrame r block Q - globalFrame r block P).rank = (Q - P).rank := by
  rw [CodedSorting.RankMetric.matrix_rank_sub_symm]
  rw [globalFrame_difference_rank r block Q P hq hp hqp hpq]
  exact CodedSorting.RankMetric.matrix_rank_sub_symm _ _

theorem globalFrame_chain (r : TensorLiftProgram.Round) (block : Block)
    (P : LocalMatrix) (xs : List LocalMatrix) (h : LocalChain P xs) :
    CodedSorting.TensorLabels.IsNestedChain (globalFrame r block P)
      (xs.map (globalFrame r block)) := by
  have hl := liftFrame_chain r block.2.1 block.2.2 P xs h
  simpa [globalFrame, List.map_map, Function.comp_def] using
    globalize_chain block.1 _ _ hl

end
end CodedSorting.Construction.TensorFrameGeometry
end TensorFrameLift

section TensorFrameEndpoints
/-!
Endpoint interpretation for the lightweight algebra certificates used by the
network proof. Line-membership tables are not needed: the actual endpoint
integer equations and positive denominators suffice.
-/

set_option autoImplicit false

namespace CodedSorting.Construction.TensorFrameGeometry

open scoped Matrix
open FiniteCertificate IntegerProjection

def endpointLineMatrix (t : Nat) : LocalMatrix :=
  (1 / 4 : ℚ) • Matrix.vecMulVec (vectorOfInts (endpointLine t)) (vectorOfInts (endpointLine t))

theorem lineProjector_eq_endpointLineMatrix (a : ThreeCopySchedule.Line) :
    lineProjector a = endpointLineMatrix a.val := by
  unfold lineProjector TriangularConjugacy.lineProjection
  rw [lineVector_norm]
  change (4 : ℚ)⁻¹ • Matrix.vecMulVec (lineVector a) (lineVector a) =
    (1 / 4 : ℚ) • Matrix.vecMulVec (lineVector a) (lineVector a)
  rw [one_div]

private theorem from_zero_entries (p : Projection)
    (h : ∀ i j : Fin 8, certificateNumerator p i j = 0) :
    certificateMatrix p = 0 := by
  ext i j
  simp [certificateMatrix, projectionOfInts, h]

private theorem from_one_entries (p : Projection) (hd : 0 < p.denominator)
    (h : ∀ i j : Fin 8, certificateNumerator p i j = if i = j then p.denominator else 0) :
    certificateMatrix p = 1 := by
  ext i j
  by_cases hij : i = j
  · simp only [certificateMatrix, projectionOfInts, h, Matrix.one_apply, hij, if_true]
    exact div_self (denominator_ne_zero hd)
  · simp [certificateMatrix, projectionOfInts, h, Matrix.one_apply, hij]

private theorem from_line_entries (p : Projection) (t : Nat) (hd : 0 < p.denominator)
    (h : ∀ i j : Fin 8, 4 * certificateNumerator p i j =
      p.denominator * endpointLine t i *
        endpointLine t j) :
    certificateMatrix p = endpointLineMatrix t := by
  ext i j
  have hc : 4 * (certificateNumerator p i j : ℚ) =
      (p.denominator : ℚ) * (endpointLine t i : ℚ) *
        (endpointLine t j : ℚ) := by
    exact_mod_cast h i j
  simp only [certificateMatrix, projectionOfInts, endpointLineMatrix,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, vectorOfInts]
  apply (div_eq_iff (denominator_ne_zero hd)).mpr
  nlinarith only [hc]

private theorem from_complement_entries (p : Projection) (t : Nat) (hd : 0 < p.denominator)
    (h : ∀ i j : Fin 8, 4 * certificateNumerator p i j = p.denominator *
      ((if i = j then 4 else 0) - endpointLine t i *
        endpointLine t j)) :
    certificateMatrix p = 1 - endpointLineMatrix t := by
  ext i j
  have hc : 4 * (certificateNumerator p i j : ℚ) = (p.denominator : ℚ) *
      ((if i = j then 4 else 0) - (endpointLine t i : ℚ) *
        (endpointLine t j : ℚ)) := by
    exact_mod_cast h i j
  simp only [certificateMatrix, projectionOfInts, endpointLineMatrix,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, vectorOfInts,
    Matrix.sub_apply, Matrix.one_apply]
  apply (div_eq_iff (denominator_ne_zero hd)).mpr
  by_cases hij : i = j
  · simp only [hij, if_true] at hc ⊢
    nlinarith only [hc]
  · simp only [hij, if_false] at hc ⊢
    nlinarith only [hc]

theorem source_start_of_equations (t : Fin 111) (he : EndpointEquations)
    (hf : ProjectionEquations projections[startFrames[t.val]!]!) :
    certificateMatrix projections[startFrames[t.val]!]! = lineProjector t := by
  rw [from_line_entries _ _ hf.denominator_pos
    (he.sourceEntry t).1]
  exact (lineProjector_eq_endpointLineMatrix t).symm

theorem source_end_of_equations (t : Fin 111) (he : EndpointEquations)
    (hf : ProjectionEquations projections[finalFrames[t.val]!]!) :
    certificateMatrix projections[finalFrames[t.val]!]! = 1 :=
  from_one_entries _ hf.denominator_pos (he.sourceEntry t).2

theorem target_start_of_equations (t : Fin 111) (he : EndpointEquations) :
    certificateMatrix projections[startFrames[portCount+t.val]!]! = 0 :=
  from_zero_entries _ (he.targetEntry t).1

theorem target_end_of_equations (t : Fin 111) (he : EndpointEquations)
    (hf : ProjectionEquations projections[finalFrames[portCount+t.val]!]!) :
    certificateMatrix projections[finalFrames[portCount+t.val]!]! = 1 - lineProjector t := by
  rw [from_complement_entries _ _ hf.denominator_pos
    (he.targetEntry t).2, lineProjector_eq_endpointLineMatrix]

theorem helper_start_of_equations (h : Fin 439) (he : EndpointEquations) :
    certificateMatrix projections[startFrames[222+h.val]!]! = 0 :=
  from_zero_entries _ (he.helperEntry h).1

theorem helper_end_of_equations (h : Fin 439) (he : EndpointEquations)
    (hf : ProjectionEquations projections[finalFrames[222+h.val]!]!) :
    certificateMatrix projections[finalFrames[222+h.val]!]! = 1 :=
  from_one_entries _ hf.denominator_pos (he.helperEntry h).2

end CodedSorting.Construction.TensorFrameGeometry
end TensorFrameEndpoints

section TensorFrameProgram
/-!
Annotated gates retain the exact executable gate while attaching its matrix
frame. The global order below is proved to erase to the existing three-round
program. Frame correctness and the rank budget are separate theorems.
-/

set_option autoImplicit false

namespace CodedSorting.Construction.TensorFrameProgram

open CodedSorting.CircuitProgram
open ThreeCopySchedule TensorLiftProgram TensorThreeRound TensorFrameGeometry

structure FramedGate where
  gate : XorGate LocalReg
  frame : LocalMatrix

abbrev Stage := Round × (Block × FramedGate)

noncomputable def stageGate (pi : Equiv.Perm Line) (s : Stage) : XorGate GlobalReg :=
  s.2.2.gate.lift (fiberEmbedding s.1 (roundAssignment pi s.1) s.2.1)

def stageLabel (s : Stage) : GlobalMatrix :=
  globalFrame s.1 s.2.1 s.2.2.frame

noncomputable def roundStages (r : Round) (word : List FramedGate) : List Stage :=
  Finset.univ.toList.flatMap (fun block => word.map (fun g => (r, block, g)))

noncomputable def stages (one two three : List FramedGate) : List Stage :=
  roundStages .first one ++ roundStages .second two ++ roundStages .third three

theorem roundStages_program (pi : Equiv.Perm Line) (r : Round) (word : List FramedGate) :
    (roundStages r word).map (stageGate pi) =
      roundProgram (word.map FramedGate.gate) r (roundAssignment pi r) := by
  simp [roundStages, TensorLiftProgram.roundProgram, partitionProgram, List.map_flatMap, List.map_map,
    stageGate, Function.comp_def]

/-- Erasing annotations gives literally the program whose payload theorem is
proved in `TensorThreeRound`; no replacement gate is introduced. -/
theorem stages_program (pi : Equiv.Perm Line) (one two three : List FramedGate) :
    (stages one two three).map (stageGate pi) =
      threeRoundProgram (one.map FramedGate.gate) (two.map FramedGate.gate)
        (three.map FramedGate.gate) pi := by
  simp only [stages, List.map_append, roundStages_program, threeRoundProgram]

def localVisits (word : List FramedGate) (r : LocalReg) : List LocalMatrix :=
  (word.filter (fun g => decide (r ∈ g.gate.ports))).map FramedGate.frame

theorem mem_fiber_ports (pi : Equiv.Perm Line) (round : Round)
    (b c : Block) (g : FramedGate) (r : LocalReg) :
    fiberEmbedding round (roundAssignment pi round) b r ∈
      (stageGate pi (round,c,g)).ports ↔ b = c ∧ r ∈ g.gate.ports := by
  classical
  by_cases he : b = c
  · subst c
    simp [stageGate, XorGate.lift]
  · constructor
    · intro hm
      obtain ⟨s, hs, heq⟩ := Finset.mem_map.mp hm
      exact (fiberEmbedding_disjoint round (roundAssignment pi round)
        c b (Ne.symm he) s r heq).elim
    · intro hh
      exact (he hh.1).elim

/-- The chronological visits of an original register in one round come from
its unique block, in exactly local word order. -/
theorem roundStages_filter (pi : Equiv.Perm Line) (round : Round)
    (word : List FramedGate) (block : Block) (r : LocalReg) :
    (roundStages round word).filter (fun s => decide
      (fiberEmbedding round (roundAssignment pi round) block r ∈ (stageGate pi s).ports)) =
      (word.filter (fun g => decide (r ∈ g.gate.ports))).map (fun g => (round,block,g)) := by
  classical
  unfold roundStages
  rw [List.filter_flatMap]
  have hb : ∀ b : Block,
      (word.map (fun g => (round,b,g))).filter (fun s => decide
        (fiberEmbedding round (roundAssignment pi round) block r ∈ (stageGate pi s).ports)) =
      if b = block then
        (word.filter (fun g => decide (r ∈ g.gate.ports))).map (fun g => (round,b,g))
      else [] := by
    intro b
    rw [List.filter_map]
    by_cases he : b = block
    · subst b
      simp [mem_fiber_ports, Function.comp_def]
    · simp [mem_fiber_ports, Function.comp_def, he, Ne.symm he]
  simp_rw [hb]
  exact flatMap_if_single block _

theorem roundStages_labels (pi : Equiv.Perm Line) (round : Round)
    (word : List FramedGate) (block : Block) (r : LocalReg) :
    ((roundStages round word).filter (fun s => decide
      (fiberEmbedding round (roundAssignment pi round) block r ∈ (stageGate pi s).ports))).map
        stageLabel =
      (localVisits word r).map (globalFrame round block) := by
  rw [roundStages_filter]
  simp [localVisits, stageLabel, List.map_map, Function.comp_def]

end CodedSorting.Construction.TensorFrameProgram
end TensorFrameProgram
