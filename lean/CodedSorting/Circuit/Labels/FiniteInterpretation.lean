import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import CodedSorting.Generated.FiniteCircuit.EndpointAlgebraChecks

section IntegerProjection
/-!
# Integer certificates as actual rational projections

The finite certificate stores an integer numerator and a positive integer
denominator. This file proves the generic algebraic bridge to Mathlib matrices,
their ranges and their actual ranks. Every integer equation remains an explicit
input: no claim that the large concrete Boolean certificate has been proved is
made here.
-/

namespace CodedSorting.Construction.IntegerProjection

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I]

def projectionOfInts (denominator : Int) (numerator : Matrix I I Int) : Matrix I I ℚ :=
  fun i j => (numerator i j : ℚ) / (denominator : ℚ)

def vectorOfInts (v : I → Int) : I → ℚ := fun i => (v i : ℚ)

theorem denominator_ne_zero {d : Int} (hd : 0 < d) : (d : ℚ) ≠ 0 := by
  exact_mod_cast (ne_of_gt hd)

omit [Fintype I] in
theorem symmetric (d : Int) (N : Matrix I I Int)
    (hN : ∀ i j, N i j = N j i) :
    (projectionOfInts d N)ᵀ = projectionOfInts d N := by
  ext i j
  simp only [Matrix.transpose_apply, projectionOfInts, hN j i]

/-- A cleared product equation gives the genuine rational product equation. -/
theorem multiply (d e : Int) (N M : Matrix I I Int)
    (hd : 0 < d) (he : 0 < e)
    (hMN : ∀ i j, ∑ k, M i k * N k j = e * N i j) :
    projectionOfInts e M * projectionOfInts d N = projectionOfInts d N := by
  ext i j
  have hs : (∑ k, (M i k : ℚ) * (N k j : ℚ)) = (e : ℚ) * (N i j : ℚ) := by
    exact_mod_cast hMN i j
  calc
    _ = (∑ k, (M i k : ℚ) * (N k j : ℚ)) / ((e : ℚ) * (d : ℚ)) := by
      simp only [Matrix.mul_apply, projectionOfInts]
      simp_rw [div_mul_div_comm]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = ((e : ℚ) * (N i j : ℚ)) / ((e : ℚ) * (d : ℚ)) := by rw [hs]
    _ = _ := by
      dsimp [projectionOfInts]
      field_simp [denominator_ne_zero hd, denominator_ne_zero he]
      ring

theorem idempotent (d : Int) (N : Matrix I I Int) (hd : 0 < d)
    (hNN : ∀ i j, ∑ k, N i k * N k j = d * N i j) :
    projectionOfInts d N * projectionOfInts d N = projectionOfInts d N :=
  multiply d d N N hd hd hNN

/-- One product direction suffices for nested symmetric projections. -/
theorem nested (d e : Int) (N M : Matrix I I Int)
    (hd : 0 < d) (he : 0 < e)
    (hN : ∀ i j, N i j = N j i) (hM : ∀ i j, M i j = M j i)
    (hMN : ∀ i j, ∑ k, M i k * N k j = e * N i j) :
    projectionOfInts d N * projectionOfInts e M = projectionOfInts d N ∧
    projectionOfInts e M * projectionOfInts d N = projectionOfInts d N := by
  have h := multiply d e N M hd he hMN
  refine ⟨?_, h⟩
  have ht := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul, symmetric d N hN, symmetric e M hM] using ht

theorem fixes_integer_vector (d : Int) (N : Matrix I I Int) (v : I → Int)
    (hd : 0 < d) (hv : ∀ i, ∑ k, N i k * v k = d * v i) :
    projectionOfInts d N *ᵥ vectorOfInts v = vectorOfInts v := by
  ext i
  have hs : (∑ k, (N i k : ℚ) * (v k : ℚ)) = (d : ℚ) * (v i : ℚ) := by
    exact_mod_cast hv i
  calc
    _ = (∑ k, (N i k : ℚ) * (v k : ℚ)) / (d : ℚ) := by
      simp only [Matrix.mulVec, dotProduct, projectionOfInts, vectorOfInts]
      simp_rw [div_mul_eq_mul_div]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = ((d : ℚ) * (v i : ℚ)) / (d : ℚ) := by rw [hs]
    _ = _ := by
      dsimp [vectorOfInts]
      field_simp [denominator_ne_zero hd]

theorem integer_vector_mem_range (d : Int) (N : Matrix I I Int) (v : I → Int)
    (hd : 0 < d) (hv : ∀ i, ∑ k, N i k * v k = d * v i) :
    vectorOfInts v ∈ LinearMap.range (projectionOfInts d N).mulVecLin :=
  ⟨vectorOfInts v, fixes_integer_vector d N v hd hv⟩

theorem fixes_integer_vector_iff (d : Int) (N : Matrix I I Int) (v : I → Int)
    (hd : 0 < d) :
    projectionOfInts d N *ᵥ vectorOfInts v = vectorOfInts v ↔
      ∀ i, ∑ k, N i k * v k = d * v i := by
  constructor
  · intro h i
    have hi := congrFun h i
    have hs : (∑ k, (N i k : ℚ) * (v k : ℚ)) / (d : ℚ) = (v i : ℚ) := by
      calc
        _ = (projectionOfInts d N *ᵥ vectorOfInts v) i := by
          simp only [Matrix.mulVec, dotProduct, projectionOfInts, vectorOfInts]
          simp_rw [div_mul_eq_mul_div]
          simp only [div_eq_mul_inv, Finset.sum_mul]
        _ = _ := hi
    have ht : (∑ k, (N i k : ℚ) * (v k : ℚ)) = (d : ℚ) * (v i : ℚ) := by
      simpa only [mul_comm] using (div_eq_iff (denominator_ne_zero hd)).mp hs
    exact_mod_cast ht
  · exact fixes_integer_vector d N v hd

theorem mem_range_iff_fixed (P : Matrix I I ℚ) (hP : P * P = P) (v : I → ℚ) :
    v ∈ LinearMap.range P.mulVecLin ↔ P *ᵥ v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change P *ᵥ (P *ᵥ w) = P *ᵥ w
    rw [Matrix.mulVec_mulVec, hP]
  · intro h
    exact ⟨v, h⟩

theorem integer_vector_mem_range_iff (d : Int) (N : Matrix I I Int) (v : I → Int)
    (hd : 0 < d) (hNN : ∀ i j, ∑ k, N i k * N k j = d * N i j) :
    vectorOfInts v ∈ LinearMap.range (projectionOfInts d N).mulVecLin ↔
      ∀ i, ∑ k, N i k * v k = d * v i := by
  rw [mem_range_iff_fixed _ (idempotent d N hd hNN), fixes_integer_vector_iff d N v hd]

theorem range_le_of_integer_product (d e : Int) (N M : Matrix I I Int)
    (hd : 0 < d) (he : 0 < e)
    (hMN : ∀ i j, ∑ k, M i k * N k j = e * N i j) :
    LinearMap.range (projectionOfInts d N).mulVecLin ≤
      LinearMap.range (projectionOfInts e M).mulVecLin := by
  rintro x ⟨y, rfl⟩
  refine ⟨projectionOfInts d N *ᵥ y, ?_⟩
  change projectionOfInts e M *ᵥ (projectionOfInts d N *ᵥ y) = _
  rw [Matrix.mulVec_mulVec, multiply d e N M hd he hMN]
  rfl

theorem trace_of_integer_trace (d : Int) (N : Matrix I I Int) (dimension : Nat)
    (hd : 0 < d) (ht : ∑ i, N i i = d * (dimension : Int)) :
    Matrix.trace (projectionOfInts d N) = (dimension : ℚ) := by
  have hs : (∑ i, (N i i : ℚ)) = (d : ℚ) * (dimension : ℚ) := by
    exact_mod_cast ht
  calc
    _ = (∑ i, (N i i : ℚ)) / (d : ℚ) := by
      simp only [Matrix.trace, Matrix.diag, projectionOfInts, div_eq_mul_inv, Finset.sum_mul]
    _ = ((d : ℚ) * (dimension : ℚ)) / (d : ℚ) := by rw [hs]
    _ = _ := by field_simp [denominator_ne_zero hd]

/-- The trace of an idempotent is its actual Mathlib matrix rank. -/
theorem trace_eq_rank (P : Matrix I I ℚ) (hP : P * P = P) :
    Matrix.trace P = (P.rank : ℚ) := by
  classical
  have hproj : LinearMap.IsProj (LinearMap.range P.mulVecLin) P.mulVecLin := by
    constructor
    · intro x
      exact LinearMap.mem_range_self _ x
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      change P *ᵥ (P *ᵥ y) = P *ᵥ y
      rw [Matrix.mulVec_mulVec, hP]
  have ht := hproj.trace
  rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ I),
    LinearMap.toMatrix_eq_toMatrix', ← Matrix.toLin'_apply',
    LinearMap.toMatrix'_toLin'] at ht
  exact ht

theorem rank_of_integer_trace (d : Int) (N : Matrix I I Int) (dimension : Nat)
    (hd : 0 < d)
    (hNN : ∀ i j, ∑ k, N i k * N k j = d * N i j)
    (ht : ∑ i, N i i = d * (dimension : Int)) :
    (projectionOfInts d N).rank = dimension := by
  have hr := trace_eq_rank (projectionOfInts d N) (idempotent d N hd hNN)
  rw [trace_of_integer_trace d N dimension hd ht] at hr
  exact_mod_cast hr.symm

/-- Exact indexing used by the finite certificate's 8 by 8 flattened arrays. -/
def certificateNumerator (p : FiniteCertificate.Projection) : Matrix (Fin 8) (Fin 8) Int :=
  fun i j => p.numerator[8 * i.val + j.val]!

def certificateMatrix (p : FiniteCertificate.Projection) : Matrix (Fin 8) (Fin 8) ℚ :=
  projectionOfInts p.denominator (certificateNumerator p)

/-- The exact algebraic obligations extracted from a finite array certificate. -/
structure ProjectionEquations (p : FiniteCertificate.Projection) : Prop where
  denominator_pos : 0 < p.denominator
  numerator_size : p.numerator.size = 64
  numerator_symmetric : ∀ i j, certificateNumerator p i j = certificateNumerator p j i
  numerator_idempotent : ∀ i j,
    ∑ k, certificateNumerator p i k * certificateNumerator p k j =
      p.denominator * certificateNumerator p i j
  numerator_trace : ∑ i, certificateNumerator p i i = p.denominator * (p.dimension : Int)

def certificateFrame (p : FiniteCertificate.Projection) : Submodule ℚ (Fin 8 → ℚ) :=
  LinearMap.range (certificateMatrix p).mulVecLin

theorem certificate_symmetric (p : FiniteCertificate.Projection) (h : ProjectionEquations p) :
    (certificateMatrix p)ᵀ = certificateMatrix p :=
  symmetric _ _ h.numerator_symmetric

theorem certificate_idempotent (p : FiniteCertificate.Projection) (h : ProjectionEquations p) :
    certificateMatrix p * certificateMatrix p = certificateMatrix p :=
  idempotent _ _ h.denominator_pos h.numerator_idempotent

theorem certificate_rank (p : FiniteCertificate.Projection) (h : ProjectionEquations p) :
    (certificateMatrix p).rank = p.dimension :=
  rank_of_integer_trace _ _ _ h.denominator_pos h.numerator_idempotent h.numerator_trace

theorem certificate_frame_finrank (p : FiniteCertificate.Projection) (h : ProjectionEquations p) :
    Module.finrank ℚ (certificateFrame p) = p.dimension :=
  certificate_rank p h

theorem certificate_frame_membership (p : FiniteCertificate.Projection)
    (h : ProjectionEquations p) (v : Fin 8 → Int) :
    vectorOfInts v ∈ certificateFrame p ↔
      ∀ i, ∑ k, certificateNumerator p i k * v k = p.denominator * v i :=
  integer_vector_mem_range_iff _ _ _ h.denominator_pos h.numerator_idempotent

end CodedSorting.Construction.IntegerProjection
end IntegerProjection

section EndpointEquations
/-! Only the concrete endpoint integer equations used by the network proof.
The certificate producer proves these without any line-membership tables. -/

namespace CodedSorting.Construction

open FiniteCertificate IntegerProjection

def endpointLine (t : Nat) (i : Fin 8) : Int := (lines[t]!)[i.val]!

structure EndpointEquations : Prop where
  sourceEntry : ∀ a : Fin 111,
    (∀ i j : Fin 8,
      4 * certificateNumerator projections[startFrames[a.val]!]! i j =
        projections[startFrames[a.val]!]!.denominator * endpointLine a.val i * endpointLine a.val j) ∧
    (∀ i j : Fin 8, certificateNumerator projections[finalFrames[a.val]!]! i j =
      if i = j then projections[finalFrames[a.val]!]!.denominator else 0)
  targetEntry : ∀ a : Fin 111,
    (∀ i j : Fin 8,
      certificateNumerator projections[startFrames[111+a.val]!]! i j = 0) ∧
    (∀ i j : Fin 8,
      4 * certificateNumerator projections[finalFrames[111+a.val]!]! i j =
        projections[finalFrames[111+a.val]!]!.denominator *
          ((if i = j then 4 else 0) - endpointLine a.val i * endpointLine a.val j))
  helperEntry : ∀ h : Fin 439,
    (∀ i j : Fin 8,
      certificateNumerator projections[startFrames[222+h.val]!]! i j = 0) ∧
    (∀ i j : Fin 8,
      certificateNumerator projections[finalFrames[222+h.val]!]! i j =
        if i = j then projections[finalFrames[222+h.val]!]!.denominator else 0)

end CodedSorting.Construction
end EndpointEquations

section FiniteProjectionInterpretation
/-!
# Meaning of the finite projection checker

Theorems in this file interpret a successful finite Boolean check in actual
rational linear algebra. They do not assert that any particular large check
has evaluated to true.
-/

namespace CodedSorting.Construction.FiniteProjectionInterpretation

open scoped BigOperators Matrix
open FiniteCertificate IntegerProjection

theorem range_eight_fold_sum (f : Nat → Int) :
    (List.range 8).foldl (fun s k => s + f k) 0 = ∑ i : Fin 8, f i.val := by
  simp [List.range_succ, Fin.sum_univ_succ, add_assoc]

theorem all_eight_iff (p : Nat → Bool) :
    (List.range 8).all p = true ↔ ∀ i : Fin 8, p i.val = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h i hi
    exact h ⟨i, hi⟩

/-- Extract the integer equations without evaluating the underlying arrays. -/
theorem projection_equations_of_valid (f : Nat) (hf : frameProjectionValid f = true) :
    ProjectionEquations projections[f]! := by
  unfold frameProjectionValid at hf
  simp only [Id.run, Bind.bind, Pure.pure] at hf
  split at hf
  · cases hf
  · rename_i hp
    split at hf
    · cases hf
    · rename_i hm
      split at hf
      · cases hf
      · rename_i ht
        have hp' : (0 < projections[f]!.denominator ∧ projections[f]!.numerator.size = 64) ∧
            projections[f]!.dimension ≤ 8 := by
          simpa using hp
        simp at hm
        refine ⟨hp'.1.1, hp'.1.2, ?_, ?_, ?_⟩
        · intro i j
          have hij := hm i.val i.isLt j.val j.isLt
          simpa [certificateNumerator, matrixEntry] using hij.1
        · intro i j
          have hij := hm i.val i.isLt j.val j.isLt
          have heq := hij.2
          simpa [range_eight_fold_sum, certificateNumerator, matrixEntry] using heq
        · simpa [range_eight_fold_sum, certificateNumerator, matrixEntry] using ht

def lineVector (t : Nat) : Fin 8 → Int := fun i => (lines[t]!)[i.val]!

theorem checked_frame_rank (f : Nat) (hf : frameProjectionValid f = true) :
    (certificateMatrix projections[f]!).rank = projections[f]!.dimension :=
  certificate_rank _ (projection_equations_of_valid f hf)

theorem checked_frame_finrank (f : Nat) (hf : frameProjectionValid f = true) :
    Module.finrank ℚ (certificateFrame projections[f]!) = projections[f]!.dimension :=
  certificate_frame_finrank _ (projection_equations_of_valid f hf)

theorem checked_frame_membership (f t : Nat) (ht : t < portCount)
    (hf : frameProjectionValid f = true) :
    vectorOfInts (lineVector t) ∈ certificateFrame projections[f]! ↔
      frames[f]!.contains t = true := by
  rw [certificate_frame_membership _ (projection_equations_of_valid f hf)]
  unfold frameProjectionValid at hf
  simp only [Id.run, Bind.bind, Pure.pure] at hf
  split at hf
  · cases hf
  · split at hf
    · cases hf
    · split at hf
      · cases hf
      · have heq := (List.all_eq_true.mp hf) t (List.mem_range.mpr ht)
        have heq' : (List.range 8).all (fun i =>
            dotLine projections[f]! i lines[t]! == projections[f]!.denominator * (lines[t]!)[i]!) =
            frames[f]!.contains t := by
          simpa using heq
        rw [← heq', all_eight_iff]
        simp [dotLine, range_eight_fold_sum, certificateNumerator, matrixEntry, lineVector]

theorem integer_nested_of_checked (a b : Nat) (h : frameNested a b = true) :
    ∀ i j : Fin 8,
      ∑ k, certificateNumerator projections[b]! i k * certificateNumerator projections[a]! k j =
        projections[b]!.denominator * certificateNumerator projections[a]! i j := by
  simp [frameNested] at h
  intro i j
  have hij := h i.val i.isLt j.val j.isLt
  simpa [range_eight_fold_sum, certificateNumerator, matrixEntry] using hij

theorem checked_frame_nested (a b : Nat)
    (ha : frameProjectionValid a = true) (hb : frameProjectionValid b = true)
    (hab : frameNested a b = true) :
    certificateMatrix projections[a]! * certificateMatrix projections[b]! =
        certificateMatrix projections[a]! ∧
      certificateMatrix projections[b]! * certificateMatrix projections[a]! =
        certificateMatrix projections[a]! := by
  have hpa := projection_equations_of_valid a ha
  have hpb := projection_equations_of_valid b hb
  exact nested _ _ _ _ hpa.denominator_pos hpb.denominator_pos
    hpa.numerator_symmetric hpb.numerator_symmetric (integer_nested_of_checked a b hab)

theorem checked_frame_inclusion (a b : Nat)
    (ha : frameProjectionValid a = true) (hb : frameProjectionValid b = true)
    (hab : frameNested a b = true) :
    certificateFrame projections[a]! ≤ certificateFrame projections[b]! := by
  have hpa := projection_equations_of_valid a ha
  have hpb := projection_equations_of_valid b hb
  exact range_le_of_integer_product _ _ _ _ hpa.denominator_pos hpb.denominator_pos
    (integer_nested_of_checked a b hab)

end CodedSorting.Construction.FiniteProjectionInterpretation
end FiniteProjectionInterpretation

section EndpointAlgebraInterpretation
namespace CodedSorting.Construction
open FiniteCertificate IntegerProjection

private theorem sourceMatrixEntries (p q : Projection) (line : Array Int)
    (hc : endpointMatrixCheck 0 p q line = true) (i j : Fin 8) :
    (4 * matrixEntry p i.val j.val = p.denominator * line[i.val]! * line[j.val]!) ∧
    (matrixEntry q i.val j.val = if i.val = j.val then q.denominator else 0) := by
  simp only [endpointMatrixCheck, List.all_eq_true, List.mem_range] at hc
  simpa only [ite_true, Bool.and_eq_true, beq_iff_eq] using hc i.val i.isLt j.val j.isLt

private theorem targetMatrixEntries (p q : Projection) (line : Array Int)
    (hc : endpointMatrixCheck 1 p q line = true) (i j : Fin 8) :
    (matrixEntry p i.val j.val = 0) ∧
    (4 * matrixEntry q i.val j.val = q.denominator *
      ((if i.val = j.val then 4 else 0) - line[i.val]! * line[j.val]!)) := by
  simp only [endpointMatrixCheck, List.all_eq_true, List.mem_range] at hc
  simpa only [Nat.one_ne_zero, ite_false, ite_true, Bool.and_eq_true, beq_iff_eq] using hc i.val i.isLt j.val j.isLt

private theorem helperMatrixEntries (p q : Projection)
    (hc : endpointMatrixCheck 2 p q #[] = true) (i j : Fin 8) :
    (matrixEntry p i.val j.val = 0) ∧
    (matrixEntry q i.val j.val = if i.val = j.val then q.denominator else 0) := by
  simp only [endpointMatrixCheck, List.all_eq_true, List.mem_range] at hc
  simpa only [Nat.reduceEqDiff, ite_false, Bool.and_eq_true, beq_iff_eq] using hc i.val i.isLt j.val j.isLt

theorem endpoint_equations_of_checks
    (hc : ∀ r : Nat, r < 661 → endpointAlgebraAt r = true) : EndpointEquations := by
  constructor
  · intro a
    have ha : a.val < portCount := a.isLt
    have h := hc a.val (by have ht := a.isLt; omega)
    rw [endpointAlgebraAt, if_pos ha] at h
    have hh := sourceMatrixEntries _ _ _ h
    constructor <;> intro i j
    · simpa only [certificateNumerator, matrixEntry, endpointLine] using
        (hh i j).1
    · simpa only [certificateNumerator, matrixEntry, endpointLine, Fin.ext_iff, portCount, Nat.add_sub_cancel_left] using
        (hh i j).2
  · intro a
    have h0 : ¬111 + a.val < portCount := by simp only [portCount]; omega
    have h1 : 111 + a.val < 2 * portCount := by
      have ht := a.isLt
      simp only [portCount]
      omega
    have h := hc (111+a.val) (by have ht := a.isLt; omega)
    rw [endpointAlgebraAt, if_neg h0, if_pos h1] at h
    have hh := targetMatrixEntries _ _ _ h
    constructor <;> intro i j
    · simpa only [certificateNumerator, matrixEntry] using
        (hh i j).1
    · simpa only [certificateNumerator, matrixEntry, endpointLine, Fin.ext_iff, portCount, Nat.add_sub_cancel_left] using
        (hh i j).2
  · intro a
    have h0 : ¬222 + a.val < portCount := by simp only [portCount]; omega
    have h1 : ¬222 + a.val < 2 * portCount := by simp only [portCount]; omega
    have h := hc (222+a.val) (by have ht := a.isLt; omega)
    rw [endpointAlgebraAt, if_neg h0, if_neg h1] at h
    have hh := helperMatrixEntries _ _ h
    constructor <;> intro i j
    · simpa only [certificateNumerator, matrixEntry] using
        (hh i j).1
    · simpa only [certificateNumerator, matrixEntry, Fin.ext_iff] using
        (hh i j).2

end CodedSorting.Construction
end EndpointAlgebraInterpretation

section FiniteEndpointInterpretation
/-! The concrete endpoint checker implies the actual rational endpoint
matrices. All checker success hypotheses are explicit. -/

namespace CodedSorting.Construction.FiniteEndpointInterpretation

open scoped BigOperators Matrix
open FiniteCertificate IntegerProjection FiniteProjectionInterpretation

def lineMatrix (t : Nat) : Matrix (Fin 8) (Fin 8) ℚ :=
  (1 / 4 : ℚ) • Matrix.vecMulVec (vectorOfInts (lineVector t)) (vectorOfInts (lineVector t))

theorem source_entries (t : Fin 111) (he : endpointsValid = true) :
    (∀ i j : Fin 8,
      4 * certificateNumerator projections[startFrames[t.val]!]! i j =
        projections[startFrames[t.val]!]!.denominator * lineVector t.val i * lineVector t.val j) ∧
    (∀ i j : Fin 8,
      certificateNumerator projections[finalFrames[t.val]!]! i j =
        if i = j then projections[finalFrames[t.val]!]!.denominator else 0) := by
  simp [endpointsValid] at he
  have hr : t.val < registerCount := by
    have ht := t.isLt
    simp only [registerCount]
    omega
  have ht : t.val < portCount := t.isLt
  have h := he t.val hr
  simp only [ht, if_pos] at h
  constructor <;> intro i j
  · have hij := (h.2 i.val i.isLt j.val j.isLt).1
    simpa [certificateNumerator, matrixEntry, lineVector] using hij
  · have hij := (h.2 i.val i.isLt j.val j.isLt).2
    simpa [certificateNumerator, matrixEntry, Fin.ext_iff] using hij

theorem target_entries (t : Fin 111) (he : endpointsValid = true) :
    (∀ i j : Fin 8,
      certificateNumerator projections[startFrames[portCount + t.val]!]! i j = 0) ∧
    (∀ i j : Fin 8,
      4 * certificateNumerator projections[finalFrames[portCount + t.val]!]! i j =
        projections[finalFrames[portCount + t.val]!]!.denominator *
          ((if i = j then 4 else 0) - lineVector t.val i * lineVector t.val j)) := by
  simp [endpointsValid] at he
  have hr : portCount + t.val < registerCount := by
    have ht := t.isLt
    simp only [portCount, registerCount]
    omega
  have ht : ¬portCount + t.val < portCount := by omega
  have ht' : portCount + t.val < 2 * portCount := by
    have h := t.isLt
    simp only [portCount]
    omega
  have h := he (portCount + t.val) hr
  simp only [ht, if_neg, ht', if_pos] at h
  constructor <;> intro i j
  · have hij := (h.1.2 i.val i.isLt j.val j.isLt).1
    simpa [certificateNumerator, matrixEntry] using hij
  · have hij := (h.1.2 i.val i.isLt j.val j.isLt).2
    simpa [certificateNumerator, matrixEntry, lineVector, Fin.ext_iff] using hij

theorem helper_entries (r : Nat) (hr : 2 * portCount ≤ r) (hr' : r < registerCount)
    (he : endpointsValid = true) :
    (∀ i j : Fin 8, certificateNumerator projections[startFrames[r]!]! i j = 0) ∧
    (∀ i j : Fin 8, certificateNumerator projections[finalFrames[r]!]! i j =
      if i = j then projections[finalFrames[r]!]!.denominator else 0) := by
  simp [endpointsValid] at he
  have ht : ¬r < portCount := by omega
  have ht' : ¬r < 2 * portCount := by omega
  have h := he r hr'
  simp only [ht, ht', if_neg] at h
  constructor <;> intro i j
  · have hij := (h.2 i.val i.isLt j.val j.isLt).1
    simpa [certificateNumerator, matrixEntry] using hij
  · have hij := (h.2 i.val i.isLt j.val j.isLt).2
    simpa [certificateNumerator, matrixEntry, Fin.ext_iff] using hij

private theorem matrix_eq_zero (p : Projection)
    (h : ∀ i j : Fin 8, certificateNumerator p i j = 0) :
    certificateMatrix p = 0 := by
  ext i j
  simp [certificateMatrix, projectionOfInts, h]

private theorem matrix_eq_one (p : Projection) (hd : 0 < p.denominator)
    (h : ∀ i j : Fin 8, certificateNumerator p i j = if i = j then p.denominator else 0) :
    certificateMatrix p = 1 := by
  ext i j
  by_cases hij : i = j
  · simp only [certificateMatrix, projectionOfInts, h, Matrix.one_apply, hij, if_true]
    exact div_self (denominator_ne_zero hd)
  · simp [certificateMatrix, projectionOfInts, h, Matrix.one_apply, hij]

private theorem matrix_eq_line (p : Projection) (t : Nat) (hd : 0 < p.denominator)
    (h : ∀ i j : Fin 8, 4 * certificateNumerator p i j =
      p.denominator * lineVector t i * lineVector t j) :
    certificateMatrix p = lineMatrix t := by
  ext i j
  have hc : 4 * (certificateNumerator p i j : ℚ) =
      (p.denominator : ℚ) * (lineVector t i : ℚ) * (lineVector t j : ℚ) := by
    exact_mod_cast h i j
  simp only [certificateMatrix, projectionOfInts, lineMatrix, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, vectorOfInts]
  apply (div_eq_iff (denominator_ne_zero hd)).mpr
  nlinarith only [hc]

private theorem matrix_eq_complement (p : Projection) (t : Nat) (hd : 0 < p.denominator)
    (h : ∀ i j : Fin 8, 4 * certificateNumerator p i j =
      p.denominator * ((if i = j then 4 else 0) - lineVector t i * lineVector t j)) :
    certificateMatrix p = 1 - lineMatrix t := by
  ext i j
  have hc : 4 * (certificateNumerator p i j : ℚ) = (p.denominator : ℚ) *
      ((if i = j then 4 else 0) - (lineVector t i : ℚ) * (lineVector t j : ℚ)) := by
    exact_mod_cast h i j
  simp only [certificateMatrix, projectionOfInts, lineMatrix, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, vectorOfInts, Matrix.sub_apply, Matrix.one_apply]
  apply (div_eq_iff (denominator_ne_zero hd)).mpr
  by_cases hij : i = j
  · simp only [hij, if_true] at hc ⊢
    nlinarith only [hc]
  · simp only [hij, if_false] at hc ⊢
    nlinarith only [hc]

theorem checked_source_start (t : Fin 111) (he : endpointsValid = true)
    (hf : frameProjectionValid startFrames[t.val]! = true) :
    certificateMatrix projections[startFrames[t.val]!]! = lineMatrix t.val :=
  matrix_eq_line _ _ (projection_equations_of_valid _ hf).denominator_pos (source_entries t he).1

theorem checked_source_end (t : Fin 111) (he : endpointsValid = true)
    (hf : frameProjectionValid finalFrames[t.val]! = true) :
    certificateMatrix projections[finalFrames[t.val]!]! = 1 :=
  matrix_eq_one _ (projection_equations_of_valid _ hf).denominator_pos (source_entries t he).2

theorem checked_target_start (t : Fin 111) (he : endpointsValid = true) :
    certificateMatrix projections[startFrames[portCount + t.val]!]! = 0 :=
  matrix_eq_zero _ (target_entries t he).1

theorem checked_target_end (t : Fin 111) (he : endpointsValid = true)
    (hf : frameProjectionValid finalFrames[portCount + t.val]! = true) :
    certificateMatrix projections[finalFrames[portCount + t.val]!]! = 1 - lineMatrix t.val :=
  matrix_eq_complement _ _ (projection_equations_of_valid _ hf).denominator_pos
    (target_entries t he).2

theorem checked_helper_start (r : Nat) (hr : 2 * portCount ≤ r) (hr' : r < registerCount)
    (he : endpointsValid = true) :
    certificateMatrix projections[startFrames[r]!]! = 0 :=
  matrix_eq_zero _ (helper_entries r hr hr' he).1

theorem checked_helper_end (r : Nat) (hr : 2 * portCount ≤ r) (hr' : r < registerCount)
    (he : endpointsValid = true) (hf : frameProjectionValid finalFrames[r]! = true) :
    certificateMatrix projections[finalFrames[r]!]! = 1 :=
  matrix_eq_one _ (projection_equations_of_valid _ hf).denominator_pos (helper_entries r hr hr' he).2

end CodedSorting.Construction.FiniteEndpointInterpretation
end FiniteEndpointInterpretation

section FiniteEndpointEquations
namespace CodedSorting.Construction

theorem actualEndpointEquations : EndpointEquations :=
  endpoint_equations_of_checks FiniteCertificate.allEndpointAlgebraValid

#print axioms actualEndpointEquations
end CodedSorting.Construction
end FiniteEndpointEquations
