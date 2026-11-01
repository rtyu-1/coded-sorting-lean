import CodedSorting.Circuit.Composition.TensorFrameCertifiedBudget
import CodedSorting.Circuit.NetworkModel.Adjacency

section ExchangeFrameAlgebra
/-! Address-frame identities for the actual Construction exchange.  These are identities
of rational matrices; finite specialization is performed jointly in the
separate exchange specialization module. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.ExchangeFrameAlgebra

open Matrix TriangularConjugacy

section Algebra
variable {I : Type*} [Fintype I] [DecidableEq I]

def Projection (P : Matrix I I ℚ) : Prop := Pᵀ = P ∧ P * P = P

def Nested (P Q : Matrix I I ℚ) : Prop := P * Q = P ∧ Q * P = P

theorem projection_zero : Projection (0 : Matrix I I ℚ) := by
  simp [Projection]

theorem projection_one : Projection (1 : Matrix I I ℚ) := by
  simp [Projection]

theorem projection_complement (P : Matrix I I ℚ) (hP : Projection P) :
    Projection (1 - P) := by
  refine ⟨by simp [Matrix.transpose_sub, hP.1], ?_⟩
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP.2]
  abel

theorem projection_difference (P Q : Matrix I I ℚ)
    (hP : Projection P) (hQ : Projection Q) (h : Nested P Q) :
    Projection (Q - P) := by
  refine ⟨by simp [Matrix.transpose_sub, hP.1, hQ.1], ?_⟩
  simp only [sub_mul, mul_sub, hP.2, hQ.2, h.1, h.2]
  abel

end Algebra

section Swaps
variable {I : Type*} [Fintype I] [LinearOrder I]
local instance doubledDecEq : DecidableEq (I ⊕ₗ I) :=
  (inferInstance : LinearOrder (I ⊕ₗ I)).toDecidableEq

theorem partialSwap_involution (P : Matrix I I ℚ) (hP : P * P = P) :
    partialSwap P * partialSwap P = 1 := by
  unfold partialSwap
  rw [Matrix.fromBlocks_multiply]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
  have hdiag : (1 - P - P + P) + P = 1 := by abel
  have hoff : (P - P) + (P - P) = 0 := by abel
  simp only [hdiag, hoff]
  ext r c
  rcases r with r | r <;> rcases c with c | c <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- Crossing nested frames executes a partial swap of their difference. -/
theorem partialSwap_nested (P Q : Matrix I I ℚ) (h : Nested P Q) :
    partialSwap Q * partialSwap P = partialSwap (Q - P) := by
  unfold partialSwap
  rw [Matrix.fromBlocks_multiply]
  simp only [sub_mul, mul_sub, one_mul, mul_one, h.2]
  congr 1 <;> abel

theorem partialSwap_reverse_nested (P Q : Matrix I I ℚ) (h : Nested Q P) :
    partialSwap Q * partialSwap P = partialSwap (P - Q) := by
  unfold partialSwap
  rw [Matrix.fromBlocks_multiply]
  simp only [sub_mul, mul_sub, one_mul, mul_one, h.1]
  congr 1 <;> abel

/-- Complementary endpoint frames perform the full H/D bank exchange. -/
theorem partialSwap_complement (P : Matrix I I ℚ) (hP : P * P = P) :
    partialSwap (1 - P) * partialSwap P = partialSwap 1 := by
  unfold partialSwap
  rw [Matrix.fromBlocks_multiply]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
  ext r c
  rcases r with r | r <;> rcases c with c | c <;>
    simp [Matrix.fromBlocks, Matrix.sub_apply, Matrix.add_apply] <;> ring

end Swaps

open TensorFrameGeometry TensorThreeRound ThreeCopySchedule

/-- The actual selected-session permutation pairs complementary frames,
including persistent helpers.  This is stronger than endpoint full rank. -/
theorem actual_endpoint_complement (r : IndependentStream) :
    terminalLabel (originalSwap r) = 1 - sourceLabel r := by
  rcases r with a | h
  · have hb : a.2.1 = 0 ∨ a.2.1 = 1 := by omega
    rcases hb with hb | hb
    · simp [sourceLabel, terminalLabel, originalSwap, dataTerminal, dataSource,
        dataPartner, hb, dataProjector]
    · simp [sourceLabel, terminalLabel, originalSwap, dataTerminal, dataSource,
        dataPartner, hb, dataProjector]
  · simp [sourceLabel, terminalLabel, originalSwap]

theorem actual_source_projection (r : IndependentStream) : Projection (sourceLabel r) := by
  rcases r with a | h
  · by_cases hb : a.2.1 = 0
    · simpa [sourceLabel, dataSource, hb, Projection] using
        And.intro (dataProjector_symmetric a) (dataProjector_idempotent a)
    · simp [sourceLabel, dataSource, hb, Projection]
  · simp [sourceLabel, Projection]

#print axioms actual_endpoint_complement

end CodedSorting.Construction.ExchangeFrameAlgebra
end ExchangeFrameAlgebra

section ExchangeFramePaths
/-! The actual Construction frame paths as symmetric projectors and comparable
successive labels. Temporary retained-copy paths may run downwards. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.ExchangeFramePaths

open ExchangeFrameAlgebra TensorFrameGeometry TensorFrameNetwork TensorFrameProgram
open TensorFrameGlobalVisits PhysicalFramePaths ThreeCopySchedule TensorLiftProgram
open TensorThreeRound IntegerProjection
open FiniteCertificate (gates projections startFrames finalFrames)
open CodedSorting.TensorLabels
open scoped Matrix

noncomputable section

attribute [local irreducible] forwardWord middleWord annotatedStages program
  gates projections startFrames finalFrames

def Comparable (P Q : GlobalMatrix) : Prop :=
  P = Q ∨ CodedSorting.TensorLabels.Nested P Q ∨ CodedSorting.TensorLabels.Nested Q P

theorem comparable_refl (P : GlobalMatrix) : Comparable P P := Or.inl rfl

theorem frameMatrix_projection (f : Nat) (hf : f < 636) :
    Projection (frameMatrix f) :=
  ⟨certificate_symmetric _ (allProjectionEquations f hf),
    certificate_idempotent _ (allProjectionEquations f hf)⟩

theorem tensor3_symmetric (A B C : LocalMatrix)
    (hA : Aᵀ = A) (hB : Bᵀ = B) (hC : Cᵀ = C) :
    (tensor3 A B C)ᵀ = tensor3 A B C := by
  ext i j
  change A j.1 i.1 * (B j.2.1 i.2.1 * C j.2.2 i.2.2) =
    A i.1 j.1 * (B i.2.1 j.2.1 * C i.2.2 j.2.2)
  rw [show A j.1 i.1 = A i.1 j.1 from congrFun (congrFun hA i.1) j.1,
    show B j.2.1 i.2.1 = B i.2.1 j.2.1 from congrFun (congrFun hB i.2.1) j.2.1,
    show C j.2.2 i.2.2 = C i.2.2 j.2.2 from congrFun (congrFun hC i.2.2) j.2.2]

theorem globalFrame_projection (r : TensorLiftProgram.Round) (block : Block) (P : LocalMatrix)
    (hP : Projection P) : Projection (globalFrame r block P) := by
  have hs : (liftFrame r block.2.1 block.2.2 P)ᵀ = liftFrame r block.2.1 block.2.2 P := by
    cases r <;>
      simp [liftFrame, liftBase, liftLinear, Matrix.transpose_add, Matrix.transpose_sub,
        tensor3_symmetric, lineProjector_symmetric, hP.1]
  refine ⟨?_, ?_⟩
  · ext i j
    exact congrFun (congrFun hs (copyView block.1 i)) (copyView block.1 j)
  · rw [globalFrame, globalize_mul, liftFrame_idempotent _ _ _ _ hP.2]

theorem forwardWord_projection (g : FramedGate) (hg : g ∈ forwardWord) :
    Projection g.frame := by
  rw [forwardWord] at hg
  simp only [List.mem_append, List.mem_map] at hg
  rcases hg with ((h | h) | h) | h
  · obtain ⟨g, hg, rfl⟩ := h
    exact frameMatrix_projection g.frame (ConcreteLocalProgram.prefix_frames g hg)
  · obtain ⟨t, ht, rfl⟩ := h
    exact frameMatrix_projection (510 + t.val) (by omega)
  · obtain ⟨g, hg, rfl⟩ := h
    exact frameMatrix_projection 0 (by decide)
  · obtain ⟨g, hg, rfl⟩ := h
    exact frameMatrix_projection g.frame (ConcreteLocalProgram.suffix_frames g hg)

theorem middleRawWord_projection (g : FramedGate) (hg : g ∈ middleRawWord) :
    Projection g.frame := by
  rw [middleRawWord] at hg
  simp only [List.mem_append, List.mem_map, List.mem_reverse] at hg
  rcases hg with ((h | h) | h) | h
  · obtain ⟨g, hg, rfl⟩ := h
    exact frameMatrix_projection g.frame (ConcreteLocalProgram.suffix_frames g hg)
  · obtain ⟨t, ht, rfl⟩ := h
    exact frameMatrix_projection (510 + t.val) (by omega)
  · obtain ⟨g, hg, rfl⟩ := h
    exact frameMatrix_projection 0 (by decide)
  · obtain ⟨g, hg, rfl⟩ := h
    exact frameMatrix_projection g.frame (ConcreteLocalProgram.prefix_frames g hg)

theorem middleWord_projection (g : FramedGate) (hg : g ∈ middleWord) :
    Projection g.frame := by
  rw [middleWord] at hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  change Projection (1 - a.frame)
  exact projection_complement _ (middleRawWord_projection a ha)

theorem roundStages_projection (r : TensorLiftProgram.Round) (word : List FramedGate)
    (hw : ∀ g ∈ word, Projection g.frame)
    (s : Stage) (hs : s ∈ roundStages r word) : Projection (stageLabel s) := by
  simp only [roundStages, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨block, hb, g, hg, rfl⟩ := hs
  exact globalFrame_projection r block g.frame (hw g hg)

theorem annotatedStages_projection (s : Stage) (hs : s ∈ annotatedStages) :
    Projection (stageLabel s) := by
  rw [annotatedStages, stages] at hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact roundStages_projection .first _ forwardWord_projection s hs
    · exact roundStages_projection .second _ middleWord_projection s hs
  · exact roundStages_projection .third _ forwardWord_projection s hs

theorem physicalSource_projection (r : GlobalReg) : Projection (physicalSource r) := by
  rcases r with r | ⟨round, block, t⟩
  · exact actual_source_projection r
  · unfold physicalSource tempSource
    apply globalFrame_projection
    split_ifs
    · exact projection_complement _ (frameMatrix_projection (510+t.val) (by omega))
    · exact frameMatrix_projection (510+t.val) (by omega)

theorem physicalTerminal_projection (r : GlobalReg) : Projection (physicalTerminal r) := by
  rcases r with r | ⟨round, block, t⟩
  · rcases r with a | h
    · by_cases hb : a.2.1 = 0
      · simp [physicalTerminal, terminalLabel, dataTerminal, hb, Projection]
      · simp [physicalTerminal, terminalLabel, dataTerminal, hb, Projection,
          Matrix.transpose_sub, dataProjector_symmetric, sub_mul, mul_sub,
          dataProjector_idempotent]
    · simp [physicalTerminal, terminalLabel, Projection]
  · unfold physicalTerminal tempTerminal
    apply globalFrame_projection
    split_ifs
    · exact projection_one
    · exact projection_zero

theorem nestedChain_comparable (P : GlobalMatrix) (xs : List GlobalMatrix)
    (h : IsNestedChain P xs) : List.Chain' Comparable (P :: xs) := by
  induction xs generalizing P with
  | nil => simp
  | cons Q xs ih =>
    exact List.chain'_cons.mpr ⟨by simpa using (Or.inr (Or.inl h.2.1) : Comparable P Q),
      ih Q h.2.2⟩

theorem actual_data_chain (a : DataStream) :
    IsNestedChain (dataSource a)
      (visits partner annotatedStages (.inl (.inl a)) ++ [dataTerminal a]) := by
  rw [annotatedStages, data_visits]
  have hx := round_data_global_path actualGeometryChecks .first a
  have hy := round_data_global_path actualGeometryChecks .second a
  have hz := round_data_global_path actualGeometryChecks .third a
  have hlast := join_paths_across_boundary _ _ hy (data_second_third a) hz
  have hall := join_paths_across_boundary _ _ hx (data_first_second a) hlast
  rw [dataEntry_first, dataExit_third] at hall
  simpa only [roundWord, List.append_assoc] using hall

theorem actual_helper_chain (pool : Pool) (h : Fin 439) :
    IsNestedChain 0
      (visits partner annotatedStages (.inl (.inr (pool,h))) ++ [1]) := by
  rw [annotatedStages, helper_visits]
  have hx := round_helper_global_path actualGeometryChecks .first pool h
  have hy := round_helper_global_path actualGeometryChecks .second pool h
  have hz := round_helper_global_path actualGeometryChecks .third pool h
  have hb := scheduled_helper_boundary_chain pool
  have h12 := hb.2.2.2.1
  have h23 := hb.2.2.2.2.2.2.2.1
  have hlast := join_paths_across_boundary _ _ hy h23 hz
  have hall := join_paths_across_boundary _ _ hx h12 hlast
  rw [helperEntry_first, helperExit_third] at hall
  simpa only [roundWord, List.append_assoc] using hall

theorem comparable_constant_path (P Q : GlobalMatrix) (n : Nat)
    (hPQ : Comparable P Q) :
    List.Chain' Comparable (P :: (P :: List.replicate n Q) ++ [Q]) := by
  have hh : ∀ k, List.Chain' Comparable (P :: List.replicate k Q ++ [Q]) := by
    intro k
    induction k with
    | zero => simpa using hPQ
    | succ k ih =>
      apply List.chain'_cons.mpr
      refine ⟨hPQ, ?_⟩
      have hr := List.chain'_replicate_of_rel (k + 2) (comparable_refl Q)
      simpa only [show k+2 = 1+k+1 by omega, List.replicate_add,
        List.replicate_one, List.singleton_append] using hr
  exact List.chain'_cons.mpr ⟨comparable_refl P, hh n⟩

theorem actual_temporary_chain (round : TensorLiftProgram.Round) (block : Block) (t : Fin 9) :
    List.Chain' Comparable (physicalSource (.inr (round,block,t)) ::
      visits partner annotatedStages (.inr (round,block,t)) ++
      [physicalTerminal (.inr (round,block,t))]) := by
  rw [annotatedStages, temp_visits]
  have hz : frameMatrix 0 = 0 := zero_certificate_matrix
  have hf := frameMatrix_projection (510+t.val) (by omega)
  have hzero : CodedSorting.TensorLabels.Nested
      (globalFrame round block 0) (globalFrame round block (frameMatrix (510+t.val))) :=
    globalize_nested block.1 (liftFrame_nested round _ _ _ _ (by simp) (by simp))
  have hone : CodedSorting.TensorLabels.Nested
      (globalFrame round block (1-frameMatrix (510+t.val))) (globalFrame round block 1) :=
    globalize_nested block.1 (liftFrame_nested round _ _ _ _ (by simp) (by simp))
  cases round with
  | first =>
    obtain ⟨n, hn⟩ := forward_temporary_visits t actualGeometryChecks.operands
    change localVisits forwardWord (.inr (.inr t)) = _ at hn
    rw [hn, List.map_cons, List.map_replicate, hz]
    exact comparable_constant_path _ _ n (Or.inr (Or.inr hzero))
  | second =>
    obtain ⟨n, hn⟩ := middle_temporary_visits t actualGeometryChecks.operands
    change localVisits middleWord (.inr (.inr t)) = _ at hn
    rw [hn, List.map_cons, List.map_replicate, hz, sub_zero]
    exact comparable_constant_path _ _ n (Or.inr (Or.inl hone))
  | third =>
    obtain ⟨n, hn⟩ := forward_temporary_visits t actualGeometryChecks.operands
    change localVisits forwardWord (.inr (.inr t)) = _ at hn
    rw [hn, List.map_cons, List.map_replicate, hz]
    exact comparable_constant_path _ _ n (Or.inr (Or.inr hzero))

theorem actual_register_chain (r : GlobalReg) :
    List.Chain' Comparable (physicalSource r ::
      visits partner annotatedStages r ++ [physicalTerminal r]) := by
  rcases r with (a | ⟨pool, h⟩) | ⟨round, block, t⟩
  · exact nestedChain_comparable _ _ (actual_data_chain a)
  · exact nestedChain_comparable _ _ (actual_helper_chain pool h)
  · exact actual_temporary_chain round block t

open CodedSorting.ProgramNetwork CodedSorting.StageLabels

theorem rawLabel_projection
    (v : Vertex GlobalReg (annotatedStages.map (stageGate partner)).length) :
    Projection (rawLabel v) := by
  cases v with
  | source r => exact physicalSource_projection r
  | sink r => exact physicalTerminal_projection r
  | gate i =>
    exact annotatedStages_projection _ (List.get_mem _ _)
  | pass i r =>
    apply MachineNetworkAdjacency.stageLabels_property Projection
      (fun s => decide (r ∈ (stageGate partner s).ports)) stageLabel annotatedStages
      (physicalSource r) (physicalSource_projection r)
      (fun s hs _ => annotatedStages_projection s hs)
    exact List.get_mem _ _

theorem raw_edge_comparable
    (e : Wire GlobalReg (annotatedStages.map (stageGate partner)).length) :
    Comparable (rawLabel (wireTail (annotatedStages.map (stageGate partner)) e))
      (rawLabel (wireHead (annotatedStages.map (stageGate partner)) e)) :=
  MachineNetworkAdjacency.physical_edge_relation Comparable comparable_refl
    annotatedStages (stageGate partner) stageLabel physicalSource physicalTerminal e
      (actual_register_chain e.2)

theorem transport_vertex_property {Reg : Type*} [DecidableEq Reg]
    {p q : List (CodedSorting.CircuitProgram.XorGate Reg)} (h : p = q)
    (label : Vertex Reg p.length → GlobalMatrix) (Good : GlobalMatrix → Prop)
    (hg : ∀ v, Good (label v)) : ∀ v, Good (transportLabel h label v) := by
  subst q
  exact hg

theorem transport_edge_relation {Reg : Type*} [DecidableEq Reg]
    {p q : List (CodedSorting.CircuitProgram.XorGate Reg)} (h : p = q)
    (label : Vertex Reg p.length → GlobalMatrix) (R : GlobalMatrix → GlobalMatrix → Prop)
    (hr : ∀ e, R (label (wireTail p e)) (label (wireHead p e))) :
    ∀ e, R (transportLabel h label (wireTail q e))
      (transportLabel h label (wireHead q e)) := by
  subst q
  exact hr

theorem actualLabel_projection (v : Vertex GlobalReg program.length) :
    Projection (actualLabel v) :=
  transport_vertex_property annotatedStages_program rawLabel Projection rawLabel_projection v

/-- Every literal physical edge has comparable symmetric projector labels,
including zero-cost subdivisions and reversed temporary transitions. -/
theorem actual_edge_comparable (e : Wire GlobalReg program.length) :
    Comparable (actualLabel (wireTail program e)) (actualLabel (wireHead program e)) :=
  transport_edge_relation annotatedStages_program rawLabel Comparable raw_edge_comparable e

#print axioms actualLabel_projection
#print axioms actual_edge_comparable

end
end CodedSorting.Construction.ExchangeFramePaths
end ExchangeFramePaths
