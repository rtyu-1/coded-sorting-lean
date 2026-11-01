import CodedSorting.Circuit.MemoryAccess.PhysicalFrameWord

section TensorFrameBoundaries
/-!
Exact data-entry and data-exit labels for the executable cyclic fibers.
Inter-round data conversions are inclusions, not identities; their costs
are retained by inserting these entries into the full monotone wire path.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.TensorFrameGeometry

noncomputable section

open scoped Matrix Kronecker
open ThreeCopySchedule TensorLiftProgram
open CodedSorting.TensorLabels

theorem tensor3_add_first (A B C D : LocalMatrix) :
    tensor3 (A + B) C D = tensor3 A C D + tensor3 B C D := by
  ext i j
  simp [tensor3, Matrix.kroneckerMap_apply]
  ring

theorem tensor3_add_second (A B C D : LocalMatrix) :
    tensor3 A (B + C) D = tensor3 A B D + tensor3 A C D := by
  ext i j
  simp [tensor3, Matrix.kroneckerMap_apply]
  ring

theorem tensor3_sub_first (A B C D : LocalMatrix) :
    tensor3 (A - B) C D = tensor3 A C D - tensor3 B C D := by
  ext i j
  simp [tensor3, Matrix.kroneckerMap_apply]
  ring

theorem tensor3_sub_second (A B C D : LocalMatrix) :
    tensor3 A (B - C) D = tensor3 A B D - tensor3 A C D := by
  ext i j
  simp [tensor3, Matrix.kroneckerMap_apply]
  ring

theorem tensor3_sub_third (A B C D : LocalMatrix) :
    tensor3 A B (C - D) = tensor3 A B C - tensor3 A B D := by
  ext i j
  simp [tensor3, Matrix.kroneckerMap_apply]
  ring

def localDataEntry (r : TensorLiftProgram.Round) (a : Coordinates) (bank : Fin 2) : GlobalMatrix :=
  let v := coordinateView r a
  liftFrame r v.2.1 v.2.2 (if bank = 0 then lineProjector v.1 else 0)

def localDataExit (r : TensorLiftProgram.Round) (a : Coordinates) (bank : Fin 2) : GlobalMatrix :=
  let v := coordinateView r a
  liftFrame r v.2.1 v.2.2 (if bank = 0 then 1 else 1 - lineProjector v.1)

theorem localDataEntry_first (a : Coordinates) (bank : Fin 2) :
    localDataEntry .first a bank = if bank = 0 then tensorLine a else 0 := by
  by_cases h : bank = 0 <;>
    simp [localDataEntry, coordinateView, liftFrame, liftBase, liftLinear, h, tensorLine, tensor3]

theorem localDataExit_first (a : Coordinates) (bank : Fin 2) :
    localDataExit .first a bank =
      if bank = 0 then firstAmbient a else firstAmbient a - tensorLine a := by
  by_cases h : bank = 0 <;>
    simp [localDataExit, coordinateView, liftFrame, liftBase, liftLinear, h,
      firstAmbient, tensorLine, tensor3_sub_first]

theorem localDataExit_second (a : Coordinates) (bank : Fin 2) :
    localDataExit .second a bank =
      if bank = 0 then secondAmbient a else secondAmbient a - tensorLine a := by
  by_cases h : bank = 0 <;>
    simp [localDataExit, coordinateView, liftFrame, liftBase, liftLinear, h,
      secondAmbient, tensorLine, tensor3_sub_first, tensor3_sub_second] <;> abel

theorem localDataExit_third (a : Coordinates) (bank : Fin 2) :
    localDataExit .third a bank = if bank = 0 then 1 else 1 - tensorLine a := by
  by_cases h : bank = 0 <;>
    simp [localDataExit, coordinateView, liftFrame, liftBase, liftLinear, h,
      tensorLine, tensor3_sub_third] <;> abel

theorem localData_entry_exit (r : TensorLiftProgram.Round) (a : Coordinates) (bank : Fin 2) :
    Nested (localDataEntry r a bank) (localDataExit r a bank) := by
  unfold localDataEntry localDataExit
  dsimp only
  apply liftFrame_nested
  · split_ifs <;> simp
  · split_ifs <;> simp

/-- These strict inclusions account for data conversions between rounds. -/
theorem localData_first_second (a : Coordinates) (bank : Fin 2) :
    Nested (localDataExit .first a bank) (localDataEntry .second a bank) := by
  by_cases h : bank = 0
  all_goals constructor <;>
    simp [localDataExit, localDataEntry, coordinateView, liftFrame, liftBase, liftLinear,
      h, add_mul, mul_add, tensor3_mul, sub_mul, mul_sub, lineProjector_idempotent,
      tensor3_sub_first, tensor3_sub_second] <;> abel

theorem localData_second_third (a : Coordinates) (bank : Fin 2) :
    Nested (localDataExit .second a bank) (localDataEntry .third a bank) := by
  by_cases h : bank = 0
  all_goals constructor <;>
    simp [localDataExit, localDataEntry, coordinateView, liftFrame, liftBase, liftLinear,
      h, add_mul, mul_add, tensor3_mul, sub_mul, mul_sub, lineProjector_idempotent,
      tensor3_sub_first, tensor3_sub_second, tensor3_sub_third] <;> abel

def helperEntry (r : TensorLiftProgram.Round) (pool : Pool) : GlobalMatrix :=
  globalFrame r (TensorThreeRound.roundAssignment partner r pool) 0

def helperExit (r : TensorLiftProgram.Round) (pool : Pool) : GlobalMatrix :=
  globalFrame r (TensorThreeRound.roundAssignment partner r pool) 1

@[simp] theorem globalize_add (i : Copy) (P Q : GlobalMatrix) :
    globalize i (P + Q) = globalize i P + globalize i Q := rfl

theorem globalize_prev_tensor (i : Copy) (A B C : LocalMatrix) :
    globalize (nextCopy.symm i) (tensor3 A B C) =
      globalize i (tensor3 B C A) := by
  fin_cases i <;> ext j k <;>
    simp [nextCopy, globalize, copyView, tensor3, Matrix.kroneckerMap_apply] <;> ring

theorem globalize_next_tensor (i : Copy) (A B C : LocalMatrix) :
    globalize (nextCopy i) (tensor3 A B C) =
      globalize i (tensor3 C A B) := by
  fin_cases i <;> ext j k <;>
    simp [nextCopy, globalize, copyView, tensor3, Matrix.kroneckerMap_apply] <;> ring

theorem helperEntry_first (pool : Pool) : helperEntry .first pool = 0 := by
  simp [helperEntry, globalFrame, TensorThreeRound.roundAssignment, roundOne,
    liftFrame, liftBase, liftLinear, tensor3]

theorem helperExit_first (pool : Pool) : helperExit .first pool =
    globalize pool.1 (HelperFrameChain.firstExit (lineProjector pool.2.1)
      (lineProjector pool.2.2)) := by
  simp [helperExit, globalFrame, TensorThreeRound.roundAssignment, roundOne,
    liftFrame, liftBase, liftLinear, HelperFrameChain.firstExit]

theorem helperEntry_second (pool : Pool) : helperEntry .second pool =
    globalize pool.1 (HelperFrameChain.secondEntry (lineProjector pool.2.1)
      (lineProjector (partner pool.2.2))) := by
  simp [helperEntry, globalFrame, TensorThreeRound.roundAssignment, roundTwo,
    liftFrame, liftBase, liftLinear, HelperFrameChain.secondEntry,
    globalize_prev_tensor]

theorem helperExit_second (pool : Pool) : helperExit .second pool =
    globalize pool.1 (HelperFrameChain.secondExit (lineProjector pool.2.1)) := by
  simp [helperExit, globalFrame, TensorThreeRound.roundAssignment, roundTwo,
    liftFrame, liftBase, liftLinear, HelperFrameChain.secondExit,
    tensor3_sub_first, globalize_prev_tensor]

theorem helperEntry_third (pool : Pool) : helperEntry .third pool =
    globalize pool.1 (HelperFrameChain.thirdEntry (lineProjector (partner pool.2.1))
      (lineProjector (partner pool.2.2))) := by
  simp [helperEntry, globalFrame, TensorThreeRound.roundAssignment, roundThree,
    liftFrame, liftBase, liftLinear, HelperFrameChain.thirdEntry,
    globalize_next_tensor]

theorem helperExit_third (pool : Pool) : helperExit .third pool = 1 := by
  simp [helperExit, globalFrame, TensorThreeRound.roundAssignment, roundThree,
    liftFrame, liftBase, liftLinear]

/-- Literal scheduled helper boundaries coincide with the five-boundary
chain, including both charged inter-round increases. -/
theorem scheduled_helper_boundary_chain (pool : Pool) :
    IsNestedChain (helperEntry .first pool)
      [helperExit .first pool, helperEntry .second pool, helperExit .second pool,
        helperEntry .third pool, helperExit .third pool] := by
  rw [helperEntry_first, helperExit_first, helperEntry_second, helperExit_second,
    helperEntry_third, helperExit_third]
  simpa [helperBoundaryPath, HelperFrameChain.boundaries] using
    helperBoundaryPath_nested (pool, (0 : Fin 439))

def dataEntry (r : TensorLiftProgram.Round) (a : DataStream) : GlobalMatrix :=
  globalize a.1 (localDataEntry r a.2.2 a.2.1)

def dataExit (r : TensorLiftProgram.Round) (a : DataStream) : GlobalMatrix :=
  globalize a.1 (localDataExit r a.2.2 a.2.1)

theorem dataEntry_first (a : DataStream) : dataEntry .first a = dataSource a := by
  rw [dataEntry, localDataEntry_first]
  by_cases h : a.2.1 = 0 <;> simp [dataSource, dataProjector, h]

theorem dataExit_third (a : DataStream) : dataExit .third a = dataTerminal a := by
  rw [dataExit, localDataExit_third]
  by_cases h : a.2.1 = 0 <;> simp [dataTerminal, dataProjector, h]

theorem data_first_second (a : DataStream) :
    Nested (dataExit .first a) (dataEntry .second a) :=
  globalize_nested a.1 (localData_first_second a.2.2 a.2.1)

theorem data_second_third (a : DataStream) :
    Nested (dataExit .second a) (dataEntry .third a) :=
  globalize_nested a.1 (localData_second_third a.2.2 a.2.1)

/-- Three actual visit lists retain every data conversion in their rank
distance. The virtual exit/entry labels are removed only by transitivity. -/
theorem data_three_path_cost (a : DataStream) (xs ys zs : List GlobalMatrix)
    (hx : IsNestedChain (dataEntry .first a) (xs ++ [dataExit .first a]))
    (hy : IsNestedChain (dataEntry .second a) (ys ++ [dataExit .second a]))
    (hz : IsNestedChain (dataEntry .third a) (zs ++ [dataExit .third a])) :
    chainCost (dataSource a) (xs ++ ys ++ zs ++ [dataTerminal a]) = 511 := by
  have hlast := join_paths_across_boundary ys (zs ++ [dataExit .third a]) hy
    (data_second_third a) hz
  have hall := join_paths_across_boundary xs
    (ys ++ (zs ++ [dataExit .third a])) hx (data_first_second a) hlast
  rw [dataEntry_first, dataExit_third] at hall
  apply data_path_rank_cost
  · simpa only [List.append_assoc] using hall
  · simp [chainLast_append, chainLast]

theorem helper_three_path_cost (pool : Pool) (xs ys zs : List GlobalMatrix)
    (hx : IsNestedChain (helperEntry .first pool) (xs ++ [helperExit .first pool]))
    (hy : IsNestedChain (helperEntry .second pool) (ys ++ [helperExit .second pool]))
    (hz : IsNestedChain (helperEntry .third pool) (zs ++ [helperExit .third pool])) :
    chainCost 0 (xs ++ ys ++ zs ++ [1]) = 512 := by
  have hb := scheduled_helper_boundary_chain pool
  have h12 : Nested (helperExit .first pool) (helperEntry .second pool) := hb.2.2.2.1
  have h23 : Nested (helperExit .second pool) (helperEntry .third pool) :=
    hb.2.2.2.2.2.2.2.1
  have hlast := join_paths_across_boundary ys (zs ++ [helperExit .third pool]) hy h23 hz
  have hall := join_paths_across_boundary xs
    (ys ++ (zs ++ [helperExit .third pool])) hx h12 hlast
  rw [helperEntry_first, helperExit_third] at hall
  apply helper_path_rank_cost
  · simpa only [List.append_assoc] using hall
  · simp [chainLast_append, chainLast]

end
end CodedSorting.Construction.TensorFrameGeometry
end TensorFrameBoundaries

section TensorFrameZero
namespace CodedSorting.Construction.IntegerProjection

open FiniteCertificate

theorem zero_certificate_numerator :
    projections[0]!.numerator = Array.replicate 64 (0 : Int) := by
  rw [projections_lookup]
  rfl

theorem zero_certificate_matrix : certificateMatrix projections[0]! = 0 := by
  ext i j
  have hn : certificateNumerator projections[0]! i j = 0 := by
    have hlt : 8*i.val+j.val < 64 := by omega
    simp [certificateNumerator, zero_certificate_numerator,
      getElem!_pos, hlt]
  simp [certificateMatrix, projectionOfInts, hn]

end CodedSorting.Construction.IntegerProjection
end TensorFrameZero

section TensorFrameGlobalVisits
/-!
Exact chronological frame visits of the actual three-round program.
All statements below are symbolic: no expanded global gate list is evaluated.
-/

set_option autoImplicit false

namespace CodedSorting.Construction.TensorFrameGlobalVisits

open CodedSorting.CircuitProgram
open ThreeCopySchedule TensorLiftProgram TensorThreeRound TensorFrameGeometry
open TensorFrameProgram

def dataBlock (round : Round) (a : DataStream) : Block :=
  (a.1, (coordinateView round a.2.2).2)

def dataLocal (round : Round) (a : DataStream) : LocalReg :=
  .inl ((bankView round).symm a.2.1, (coordinateView round a.2.2).1)

noncomputable def visits (pi : Equiv.Perm Line) (ss : List Stage)
    (r : GlobalReg) : List GlobalMatrix :=
  (ss.filter (fun s => decide (r ∈ (stageGate pi s).ports))).map stageLabel

theorem visits_append (pi : Equiv.Perm Line) (ss ts : List Stage) (r : GlobalReg) :
    visits pi (ss ++ ts) r = visits pi ss r ++ visits pi ts r := by
  simp [visits, List.filter_append]

theorem visits_stages (pi : Equiv.Perm Line)
    (one two three : List FramedGate) (r : GlobalReg) :
    visits pi (stages one two three) r =
      visits pi (roundStages .first one) r ++
      visits pi (roundStages .second two) r ++
      visits pi (roundStages .third three) r := by
  simp only [stages, visits_append]

theorem data_embedding (pi : Equiv.Perm Line) (round : Round) (a : DataStream) :
    fiberEmbedding round (roundAssignment pi round) (dataBlock round a)
      (dataLocal round a) = .inl (.inl a) := by
  rcases a with ⟨i, bank, coords⟩
  simp [dataBlock, dataLocal, fiberEmbedding, fiberMap, fiberDataEquiv]

theorem round_data_visits (pi : Equiv.Perm Line) (round : Round)
    (word : List FramedGate) (a : DataStream) :
    visits pi (roundStages round word) (.inl (.inl a)) =
      (localVisits word (dataLocal round a)).map (globalFrame round (dataBlock round a)) := by
  rw [← data_embedding pi round a]
  exact roundStages_labels pi round word (dataBlock round a) (dataLocal round a)

theorem round_helper_visits (pi : Equiv.Perm Line) (round : Round)
    (word : List FramedGate) (pool : Pool) (h : Fin 439) :
    visits pi (roundStages round word) (.inl (.inr (pool,h))) =
      (localVisits word (.inr (.inl h))).map
        (globalFrame round (roundAssignment pi round pool)) := by
  simpa [visits, fiberEmbedding, fiberMap] using
    roundStages_labels pi round word (roundAssignment pi round pool) (.inr (.inl h))

theorem round_temp_visits (pi : Equiv.Perm Line) (round : Round)
    (word : List FramedGate) (block : Block) (t : Fin 9) :
    visits pi (roundStages round word) (.inr (round,block,t)) =
      (localVisits word (.inr (.inr t))).map (globalFrame round block) := by
  exact roundStages_labels pi round word block (.inr (.inr t))

theorem temp_not_other_port (pi : Equiv.Perm Line) (round other : Round)
    (hne : other ≠ round) (block b : Block) (t : Fin 9) (g : FramedGate) :
    (.inr (other,block,t) : GlobalReg) ∉ (stageGate pi (round,b,g)).ports := by
  intro hm
  obtain ⟨r, _, he⟩ := Finset.mem_map.mp hm
  rcases r with d | h | u
  · simp [stageGate, fiberEmbedding, fiberMap] at he
  · simp [stageGate, fiberEmbedding, fiberMap] at he
  · have hr : round = other := by
      have hh : round = other ∧ b = block ∧ u = t := by
        simpa [fiberEmbedding, fiberMap] using he
      exact hh.1
    exact hne hr.symm

theorem round_temp_other (pi : Equiv.Perm Line) (round other : Round)
    (hne : other ≠ round) (word : List FramedGate) (block : Block) (t : Fin 9) :
    visits pi (roundStages round word) (.inr (other,block,t)) = [] := by
  classical
  have hz (b : Block) (g : FramedGate) :
      decide ((.inr (other,block,t) : GlobalReg) ∈ (stageGate pi (round,b,g)).ports) = false := by
    simp [temp_not_other_port pi round other hne block b t g]
  simp [visits, roundStages, List.filter_flatMap, List.filter_map, Function.comp_def, hz]

theorem data_visits (pi : Equiv.Perm Line) (one two three : List FramedGate)
    (a : DataStream) :
    visits pi (stages one two three) (.inl (.inl a)) =
      (localVisits one (dataLocal .first a)).map (globalFrame .first (dataBlock .first a)) ++
      (localVisits two (dataLocal .second a)).map (globalFrame .second (dataBlock .second a)) ++
      (localVisits three (dataLocal .third a)).map (globalFrame .third (dataBlock .third a)) := by
  simp only [visits_stages, round_data_visits]

theorem helper_visits (pi : Equiv.Perm Line) (one two three : List FramedGate)
    (pool : Pool) (h : Fin 439) :
    visits pi (stages one two three) (.inl (.inr (pool,h))) =
      (localVisits one (.inr (.inl h))).map (globalFrame .first (roundAssignment pi .first pool)) ++
      (localVisits two (.inr (.inl h))).map (globalFrame .second (roundAssignment pi .second pool)) ++
      (localVisits three (.inr (.inl h))).map (globalFrame .third (roundAssignment pi .third pool)) := by
  simp only [visits_stages, round_helper_visits]

theorem temp_visits (pi : Equiv.Perm Line) (one two three : List FramedGate)
    (round : Round) (block : Block) (t : Fin 9) :
    visits pi (stages one two three) (.inr (round,block,t)) =
      (localVisits (match round with | .first => one | .second => two | .third => three)
        (.inr (.inr t))).map (globalFrame round block) := by
  rw [visits_stages]
  cases round <;> simp [round_temp_visits, round_temp_other]

#print axioms data_visits
#print axioms helper_visits
#print axioms temp_visits

end CodedSorting.Construction.TensorFrameGlobalVisits
end TensorFrameGlobalVisits

section TensorFrameRankSum
/-!
The final cardinality calculation is proved for an abstract cost function.
This keeps the actual physical word out of finite-sum normalization.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace CodedSorting.Construction.TensorFrameGeometry

open scoped BigOperators
open ThreeCopySchedule TensorLiftProgram

noncomputable section

private theorem triple_sum {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (cost : (A ⊕ B) ⊕ C → Nat) :
    (∑ r, cost r) =
      (∑ a, cost (.inl (.inl a))) +
      (∑ b, cost (.inl (.inr b))) +
      (∑ c, cost (.inr c)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]

theorem temporary_stream_card : Fintype.card TemporaryStream = 998001 := by
  have hround : Fintype.card TensorLiftProgram.Round = 3 := by decide
  simp [TemporaryStream, Fintype.card_prod, hround, Block, Copy, Line]

theorem weighted_global_sum (cost : GlobalReg → Nat)
    (hd : ∀ a : DataStream, cost (.inl (.inl a)) = 511)
    (hh : ∀ h : HelperStream, cost (.inl (.inr h)) = 512)
    (ht : ∀ t : TemporaryStream, cost (.inr t) = 7) :
    (∑ r, cost r) = rankBudget := by
  rw [triple_sum cost,
    sum_uniform_rank_cost _ 511 hd,
    sum_uniform_rank_cost _ 512 hh,
    sum_uniform_rank_cost _ 7 ht,
    data_stream_count, helper_count, temporary_stream_card, rankBudget_eq]

end
end CodedSorting.Construction.TensorFrameGeometry
end TensorFrameRankSum

section TensorFrameNetwork
/-!
Concrete labels on the same annotated physical program used by the payload
proof. Source and terminal labels of non-session temporary wires are chosen
at their copy and scatter frames. The final cost theorem explicitly consumes
the still-separate per-register physical-history proofs.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.TensorFrameNetwork

open scoped BigOperators
open CodedSorting.TensorLabels CodedSorting.ProgramNetwork CodedSorting.StageLabels
open ThreeCopySchedule TensorLiftProgram TensorThreeRound TensorFrameGeometry
open TensorFrameProgram TensorFrameGlobalVisits PhysicalFramePaths

attribute [local irreducible] forwardWord middleWord
  ConcreteLocalProgram.forward ConcreteLocalProgram.middle

noncomputable section

def annotatedStages : List Stage := stages forwardWord middleWord forwardWord

def program := threeRoundProgram ConcreteLocalProgram.forward ConcreteLocalProgram.middle
  ConcreteLocalProgram.forward partner

attribute [local irreducible] annotatedStages program

theorem annotatedStages_program : annotatedStages.map (stageGate partner) = program := by
  unfold program
  rw [annotatedStages, stages_program, forwardWord_program, middleWord_program]

def tempSource (r : TensorLiftProgram.Round) (block : Block) (t : Fin 9) : GlobalMatrix :=
  globalFrame r block (if r = .second then 1 - frameMatrix (510+t.val)
    else frameMatrix (510+t.val))

def tempTerminal (r : TensorLiftProgram.Round) (block : Block) : GlobalMatrix :=
  globalFrame r block (if r = .second then 1 else 0)

def physicalSource : GlobalReg → GlobalMatrix
  | .inl r => sourceLabel r
  | .inr (r,block,t) => tempSource r block t

def physicalTerminal : GlobalReg → GlobalMatrix
  | .inl r => terminalLabel r
  | .inr (r,block,_) => tempTerminal r block

def rawLabel : Vertex GlobalReg (annotatedStages.map (stageGate partner)).length → GlobalMatrix :=
  vertexLabel annotatedStages (stageGate partner) stageLabel physicalSource physicalTerminal

def actualLabel : Vertex GlobalReg program.length → GlobalMatrix :=
  transportLabel annotatedStages_program rawLabel

theorem actualLabel_source (r : IndependentStream) :
    actualLabel (.source (.inl r)) = sourceLabel r := by
  rw [actualLabel, transportLabel_source]
  rfl

theorem actualLabel_terminal (r : IndependentStream) :
    actualLabel (.sink (.inl r)) = terminalLabel r := by
  rw [actualLabel, transportLabel_sink]
  rfl

theorem actualLabel_endpoint_rank (r : IndependentStream) :
    (actualLabel (.sink (.inl (originalSwap r))) - actualLabel (.source (.inl r))).rank = 512 := by
  rw [actualLabel_source, actualLabel_terminal]
  exact all_endpoint_ranks r

def actualWireCost (r : GlobalReg) : Nat :=
  chainCost (physicalSource r) (visits partner annotatedStages r ++ [physicalTerminal r])

/-- This equality sums the literal network edges, including all private pass
subdivisions and all temporary wires. -/
theorem actualRank_eq_wireCosts : physicalRank program actualLabel =
    ∑ r : GlobalReg, actualWireCost r := by
  unfold actualLabel
  rw [physicalRank_transport]
  change networkRank annotatedStages (stageGate partner) stageLabel physicalSource physicalTerminal = _
  rw [networkRank_eq_filtered]
  rfl

theorem temporary_stream_count : Fintype.card TemporaryStream = 998001 := by
  have hround : Fintype.card TensorLiftProgram.Round = 3 := by decide
  simp [TemporaryStream, Fintype.card_prod, hround, Block, Copy, Line]


end
end CodedSorting.Construction.TensorFrameNetwork
end TensorFrameNetwork

section TensorFrameConcretePaths
/-!
The actual physical local histories are joined through the exact tensor
boundary labels. `GeometryChecks` records only concrete finite propositions;
the separate certified-budget module must instantiate every field.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace CodedSorting.Construction.TensorFrameNetwork

noncomputable section

open CodedSorting.TensorLabels (IsNestedChain chainCost)
open ThreeCopySchedule TensorLiftProgram TensorThreeRound TensorFrameGeometry
open TensorFrameProgram TensorFrameGlobalVisits PhysicalFramePaths
open LocalPhysicalSemantics LocalPhysicalContract FiniteCertificate IntegerProjection

attribute [local irreducible] gates projections startFrames finalFrames
  forwardEvents forwardWord middleWord

structure GeometryChecks : Prop where
  operands : ∀ g ∈ gates.toList,
    g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount
  frames : ∀ r : OriginalReg,
    ∀ f ∈ startFrames[r.val]! :: eventVisits r.val forwardEvents ++ [finalFrames[r.val]!],
      ProjectionEquations projections[f]!
  paths : ∀ r : OriginalReg, forwardPathValid r.val = true
  endpoints : EndpointEquations
  copies : ∀ t : Fin 9, ProjectionEquations projections[510+t.val]!
  copyDimensions : ∀ t : Fin 9, projections[510+t.val]!.dimension = 7

theorem GeometryChecks.start_valid (hc : GeometryChecks) (r : OriginalReg) :
    ProjectionEquations projections[startFrames[r.val]!]! := by
  apply hc.frames r
  exact List.mem_cons_self

theorem GeometryChecks.end_valid (hc : GeometryChecks) (r : OriginalReg) :
    ProjectionEquations projections[finalFrames[r.val]!]! := by
  apply hc.frames r
  apply List.mem_cons_of_mem
  exact List.mem_append_right (eventVisits r.val forwardEvents) (List.mem_singleton_self _)

theorem forward_source_path (hc : GeometryChecks) (a : Line) :
    LocalChain (lineProjector a) (localVisits forwardWord (.inl (0,a)) ++ [1]) := by
  have h := forward_original_chain (sourceIndex a) hc.operands (hc.frames _) (hc.paths _)
  simp only [index_symm_source] at h
  have hs := source_start_of_equations a hc.endpoints (hc.start_valid (sourceIndex a))
  have ht := source_end_of_equations a hc.endpoints (hc.end_valid (sourceIndex a))
  change LocalChain (frameMatrix startFrames[a.val]!)
    (localVisits forwardWord (.inl (0,a)) ++ [frameMatrix finalFrames[a.val]!]) at h
  simpa only [frameMatrix, hs, ht] using h

theorem forward_target_path (hc : GeometryChecks) (a : Line) :
    LocalChain 0 (localVisits forwardWord (.inl (1,a)) ++ [1-lineProjector a]) := by
  have h := forward_original_chain (targetIndex a) hc.operands (hc.frames _) (hc.paths _)
  simp only [index_symm_target] at h
  have hs := target_start_of_equations a hc.endpoints
  have ht := target_end_of_equations a hc.endpoints (hc.end_valid (targetIndex a))
  change LocalChain (frameMatrix startFrames[portCount+a.val]!)
    (localVisits forwardWord (.inl (1,a)) ++ [frameMatrix finalFrames[portCount+a.val]!]) at h
  simpa only [frameMatrix, hs, ht] using h

theorem middle_source_path (hc : GeometryChecks) (a : Line) :
    LocalChain 0 (localVisits middleWord (.inl (0,a)) ++ [1-lineProjector a]) := by
  have h := middle_original_chain (sourceIndex a) hc.operands (hc.frames _) (hc.paths _)
  simp only [index_symm_source] at h
  have hs := source_start_of_equations a hc.endpoints (hc.start_valid (sourceIndex a))
  have ht := source_end_of_equations a hc.endpoints (hc.end_valid (sourceIndex a))
  change LocalChain (1-frameMatrix finalFrames[a.val]!)
    (localVisits middleWord (.inl (0,a)) ++ [1-frameMatrix startFrames[a.val]!]) at h
  simpa only [frameMatrix, hs, ht, sub_self] using h

theorem middle_target_path (hc : GeometryChecks) (a : Line) :
    LocalChain (lineProjector a) (localVisits middleWord (.inl (1,a)) ++ [1]) := by
  have h := middle_original_chain (targetIndex a) hc.operands (hc.frames _) (hc.paths _)
  simp only [index_symm_target] at h
  have hs := target_start_of_equations a hc.endpoints
  have ht := target_end_of_equations a hc.endpoints (hc.end_valid (targetIndex a))
  change LocalChain (1-frameMatrix finalFrames[portCount+a.val]!)
    (localVisits middleWord (.inl (1,a)) ++ [1-frameMatrix startFrames[portCount+a.val]!]) at h
  simpa only [frameMatrix, hs, ht, sub_zero, sub_sub_cancel] using h

theorem forward_helper_path (hc : GeometryChecks) (h : Fin 439) :
    LocalChain 0 (localVisits forwardWord (.inr (.inl h)) ++ [1]) := by
  have hp := forward_original_chain (helperIndex h) hc.operands (hc.frames _) (hc.paths _)
  simp only [index_symm_helper] at hp
  have hs := helper_start_of_equations h hc.endpoints
  have ht := helper_end_of_equations h hc.endpoints (hc.end_valid (helperIndex h))
  change LocalChain (frameMatrix startFrames[222+h.val]!)
    (localVisits forwardWord (.inr (.inl h)) ++ [frameMatrix finalFrames[222+h.val]!]) at hp
  simpa only [frameMatrix, hs, ht] using hp

theorem middle_helper_path (hc : GeometryChecks) (h : Fin 439) :
    LocalChain 0 (localVisits middleWord (.inr (.inl h)) ++ [1]) := by
  have hp := middle_original_chain (helperIndex h) hc.operands (hc.frames _) (hc.paths _)
  simp only [index_symm_helper] at hp
  have hs := helper_start_of_equations h hc.endpoints
  have ht := helper_end_of_equations h hc.endpoints (hc.end_valid (helperIndex h))
  change LocalChain (1-frameMatrix finalFrames[222+h.val]!)
    (localVisits middleWord (.inr (.inl h)) ++ [1-frameMatrix startFrames[222+h.val]!]) at hp
  simpa only [frameMatrix, hs, ht, sub_self, sub_zero] using hp

def roundWord : TensorLiftProgram.Round → List FramedGate
  | .first => forwardWord
  | .second => middleWord
  | .third => forwardWord

/-- The physical bank swap of the middle round is accounted for before
lifting the checked local histories. -/
theorem round_data_local_path (hc : GeometryChecks) (r : TensorLiftProgram.Round)
    (a : DataStream) :
    LocalChain (if a.2.1 = 0 then lineProjector (coordinateView r a.2.2).1 else 0)
      (localVisits (roundWord r) (dataLocal r a) ++
        [if a.2.1 = 0 then 1 else 1-lineProjector (coordinateView r a.2.2).1]) := by
  rcases a with ⟨i, bank, coords⟩
  fin_cases bank <;> cases r
  · simpa [roundWord, dataLocal, bankView] using forward_source_path hc coords.1
  · simpa [roundWord, dataLocal, bankView, coordinateView] using middle_target_path hc coords.2.1
  · simpa [roundWord, dataLocal, bankView, coordinateView] using forward_source_path hc coords.2.2
  · simpa [roundWord, dataLocal, bankView] using forward_target_path hc coords.1
  · simpa [roundWord, dataLocal, bankView, coordinateView] using middle_source_path hc coords.2.1
  · simpa [roundWord, dataLocal, bankView, coordinateView] using forward_target_path hc coords.2.2

theorem round_data_global_path (hc : GeometryChecks) (r : TensorLiftProgram.Round)
    (a : DataStream) :
    IsNestedChain (dataEntry r a)
      ((localVisits (roundWord r) (dataLocal r a)).map (globalFrame r (dataBlock r a)) ++
        [dataExit r a]) := by
  have h := globalFrame_chain r (dataBlock r a) _ _ (round_data_local_path hc r a)
  simpa only [List.map_append, List.map_cons, List.map_nil, dataBlock, globalFrame,
    dataEntry, dataExit, localDataEntry, localDataExit] using h

theorem round_helper_global_path (hc : GeometryChecks) (r : TensorLiftProgram.Round)
    (pool : Pool) (h : Fin 439) :
    IsNestedChain (helperEntry r pool)
      ((localVisits (roundWord r) (.inr (.inl h))).map
        (globalFrame r (roundAssignment partner r pool)) ++ [helperExit r pool]) := by
  have hp : LocalChain 0 (localVisits (roundWord r) (.inr (.inl h)) ++ [1]) := by
    cases r
    · exact forward_helper_path hc h
    · exact middle_helper_path hc h
    · exact forward_helper_path hc h
  simpa only [List.map_append, List.map_cons, List.map_nil, helperEntry, helperExit] using
    globalFrame_chain r (roundAssignment partner r pool) _ _ hp

theorem actual_data_cost (hc : GeometryChecks) (a : DataStream) :
    actualWireCost (.inl (.inl a)) = 511 := by
  unfold actualWireCost
  rw [annotatedStages, data_visits]
  exact data_three_path_cost a _ _ _
    (round_data_global_path hc .first a)
    (round_data_global_path hc .second a)
    (round_data_global_path hc .third a)

theorem actual_helper_cost (hc : GeometryChecks) (h : HelperStream) :
    actualWireCost (.inl (.inr h)) = 512 := by
  rcases h with ⟨pool,h⟩
  unfold actualWireCost
  rw [annotatedStages, helper_visits]
  exact helper_three_path_cost pool _ _ _
    (round_helper_global_path hc .first pool h)
    (round_helper_global_path hc .second pool h)
    (round_helper_global_path hc .third pool h)

theorem actual_temporary_cost (hc : GeometryChecks) (t : TemporaryStream) :
    actualWireCost (.inr t) = 7 := by
  rcases t with ⟨r,block,t⟩
  have hz : frameMatrix 0 = 0 := zero_certificate_matrix
  have hi : localPhysicalIndex.symm (.inr t) = .inr (.inr t) := rfl
  unfold actualWireCost
  rw [annotatedStages, temp_visits]
  cases r
  · simpa [physicalSource, physicalTerminal, tempSource, tempTerminal, hi] using
      forward_temporary_global_cost .first block t hc.operands hz (hc.copies t) (hc.copyDimensions t)
  · simpa [physicalSource, physicalTerminal, tempSource, tempTerminal, hi] using
      middle_temporary_global_cost .second block t hc.operands hz (hc.copies t) (hc.copyDimensions t)
  · simpa [physicalSource, physicalTerminal, tempSource, tempTerminal, hi] using
      forward_temporary_global_cost .third block t hc.operands hz (hc.copies t) (hc.copyDimensions t)


end
end CodedSorting.Construction.TensorFrameNetwork
end TensorFrameConcretePaths

section TensorFrameRankBudget
set_option autoImplicit false

namespace CodedSorting.Construction.TensorFrameNetwork

open ThreeCopySchedule TensorLiftProgram
open CodedSorting.StageLabels

theorem actualRank_eq_budget_of_costs
    (hdata : ∀ a : DataStream, actualWireCost (.inl (.inl a)) = 511)
    (hhelper : ∀ h : HelperStream, actualWireCost (.inl (.inr h)) = 512)
    (htemp : ∀ t : TemporaryStream, actualWireCost (.inr t) = 7) :
    physicalRank program actualLabel = rankBudget :=
  actualRank_eq_wireCosts.trans
    (TensorFrameGeometry.weighted_global_sum actualWireCost hdata hhelper htemp)

/-- Every actual wire cost has been proved from its literal visit path.
Only finite local checks remain to be supplied in the certified wrapper. -/
theorem actualRank_eq_budget_of_checks (hc : GeometryChecks) :
    physicalRank program actualLabel = rankBudget :=
  actualRank_eq_budget_of_costs
    (actual_data_cost hc) (actual_helper_cost hc) (actual_temporary_cost hc)

end CodedSorting.Construction.TensorFrameNetwork
end TensorFrameRankBudget
