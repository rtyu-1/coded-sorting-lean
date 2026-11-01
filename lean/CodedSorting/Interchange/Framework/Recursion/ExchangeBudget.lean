import CodedSorting.Interchange.Framework.Recursion.ExchangeFamily
import CodedSorting.Interchange.Framework.Recursion.NetworkFrame

section ExchangeRun
/-! From the certificates of a concrete recursive exchange program to one
halted execution on the common finite RAM/disk machine. The same run gives
the exchanged file, the disk frame, and the charged I/O bound. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open PhysicalFieldPacking RecursiveExchange Circuit Address
attribute [local irreducible] CommonStaticSchedule.executeRaw ControlledNormalization.runLogical
noncomputable section

/-- Apply this theorem to `baseProgram` or to the proved recursive constructor;
no second execution or different program is used for resource accounting. -/
theorem complete (q : Configuration) (f P G S source buffer limit : ℕ)
    (p : Program q f P G S source buffer limit) (s : Machine q)
    (hsize : p.charge≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ a : ScalarAddress f P G S,
      readBit q result.1.disk source (scalarLayout f P G S a).val=
      readBit q s.disk source (scalarLayout f P G S (exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (ScalarVolume f P G S)≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧ result.2≤p.charge ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have hr := run_code_disk q p.instructions (p.length_le.trans hsize) p.safe s hpc
  dsimp (config := {proj := false}) only
  refine ⟨?_,?_,hr.2.1,hr.2.2.1.le.trans p.cost_le,hr.2.2.2⟩
  · exact (congrArg (fun disk : Disk q => ∀ a : ScalarAddress f P G S,
      readBit q disk source (scalarLayout f P G S a).val=
      readBit q s.disk source (scalarLayout f P G S (exchange a)).val) hr.1).mpr (p.correct s)
  · exact (congrArg (fun disk : Disk q => ∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (ScalarVolume f P G S)≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → disk a=s.disk a) hr.1).mpr (p.frame s)

end
end CodedSorting.CommonRecursiveExchange
end ExchangeRun

section OuterCost
/-! Complete finite-machine execution and resource bounds for the seven
stages of the recursive parent coded exchange. Every charge below is for the
same actual instruction list, including the original network gates. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

namespace CodedSorting.CommonRecursiveOuterResources

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonRecursiveOuter CommonOneLevelSemantics
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge Address Circuit

noncomputable section

def outsideNetwork (q : Configuration) (p : Setup q) : ℕ :=
  (72*Parameters.m+12*Parameters.W)*parentBlocks q p+12*Parameters.W*liveBlocks q p

def charge (q : Configuration) (p : Setup q) (network : List (Instruction q)) : ℕ :=
  outsideNetwork q p+cost q network

def textLength (q : Configuration) (p : Setup q) (network : List (Instruction q)) : ℕ :=
  outsideNetwork q p+network.length

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q)
    (network : List (Instruction q)) (hsafe : ∀ i∈network, RespectsPC q i) :
    ∀ i∈CommonRecursiveOuter.code q reader p network, RespectsPC q i := by
  intro i hi
  simp only [CommonRecursiveOuter.code, List.mem_append] at hi
  rcases hi with (((((h|h)|h)|h)|h)|h)|h
  · unfold beforeCode at h
    exact CommonOuterExecution.safe q reader p.f (p.R*Parameters.W) p.G (suffix q p)
      OuterExchangeProgram.coordinates p.source p.temporary i h
  · unfold transposeCode at h
    exact CommonOneLevelRoles.forward_safe q reader p.f p.R p.G (suffix q p)
      p.source p.temporary i h
  · unfold splitCode at h
    exact CommonStaticSlabSplit.code_safe q reader Parameters.W (words q p)
      p.temporary (inputs q p) i h
  · exact hsafe i h
  · unfold joinCode at h
    exact CommonStaticSlabJoinMapped.code_safe q reader (words q p) Parameters.W
      p.source (sinks q p) i h
  · unfold inverseCode at h
    exact CommonOneLevelRoles.inverse_safe q reader p.f p.R p.G (suffix q p)
      p.source p.temporary i h
  · unfold afterCode at h
    exact CommonScanProgram.code_safe q reader
      (OuterExchangeProgram.afterProgram p.f (p.R*Parameters.W) p.G (suffix q p) (suffix_pos q p))
      p.temporary p.source i h

private theorem before_length (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) : (beforeCode q reader p).length≤12*Parameters.m*parentBlocks q p := by
  unfold beforeCode
  have h := CommonOuterExecution.length_le q reader p.f (p.R*Parameters.W) p.G (suffix q p)
    OuterExchangeProgram.coordinates p.source p.temporary
  simpa only [OuterExchangeProgram.coordinates_length] using h

private theorem after_length (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) : (afterCode q reader p).length≤60*Parameters.m*parentBlocks q p := by
  unfold afterCode
  have h := CommonScanProgram.code_length q reader
    (OuterExchangeProgram.afterProgram p.f (p.R*Parameters.W) p.G (suffix q p) (suffix_pos q p))
    p.temporary p.source
  rw [OuterExchangeProgram.after_constant] at h
  have he : 3*(20*Parameters.m)=60*Parameters.m := by ring
  rw [he] at h
  exact h

theorem code_length_bound (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (network : List (Instruction q)) : (CommonRecursiveOuter.code q reader p network).length≤textLength q p network := by
  have h1 := before_length q reader p
  have h2 := CommonOneLevelRoles.forward_length q reader p.f p.R p.G (suffix q p)
    p.source p.temporary
  have h3 := CommonStaticSlabSplit.code_length q reader Parameters.W (words q p)
    p.temporary (inputs q p)
  have h5 := CommonStaticSlabJoinMapped.code_length q reader (words q p) Parameters.W
    p.source (sinks q p)
  have h6 := CommonOneLevelRoles.inverse_length q reader p.f p.R p.G (suffix q p)
    p.source p.temporary
  have h7 := after_length q reader p
  change (transposeCode q reader p).length≤6*Parameters.W*parentBlocks q p at h2
  change (splitCode q reader p).length=6*(Parameters.W*liveBlocks q p) at h3
  change (joinCode q reader p).length=6*(Parameters.W*liveBlocks q p) at h5
  change (inverseCode q reader p).length≤6*Parameters.W*parentBlocks q p at h6
  simp only [CommonRecursiveOuter.code, List.length_append]
  unfold textLength outsideNetwork
  nlinarith

theorem code_cost_bound (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (network : List (Instruction q)) : cost q (CommonRecursiveOuter.code q reader p network)≤charge q p network := by
  have h1 := before_length q reader p
  have he : cost q (beforeCode q reader p)=(beforeCode q reader p).length :=
    CommonOuterExecution.cost_eq_length q reader p.f (p.R*Parameters.W) p.G (suffix q p)
      OuterExchangeProgram.coordinates p.source p.temporary
  rw [← he] at h1
  have h2 := CommonOneLevelRoles.forward_cost q reader p.f p.R p.G (suffix q p)
    p.source p.temporary
  have h3 := CommonStaticSlabSplit.code_cost q reader Parameters.W (words q p)
    p.temporary (inputs q p)
  have h5 := CommonStaticSlabJoinMapped.code_cost q reader (words q p) Parameters.W
    p.source (sinks q p)
  have h6 := CommonOneLevelRoles.inverse_cost q reader p.f p.R p.G (suffix q p)
    p.source p.temporary
  have h7 : cost q (afterCode q reader p)≤60*Parameters.m*parentBlocks q p := by
    unfold afterCode
    have h := CommonScanProgram.code_cost q reader
      (OuterExchangeProgram.afterProgram p.f (p.R*Parameters.W) p.G (suffix q p) (suffix_pos q p))
      p.temporary p.source
    rw [OuterExchangeProgram.after_constant] at h
    have he : 3*(20*Parameters.m)=60*Parameters.m := by ring
    rw [he] at h
    exact h
  change cost q (transposeCode q reader p)≤6*Parameters.W*parentBlocks q p at h2
  change cost q (splitCode q reader p)=6*(Parameters.W*liveBlocks q p) at h3
  change cost q (joinCode q reader p)=6*(Parameters.W*liveBlocks q p) at h5
  change cost q (inverseCode q reader p)≤6*Parameters.W*parentBlocks q p at h6
  simp only [CommonRecursiveOuter.code, CommonPermutationPairs.cost_append]
  unfold charge outsideNetwork
  nlinarith


end
end CodedSorting.CommonRecursiveOuterResources
end OuterCost

section ExchangeNode
/-! One actual recursive parent assembled from already constructed smaller
scalar programs. The complete tree builder discharges these programs by
structural recursion; no successful child execution is an external premise.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open CoordinateLayoutBridge Address Circuit
attribute [local irreducible] CommonStaticSchedule.executeRaw
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W
noncomputable section

abbrev NodeChildren (q : Configuration) (f R G S buffer limit : ℕ) :=
  (c : Child) → Program q f (childP f R c) (childG f G c) (childS f (S*q.w) c)
    (CommonResidentNetwork.scratchBase (networkBase q f R G S buffer) (childCount q f R G S))
    (childBase q f R G S buffer) limit

def nodeEdges (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :=
  CommonRankEdge.networkEdgePrograms q reader f R G (S*q.w) hG
    (Nat.mul_pos hS (by have:=q.word_width; omega))
    (networkLayout q f R G S source buffer limit a) a.child_fits
    (scalarChildren q f R G (S*q.w)
      (CommonRankEdge.networkAllocation q f R G (S*q.w)
        (networkLayout q f R G S source buffer limit a) a.child_fits) children)

def nodeNetwork (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :=
  CommonRecursiveNetwork.code q reader f R G (S*q.w)
    (networkLayout q f R G S source buffer limit a)
    (nodeEdges q reader f R G S source buffer limit hG hS a children)

theorem nodeNetwork_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :
    CommonRecursiveOuter.NetworkCorrect q (outerSetup q f R G S source buffer limit hS a)
      (nodeNetwork q reader f R G S source buffer limit hG hS a children) := by
  intro s input hv r x
  exact CommonRecursiveNetwork.raw_sink q reader f R G (S*q.w)
    (networkLayout q f R G S source buffer limit a)
    (nodeEdges q reader f R G S source buffer limit hG hS a children) s input hv r x

theorem nodeNetwork_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit)
    (s : Machine q) (i : Fin (q.N^q.exponent))
    (hi : i.val<networkBase q f R G S buffer ∨ limit≤ i.val) :
    (executeRaw q (nodeNetwork q reader f R G S source buffer limit hG hS a children) s).1.disk i=s.disk i := by
  have heq : nodeNetwork q reader f R G S source buffer limit hG hS a children =
      CommonRecursiveNetwork.code q reader f R G (S*q.w)
        (networkLayout q f R G S source buffer limit a)
        (nodeEdges q reader f R G S source buffer limit hG hS a children) := rfl
  exact (congrArg (fun code : List (Instruction q) =>
      (executeRaw q code s).1.disk i=s.disk i) heq).mpr
    (CommonRecursiveNetwork.raw_outside q reader f R G (S*q.w)
      (networkLayout q f R G S source buffer limit a)
      (nodeEdges q reader f R G S source buffer limit hG hS a children) s i hi)

theorem nodeNetwork_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :
    ∀ i∈nodeNetwork q reader f R G S source buffer limit hG hS a children,RespectsPC q i :=
  CommonRecursiveNetwork.code_safe q reader f R G (S*q.w)
    (networkLayout q f R G S source buffer limit a)
    (nodeEdges q reader f R G S source buffer limit hG hS a children)

def nodeCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :=
  CommonRecursiveOuter.code q reader (outerSetup q f R G S source buffer limit hS a)
    (nodeNetwork q reader f R G S source buffer limit hG hS a children) ++
  copyCode q reader (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)) buffer source

def nodeCharge (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :=
  CommonRecursiveOuterResources.outsideNetwork q (outerSetup q f R G S source buffer limit hS a)+
    CommonRecursiveExchangeCost.networkCharge q f R G (S*q.w) hG
      (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>(children c).charge)+
    6*parentCount q f R G S

theorem node_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit)
    (s : Machine q) (x : ScalarAddress (Parameters.m*f) (R*Parameters.W) G (S*q.w)) :
    readBit q (executeRaw q (nodeCode q reader f R G S source buffer limit hG hS a children) s).1.disk
      source (scalarLayout (Parameters.m*f) (R*Parameters.W) G (S*q.w) x).val=
    readBit q s.disk source
      (scalarLayout (Parameters.m*f) (R*Parameters.W) G (S*q.w) (exchange x)).val := by
  let p:=outerSetup q f R G S source buffer limit hS a
  let n:=nodeNetwork q reader f R G S source buffer limit hG hS a children
  let L:=scalarLayout (Parameters.m*f) (R*Parameters.W) G (S*q.w)
  let F:=fun y => readBit q s.disk source (L y).val
  let P:=fun t : Machine q => ∀ y,readBit q t.disk source (L y).val=F y
  let Q:=fun t : Machine q => ∀ y,readBit q t.disk buffer (L y).val=F (exchange y)
  let T:=fun t : Machine q => ∀ y,readBit q t.disk source (L y).val=F (exchange y)
  have h1 : ∀ t,P t→Q (executeRaw q (CommonRecursiveOuter.code q reader p n) t).1 := by
    intro t ht y
    have hh:=CommonRecursivePacking.scalar_of_long q f (R*Parameters.W) G (S*q.w) source buffer
      t.disk (executeRaw q (CommonRecursiveOuter.code q reader p n) t).1.disk
      (CommonRecursiveOuter.raw_correct q reader p n
        (nodeNetwork_correct q reader f R G S source buffer limit hG hS a children) t) y
    exact hh.trans (ht (exchange y))
  have h2 : ∀ t,Q t→T (executeRaw q (copyCode q reader
      (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)) buffer source) t).1 := by
    intro t ht y
    have hs:=CommonRecursiveOuter.source_fits q p
    have hb:=CommonRecursiveOuter.temporary_fits q p
    have hp:=a.source_separate
    change source+count q (longVolume f (R*Parameters.W) G (S*q.w))≤q.N^q.exponent at hs
    change buffer+count q (longVolume f (R*Parameters.W) G (S*q.w))≤q.N^q.exponent at hb
    change source+count q (longVolume f (R*Parameters.W) G (S*q.w))≤buffer at hp
    rw [←packedVolume] at hs hb hp
    exact ((copyCode_raw q reader _ buffer source t hb hs (Or.inr hp)).1 (L y)).trans (ht y)
  exact CommonRawComposition.hoare_two q _ _ P Q T h1 h2 s (fun _=>rfl) x

theorem node_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit)
    (s : Machine q) (i : Fin (q.N^q.exponent))
    (hs : i.val<source ∨ source+count q (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w))≤ i.val)
    (hw : i.val<buffer ∨ limit≤ i.val) :
    (executeRaw q (nodeCode q reader f R G S source buffer limit hG hS a children) s).1.disk i=s.disk i := by
  let p:=outerSetup q f R G S source buffer limit hS a
  let n:=nodeNetwork q reader f R G S source buffer limit hG hS a children
  have hlimit : p.workspace+CommonResidentNetwork.fileCount*CommonRecursiveOuter.stride q p≤limit :=
    (Nat.le_add_right _ _).trans a.child_fits
  have heq : nodeCode q reader f R G S source buffer limit hG hS a children =
      CommonRecursiveOuter.code q reader p n ++ copyCode q reader
        (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)) buffer source := rfl
  exact (congrArg (fun code : List (Instruction q) =>
      (executeRaw q code s).1.disk i=s.disk i) heq).mpr
    (outer_copy_frame q reader p n _ limit (packedVolume f (R*Parameters.W) G (S*q.w))
      hlimit (nodeNetwork_frame q reader f R G S source buffer limit hG hS a children) s i hs hw)

attribute [local irreducible] CommonStaticSchedule.cost nodeNetwork CommonRecursiveExchangeCost.networkCharge

theorem node_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :
    ∀ i∈nodeCode q reader f R G S source buffer limit hG hS a children,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact CommonRecursiveOuterResources.code_safe q reader _ _
      (nodeNetwork_safe q reader f R G S source buffer limit hG hS a children) i hi
  · exact copyCode_safe q reader _ buffer source i hi

theorem node_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :
    cost q (nodeCode q reader f R G S source buffer limit hG hS a children)≤nodeCharge q reader f R G S source buffer limit hG hS a children := by
  have h1:=CommonRecursiveOuterResources.code_cost_bound q reader
    (outerSetup q f R G S source buffer limit hS a)
    (nodeNetwork q reader f R G S source buffer limit hG hS a children)
  have h2:=copyCode_cost q reader (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)) buffer source
  have hn : cost q (nodeNetwork q reader f R G S source buffer limit hG hS a children)≤
      CommonRecursiveExchangeCost.networkCharge q f R G (S*q.w) hG
      (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>(children c).charge) := by
    unfold nodeNetwork nodeEdges
    exact scalarNetwork_cost q reader f R G (S*q.w) hG
      (Nat.mul_pos hS (by have:=q.word_width; omega))
      (networkLayout q f R G S source buffer limit a) a.child_fits children
  dsimp only [CommonRecursiveOuterResources.charge] at h1
  have h2' := h2.trans_eq
    (congrArg (fun V : ℕ=>6*count q V) (packedVolume f (R*Parameters.W) G (S*q.w)))
  rw [nodeCode,cost_append]
  dsimp only [nodeCharge,CommonRecursiveOuterResources.charge,parentCount]
  exact Nat.add_le_add (h1.trans (Nat.add_le_add_left hn _)) h2'

theorem node_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :
    (nodeCode q reader f R G S source buffer limit hG hS a children).length≤nodeCharge q reader f R G S source buffer limit hG hS a children := by
  have h1:=CommonRecursiveOuterResources.code_length_bound q reader
    (outerSetup q f R G S source buffer limit hS a)
    (nodeNetwork q reader f R G S source buffer limit hG hS a children)
  have h2:=copyCode_length q reader (ScalarVolume (Parameters.m*f) (R*Parameters.W) G (S*q.w)) buffer source
  have hn : (nodeNetwork q reader f R G S source buffer limit hG hS a children).length≤
      CommonRecursiveExchangeCost.networkCharge q f R G (S*q.w) hG
      (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>(children c).charge) := by
    unfold nodeNetwork nodeEdges
    exact scalarNetwork_length q reader f R G (S*q.w) hG
      (Nat.mul_pos hS (by have:=q.word_width; omega))
      (networkLayout q f R G S source buffer limit a) a.child_fits children
  dsimp only [CommonRecursiveOuterResources.textLength] at h1
  have h2' := h2.trans_eq
    (congrArg (fun V : ℕ=>6*count q V) (packedVolume f (R*Parameters.W) G (S*q.w)))
  rw [nodeCode,List.length_append]
  dsimp only [nodeCharge,CommonRecursiveOuterResources.textLength,parentCount]
  exact Nat.add_le_add (h1.trans (Nat.add_le_add_left hn _)) h2'

def nodeProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (f R G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (a : NodeAllocation q f R G S source buffer limit)
    (children : NodeChildren q f R G S buffer limit) :
    Program q (Parameters.m*f) (R*Parameters.W) G (S*q.w) source buffer limit where
  instructions:=nodeCode q reader f R G S source buffer limit hG hS a children
  charge:=nodeCharge q reader f R G S source buffer limit hG hS a children
  correct:=node_correct q reader f R G S source buffer limit hG hS a children
  frame:=node_frame q reader f R G S source buffer limit hG hS a children
  safe:=node_safe q reader f R G S source buffer limit hG hS a children
  cost_le:=node_cost q reader f R G S source buffer limit hG hS a children
  length_le:=node_length q reader f R G S source buffer limit hG hS a children

end
end CodedSorting.CommonRecursiveExchange
end ExchangeNode

section ExchangeBuild
/-! A closed finite-machine exchange program for every finite recursion tree.
Every child program is constructed recursively. The only execution premises
are explicit disk/program capacities and the initial program counter.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open Address Circuit
noncomputable section

/-- Compile the full recursion tree into one chronological instruction list.
The arguments contain public dimensions and allocation bounds only. -/
def build (q : Configuration) (reader : Fin q.inventory.readers)
    {f P G S : ℕ} (t : Tree q f P G S) :
    ∀ source buffer limit : ℕ,
      source+count q (ScalarVolume f P G S)≤buffer →
      buffer+space q t≤limit → limit≤q.N^q.exponent →
      Program q f P G S source buffer limit := by
  induction t with
  | leaf f P G S =>
    intro source buffer limit hs hw hl
    exact baseProgram q reader f P G S source buffer limit hs hw hl
  | node f R G S hG hS children ih =>
    intro source buffer limit hs hw hl
    let a:=treeAllocation q f R G S source buffer limit hG hS children hs hw hl
    apply nodeProgram q reader f R G S source buffer limit hG hS a
    intro c
    apply ih c
      (CommonResidentNetwork.scratchBase (networkBase q f R G S buffer) (childCount q f R G S))
      (childBase q f R G S buffer) limit
    · rw [ScalarVolume,child_volume]
      exact scratch_separate q f R G S source buffer limit a
    · exact child_workspace q f R G S buffer limit hG hS children hw c
    · exact hl

/-- Arbitrary recursion depth, with all smaller calls supplied by `build`.
There is no resident-stream premise and no assumed child-success predicate. -/
def canonicalProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (base k rows G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (hs : source+count q (ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w))≤buffer)
    (hw : buffer+space q (canonical q base k rows G S hG hS)≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w) source buffer limit :=
  build q reader (canonical q base k rows G S hG hS) source buffer limit hs hw hl

end
end CodedSorting.CommonRecursiveExchange
end ExchangeBuild

section ExchangeBudget
/-! A public recursive budget for the fully generated instruction list.
It depends only on the recursion tree and dimensions, not payload data,
reader choice, allocation addresses, or a successful execution premise. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open RecursiveExchange RecursiveExchangeCost PhysicalFieldPacking
open CommonRecursiveExchangeCost PhysicalStreamCursor
noncomputable section
attribute [local irreducible] CommonResidentNetwork.edgeCount CircuitProgram.globalProgram Parameters.W

def budget (q : Configuration) : {f P G S : ℕ} → Tree q f P G S → ℕ
  | f,P,G,S,.leaf _ _ _ _ => baseCharge q f P G S
  | _,_,_,_,.node f R G S hG hS children =>
      (72*Parameters.m+12*Parameters.W)*parentCount q f R G S+
      12*Parameters.W*blockCount q.block (longVolume f R G S)+
      networkCharge q f R G (S*q.w) hG
        (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>budget q (children c))+
      6*parentCount q f R G S

theorem build_charge (q : Configuration) (reader : Fin q.inventory.readers)
    {f P G S : ℕ} (t : Tree q f P G S) :
    ∀ (source buffer limit : ℕ)
      (hs : source+count q (ScalarVolume f P G S)≤buffer)
      (hw : buffer+space q t≤limit) (hl : limit≤q.N^q.exponent),
      (build q reader t source buffer limit hs hw hl).charge=budget q t := by
  induction t with
  | leaf f P G S => intro source buffer limit hs hw hl; rfl
  | node f R G S hG hS children ih =>
    intro source buffer limit hs hw hl
    simp only [build,nodeProgram,nodeCharge,budget,CommonRecursiveOuterResources.outsideNetwork,
      CommonRecursiveOuter.parentBlocks,CommonRecursiveOuter.parentBits,CommonRecursiveOuter.suffix,
      CommonRecursiveOuter.liveBlocks,CommonRecursiveOuter.words,outerSetup,parentCount]
    congr 2
    apply congrArg (networkCharge q f R G (S*q.w) hG _)
    funext c
    exact ih c _ _ _ _ _ _

/-- The canonical family's public budget has no allocation or reader inputs. -/
theorem canonical_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (base k rows G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (hs : source+count q (ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G (S*q.w))≤buffer)
    (hw : buffer+space q (canonical q base k rows G S hG hS)≤limit)
    (hl : limit≤q.N^q.exponent) :
    (canonicalProgram q reader base k rows G S source buffer limit hG hS hs hw hl).charge=
      budget q (canonical q base k rows G S hG hS) :=
  build_charge q reader (canonical q base k rows G S hG hS) source buffer limit hs hw hl


theorem build_cost_le (q : Configuration) (reader : Fin q.inventory.readers)
    {f P G S : ℕ} (t : Tree q f P G S) (source buffer limit : ℕ)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+space q t≤limit) (hl : limit≤q.N^q.exponent) :
    cost q (build q reader t source buffer limit hs hw hl).instructions≤budget q t :=
  (build q reader t source buffer limit hs hw hl).cost_le.trans_eq
    (build_charge q reader t source buffer limit hs hw hl)

theorem build_length_le (q : Configuration) (reader : Fin q.inventory.readers)
    {f P G S : ℕ} (t : Tree q f P G S) (source buffer limit : ℕ)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+space q t≤limit) (hl : limit≤q.N^q.exponent) :
    (build q reader t source buffer limit hs hw hl).instructions.length≤budget q t :=
  (build q reader t source buffer limit hs hw hl).length_le.trans_eq
    (build_charge q reader t source buffer limit hs hw hl)

/-- All network-local work has one fixed construction constant. The remaining
sum contains exactly the rank-selected child invocations. -/
theorem networkCharge_le (q : Configuration) (f P G S : ℕ) (hG : 0<G) (hS : 0<S)
    (childCharge : Child→ℕ) :
    networkCharge q f P G S hG hS childCharge≤
      (3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
        CommonRankEdge.constructionConstant)*count q (longVolume f P G S)+
      ∑ c : Child,childCharge c := by
  unfold networkCharge
  rw [CommonRecursiveNetwork.edgeSum_eq_sum,Finset.sum_add_distrib,CommonRankEdge.childSum_total]
  have hh:=CommonRankEdge.localCharge_total q f P G S hG hS
  calc
    _ ≤ 3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl*
        count q (longVolume f P G S)+
      (CommonRankEdge.constructionConstant*count q (longVolume f P G S)+
        ∑ c : Child,childCharge c) := Nat.add_le_add_left (Nat.add_le_add_right hh _) _
    _ = _ := by simp only [Nat.add_mul,Nat.add_assoc]

theorem budget_node_le (q : Configuration) (f R G S : ℕ) (hG : 0<G) (hS : 0<S)
    (children : (c : Child) →
      Tree q f (childP f R c) (childG f G c)
        (childS f (S*q.w) c)) :
    budget q (.node f R G S hG hS children)≤
      (72*Parameters.m+12*Parameters.W+6)*parentCount q f R G S+
      (12*Parameters.W+3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
        CommonRankEdge.constructionConstant)*childCount q f R G S+
      ∑ c : Child,budget q (children c) := by
  have hh:=networkCharge_le q f R G (S*q.w) hG
    (Nat.mul_pos hS (by have:=q.word_width; omega)) (fun c=>budget q (children c))
  have hc : blockCount q.block (longVolume f R G S)=childCount q f R G S := by
    exact (CommonOneLevelAllocation.local_count q f R G S).symm
  change _≤_ at hh
  dsimp only [budget]
  rw [hc]
  change _≤(72*Parameters.m+12*Parameters.W+6)*parentCount q f R G S+
    (12*Parameters.W+3*CommonResidentNetwork.prefixWeight CommonResidentNetwork.edgeCount le_rfl+
      CommonRankEdge.constructionConstant)*count q (longVolume f R G (S*q.w))+_
  dsimp only [childCount]
  nlinarith

end
end CodedSorting.CommonRecursiveExchange
end ExchangeBudget
