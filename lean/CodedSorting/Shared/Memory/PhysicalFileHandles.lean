import CodedSorting.Shared.Memory.WordAlignment
import CodedSorting.Interchange.Framework.Memory.OuterExchangeProgram
import CodedSorting.Circuit.NetworkModel.Framework.PhysicalNetworkCost
import CodedSorting.Circuit.Framework.CircuitWorkspace
import CodedSorting.Interchange.Framework.Memory.BaseExchangeProgram
import CodedSorting.Shared.Memory.PhysicalStreamCursor

section PhysicalWholeLevel
/-! One actual recursion level, with the same output disk passed through
outer scans, role partitioning, the coded network, role collection and the
last outer scans. At this file-interpreter layer the only unresolved
execution interface is its children; global allocation/control refinement is separate. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace CodedSorting.PhysicalWholeLevel
open RecursiveExchange RecursiveExchangeCost PhysicalRecursiveExchange
open PhysicalNetwork PhysicalNetworkCost PhysicalRecursiveCost PhysicalRolePartition
open CoordinateLayoutBridge ScanProgram Address CodedSimulation
open Circuit CircuitProgram ProgramNetwork
open scoped BigOperators
noncomputable section
variable {σ : Type}

/-- Directory lookup reads a fixed role descriptor, not a payload array. -/
def inputFiles (files : List File) (r : Reg) : File :=
  files[(roleEnumeration r).val]?.getD []

def sinkFiles (files : Edge → File) : List File :=
  List.ofFn (fun r : Fin Parameters.W =>
    files (sinkWire (globalProgram Parameters.d) (globalSwap (roleEnumeration.symm r))))

/-- The exact file returned by each operation is the next operation's input.
The fixed sink directory contains no newly manufactured payload. -/
def executeLevel (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (runChild : FileChild σ) (source : File) (state : σ) : Option (Output σ) := do
  let before ← executeProgram B hB (OuterExchangeProgram.beforeProgram f (R*Parameters.W) G S) source
  let scattered ← scatterRoles R Parameters.W (segmentVolume f G S) B before.1
  let network ← PhysicalNetwork.execute (f := f) (P := R) (G := G) (S := S) (hG := hG) (hS := hS)
    B hB runChild (inputFiles scattered.1) ((globalProgram Parameters.d).length+1) state
  let gathered ← gatherRoles R Parameters.W (segmentVolume f G S) B (sinkFiles network.files)
  let after ← executeProgram B hB (OuterExchangeProgram.afterProgram f (R*Parameters.W) G S hS) gathered.1
  return ⟨after.1,network.state,before.2+scattered.2+network.localCost+gathered.2+after.2,
    network.recursiveCost⟩

def networkConstant : ℕ := ∑ e : Edge,networkCoefficient e

def partitionConstant : ℕ := 3*Parameters.W+9

def levelCoefficient : ℕ := 30*Parameters.m+2*partitionConstant+networkConstant

theorem scanCost_from_scaled {cost V K B : ℕ} (hB : 0 < B)
    (hc : cost*B ≤ 6*V+(3*K+3)*B) : cost ≤ (3*K+9)*(V/B+1) := by
  have hmod := Nat.mod_lt V hB
  have hdiv := Nat.div_add_mod V B
  have hv : V ≤ (V/B+1)*B := by nlinarith
  have he : (3*K+3)*B ≤ ((3*K+3)*(V/B+1))*B := by
    simpa only [Nat.mul_one] using (Nat.mul_le_mul_right B
      (Nat.mul_le_mul_left (3*K+3) (show (1 : ℕ) ≤ V/B+1 from Nat.succ_le_succ (Nat.zero_le _))))
  have hc' : cost*B ≤ ((3*K+9)*(V/B+1))*B := by nlinarith
  exact Nat.le_of_mul_le_mul_right hc' hB

theorem child_volume_le (f R G S : ℕ) :
    longVolume f R G S ≤ longVolume f (R*Parameters.W) G S := by
  rw [local_volume,parent_volume]
  have hW : 1 ≤ Parameters.W := by rw [Parameters.W_value]; omega
  simpa only [one_mul] using Nat.mul_le_mul_right (R*segmentVolume f G S) hW

/-- Correctness and costs are for a single actual Option execution, with
all layouts instantiated. No external oracle supplies scatter, gather or
outer-scan correctness. -/
theorem level_execution_cost (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : StatefulRecursiveExchange.ChildAction (Prefix := Fin R) (Gap := Fin G)
      (Suffix := Fin S) σ f) (runChild : FileChild σ) (C : ℕ)
    (hc : ChildAvailable (actualLayouts f R G S hG hS).layout B hB child runChild)
    (hcost : ChildCostBound (actualLayouts f R G S hG hS) B hB child runChild C)
    (F : EdgeStream f (R*Parameters.W) G S) (source : File) (state : σ)
    (hsource : source = represented (commonLayout f (R*Parameters.W) G S) B hB F) :
    ∃ out,
      executeLevel f R G S B hG hS hB runChild source state = some out ∧
      out.output = represented (commonLayout f (R*Parameters.W) G S) B hB
        (StatefulRecursiveExchange.full f child F state).1 ∧
      out.state = (StatefulRecursiveExchange.full f child F state).2 ∧
      out.localCost ≤ levelCoefficient*(longVolume f (R*Parameters.W) G S/B+1) ∧
      out.recursiveCost ≤ Parameters.S*C := by
  let layout := commonLayout f (R*Parameters.W) G S
  let pre := transport (mapPairEquiv lowerSubtractEquiv) F
  obtain ⟨preFile,cb,hbefore,hcb⟩ := scanRun_exists layout B hB
    (OuterExchangeProgram.beforeProgram f (R*Parameters.W) G S)
    (mapPairEquiv lowerSubtractEquiv) (OuterExchangeProgram.before_destination f (R*Parameters.W) G S)
    F source hsource
  obtain ⟨cs,hscatter,hcs⟩ := recursive_scatter_execution f R G S B hB pre
  rw [← hbefore.target_eq] at hscatter
  let scattered : List File := List.ofFn (fun r : Fin Parameters.W =>
    represented (commonLayout f R G S) B hB (splitInput f pre (roleEnumeration.symm r)))
  have hinputs : ∀ r,inputFiles scattered r =
      represented (actualLayouts f R G S hG hS).layout B hB (splitInput f pre r) := by
    intro r
    change inputFiles scattered r = represented (commonLayout f R G S) B hB (splitInput f pre r)
    simp only [inputFiles,scattered,List.getElem?_ofFn,dif_pos (roleEnumeration r).isLt,
      Option.getD_some,Fin.eta,Equiv.symm_apply_apply]
  obtain ⟨network,hnrun,hnactual,hnfiles,hnlocal,hnrec⟩ := actual_network_execution_cost B hB
    child runChild C hc hcost (splitInput f pre) (inputFiles scattered) state hinputs
  have hnstate := (NetworkRun.projection (actualLayouts f R G S hG hS) B hB child runChild
    (splitInput f pre) (inputFiles scattered) state _ network hnrun).2
  let semantic := StatefulRecursiveExchange.execute f (splitInput f pre)
    (fun e => StatefulRecursiveExchange.edgeProgram f e child) ((globalProgram Parameters.d).length+1) state
  let outputs : Reg → EdgeStream f R G S := fun r =>
    semantic.1 (sinkWire (globalProgram Parameters.d) (globalSwap r))
  obtain ⟨cg,hgather,hcg⟩ := recursive_gather_output_execution f R G S B hB outputs
  have hsinks : sinkFiles network.files = List.ofFn (fun r : Fin Parameters.W =>
      represented (commonLayout f R G S) B hB (outputs (roleEnumeration.symm r))) := by
    unfold sinkFiles
    apply congrArg List.ofFn
    funext r
    exact hnfiles _
  rw [← hsinks] at hgather
  obtain ⟨postFile,ca,hafter,hca⟩ := scanRun_exists layout B hB
    (OuterExchangeProgram.afterProgram f (R*Parameters.W) G S hS)
    (mapPairEquiv lowerReflectEquiv)
    (OuterExchangeProgram.after_destination f (R*Parameters.W) G S hS)
    (gatherOutput f outputs) (represented layout B hB (gatherOutput f outputs)) rfl
  let out : Output σ := ⟨postFile,network.state,cb+cs+network.localCost+cg+ca,network.recursiveCost⟩
  refine ⟨out,?_,?_,?_,?_,hnrec⟩
  · have hscatter' : scatterRoles R Parameters.W (segmentVolume f G S) B preFile = some (scattered,cs) := hscatter
    unfold executeLevel
    rw [hbefore.actual]
    try rw [Option.bind_eq_bind]
    rw [Option.some_bind]
    rw [hscatter']
    try rw [Option.bind_eq_bind]
    rw [Option.some_bind]
    rw [hnactual]
    try rw [Option.bind_eq_bind]
    rw [Option.some_bind]
    rw [hgather]
    try rw [Option.bind_eq_bind]
    rw [Option.some_bind]
    rw [hafter.actual]
    rfl
  · exact hafter.target_eq
  · exact hnstate
  · rw [OuterExchangeProgram.before_constant] at hcb
    rw [OuterExchangeProgram.after_constant] at hca
    have hcs' : cs ≤ partitionConstant*(longVolume f (R*Parameters.W) G S/B+1) := by
      apply scanCost_from_scaled hB
      simpa only [parent_volume] using hcs
    have hcg' : cg ≤ partitionConstant*(longVolume f (R*Parameters.W) G S/B+1) := by
      apply scanCost_from_scaled hB
      simpa only [parent_volume] using hcg
    have hv : longVolume f R G S/B ≤ longVolume f (R*Parameters.W) G S/B :=
      Nat.div_le_div_right (child_volume_le f R G S)
    have hnlocal' : network.localCost ≤ networkConstant*(longVolume f (R*Parameters.W) G S/B+1) :=
      hnlocal.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hv 1))
    change cb+cs+network.localCost+cg+ca ≤ _
    unfold levelCoefficient
    nlinarith

/-- Semantic child callback used when recursive calls swap the selected
short fields and return their genuine continuation identifier unchanged. -/
def exchangeChild (f R G S : ℕ) :
    StatefulRecursiveExchange.ChildAction (Prefix := Fin R) (Gap := Fin G) (Suffix := Fin S) σ f :=
  fun c F state => ((transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F,c),state)

theorem full_exchange_semantics (f R G S : ℕ) (F : EdgeStream f (R*Parameters.W) G S) (state : σ) :
    StatefulRecursiveExchange.full f (exchangeChild f R G S) F state =
      (transport exchangeEquiv F,state) := by
  let pureChild := fun (c : Child) (F : EdgeStream f R G S) =>
    transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F
  have hp := StatefulRecursiveExchange.full_projection f (exchangeChild f R G S) pureChild
    (fun s => s=state) (fun _ _ _ hs => ⟨rfl,hs⟩) F state rfl
  apply Prod.ext
  · exact hp.1.trans (factoredFullExchange_correct f pureChild (fun _ _ => rfl) F)
  · exact hp.2

/-- The induction interface for physical recursive sorting: only smaller
child executions and their true costs are assumptions. -/
theorem exchange_execution_cost (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (runChild : FileChild σ) (C : ℕ)
    (hc : ChildAvailable (actualLayouts f R G S hG hS).layout B hB (exchangeChild f R G S) runChild)
    (hcost : ChildCostBound (actualLayouts f R G S hG hS) B hB (exchangeChild f R G S) runChild C)
    (F : EdgeStream f (R*Parameters.W) G S) (source : File) (state : σ)
    (hsource : source = represented (commonLayout f (R*Parameters.W) G S) B hB F) :
    ∃ out,
      executeLevel f R G S B hG hS hB runChild source state = some out ∧
      out.output = represented (commonLayout f (R*Parameters.W) G S) B hB (transport exchangeEquiv F) ∧
      out.state = state ∧
      out.localCost ≤ levelCoefficient*(longVolume f (R*Parameters.W) G S/B+1) ∧
      out.recursiveCost ≤ Parameters.S*C := by
  simpa only [full_exchange_semantics] using
    level_execution_cost f R G S B hG hS hB (exchangeChild f R G S) runChild C hc hcost F source state hsource

end
end CodedSorting.PhysicalWholeLevel
end PhysicalWholeLevel

section InvocationWorkspace
/-! File names for one complete exchange invocation.  Besides the network's
matrix and XOR scans, the inventory includes the two outer programs, the
role transpose/split/join files, and the variable number of leaf buckets.
The contents below are proof specifications of files written by the existing
stream primitives; allocating an unused slot does not write its payload. -/
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000
namespace CodedSorting.InvocationWorkspace
open RecursiveExchange RecursiveExchangeCost ProgramWorkspace CircuitWorkspace
open WorkspaceAllocation BucketMachine TagErasure PhysicalRecursiveExchange
open scoped BigOperators
noncomputable section

/-- Transpose buckets, the transposed output, and the separately aligned
role files created by `scatterRoles`, respectively. -/
abbrev ScatterSlot (K : ℕ) := Fin K ⊕ Unit ⊕ Fin K

/-- The joined input, inverse-transpose buckets, and its final output. -/
abbrev GatherSlot (K : ℕ) := Unit ⊕ Fin K ⊕ Unit

theorem scatter_slot_count (K : ℕ) : Fintype.card (ScatterSlot K)=2*K+1 := by
  simp only [ScatterSlot,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
  omega

theorem gather_slot_count (K : ℕ) : Fintype.card (GatherSlot K)=K+2 := by
  simp only [GatherSlot,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
  omega

/-- These are the actual pass lists used on either side of executeLevel. -/
abbrev OuterSlot (f R G S : ℕ) (hS : 0<S) :=
  ProgramSlot (OuterExchangeProgram.beforeProgram f (R*Parameters.W) G S) ⊕
  ProgramSlot (OuterExchangeProgram.afterProgram f (R*Parameters.W) G S hS)

theorem outer_slot_bound (f R G S : ℕ) (hS : 0<S) :
    Fintype.card (OuterSlot f R G S hS)≤30*Parameters.m := by
  have hb := program_slot_bound (OuterExchangeProgram.beforeProgram f (R*Parameters.W) G S)
  have ha := program_slot_bound (OuterExchangeProgram.afterProgram f (R*Parameters.W) G S hS)
  rw [OuterExchangeProgram.before_constant] at hb
  rw [OuterExchangeProgram.after_constant] at ha
  simp only [OuterSlot,Fintype.card_sum]
  omega

abbrev LevelSlot (f R G S : ℕ) (hG : 0<G) (hS : 0<S) :=
  KnownLayerSlot f R G S hG hS ⊕ OuterSlot f R G S hS ⊕
  ScatterSlot Parameters.W ⊕ GatherSlot Parameters.W

/-- Tagged budgets avoid normalizing the enormous concrete network's
enumeration when defining file identifiers. -/
abbrev LevelBudgetSlot := BudgetSlot ⊕ Fin (30*Parameters.m) ⊕
  ScatterSlot Parameters.W ⊕ GatherSlot Parameters.W

noncomputable def levelBudget := Fintype.card LevelBudgetSlot

def outerSlotIndex (f R G S : ℕ) (hS : 0<S) :
    OuterSlot f R G S hS↪Fin (30*Parameters.m) where
  toFun slot := ((Fintype.equivFin _) slot).castLE (outer_slot_bound f R G S hS)
  inj' x y h := by
    apply (Fintype.equivFin _).injective
    apply Fin.ext
    simpa only [Fin.coe_castLE] using congrArg (@Fin.val (30*Parameters.m)) h

def levelTagIndex (f R G S : ℕ) (hG : 0<G) (hS : 0<S) :
    LevelSlot f R G S hG hS↪LevelBudgetSlot :=
  (knownLayerTagIndex f R G S hG hS).sumMap
    ((outerSlotIndex f R G S hS).sumMap (Function.Embedding.refl _))

def levelSlotIndex (f R G S : ℕ) (hG : 0<G) (hS : 0<S) :
    LevelSlot f R G S hG hS↪Fin levelBudget :=
  (levelTagIndex f R G S hG hS).trans (Fintype.equivFin LevelBudgetSlot).toEmbedding

theorem level_slot_index_injective (f R G S : ℕ) (hG : 0<G) (hS : 0<S) :
    Function.Injective (levelSlotIndex f R G S hG hS) :=
  (levelSlotIndex f R G S hG hS).injective

attribute [local irreducible] levelBudget

/-- Includes the source and final output. In the RAM branch the bucket
slots are simply unused. -/
abbrev LeafSlot (Q : ℕ) := Fin 2 ⊕ Fin (Q*Q)

theorem leaf_slot_count (Q : ℕ) : Fintype.card (LeafSlot Q)=2+Q*Q := by
  simp only [LeafSlot,Fintype.card_sum,Fintype.card_fin]

/-- Both exchanged fields are present in the real address. Consequently
the number of leaf buckets is at most the nonempty invocation volume,
regardless of the cutoff or the available RAM. -/
theorem leaf_bucket_volume (P Q G S : ℕ) (hV : 0<BaseExchangeProgram.Volume P Q G S) :
    Q*Q≤BaseExchangeProgram.Volume P Q G S := by
  have hP : 0<P := by
    by_contra h
    have he : P=0 := by omega
    simp [BaseExchangeProgram.Volume,he] at hV
  have hG : 0<G := by
    by_contra h
    have he : G=0 := by omega
    simp [BaseExchangeProgram.Volume,he] at hV
  have hS : 0<S := by
    by_contra h
    have he : S=0 := by omega
    simp [BaseExchangeProgram.Volume,he] at hV
  have h := Nat.le_mul_of_pos_right (Q*Q) (Nat.mul_pos (Nat.mul_pos hP hG) hS)
  convert h using 1 <;> unfold BaseExchangeProgram.Volume <;> ring

/-- One fixed coefficient serves internal nodes and leaf boundary files;
the extra V slots account explicitly for the Q² leaf buckets. -/
noncomputable def fixedBudget := levelBudget+2

private theorem extra_slots (C Q V : ℕ) (h : Q*Q≤V) : 2+Q*Q≤(C+2)+V := by omega

theorem leaf_slot_bound (P Q G S C : ℕ) (hV : 0<BaseExchangeProgram.Volume P Q G S) :
    Fintype.card (LeafSlot Q)≤(C+2)+BaseExchangeProgram.Volume P Q G S := by
  rw [leaf_slot_count]
  exact extra_slots C Q (BaseExchangeProgram.Volume P Q G S)
    (leaf_bucket_volume P Q G S hV)

/-- Canonical complete files and all shorter canonical fragments fit a
V-block slot. In particular, this includes each returned XOR/scan file. -/
theorem canonical_capacity {V : ℕ} (B : ℕ) (hB : 0<B) (F : Fin V→Circuit.Bit) :
    (canonical B hB F).length≤V := by
  simpa only [canonical,List.length_ofFn] using packed_file_fits B hB (List.ofFn F)

theorem represented_capacity {A : Type} {V : ℕ} (layout : A≃Fin V)
    (B : ℕ) (hB : 0<B) (F : A→Circuit.Bit) :
    (represented layout B hB F).length≤V :=
  canonical_capacity B hB _

/-- These are exactly the bucket files consumed by the reconstruction
phase of `DiskStreamPass.run`, not hypothetical sorted copies. -/
theorem bucket_file_capacity {V K : ℕ} {Value : Type*}
    (key : Fin V→Fin K) (F : Fin V→Value) (B : ℕ) (hB : 0<B) (k : Fin K) :
    (valueWriters key F B k).finish.length≤V := by
  rw [valueWriters_erasure,mapWriter_finish,List.length_map]
  let key' := fun r : Fin V×Value => key r.1
  let xs := AffineStreams.inputRecords F
  have hv := buffered_bucket_valid key' B hB xs k
  have hc := buffered_bucket_correct key' B xs k
  rw [Writer.finish_contents] at hc
  have hp := (Writer.finish_capacity B _ hv).2
  rw [hc] at hp
  have hs := (bucket_sublist key' xs k).length_le
  have hx : xs.length=V := by simp [xs,AffineStreams.inputRecords]
  rw [hx] at hs
  have hmul := Nat.le_mul_of_pos_right ((bufferedBuckets key' B xs k).finish.length) hB
  change (bufferedBuckets key' B xs k).finish.length≤V
  by_contra hbad
  have hlt : V+1≤(bufferedBuckets key' B xs k).finish.length := by omega
  have hm := Nat.mul_le_mul_right B hlt
  nlinarith

/-- Every bucket returned by the actual distribution loop has the stated
capacity. This uses the returned bucket array, with no assumption that the
implementation chose an independently specified file. -/
theorem actual_distribution_capacity {V K : ℕ} {Value : Type*}
    (key : Fin V→Fin K) (F : Fin V→Value) (B : ℕ) (hB : 0<B) :
    ∃ source buckets,
      DiskStreamPass.distribute key B V 0 (by omega)
        (BucketReader.Reader.fromDisk (pack B hB (inputValues F)))
        (fun _ => Writer.empty)=some (source,buckets) ∧
      ∀ k,(buckets k).finish.length≤V := by
  obtain ⟨source,hr,_,_,_,_⟩ := DiskStreamPass.distribute_refines key F B V 0 (by omega)
    (BucketReader.Reader.fromDisk (pack B hB (inputValues F))) (fun _ => Writer.empty) []
    (StreamCopy.pack_reader_valid B hB _) (fun _ => Writer.empty_valid B hB)
    (by simp [BucketReader.Reader.contents,BucketReader.Reader.fromDisk,
      flatten_pack,indices_full,inputValues])
  exact ⟨source,valueWriters key F B,hr,fun k => bucket_file_capacity key F B hB k⟩

/-- Each actual prefix of an outer or edge address program returns a file
that fits its named output slot. The same lemma covers all pass indices. -/
theorem actual_program_output_capacity {V : ℕ} (ps : List (ScanProgram.Pass V))
    (F : Fin V→Circuit.Bit) (B : ℕ) (hB : 0<B) (count : ℕ) :
    ∃ output cost, executeProgram B hB (ps.take count) (canonical B hB F)=some (output,cost) ∧
      output.length≤V := by
  obtain ⟨cost,hr,_,_⟩ := executeProgram_exists B hB (ps.take count) F
  exact ⟨canonical B hB (ScanProgram.eval (ps.take count) F),cost,hr,canonical_capacity B hB _⟩

theorem role_file_capacity {R K C : ℕ} {Value : Type*}
    (F : Fin (K*(R*C))→Value) (B : ℕ) (hB : 0<B) (r : Fin K) :
    (pack B hB (PhysicalRolePartition.roleValues F r)).length≤K*(R*C) := by
  have h := packed_file_fits B hB (PhysicalRolePartition.roleValues F r)
  have hr : (PhysicalRolePartition.roleValues F r).length=R*C := by
    simp [PhysicalRolePartition.roleValues]
  rw [hr] at h
  exact h.trans (Nat.le_mul_of_pos_left _ (by have := r.isLt; omega))

theorem leaf_output_capacity {Value : Type*} (P Q G S cutoff B : ℕ) (hB : 0<B)
    (F : Fin (BaseExchangeProgram.Volume P Q G S)→Value)
    (hstartup : cutoff<BaseExchangeProgram.Volume P Q G S →
      (Q*Q)*B≤BaseExchangeProgram.Volume P Q G S+B) :
    ∃ result, BaseExchangeProgram.adaptiveRun (P := P) (Q := Q) (G := G) (S := S)
      cutoff B (pack B hB (inputValues F))=some result ∧
      result.output.finish.length≤BaseExchangeProgram.Volume P Q G S := by
  obtain ⟨r,hr,ho,_,_⟩ := BaseExchangeProgram.adaptive_correct F cutoff B hB hstartup
  refine ⟨r,hr,?_⟩
  rw [ho]
  simpa only [outputValues,List.length_map,List.length_finRange] using
    packed_file_fits B hB (outputValues BaseExchangeProgram.permutation F)

/-- A named finite inventory embeds into its proven budget, with no
identification of different bucket, edge, or pass names. -/
def slotIndex {Slot : Type} [Fintype Slot] (budget : ℕ)
    (h : Fintype.card Slot≤budget) : Slot↪Fin budget where
  toFun slot := ((Fintype.equivFin Slot) slot).castLE h
  inj' x y he := by
    apply (Fintype.equivFin Slot).injective
    apply Fin.ext
    simpa only [Fin.coe_castLE] using congrArg (@Fin.val budget) he

/-- Arithmetic addresses for the actual named files of one invocation.
Each slot reserves V blocks; the next invocation can start at next+budget*V. -/
def slotSpan {budget : ℕ} (next V : ℕ) (i : Fin budget) : Span :=
  ⟨next+i.val*V,V⟩

def levelFileSpan (f R G S : ℕ) (hG : 0<G) (hS : 0<S) (next : ℕ)
    (slot : LevelSlot f R G S hG hS) : Span :=
  slotSpan next (longVolume f (R*Parameters.W) G S)
    (levelSlotIndex f R G S hG hS slot)

def leafFileSpan (P Q G S : ℕ) (hV : 0<BaseExchangeProgram.Volume P Q G S) (next : ℕ)
    (slot : LeafSlot Q) : Span :=
  slotSpan next (BaseExchangeProgram.Volume P Q G S)
    (slotIndex ((levelBudget+2)+BaseExchangeProgram.Volume P Q G S)
      (leaf_slot_bound P Q G S levelBudget hV) slot)

theorem slot_span_bounds {budget : ℕ} (next V : ℕ) (i : Fin budget) :
    next≤(slotSpan next V i).start ∧ (slotSpan next V i).stop≤next+budget*V := by
  have hi := Nat.mul_le_mul_right V (show i.val+1≤budget from i.isLt)
  simp only [Nat.add_mul,Nat.one_mul] at hi
  simp only [slotSpan,Span.stop]
  omega

theorem slot_span_disjoint {budget : ℕ} (next V : ℕ) (i j : Fin budget) (hij : i≠j) :
    Before (slotSpan next V i) (slotSpan next V j) ∨
      Before (slotSpan next V j) (slotSpan next V i) := by
  rcases lt_or_gt_of_ne hij with h|h
  · left
    have hh := Nat.mul_le_mul_right V (show i.val+1≤j.val from h)
    simp only [Nat.add_mul,Nat.one_mul] at hh
    simp only [Before,slotSpan,Span.stop]
    omega
  · right
    have hh := Nat.mul_le_mul_right V (show j.val + 1 ≤ i.val from h)
    simp only [Nat.add_mul,Nat.one_mul] at hh
    simp only [Before,slotSpan,Span.stop]
    omega

theorem named_slot_no_alias {Slot : Type} [Fintype Slot] (next V budget : ℕ)
    (h : Fintype.card Slot≤budget) (x y : Slot) (hxy : x≠y) (a : ℕ)
    (ha : (slotSpan next V (slotIndex budget h x)).Contains a) :
    ¬(slotSpan next V (slotIndex budget h y)).Contains a := by
  have hn : slotIndex budget h x≠slotIndex budget h y :=
    fun he => hxy ((slotIndex budget h).injective he)
  rcases slot_span_disjoint next V _ _ hn with hl|hr
  · exact before_no_alias hl a ha
  · intro hy
    exact before_no_alias hr a hy ha

/-- The existing physical block-write loop can fill one named file without
modifying any other named file; unused reservation slack is untouched. -/
theorem named_write_preserves_other {Slot : Type} [Fintype Slot] {B w : ℕ}
    (next V budget : ℕ) (h : Fintype.card Slot≤budget)
    (x y : Slot) (hxy : x≠y)
    (produce : Fin V→Fin B→WordControl.Word w) (n : ℕ) (hn : n≤V)
    (disk : WordControl.BlockDisk B w) (a : ℕ)
    (ha : (slotSpan next V (slotIndex budget h y)).Contains a) :
    writePrefix (slotSpan next V (slotIndex budget h x)) produce n hn disk a=disk a := by
  apply writePrefix_outside
  exact named_slot_no_alias next V budget h y x (Ne.symm hxy) a ha

end
end CodedSorting.InvocationWorkspace
end InvocationWorkspace

section InvocationWorkspaceBound
/-! Polynomial allocation including the variable Q² leaf-bucket inventory.
The bound reserves (C+V) files of V blocks at an invocation of volume V;
`InvocationWorkspace` identifies actual file names and capacities within
this budget. Reservations are external and unused slack is never scanned. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
namespace CodedSorting.InvocationWorkspaceBound
open RecursiveExchange WorkspaceAllocation InvocationWorkspace
open PolynomialWorkspace.Exchange
open scoped BigOperators
noncomputable section

attribute [local irreducible] levelBudget

def reservation (C : ℕ) : CallTree→ℕ
  | .stop _ V _ => (C+V)*V
  | .level _ V _ children => (C+V)*V+∑ c,reservation C (children c)

def fileSizes (C : ℕ) : CallTree→List ℕ
  | .stop _ V _ => List.replicate (C+V) V
  | .level _ V _ children => List.replicate (C+V) V++
      (Finset.univ : Finset Child).toList.flatMap (fun c => fileSizes C (children c))

private theorem sum_flatMap_eq {α : Type*} (xs : List α) (f : α→List ℕ) :
    (xs.flatMap f).sum=(xs.map (fun a => (f a).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp [ih]

theorem fileSizes_sum (C : ℕ) (tree : CallTree) :
    (fileSizes C tree).sum=reservation C tree := by
  induction tree with
  | stop width V charge => simp [fileSizes,reservation]
  | level width V charge children ih =>
    simp only [fileSizes,List.sum_append,List.sum_replicate,smul_eq_mul,
      sum_flatMap_eq,Function.comp_def,ih,Finset.sum_map_toList,reservation]

theorem slotSpan_mem_allocate {budget : ℕ} (next V : ℕ) (i : Fin budget) :
    slotSpan next V i∈allocate next (List.replicate budget V) := by
  induction budget generalizing next with
  | zero => exact Fin.elim0 i
  | succ budget ih =>
    rw [List.replicate_succ,allocate,List.mem_cons]
    by_cases hz : i.val=0
    · left
      simp [slotSpan,hz]
    · right
      let j : Fin budget := ⟨i.val-1,by have := i.isLt; omega⟩
      have he : slotSpan next V i=slotSpan (next+V) V j := by
        have hi : i.val=j.val+1 := by dsimp [j]; omega
        simp only [slotSpan,hi]
        congr 1
        ring
      rw [he]
      exact ih (next+V) j

/-- The arithmetic slot assignment is literally a member of the allocator's
list, not a separate unrelated interval layout. -/
theorem named_span_mem {Slot : Type} [Fintype Slot]
    (next V C : ℕ) (h : Fintype.card Slot≤C+V) (slot : Slot) :
    slotSpan next V (slotIndex (C+V) h slot)∈
      allocate next (List.replicate (C+V) V) :=
  slotSpan_mem_allocate next V _

private theorem budget_slack (C V : ℕ) : C≤(C+2)+V := by omega

private theorem slotSpan_mem_extended {a b : ℕ} (next V : ℕ) (h : a≤b) (i : Fin a) :
    slotSpan next V i∈allocate next (List.replicate b V) :=
  slotSpan_mem_allocate next V (i.castLE h)

theorem level_span_mem_local (f R G S : ℕ) (hG : 0<G) (hS : 0<S) (next : ℕ)
    (slot : LevelSlot f R G S hG hS) :
    levelFileSpan f R G S hG hS next slot∈allocate next
      (List.replicate ((levelBudget+2)+RecursiveExchangeCost.longVolume f (R*Parameters.W) G S)
        (RecursiveExchangeCost.longVolume f (R*Parameters.W) G S)) := by
  let V := RecursiveExchangeCost.longVolume f (R*Parameters.W) G S
  let i := levelSlotIndex f R G S hG hS slot
  have h := budget_slack levelBudget V
  exact slotSpan_mem_extended next V h i

theorem leaf_span_mem_local (P Q G S : ℕ) (hV : 0<BaseExchangeProgram.Volume P Q G S)
    (next : ℕ) (slot : LeafSlot Q) :
    leafFileSpan P Q G S hV next slot∈allocate next
      (List.replicate ((levelBudget+2)+BaseExchangeProgram.Volume P Q G S)
        (BaseExchangeProgram.Volume P Q G S)) :=
  slotSpan_mem_allocate next (BaseExchangeProgram.Volume P Q G S)
    (slotIndex ((levelBudget+2)+BaseExchangeProgram.Volume P Q G S)
      (leaf_slot_bound P Q G S levelBudget hV) slot)

theorem pruned_bound (C base cutoff : ℕ) (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    (k V N : ℕ) (hVN : V≤N) :
    reservation C (CallTree.prunedBuild base cutoff leaf charge k V)≤
      (C+N)*N*(Parameters.S+1)^(k+1) := by
  induction k generalizing V with
  | zero =>
    simp only [CallTree.prunedBuild,reservation,pow_one]
    have h := Nat.mul_le_mul (Nat.add_le_add_left hVN C) hVN
    exact h.trans (Nat.le_mul_of_pos_right _ (show 0<Parameters.S+1 from Nat.zero_lt_succ _))
  | succ k ih =>
    rw [CallTree.prunedBuild]
    split_ifs
    · simp only [reservation]
      have h := Nat.mul_le_mul (Nat.add_le_add_left hVN C) hVN
      exact h.trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
    · simp only [reservation,Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul]
      have hs := Finset.sum_le_sum (fun (c : Child) (_ : c∈Finset.univ) =>
        ih (V/Parameters.W) ((Nat.div_le_self _ _).trans hVN))
      simp only [Finset.sum_const,Finset.card_univ,child_count,smul_eq_mul] at hs
      have hv := Nat.mul_le_mul (Nat.add_le_add_left hVN C) hVN
      have hh : (C+N)*N≤(C+N)*N*(Parameters.S+1)^(k+1) :=
        Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
      rw [pow_succ]
      nlinarith

/-- The additional V leaf slots cost one extra fixed exponent of the root
volume. No bound on the cutoff, memory, or leaf width is assumed. -/
theorem cutoff_polynomial (C base cutoff k rows : ℕ) (hb : 0<base)
    (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P≃Fin (rows*Parameters.W^k))
    (hV : 0<Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)) :
    let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
    reservation C (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls≤
      (C+1)*V^(2*Nat.clog radix (Parameters.S+1)+2) := by
  dsimp only
  rw [cutoffExchange_calls]
  obtain ⟨hqN,hdepth⟩ := actual_depth_bound base k hb hV
  let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
  have ht := pruned_bound C base cutoff leaf charge k V V le_rfl
  have hb' := branching_polynomial radix Parameters.S k V radix_prime.two_le hqN hdepth
  have hc : C+V≤(C+1)*V := by dsimp [V]; nlinarith
  calc
    reservation C (CallTree.prunedBuild base cutoff leaf charge k V)
        ≤(C+V)*V*(Parameters.S+1)^(k+1) := ht
    _≤((C+1)*V)*V*V^(2*Nat.clog radix (Parameters.S+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right V hc) hb'
    _=(C+1)*V^(2*Nat.clog radix (Parameters.S+1)+2) := by ring

def exponent (C : ℕ) := Nat.clog 2 (C+1)+2*Nat.clog radix (Parameters.S+1)+2

theorem cutoff_integer_polynomial (C base cutoff k rows : ℕ) (hb : 0<base)
    (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P≃Fin (rows*Parameters.W^k))
    (hV : 0<Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)) :
    let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
    reservation C (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls≤
      V^(exponent C) := by
  dsimp only
  have hp := cutoff_polynomial C base cutoff k rows hb leaf charge layout hV
  have hN := radix_prime.two_le.trans (actual_depth_bound base k hb hV).1
  have ha := absorb_coefficient (C+1) _ (2*Nat.clog radix (Parameters.S+1)+2) hN
  simpa only [exponent,Nat.add_assoc] using hp.trans ha

def files (C : ℕ) (tree : CallTree) := allocate 0 (fileSizes C tree)

theorem files_pairwise (C : ℕ) (tree : CallTree) : (files C tree).Pairwise Before :=
  allocate_pairwise _ _

theorem files_capacity (C : ℕ) (tree : CallTree) :
    ((files C tree).map Span.blocks).sum=reservation C tree := by
  rw [files,allocate_lengths,fileSizes_sum]

theorem actual_span_bound (C base cutoff k rows : ℕ) (hb : 0<base)
    (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P≃Fin (rows*Parameters.W^k))
    (hV : 0<Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z))
    (file : Span)
    (hf : file∈files C (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls) :
    let V := Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)
    file.start≤V^(exponent C) ∧ file.blocks≤V^(exponent C) ∧ file.stop≤V^(exponent C) := by
  dsimp only
  have h := (allocate_bounds 0 _ file hf).2
  rw [Nat.zero_add,fileSizes_sum] at h
  have hp := h.trans (cutoff_integer_polynomial C base cutoff k rows hb leaf charge layout hV)
  unfold Span.stop at *
  omega

end
end CodedSorting.InvocationWorkspaceBound
end InvocationWorkspaceBound

section PhysicalFileHandles
/-! Finite external-file handles and directories. A handle stores a block
base and a logical record count. A directory may contain aliases. Payload
lists occur only as views of the common physical disk, never as resident
fields. The bit view uses the existing position-preserving word codec. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.PhysicalFileHandles
open WordControl WorkspaceAllocation

structure Handle (N exponent : ℕ) where
  base : Fin (N^exponent+1)
  records : Fin (N^exponent+1)
  deriving DecidableEq

theorem handle_ext {N e : ℕ} {h k : Handle N e}
    (hb : h.base=k.base) (hr : h.records=k.records) : h=k := by
  cases h
  cases k
  cases hb
  cases hr
  rfl

abbrev Directory (N exponent : ℕ) (Key : Type*) := Key→Handle N exponent

noncomputable section
variable {N e : ℕ} {Key : Type*} [Fintype Key]

/-- Field zero is the block base; field one is the logical record count.
The field order is fixed before seeing the input payload. -/
def encodeDirectory (dir : Directory N e Key) :
    Fin (2*Fintype.card Key)→Fin (N^e+1) := fun i =>
  let pair := finProdFinEquiv.symm i
  let h := dir ((Fintype.equivFin Key).symm pair.2)
  if pair.1.val=0 then h.base else h.records

def decodeDirectory (fields : Fin (2*Fintype.card Key)→Fin (N^e+1)) : Directory N e Key :=
  fun k => ⟨fields (finProdFinEquiv (0,(Fintype.equivFin Key) k)),
    fields (finProdFinEquiv (1,(Fintype.equivFin Key) k))⟩

@[simp] theorem decode_encodeDirectory (dir : Directory N e Key) :
    decodeDirectory (encodeDirectory dir)=dir := by
  funext k
  apply handle_ext <;>
    simp [decodeDirectory,encodeDirectory]

theorem encodeDirectory_injective :
    Function.Injective (encodeDirectory (N := N) (e := e) (Key := Key)) := by
  intro a b h
  simpa only [decode_encodeDirectory] using congrArg decodeDirectory h

/-- A concrete resident word array. The lower constant in w=Θ(log N) is
charged by c words per address digit instead of changing w. -/
def directoryWords (w c : ℕ) (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (dir : Directory N e Key) : Words ((2*Fintype.card Key)*(c*(e+1))) w :=
  WordConvention.encodeTuple N w c e (2*Fintype.card Key) hN hw (encodeDirectory dir)

theorem directoryWords_injective (w c : ℕ) (hN : 2≤N) (hw : WordConvention.Covers N w c) :
    Function.Injective (directoryWords (Key := Key) (e := e) w c hN hw) := by
  intro a b h
  apply encodeDirectory_injective
  exact WordConvention.encodeTuple_injective N w c e (2*Fintype.card Key) hN hw h

theorem directoryWords_field (w c : ℕ) (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (dir : Directory N e Key) (i : Fin (2*Fintype.card Key)) :
    decodeWords (fun j => directoryWords w c hN hw dir (finProdFinEquiv (i,j)))=
      (encodeDirectory dir i).val := by
  simp only [directoryWords,WordConvention.encodeTuple,Equiv.symm_apply_apply]
  exact WordConvention.decode_encode N w c e hN hw _

end

section Views
variable {N e B : ℕ} {Value : Type*}

/-- The file name and length are resident; all values come from the disk.
Packing here specifies the list view and is not an executable operation. -/
def fileView (hB : 0<B) (disk : ℕ→Fin B→Value) (h : Handle N e) : List (List Value) :=
  BucketMachine.pack B hB (List.ofFn (fun i : Fin h.records.val =>
    disk (h.base.val+i.val/B) ⟨i.val%B,Nat.mod_lt _ hB⟩))

def Fits (B : ℕ) (h : Handle N e) (s : Span) : Prop :=
  h.base.val=s.start ∧ PhysicalStreamCursor.blockCount B h.records.val≤s.blocks

theorem handle_address_contains (hB : 0<B) (h : Handle N e) (s : Span)
    (hf : Fits B h s) (i : Fin h.records.val) :
    s.Contains (h.base.val+i.val/B) := by
  have hl : (i.val/B)*B<h.records.val := (Nat.div_mul_le_self _ _).trans_lt i.isLt
  have hc := (PhysicalStreamCursor.cursor_live_iff B h.records.val (i.val/B) hB).2 hl
  rcases hf with ⟨hb,hc'⟩
  simp only [Span.Contains,Span.stop]
  rw [hb]
  exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (hc.trans_le hc') _⟩

theorem fileView_congr (hB : 0<B) (disk disk' : ℕ→Fin B→Value)
    (h : Handle N e) (s : Span) (hf : Fits B h s)
    (hd : ∀ a,s.Contains a→disk' a=disk a) :
    fileView hB disk' h=fileView hB disk h := by
  unfold fileView
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [hd _ (handle_address_contains hB h s hf i)]

theorem fileView_capacity (hB : 0<B) (disk : ℕ→Fin B→Value) (h : Handle N e) :
    (fileView hB disk h).length≤h.records.val := by
  unfold fileView
  simpa only [List.length_ofFn] using packed_file_fits B hB
    (List.ofFn (fun i : Fin h.records.val => disk (h.base.val+i.val/B) ⟨i.val%B,Nat.mod_lt _ hB⟩))

theorem fileView_contents_length (hB : 0<B) (disk : ℕ→Fin B→Value) (h : Handle N e) :
    (fileView hB disk h).flatten.length=h.records.val := by
  simp only [fileView,BucketMachine.flatten_pack,List.length_ofFn]

/-- Equality of handles means equality of views, with no read or write. -/
theorem aliased_views (hB : 0<B) (disk : ℕ→Fin B→Value) (h k : Handle N e)
    (hk : h=k) : fileView hB disk h=fileView hB disk k := congrArg (fileView hB disk) hk

end Views

section WordDisk
variable {N e B w : ℕ}

/-- One B-word disk, viewed as B*w bits per block by the already-proved
position-preserving codec. There is no second disk in this definition. -/
def bitView (hB : 0<B*w) (disk : BlockDisk B w) (h : Handle N e) : PhysicalRecursiveExchange.File :=
  fileView hB (fun a => BitWordPacking.blockBits B w (disk a)) h

theorem bitView_congr (hB : 0<B*w) (disk disk' : BlockDisk B w)
    (h : Handle N e) (s : Span) (hf : Fits (B*w) h s)
    (hd : ∀ a,s.Contains a→disk' a=disk a) : bitView hB disk' h=bitView hB disk h :=
  fileView_congr hB _ _ h s hf (fun a ha => congrArg (BitWordPacking.blockBits B w) (hd a ha))

/-- Stack operations or scratch writes below a file's base preserve its
entire bit stream; arbitrary data elsewhere on the disk is allowed. -/
theorem bitView_preserved_above (hB : 0<B*w) (disk disk' : BlockDisk B w)
    (h : Handle N e) (limit : ℕ) (hbase : limit≤h.base.val)
    (hd : ∀ a,limit≤a→disk' a=disk a) : bitView hB disk' h=bitView hB disk h := by
  unfold bitView fileView
  congr 1
  apply congrArg List.ofFn
  funext i
  dsimp only
  rw [hd _ (hbase.trans (Nat.le_add_right _ _))]

/-- A real block write to a disjoint allocated slot preserves every aliased
directory entry referring to this source file. -/
theorem writePrefix_preserves_bitView (hB : 0<B*w) (target source : Span)
    (hs : Before target source ∨ Before source target)
    (produce : Fin target.blocks→Fin B→Word w) (n : ℕ) (hn : n≤target.blocks)
    (disk : BlockDisk B w) (h : Handle N e) (hf : Fits (B*w) h source) :
    bitView hB (writePrefix target produce n hn disk) h=bitView hB disk h :=
  bitView_congr hB disk _ h source hf
    (fun a ha => writePrefix_preserves_other target source hs produce n hn disk a ha)

end WordDisk

section Directory
variable {N e : ℕ} {Key : Type*} [DecidableEq Key]

/-- Forwarding changes only one finite pair of counters. -/
def forward (dir : Directory N e Key) (target source : Key) : Directory N e Key :=
  Function.update dir target (dir source)

theorem forward_target (dir : Directory N e Key) (target source : Key) :
    forward dir target source target=dir source := by simp [forward]

theorem forward_other (dir : Directory N e Key) (target source other : Key) (ho : other≠target) :
    forward dir target source other=dir other := by simp [forward,ho]

def Represents {B w : ℕ} (hB : 0<B*w) (disk : BlockDisk B w)
    (dir : Directory N e Key) (files : Key→PhysicalRecursiveExchange.File) : Prop :=
  ∀ k,bitView hB disk (dir k)=files k

/-- In particular, begin-layer, row-store and commit may copy directory
handles freely without moving the streams to reserved but unwritten files. -/
theorem forward_represents {B w : ℕ} (hB : 0<B*w) (disk : BlockDisk B w)
    (dir : Directory N e Key) (files : Key→PhysicalRecursiveExchange.File)
    (hr : Represents hB disk dir files) (target source : Key) :
    Represents hB disk (forward dir target source) (Function.update files target (files source)) := by
  intro k
  by_cases hk : k=target
  · subst k
    simpa only [forward,Function.update_self] using hr source
  · simpa only [forward,Function.update_of_ne hk] using hr k

end Directory

end CodedSorting.PhysicalFileHandles
end PhysicalFileHandles
