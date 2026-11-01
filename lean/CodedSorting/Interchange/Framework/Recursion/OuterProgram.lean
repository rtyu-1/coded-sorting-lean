import CodedSorting.Interchange.Framework.OneLevel.Allocation
import CodedSorting.Interchange.Framework.OneLevel.Roles
import CodedSorting.Interchange.Framework.Outer.Execution
import CodedSorting.Interchange.Framework.Outer.After
import CodedSorting.Interchange.Framework.Memory.SlabBatchAllocation
import CodedSorting.Shared.Memory.RawComposition

section OuterProgram
/-! One complete recursive parent coded exchange on the common finite machine.
The instruction sequence contains both outer transforms, the two actual
role transposes, the packed/slab scans and every real network gate and edge.
Only public sizes and addresses occur in the generated program.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace CodedSorting.CommonRecursiveOuter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonOneLevelSemantics Circuit CircuitProgram ProgramNetwork Address CodedSimulation
open PhysicalStreamCursor
noncomputable section

/-- Public allocation. The two parent buffers precede all network files.
The network implementation may recurse; no child residency is required. -/
structure Setup (q : Configuration) where
  f : ℕ
  R : ℕ
  G : ℕ
  S : ℕ
  source : ℕ
  temporary : ℕ
  workspace : ℕ
  suffix_positive : 0<S
  fileStride : ℕ
  live_le_stride : blockCount q.block (longVolume f R G S)≤fileStride
  parents_separate : source+count q (longVolume f (R*Parameters.W) G (S*q.w))≤temporary
  network_separate : temporary+count q (longVolume f (R*Parameters.W) G (S*q.w))≤workspace
  workspace_fits : workspace+CommonResidentNetwork.fileCount*fileStride≤q.N^q.exponent

abbrev suffix (q : Configuration) (p : Setup q) := p.S*q.w
abbrev words (q : Configuration) (p : Setup q) := longVolume p.f p.R p.G p.S
abbrev localBits (q : Configuration) (p : Setup q) := longVolume p.f p.R p.G (suffix q p)
abbrev parentBits (q : Configuration) (p : Setup q) := longVolume p.f (p.R*Parameters.W) p.G (suffix q p)
abbrev liveBlocks (q : Configuration) (p : Setup q) := blockCount q.block (words q p)
abbrev parentBlocks (q : Configuration) (p : Setup q) := count q (parentBits q p)
abbrev stride (q : Configuration) (p : Setup q) :=
  p.fileStride

def inputs (q : Configuration) (p : Setup q) :=
  CommonOneLevelAllocation.inputMap q p.workspace (stride q p) (liveBlocks q p)
def sinks (q : Configuration) (p : Setup q) :=
  CommonOneLevelAllocation.sinkMap q p.workspace (stride q p) (liveBlocks q p)

theorem suffix_pos (q : Configuration) (p : Setup q) : 0<suffix q p :=
  Nat.mul_pos p.suffix_positive (by have:=q.word_width; omega)
theorem source_fits (q : Configuration) (p : Setup q) : p.source+parentBlocks q p≤q.N^q.exponent := by
  have h1:=p.parents_separate; have h2:=p.network_separate; have h3:=p.workspace_fits
  dsimp only [parentBlocks,parentBits,suffix]
  omega
theorem temporary_fits (q : Configuration) (p : Setup q) : p.temporary+parentBlocks q p≤q.N^q.exponent := by
  have h2:=p.network_separate; have h3:=p.workspace_fits
  dsimp only [parentBlocks,parentBits,suffix]
  omega

def beforeCode (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q) :=
  CommonOuterExecution.code q reader p.f (p.R*Parameters.W) p.G (suffix q p)
    OuterExchangeProgram.coordinates p.source p.temporary
def transposeCode (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q) :=
  CommonOneLevelRoles.forwardCode q reader p.f p.R p.G (suffix q p) p.source p.temporary
def splitCode (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q) :=
  CommonStaticSlabSplit.code q reader Parameters.W (words q p) p.temporary (inputs q p)
def joinCode (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q) :=
  CommonStaticSlabJoinMapped.code q reader (words q p) Parameters.W p.source (sinks q p)
def inverseCode (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q) :=
  CommonOneLevelRoles.inverseCode q reader p.f p.R p.G (suffix q p) p.source p.temporary
def afterCode (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q) :=
  CommonScanProgram.code q reader
    (OuterExchangeProgram.afterProgram p.f (p.R*Parameters.W) p.G (suffix q p) (suffix_pos q p))
    p.temporary p.source

def code (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q) (network : List (Instruction q)) :=
  beforeCode q reader p ++ transposeCode q reader p ++ splitCode q reader p ++
    network ++ joinCode q reader p ++ inverseCode q reader p ++ afterCode q reader p


/-- Contract discharged by the actual recursively implemented network. -/
def NetworkCorrect (q : Configuration) (p : Setup q) (network : List (Instruction q)) : Prop :=
  ∀ (s : Machine q) (input : CommonResidentNetwork.Inputs p.f p.R p.G (suffix q p)),
    CommonResidentNetwork.InputView q p.f p.R p.G (suffix q p) p.workspace (stride q p) s.disk input →
    ∀ r a, readBit q (executeRaw q network s).1.disk
      (CommonResidentNetwork.edgeBase p.workspace (stride q p)
        (sinkWire (globalProgram Parameters.d) (globalSwap r)))
      (commonLayout p.f p.R p.G (suffix q p) a).val=
      transport (matrixLocation (1 : Matrix Index Index (Scalar p.f))) (input r) a


end
end CodedSorting.CommonRecursiveOuter
end OuterProgram

section OuterBefore
/-! The initial transform of the complete one-level program, isolated from
later execution states to keep the proof kernel's reductions local. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace CodedSorting.CommonRecursiveOuter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange CoordinateLayoutBridge CommonOneLevelSemantics
open Address CodedSimulation
noncomputable section

theorem before_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (a : Parent p.f p.R p.G (suffix q p)) :
    readBit q (executeRaw q (beforeCode q reader p) s).1.disk p.source
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val =
    transport (mapPairEquiv lowerSubtractEquiv)
      (fun a => readBit q s.disk p.source
        (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val) a := by
  have h := CommonOuterExecution.raw_correct q reader p.f (p.R*Parameters.W) p.G (suffix q p)
    OuterExchangeProgram.coordinates p.source p.temporary s (source_fits q p) (temporary_fits q p)
    (Or.inl p.parents_separate)
    (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p)
      ((mapPairEquiv lowerSubtractEquiv).symm a))
  rw [CommonOuterStreams.before_encoded,CommonOuterExecution.finalBase_coordinates,
    Equiv.apply_symm_apply] at h
  exact h

end
end CodedSorting.CommonRecursiveOuter
end OuterBefore

section OuterSplit
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 60000
namespace CodedSorting.CommonRecursiveOuter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonOneLevelSemantics Circuit CircuitProgram ProgramNetwork Address CodedSimulation
open PhysicalStreamCursor
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section

theorem split_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (r : Reg) (a : Local p.f p.R p.G (suffix q p)) :
    readBit q (executeRaw q (splitCode q reader p) s).1.disk
      (CommonResidentNetwork.inputBase p.workspace (stride q p) r)
      (commonLayout p.f p.R p.G (suffix q p) a).val=
    readBit q s.disk p.temporary ((roleEnumeration r).val*localBits q p+
      (commonLayout p.f p.R p.G (suffix q p) a).val) := by
  have hlive : liveBlocks q p≤stride q p :=
    p.live_le_stride
  have hparent : parentBlocks q p=blockCount q.block (Parameters.W*words q p) :=
    CommonOneLevelAllocation.parent_count q p.f p.R p.G p.S
  have hbits : words q p*q.w=localBits q p := CommonWordAlignment.volume_word p.f p.R p.G p.S q.w
  have hinj := CommonOneLevelAllocation.inputMap_injective q p.workspace (stride q p)
    (liveBlocks q p) hlive p.workspace_fits
  have hsep : ∀ b<blockCount q.block (Parameters.W*words q p),
      ∀ k<Parameters.W*liveBlocks q p,CommonColumnSplit.address q p.temporary b≠inputs q p k := by
    intro b hb k hk
    apply CommonOneLevelAllocation.slabMap_separate q p.workspace (stride q p)
      (liveBlocks q p) CommonOneLevelAllocation.inputFiles hlive p.workspace_fits
      p.temporary (parentBlocks q p) p.network_separate b (by simpa only [hparent] using hb) k hk
  let i : Fin (words q p*q.w) := (finCongr hbits).symm
    (commonLayout p.f p.R p.G (suffix q p) a)
  have h := CommonSlabReadBits.split_column_bits q reader (inputs q p)
    (fun c => CommonResidentNetwork.inputBase p.workspace (stride q p) (roleEnumeration.symm c))
    s hinj hsep (CommonOneLevelAllocation.inputMap_at q p.workspace (stride q p) (liveBlocks q p))
    (roleEnumeration r) i
  unfold splitCode
  simpa (config := {proj := false, zeta := false}) only
    [Equiv.symm_apply_apply,finCongr_apply_coe,hbits] using h
end
end CodedSorting.CommonRecursiveOuter
end OuterSplit

section OuterStages
/-! Arbitrary-state stage endpoints use exactly the program names occurring
in the complete instruction list. Code equalities are transported before
forming execution projections, avoiding any evaluation of the fixed graph. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
namespace CodedSorting.CommonRecursiveOuter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonOneLevelSemantics Circuit CircuitProgram ProgramNetwork Address CodedSimulation
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section

theorem transpose_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (r : Reg) (a : Local p.f p.R p.G (suffix q p)) :
    readBit q (executeRaw q (transposeCode q reader p) s).1.disk p.temporary
      ((roleEnumeration r).val*localBits q p+(commonLayout p.f p.R p.G (suffix q p) a).val)=
    readBit q s.disk p.source (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p)
      ((splitPrefix (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f).symm (r,a))).val := by
  have hc : transposeCode q reader p=
      CommonOneLevelRoles.forwardCode q reader p.f p.R p.G (suffix q p) p.source p.temporary := rfl
  exact (congrArg (fun c => readBit q (executeRaw q c s).1.disk p.temporary
    ((roleEnumeration r).val*localBits q p+(commonLayout p.f p.R p.G (suffix q p) a).val)=
    readBit q s.disk p.source (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p)
      ((splitPrefix (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f).symm (r,a))).val) hc).mpr
    (CommonOneLevelRoles.forward_raw q reader p.f p.R p.G (suffix q p) p.source p.temporary s
      (source_fits q p) (temporary_fits q p) (Or.inl p.parents_separate) r a)

theorem inverse_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q)
    (output : Reg → Local p.f p.R p.G (suffix q p) → Bit)
    (hview : ∀ r a,readBit q s.disk p.source
      ((roleEnumeration r).val*localBits q p+(commonLayout p.f p.R p.G (suffix q p) a).val)=output r a)
    (a : Parent p.f p.R p.G (suffix q p)) :
    readBit q (executeRaw q (inverseCode q reader p) s).1.disk p.temporary
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=
    gatherOutput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f output a := by
  have hc : inverseCode q reader p=
      CommonOneLevelRoles.inverseCode q reader p.f p.R p.G (suffix q p) p.source p.temporary := rfl
  exact (congrArg (fun c => readBit q (executeRaw q c s).1.disk p.temporary
    (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=
    gatherOutput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f output a) hc).mpr
    (CommonOneLevelRoles.inverse_raw q reader p.f p.R p.G (suffix q p) p.source p.temporary s
      (source_fits q p) (temporary_fits q p) (Or.inl p.parents_separate) output hview a)

theorem after_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (a : Parent p.f p.R p.G (suffix q p)) :
    readBit q (executeRaw q (afterCode q reader p) s).1.disk p.temporary
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=
    readBit q s.disk p.temporary (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p)
      ((mapPairEquiv lowerReflectEquiv).symm a)).val := by
  have hc : afterCode q reader p=CommonScanProgram.code q reader
      (OuterExchangeProgram.afterProgram p.f (p.R*Parameters.W) p.G (suffix q p) (suffix_pos q p))
      p.temporary p.source := rfl
  have h := CommonOuterAfter.raw_correct q reader p.f (p.R*Parameters.W) p.G
    (suffix q p) (suffix_pos q p) p.temporary p.source s (temporary_fits q p) (source_fits q p)
    (Or.inr p.parents_separate) ((mapPairEquiv lowerReflectEquiv).symm a)
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg (fun c => readBit q (executeRaw q c s).1.disk p.temporary
    (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=
    readBit q s.disk p.temporary (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p)
      ((mapPairEquiv lowerReflectEquiv).symm a)).val) hc).mpr h

end
end CodedSorting.CommonRecursiveOuter
end OuterStages

section OuterAssembly
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 60000
namespace CodedSorting.CommonRecursiveOuter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonOneLevelSemantics Circuit CircuitProgram ProgramNetwork Address CodedSimulation
open PhysicalStreamCursor
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section


theorem transpose_view (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q)
    (F : Parent p.f p.R p.G (suffix q p)→Bit)
    (hview : ∀ a,readBit q s.disk p.source
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=F a) :
    ∀ r a,readBit q (executeRaw q (transposeCode q reader p) s).1.disk p.temporary
      ((roleEnumeration r).val*localBits q p+(commonLayout p.f p.R p.G (suffix q p) a).val)=
      splitInput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f F r a := by
  intro r a
  exact (transpose_raw q reader p s r a).trans (hview _)


theorem split_view (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q)
    (input : CommonResidentNetwork.Inputs p.f p.R p.G (suffix q p))
    (hview : ∀ r a,readBit q s.disk p.temporary
      ((roleEnumeration r).val*localBits q p+(commonLayout p.f p.R p.G (suffix q p) a).val)=input r a) :
    ∀ r a,readBit q (executeRaw q (splitCode q reader p) s).1.disk
      (CommonResidentNetwork.inputBase p.workspace (stride q p) r)
      (commonLayout p.f p.R p.G (suffix q p) a).val=input r a := by
  intro r a
  exact (split_raw q reader p s r a).trans (hview r a)


/-- The actual role transpose followed by copies into allocated source slots. -/
theorem scatter_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q)
    (F : Parent p.f p.R p.G (suffix q p)→Bit)
    (hview : ∀ a,readBit q s.disk p.source
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=F a) :
    ∀ r a,readBit q (executeRaw q (transposeCode q reader p ++ splitCode q reader p) s).1.disk
      (CommonResidentNetwork.inputBase p.workspace (stride q p) r)
      (commonLayout p.f p.R p.G (suffix q p) a).val=
      splitInput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f F r a := by
  exact CommonRawComposition.hoare_two q (transposeCode q reader p) (splitCode q reader p)
    (fun u => ∀ a,readBit q u.disk p.source
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=F a)
    (fun u => ∀ r a,readBit q u.disk p.temporary
      ((roleEnumeration r).val*localBits q p+(commonLayout p.f p.R p.G (suffix q p) a).val)=
      splitInput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f F r a)
    (fun u => ∀ r a,readBit q u.disk
      (CommonResidentNetwork.inputBase p.workspace (stride q p) r)
      (commonLayout p.f p.R p.G (suffix q p) a).val=
      splitInput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f F r a)
    (fun u hu => transpose_view q reader p u F hu)
    (fun u hu => split_view q reader p u
      (splitInput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f F) hu)
    s hview
end
end CodedSorting.CommonRecursiveOuter
end OuterAssembly

section OuterCollect
/-! The real sink-slab join followed by the inverse role transpose. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 60000
namespace CodedSorting.CommonRecursiveOuter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonOneLevelSemantics Circuit CircuitProgram ProgramNetwork Address CodedSimulation
open PhysicalStreamCursor
noncomputable section
attribute [local irreducible] CommonStaticSchedule.executeRaw

private theorem join_code_eq (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) : joinCode q reader p=
      CommonStaticSlabJoinMapped.code q reader (words q p) Parameters.W p.source (sinks q p) := rfl

private theorem join_actual (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q)
    (output : Reg→Local p.f p.R p.G (suffix q p)→Bit)
    (hview : ∀ r a,readBit q s.disk
      (CommonResidentNetwork.edgeBase p.workspace (stride q p)
        (sinkWire (globalProgram Parameters.d) (globalSwap r)))
      (commonLayout p.f p.R p.G (suffix q p) a).val=output r a) :
    ∀ r a,readBit q (executeRaw q (CommonStaticSlabJoinMapped.code q reader (words q p) Parameters.W p.source (sinks q p)) s).1.disk p.source
      ((roleEnumeration r).val*localBits q p+
        (commonLayout p.f p.R p.G (suffix q p) a).val)=output r a := by
  let l := commonLayout p.f p.R p.G (suffix q p)
  have hs := source_fits q p
  have hlive : liveBlocks q p≤stride q p :=
    p.live_le_stride
  have hparent : parentBlocks q p=blockCount q.block (Parameters.W*words q p) :=
    CommonOneLevelAllocation.parent_count q p.f p.R p.G p.S
  have hbits : words q p*q.w=localBits q p := CommonWordAlignment.volume_word p.f p.R p.G p.S q.w
  have hjoinsep : ∀ k<Parameters.W*liveBlocks q p,
      (sinks q p k).val<p.source ∨
      p.source+blockCount q.block (Parameters.W*words q p)≤(sinks q p k).val := by
    intro k hk
    right
    rw [←hparent]
    exact CommonOneLevelAllocation.sinkMap_after q p.workspace (stride q p) (liveBlocks q p)
      hlive p.workspace_fits p.source (parentBlocks q p)
      (p.parents_separate.trans
        ((Nat.le_add_right p.temporary (parentBlocks q p)).trans p.network_separate)) k hk
  intro r a
  let i : Fin (words q p*q.w) := (finCongr hbits).symm (l a)
  have h := CommonSlabReadBits.join_column_bits q reader (sinks q p)
    (fun c => CommonResidentNetwork.edgeBase p.workspace (stride q p)
      (sinkWire (globalProgram Parameters.d) (globalSwap (roleEnumeration.symm c))))
    s (by simpa only [←hparent] using hs) hjoinsep
    (CommonOneLevelAllocation.sinkMap_at q p.workspace (stride q p) (liveBlocks q p))
    (roleEnumeration r) i
  have h' : readBit q (executeRaw q (CommonStaticSlabJoinMapped.code q reader (words q p) Parameters.W p.source (sinks q p)) s).1.disk p.source ((roleEnumeration r).val*localBits q p+(l a).val)=
      readBit q s.disk (CommonResidentNetwork.edgeBase p.workspace (stride q p)
        (sinkWire (globalProgram Parameters.d) (globalSwap r))) (l a).val := by
    dsimp (config := {proj := false, zeta := false}) only [l]
    simpa (config := {proj := false, zeta := false}) only
      [Equiv.symm_apply_apply,finCongr_apply_coe,hbits] using h
  exact h'.trans (hview r a)

theorem join_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q)
    (output : Reg→Local p.f p.R p.G (suffix q p)→Bit)
    (hview : ∀ r a,readBit q s.disk
      (CommonResidentNetwork.edgeBase p.workspace (stride q p)
        (sinkWire (globalProgram Parameters.d) (globalSwap r)))
      (commonLayout p.f p.R p.G (suffix q p) a).val=output r a) :
    ∀ r a,readBit q (executeRaw q (joinCode q reader p) s).1.disk p.source
      ((roleEnumeration r).val*localBits q p+
        (commonLayout p.f p.R p.G (suffix q p) a).val)=output r a := by
  exact (congrArg (fun xs : List (Instruction q) => ∀ r a,
    readBit q (executeRaw q xs s).1.disk p.source
      ((roleEnumeration r).val*localBits q p+
        (commonLayout p.f p.R p.G (suffix q p) a).val)=output r a)
    (join_code_eq q reader p)).mpr (join_actual q reader p s output hview)

theorem collect_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q)
    (output : Reg→Local p.f p.R p.G (suffix q p)→Bit)
    (hview : ∀ r a,readBit q s.disk
      (CommonResidentNetwork.edgeBase p.workspace (stride q p)
        (sinkWire (globalProgram Parameters.d) (globalSwap r)))
      (commonLayout p.f p.R p.G (suffix q p) a).val=output r a) :
    ∀ a,readBit q (executeRaw q (joinCode q reader p ++ inverseCode q reader p) s).1.disk
      p.temporary (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=
      gatherOutput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f output a := by
  let s5 := (executeRaw q (joinCode q reader p) s).1
  have h5 := join_raw q reader p s output hview
  have h6 := inverse_raw q reader p s5 output h5
  have hr := raw_append q (joinCode q reader p) (inverseCode q reader p) s
  exact (congrArg (fun t : Machine q => ∀ a : Parent p.f p.R p.G (suffix q p),
    readBit q t.disk p.temporary
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=
      gatherOutput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f output a)
    hr).mpr h6

end
end CodedSorting.CommonRecursiveOuter
end OuterCollect

section OuterExecution
/-! The actual seven-stage recursive parent exchange. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace CodedSorting.CommonRecursiveOuter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonOneLevelSemantics Circuit CircuitProgram ProgramNetwork Address CodedSimulation
open PhysicalStreamCursor
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section

theorem code_grouped (q : Configuration) (reader : Fin q.inventory.readers) (p : Setup q) (network : List (Instruction q)) :
    code q reader p network = beforeCode q reader p ++
      (transposeCode q reader p ++ splitCode q reader p) ++ network ++
      (joinCode q reader p ++ inverseCode q reader p) ++ afterCode q reader p := by
  simp only [code,List.append_assoc]

/-- The complete chronological execution exchanges H and D while preserving
all prefix, gap and suffix coordinates. Every stage uses the same machine. -/
theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (network : List (Instruction q))
    (hnetwork : NetworkCorrect q p network) (s : Machine q) (a : Parent p.f p.R p.G (suffix q p)) :
    readBit q (executeRaw q (code q reader p network) s).1.disk p.temporary
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) a).val=
    readBit q s.disk p.source
      (commonLayout p.f (p.R*Parameters.W) p.G (suffix q p) (exchangeEquiv.symm a)).val := by
  let L := commonLayout p.f (p.R*Parameters.W) p.G (suffix q p)
  let l := commonLayout p.f p.R p.G (suffix q p)
  let F : Parent p.f p.R p.G (suffix q p)→Bit := fun a => readBit q s.disk p.source (L a).val
  let pre := transport (mapPairEquiv lowerSubtractEquiv) F
  let input := splitInput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f pre
  let output : Reg→Local p.f p.R p.G (suffix q p)→Bit := fun r =>
    transport (matrixLocation (1 : Matrix Index Index (Scalar p.f))) (input r)
  let gathered := gatherOutput (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f output
  let P0 : Machine q→Prop := fun t => ∀ a,readBit q t.disk p.source (L a).val=F a
  let P1 : Machine q→Prop := fun t => ∀ a,readBit q t.disk p.source (L a).val=pre a
  let P2 : Machine q→Prop := fun t => CommonResidentNetwork.InputView q p.f p.R p.G
    (suffix q p) p.workspace (stride q p) t.disk input
  let P3 : Machine q→Prop := fun t => ∀ r a,readBit q t.disk
    (CommonResidentNetwork.edgeBase p.workspace (stride q p)
      (sinkWire (globalProgram Parameters.d) (globalSwap r))) (l a).val=output r a
  let P4 : Machine q→Prop := fun t => ∀ a,readBit q t.disk p.temporary (L a).val=gathered a
  let P5 : Machine q→Prop := fun t => ∀ a,readBit q t.disk p.temporary (L a).val=
    transport exchangeEquiv F a
  have h1 : ∀ t,P0 t→P1 (executeRaw q (beforeCode q reader p) t).1 := by
    intro t ht a
    exact (before_raw q reader p t a).trans (ht _)
  have h2 : ∀ t,P1 t→P2
      (executeRaw q (transposeCode q reader p ++ splitCode q reader p) t).1 := by
    intro t ht
    exact scatter_raw q reader p t pre ht
  have h3 : ∀ t,P2 t→P3 (executeRaw q (network) t).1 := by
    intro t ht
    exact hnetwork t input ht
  have h4 : ∀ t,P3 t→P4
      (executeRaw q (joinCode q reader p ++ inverseCode q reader p) t).1 := by
    intro t ht
    exact collect_raw q reader p t output ht
  have halgebra : transport (mapPairEquiv lowerReflectEquiv) gathered=transport exchangeEquiv F := by
    have hm : gathered=transport (matrixLocation (1 : Matrix Index Index (Scalar p.f))) pre :=
      gather_transported_split (Rows:=p.R) (Gap:=Fin p.G) (Suffix:=Fin (suffix q p)) p.f 1 pre
    rw [hm]
    dsimp only [pre]
    rw [matrixLocation_one,transport_comp,transport_comp,full_three_step_exchange]
  have h5 : ∀ t,P4 t→P5 (executeRaw q (afterCode q reader p) t).1 := by
    intro t ht a
    exact (after_raw q reader p t a).trans ((ht _).trans (congrFun halgebra a))
  have hrun := CommonRawComposition.hoare_five q
    (beforeCode q reader p) (transposeCode q reader p ++ splitCode q reader p)
    (network) (joinCode q reader p ++ inverseCode q reader p)
    (afterCode q reader p) P0 P1 P2 P3 P4 P5 h1 h2 h3 h4 h5 s
    (fun _ => rfl)
  have hfinal := CommonRawComposition.congr q (code q reader p network)
    (beforeCode q reader p ++ (transposeCode q reader p ++ splitCode q reader p) ++
      network ++ (joinCode q reader p ++ inverseCode q reader p) ++ afterCode q reader p)
    (code_grouped q reader p network) s P5 hrun
  exact hfinal a

end
end CodedSorting.CommonRecursiveOuter
end OuterExecution

section OuterFrame
/-! The recursive parent writes only its two parent buffers and the network's
own workspace. This frame rule is needed when the program is nested inside
an enclosing network edge. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
namespace CodedSorting.CommonRecursiveOuter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonOneLevelSemantics Circuit CircuitProgram ProgramNetwork Address CodedSimulation
open PhysicalStreamCursor
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section

private theorem frame_append (q : Configuration) (xs ys : List (Instruction q))
    (a : Fin (q.N^q.exponent))
    (hx : ∀ s : Machine q,(executeRaw q xs s).1.disk a=s.disk a)
    (hy : ∀ s : Machine q,(executeRaw q ys s).1.disk a=s.disk a) :
    ∀ s : Machine q,(executeRaw q (xs++ys) s).1.disk a=s.disk a := by
  intro s
  rw [raw_append,hy,hx]


theorem before_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (a : Fin (q.N^q.exponent))
    (hs : a.val<p.source ∨ p.source+parentBlocks q p≤a.val)
    (ht : a.val<p.temporary ∨ p.temporary+parentBlocks q p≤a.val) :
    (executeRaw q (beforeCode q reader p) s).1.disk a=s.disk a :=
  CommonOuterExecution.raw_outside q reader p.f (p.R*Parameters.W) p.G (suffix q p)
    OuterExchangeProgram.coordinates p.source p.temporary s (source_fits q p)
    (temporary_fits q p) (Or.inl p.parents_separate) a hs ht


theorem transpose_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (a : Fin (q.N^q.exponent))
    (ht : a.val<p.temporary ∨ p.temporary+parentBlocks q p≤a.val) :
    (executeRaw q (transposeCode q reader p) s).1.disk a=s.disk a := by
  have hc : transposeCode q reader p=CommonPermutationScan.program q reader
    (CommonOneLevelRoles.transpose p.f p.R p.G (suffix q p))
    (CommonOneLevelRoles.sourceColour p.f p.R p.G (suffix q p)) p.source p.temporary := rfl
  have h := (CommonPermutationScan.raw_correct q reader
    (CommonOneLevelRoles.transpose p.f p.R p.G (suffix q p))
    (CommonOneLevelRoles.sourceColour p.f p.R p.G (suffix q p)) p.source p.temporary
    (source_fits q p) (temporary_fits q p) (Or.inl p.parents_separate) s).2 a ht
  exact (congrArg (fun cs => (executeRaw q cs s).1.disk a=s.disk a) hc).mpr h


theorem split_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<p.workspace ∨ p.workspace+CommonResidentNetwork.fileCount*stride q p≤a.val) :
    (executeRaw q (splitCode q reader p) s).1.disk a=s.disk a := by
  apply CommonStaticSlabSplit.raw_outside q reader Parameters.W (words q p)
    p.temporary (inputs q p) s a
  intro k hk heq
  have hb := CommonOneLevelAllocation.slabMap_live q p.workspace (stride q p)
    (liveBlocks q p) CommonOneLevelAllocation.inputFiles p.live_le_stride p.workspace_fits k hk
  have he := congrArg Fin.val heq
  change a.val=(CommonOneLevelAllocation.slabMap q p.workspace (stride q p)
    (liveBlocks q p) CommonOneLevelAllocation.inputFiles k).val at he
  omega


theorem join_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<p.source ∨ p.source+parentBlocks q p≤a.val) :
    (executeRaw q (joinCode q reader p) s).1.disk a=s.disk a := by
  have hparent : parentBlocks q p=blockCount q.block (Parameters.W*words q p) :=
    CommonOneLevelAllocation.parent_count q p.f p.R p.G p.S
  have hjoinsep : ∀ k<Parameters.W*liveBlocks q p,
      (sinks q p k).val<p.source ∨
      p.source+blockCount q.block (Parameters.W*words q p)≤(sinks q p k).val := by
    intro k hk
    right
    rw [←hparent]
    exact CommonOneLevelAllocation.sinkMap_after q p.workspace (stride q p) (liveBlocks q p)
      p.live_le_stride p.workspace_fits p.source (parentBlocks q p)
      (p.parents_separate.trans
        ((Nat.le_add_right p.temporary (parentBlocks q p)).trans p.network_separate)) k hk
  exact CommonStaticSlabJoinMapped.raw_outside q reader (words q p) Parameters.W p.source
    (sinks q p) s (by simpa only [←hparent] using source_fits q p) hjoinsep a
    (by simpa only [←hparent] using ha)


theorem inverse_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (a : Fin (q.N^q.exponent))
    (ht : a.val<p.temporary ∨ p.temporary+parentBlocks q p≤a.val) :
    (executeRaw q (inverseCode q reader p) s).1.disk a=s.disk a := by
  have hc : inverseCode q reader p=CommonPermutationScan.program q reader
    (CommonOneLevelRoles.transpose p.f p.R p.G (suffix q p)).symm
    (CommonOneLevelRoles.targetColour p.f p.R p.G (suffix q p)) p.source p.temporary := rfl
  have h := (CommonPermutationScan.raw_correct q reader
    (CommonOneLevelRoles.transpose p.f p.R p.G (suffix q p)).symm
    (CommonOneLevelRoles.targetColour p.f p.R p.G (suffix q p)) p.source p.temporary
    (source_fits q p) (temporary_fits q p) (Or.inl p.parents_separate) s).2 a ht
  exact (congrArg (fun cs => (executeRaw q cs s).1.disk a=s.disk a) hc).mpr h


theorem after_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (s : Machine q) (a : Fin (q.N^q.exponent))
    (hs : a.val<p.source ∨ p.source+parentBlocks q p≤a.val)
    (ht : a.val<p.temporary ∨ p.temporary+parentBlocks q p≤a.val) :
    (executeRaw q (afterCode q reader p) s).1.disk a=s.disk a :=
  CommonScanProgram.raw_outside q reader
    (OuterExchangeProgram.afterProgram p.f (p.R*Parameters.W) p.G (suffix q p) (suffix_pos q p))
    p.temporary p.source s (temporary_fits q p) (source_fits q p)
    (Or.inr p.parents_separate) a ht hs

/-- A concrete address is preserved whenever it lies outside the parent
buffers, outside the network files, and is preserved by the network body. -/

theorem raw_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (network : List (Instruction q)) (a : Fin (q.N^q.exponent))
    (hs : a.val<p.source ∨ p.source+parentBlocks q p≤a.val)
    (ht : a.val<p.temporary ∨ p.temporary+parentBlocks q p≤a.val)
    (hw : a.val<p.workspace ∨ p.workspace+CommonResidentNetwork.fileCount*stride q p≤a.val)
    (hn : ∀ s : Machine q,(executeRaw q network s).1.disk a=s.disk a) :
    ∀ s : Machine q,(executeRaw q (code q reader p network) s).1.disk a=s.disk a := by
  have h1 := before_outside q reader p
  have h12 := frame_append q (beforeCode q reader p) (transposeCode q reader p) a
    (fun s => h1 s a hs ht) (fun s => transpose_outside q reader p s a ht)
  have h123 := frame_append q (beforeCode q reader p++transposeCode q reader p)
    (splitCode q reader p) a h12 (fun s => split_outside q reader p s a hw)
  have h1234 := frame_append q (beforeCode q reader p++transposeCode q reader p++splitCode q reader p)
    network a h123 hn
  have h12345 := frame_append q (beforeCode q reader p++transposeCode q reader p++splitCode q reader p++network)
    (joinCode q reader p) a h1234 (fun s => join_outside q reader p s a hs)
  have h123456 := frame_append q
    (beforeCode q reader p++transposeCode q reader p++splitCode q reader p++network++joinCode q reader p)
    (inverseCode q reader p) a h12345 (fun s => inverse_outside q reader p s a ht)
  exact frame_append q
    (beforeCode q reader p++transposeCode q reader p++splitCode q reader p++network++joinCode q reader p++inverseCode q reader p)
    (afterCode q reader p) a h123456 (fun s => after_outside q reader p s a hs ht)


/-- A recursive caller may reserve a single containing interval, including
all deeper scratch, and preserve every disk block outside that interval. -/
theorem raw_outside_interval (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Setup q) (network : List (Instruction q)) (limit : ℕ)
    (hlimit : p.workspace+CommonResidentNetwork.fileCount*stride q p≤limit)
    (hn : ∀ (s : Machine q) (a : Fin (q.N^q.exponent)),
      a.val<p.workspace ∨ limit≤a.val → (executeRaw q network s).1.disk a=s.disk a)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<p.source ∨ limit≤a.val) :
    (executeRaw q (code q reader p network) s).1.disk a=s.disk a := by
  have hp := p.parents_separate
  have hw := p.network_separate
  have hp' : p.source+parentBlocks q p≤p.temporary := hp
  have hw' : p.temporary+parentBlocks q p≤p.workspace := hw
  apply raw_outside q reader p network a
  · omega
  · omega
  · omega
  · intro t
    exact hn t a (by omega)

end
end CodedSorting.CommonRecursiveOuter
end OuterFrame
