import CodedSorting.Interchange.Framework.Resident.NetworkRun
import CodedSorting.Shared.Memory.RawComposition

/-! A real network program whose edge transforms are themselves proved
instruction lists. Stream lengths need not fit RAM. A disjoint work interval
is reused for recursive edge computations; each XOR is still an actual scan. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace CodedSorting.CommonRecursiveNetwork
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Disk Machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open PhysicalRecursiveExchange CodedSimulation Address Circuit CircuitProgram ProgramNetwork
open CommonNetworkInputs (ports)
open CommonResidentNetwork
noncomputable section

structure Layout (q : Configuration) (f P G S : ℕ) where
  workspace : ℕ
  stride : ℕ
  childBase : ℕ
  childLimit : ℕ
  count_le_stride : CommonPermutationPairs.count q (longVolume f P G S)≤stride
  network_le_child : workspace+fileCount*stride≤childBase
  child_le_limit : childBase≤childLimit
  fit : childLimit≤q.N^q.exponent

namespace Layout
variable {q : Configuration} {f P G S : ℕ}
theorem network_fits (p : Layout q f P G S) :
    p.workspace+fileCount*p.stride≤q.N^q.exponent :=
  p.network_le_child.trans (p.child_le_limit.trans p.fit)
end Layout

/-- The fields certify the supplied finite instruction lists for arbitrary
initial machine contents. No successful execution is assumed by the network. -/
structure EdgeProgram (q : Configuration) (f P G S : ℕ) (p : Layout q f P G S) where
  instructions : Edge → List (Instruction q)
  correct : ∀ (e : Edge) (s : Machine q) (input : EdgeStream f P G S),
    (∀ a,CommonPermutationPairs.readBit q s.disk (scratchBase p.workspace p.stride)
      (commonLayout f P G S a).val=input a) →
    ∀ a,CommonPermutationPairs.readBit q (executeRaw q (instructions e) s).1.disk
      (edgeBase p.workspace p.stride e) (commonLayout f P G S a).val=
      transport (matrixLocation (reducedEdgeMatrix f e)) input a
  frame : ∀ (e : Edge) (s : Machine q) (a : Fin (q.N^q.exponent)),
    (a.val<scratchBase p.workspace p.stride ∨ scratchBase p.workspace p.stride+p.stride≤a.val) →
    (a.val<edgeBase p.workspace p.stride e ∨ edgeBase p.workspace p.stride e+p.stride≤a.val) →
    (a.val<p.childBase ∨ p.childLimit≤a.val) →
    (executeRaw q (instructions e) s).1.disk a=s.disk a
  safe : ∀ e i,i∈instructions e → RespectsPC q i

def edgeCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (e : Edge) : List (Instruction q) :=
  CommonXorAccumulator.code q reader (longVolume f P G S) (scratchBase p.workspace p.stride)
    (portBases p.workspace p.stride e) ++ ep.instructions e

def prefixCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) :
    (n : ℕ) → n≤edgeCount → List (Instruction q)
  | 0,_ => []
  | n+1,hn => prefixCode q reader f P G S p ep n (by omega) ++
      edgeCode q reader f P G S p ep (edgeEnumeration.symm ⟨n,by omega⟩)

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) :=
  prefixCode q reader f P G S p ep edgeCount le_rfl

theorem edgeCode_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p) (e : Edge) :
    ∀ i∈edgeCode q reader f P G S p ep e,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact CommonXorAccumulator.code_safe q reader _ _ _ i hi
  · exact ep.safe e i hi

theorem edge_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (p : Layout q f P G S) (ep : EdgeProgram q f P G S p)
    (e : Edge) (s : Machine q) (input : Inputs f P G S)
    (hinput : InputView q f P G S p.workspace p.stride s.disk input)
    (hprevious : EdgeView q f P G S p.workspace p.stride (edgeEnumeration e).val s.disk input) :
    let result := executeRaw q (edgeCode q reader f P G S p ep e) s
    (∀ a,CommonPermutationPairs.readBit q result.1.disk (edgeBase p.workspace p.stride e)
      (commonLayout f P G S a).val=idealWire f input e a) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<scratchBase p.workspace p.stride ∨ scratchBase p.workspace p.stride+p.stride≤a.val) →
      (a.val<edgeBase p.workspace p.stride e ∨ edgeBase p.workspace p.stride e+p.stride≤a.val) →
      (a.val<p.childBase ∨ p.childLimit≤a.val) → result.1.disk a=s.disk a) := by
  let V := longVolume f P G S
  have hc : CommonPermutationPairs.count q V≤p.stride := p.count_le_stride
  have hfit := p.network_fits
  have hscratch := base_fits q p.workspace p.stride hfit (.inr (.inr ()))
  have ht : scratchBase p.workspace p.stride+CommonPermutationPairs.count q V≤q.N^q.exponent := by
    change base p.workspace p.stride (.inr (.inr ()))+_≤_; omega
  have hs : ∀ x∈portBases p.workspace p.stride e,x+CommonPermutationPairs.count q V≤q.N^q.exponent := by
    intro x hx
    obtain ⟨port,_,rfl⟩ := List.mem_map.mp hx
    have hf := base_fits q p.workspace p.stride hfit (portFile e port)
    omega
  have hsep : ∀ x∈portBases p.workspace p.stride e,
      CommonXorAccumulator.Separate q V (scratchBase p.workspace p.stride) x := by
    intro x hx
    obtain ⟨port,_,rfl⟩ := List.mem_map.mp hx
    have hz := base_separate p.workspace p.stride (portFile e port) (.inr (.inr ()))
      (portFile_ne_scratch e port)
    rcases hz with hz|hz
    · left; exact (Nat.add_le_add_left hc _).trans hz
    · right; exact (Nat.add_le_add_left hc _).trans hz
  let mid := (executeRaw q (CommonXorAccumulator.code q reader V (scratchBase p.workspace p.stride)
    (portBases p.workspace p.stride e)) s).1
  obtain ⟨hm,ho,_⟩ := CommonXorAccumulator.raw_complete q reader V (scratchBase p.workspace p.stride)
    (portBases p.workspace p.stride e) s ht hs hsep
  have hports : ∀ port : Port e,∀ a,
      CommonPermutationPairs.readBit q s.disk (base p.workspace p.stride (portFile e port))
        (commonLayout f P G S a).val=portValue f P G S input e port a := by
    intro port a
    cases port with
    | inl r => exact hinput r.val a
    | inr incoming =>
      exact hprevious incoming.val
        (edgeEnumeration_prior _ _ (incoming_index_lt e incoming.val incoming.property)) a
  have hsum : ∀ a,CommonPermutationPairs.readBit q mid.disk (scratchBase p.workspace p.stride)
      (commonLayout f P G S a).val=
      ((ports e).map (fun port => portValue f P G S input e port a)).sum := by
    intro a
    rw [hm (commonLayout f P G S a)]
    simp only [portBases,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro port hp
    exact hports port a
  have he := ep.correct e mid
    (fun a => ((ports e).map (fun port => portValue f P G S input e port a)).sum) hsum
  dsimp only
  rw [edgeCode,CommonPermutationPairs.raw_append]
  refine ⟨?_,?_⟩
  · intro a
    exact (he a).trans (congrFun (portSum_transport f P G S input e) a)
  · intro a ha hb hw
    rw [ep.frame e mid a ha hb hw]
    apply ho a
    rcases ha with ha|ha
    · left; exact ha
    · right; exact (Nat.add_le_add_left hc _).trans ha

end
end CodedSorting.CommonRecursiveNetwork
