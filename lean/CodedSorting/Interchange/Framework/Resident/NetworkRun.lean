import CodedSorting.Shared.Memory.EdgeReadBit
import CodedSorting.Circuit.NetworkModel.Framework.NetworkInputs
import CodedSorting.Shared.Memory.XorAccumulator

section NetworkLayout
/-! Public disk allocation for the fixed finite network. Original inputs,
each physical edge, and the single XOR accumulator have disjoint slabs.
Only addresses and the fixed graph enter this allocation. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace CodedSorting.CommonResidentNetwork
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Disk Machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge Circuit CircuitProgram
noncomputable section

def edgeCount : ℕ := ((globalProgram Parameters.d).length+1)*Parameters.W

def edgeEnumeration : Edge ≃ Fin edgeCount :=
  (Equiv.prodCongr (Equiv.refl _) roleEnumeration).trans finProdFinEquiv

@[simp] theorem edgeEnumeration_val (e : Edge) :
    (edgeEnumeration e).val=(roleEnumeration e.2).val+Parameters.W*e.1.val := rfl

theorem edgeEnumeration_prior (a b : Edge) (h : a.1.val<b.1.val) :
    (edgeEnumeration a).val<(edgeEnumeration b).val := by
  have ha := (roleEnumeration a.2).isLt
  simp only [edgeEnumeration_val]
  nlinarith

abbrev File := Reg ⊕ (Edge ⊕ Unit)

def indexedSlot {m n : ℕ} : Fin m ⊕ (Fin n ⊕ Unit) → ℕ
  | .inl r => r.val
  | .inr (.inl e) => m+e.val
  | .inr (.inr _) => m+n

def indexedCount (m n : ℕ) : ℕ := m+n+1

theorem indexedSlot_lt {m n : ℕ} (a : Fin m ⊕ (Fin n ⊕ Unit)) : indexedSlot a < indexedCount m n := by
  unfold indexedCount
  cases a with
  | inl r => have := r.isLt; simp only [indexedSlot]; omega
  | inr a => cases a with
    | inl e => have := e.isLt; simp only [indexedSlot]; omega
    | inr u => simp only [indexedSlot]; omega

theorem indexedSlot_injective {m n : ℕ} : Function.Injective (@indexedSlot m n) := by
  intro a b h
  cases a with
  | inl r => cases b with
    | inl s => exact congrArg Sum.inl (Fin.ext h)
    | inr b => cases b with
      | inl e => have := r.isLt; simp only [indexedSlot] at h; omega
      | inr u => have := r.isLt; simp only [indexedSlot] at h; omega
  | inr a => cases b with
    | inl r => cases a with
      | inl e => have := r.isLt; simp only [indexedSlot] at h; omega
      | inr u => have := r.isLt; simp only [indexedSlot] at h; omega
    | inr b => cases a with
      | inl e => cases b with
        | inl d =>
          exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.ext (Nat.add_left_cancel h))
        | inr u => have := e.isLt; simp only [indexedSlot] at h; omega
      | inr u => cases b with
        | inl e => have := e.isLt; simp only [indexedSlot] at h; omega
        | inr v => congr

def fileEnumeration : File ≃ (Fin Parameters.W ⊕ (Fin edgeCount ⊕ Unit)) :=
  Equiv.sumCongr roleEnumeration (Equiv.sumCongr edgeEnumeration (Equiv.refl _))

def slot (a : File) := indexedSlot (fileEnumeration a)
def fileCount := indexedCount Parameters.W edgeCount

theorem slot_lt (a : File) : slot a<fileCount := @indexedSlot_lt Parameters.W edgeCount (fileEnumeration a)

theorem slot_injective : Function.Injective slot :=
  (@indexedSlot_injective Parameters.W edgeCount).comp fileEnumeration.injective

def base (workspace stride : ℕ) (a : File) := workspace+slot a*stride

def inputBase (workspace stride : ℕ) (r : Reg) := base workspace stride (.inl r)
def edgeBase (workspace stride : ℕ) (e : Edge) := base workspace stride (.inr (.inl e))
def scratchBase (workspace stride : ℕ) := base workspace stride (.inr (.inr ()))

theorem base_fits (q : Configuration) (workspace stride : ℕ)
    (hfit : workspace+fileCount*stride≤q.N^q.exponent) (a : File) :
    base workspace stride a+stride≤q.N^q.exponent := by
  have hs := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt (slot_lt a))
  dsimp only [base]
  nlinarith

theorem base_separate (workspace stride : ℕ) (a b : File) (hne : a≠b) :
    base workspace stride a+stride≤base workspace stride b ∨
      base workspace stride b+stride≤base workspace stride a := by
  have hs : slot a≠slot b := fun h => hne (slot_injective h)
  rcases lt_or_gt_of_ne hs with h|h
  · left
    have := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt h)
    dsimp only [base]; nlinarith
  · right
    have := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt h)
    dsimp only [base]; nlinarith

/-- Equality outside one written slab preserves the complete bit view of
any other allocated file, including a partial final block. -/
theorem readBit_preserved (q : Configuration) (V workspace stride : ℕ)
    (hcount : CommonPermutationPairs.count q V≤stride)
    (hfit : workspace+fileCount*stride≤q.N^q.exponent)
    (before after : Disk q) (written other : File) (hne : other≠written)
    (hout : ∀ a : Fin (q.N^q.exponent),a.val<base workspace stride written ∨
      base workspace stride written+stride≤a.val → after a=before a)
    (i : Fin V) :
    CommonPermutationPairs.readBit q after (base workspace stride other) i.val=
      CommonPermutationPairs.readBit q before (base workspace stride other) i.val := by
  have hi : i.val/CommonPermutationPairs.width q<CommonPermutationPairs.count q V := by
    apply (PhysicalStreamCursor.cursor_live_iff _ V _ (CommonPermutationPairs.width_pos q)).2
    exact (Nat.div_mul_le_self _ _).trans_lt i.isLt
  have hf := base_fits q workspace stride hfit other
  have ha : base workspace stride other+i.val/CommonPermutationPairs.width q<q.N^q.exponent := by omega
  unfold CommonPermutationPairs.readBit
  rw [hout]
  rw [CommonColumnSplit.address_val q _ _ ha]
  rcases base_separate workspace stride other written hne with h|h
  · left; omega
  · right
    exact h.trans (Nat.le_add_right _ _)

end
end CodedSorting.CommonResidentNetwork
end NetworkLayout

section Network
/-! Complete lowest-level network execution on the common finite machine.
Every local XOR is computed by scans into one disk accumulator. Each edge
then performs its resident-size matrix permutation, writing a fresh slab.
The public stage-major edge order preserves every input and previous edge. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
namespace CodedSorting.CommonResidentNetwork
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Disk Machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open PhysicalRecursiveExchange CodedSimulation Address Circuit CircuitProgram ProgramNetwork
open CommonNetworkInputs (ports)
noncomputable section

abbrev Port (e : Edge) := InputPort (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e)

def portFile (e : Edge) : Port e → File
  | .inl r => .inl r.val
  | .inr a => .inr (.inl a.val)

def portBases (workspace stride : ℕ) (e : Edge) : List ℕ :=
  (ports e).map (fun p => base workspace stride (portFile e p))

def edgeCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) (e : Edge) : List (Instruction q) :=
  let K := CommonEdgeExecution.blocks q f P G S hV
  CommonXorAccumulator.code q reader (longVolume f P G S) (scratchBase workspace K)
    (portBases workspace K e) ++
  CommonEdgeExecution.code q f P G S e hV (scratchBase workspace K) (edgeBase workspace K e)

/-- An explicit topological prefix; the argument n is public program text. -/
def prefixCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) : (n : ℕ) → n≤edgeCount → List (Instruction q)
  | 0,_ => []
  | n+1,hn => prefixCode q reader f P G S hV workspace n (by omega) ++
      edgeCode q reader f P G S hV workspace (edgeEnumeration.symm ⟨n,by omega⟩)

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) := prefixCode q reader f P G S hV workspace edgeCount le_rfl

def prefixWeight : (n : ℕ) → n≤edgeCount → ℕ
  | 0,_ => 0
  | n+1,hn => prefixWeight n (by omega)+(ports (edgeEnumeration.symm ⟨n,by omega⟩)).length+1

def weight := prefixWeight edgeCount le_rfl

abbrev Inputs (f P G S : ℕ) := Reg → EdgeStream f P G S

def InputView (q : Configuration) (f P G S workspace stride : ℕ)
    (disk : Disk q) (input : Inputs f P G S) : Prop :=
  ∀ r a,CommonPermutationPairs.readBit q disk (inputBase workspace stride r)
    (commonLayout f P G S a).val=input r a

def EdgeView (q : Configuration) (f P G S workspace stride n : ℕ)
    (disk : Disk q) (input : Inputs f P G S) : Prop :=
  ∀ e,(edgeEnumeration e).val<n → ∀ a,
    CommonPermutationPairs.readBit q disk (edgeBase workspace stride e)
      (commonLayout f P G S a).val=idealWire f input e a

def portValue (f P G S : ℕ) (input : Inputs f P G S) (e : Edge) : Port e → EdgeStream f P G S
  | .inl r => input r.val
  | .inr a => idealWire f input a.val

/-- The per-edge finite XOR list is exactly the previously proved physical
network map, not a replacement gate oracle. -/
theorem portSum_transport (f P G S : ℕ) (input : Inputs f P G S) (e : Edge) :
    transport (matrixLocation (reducedEdgeMatrix f e))
      (fun a => ((ports e).map (fun p => portValue f P G S input e p a)).sum)=
      idealWire f input e := by
  rw [←physicalWire_correct f input (idealWire f input) e (fun _ _ => rfl)]
  funext a
  unfold transport physicalWire
  change _ = localMap (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e) _ ⟨e,rfl⟩
  rw [CommonNetworkInputs.localMap_ports]
  dsimp only
  congr 1
  apply List.map_congr_left
  intro p hp
  cases p <;> rfl


theorem edgeCode_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) (e : Edge) :
    (edgeCode q reader f P G S hV workspace e).length=
      3*((ports e).length+1)*CommonPermutationPairs.count q (longVolume f P G S)+
      3*CommonEdgeExecution.blocks q f P G S hV+1 := by
  simp only [edgeCode,List.length_append,CommonXorAccumulator.code_length,
    CommonEdgeExecution.code_length,portBases,List.length_map]
  omega

theorem edgeCode_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) (e : Edge)
    (hfit : workspace+fileCount*CommonEdgeExecution.blocks q f P G S hV≤q.N^q.exponent) :
    cost q (edgeCode q reader f P G S hV workspace e)=
      3*((ports e).length+1)*CommonPermutationPairs.count q (longVolume f P G S)+
      2*CommonEdgeExecution.blocks q f P G S hV := by
  rw [edgeCode,CommonPermutationPairs.cost_append,CommonXorAccumulator.code_cost,
    CommonEdgeExecution.code_cost q f P G S e hV
      (scratchBase workspace (CommonEdgeExecution.blocks q f P G S hV))
      (edgeBase workspace (CommonEdgeExecution.blocks q f P G S hV) e)
      (base_fits q _ _ hfit (.inr (.inr ()))) (base_fits q _ _ hfit (.inr (.inl e)))]
  simp only [portBases,List.length_map]

theorem edgeCode_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) (e : Edge) :
    ∀ i∈edgeCode q reader f P G S hV workspace e,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact CommonXorAccumulator.code_safe q reader _ _ _ i hi
  · exact CommonEdgeExecution.code_safe q f P G S e hV _ _ i hi

theorem portFile_ne_scratch (e : Edge) (p : Port e) : portFile e p≠.inr (.inr ()) := by
  cases p <;> simp only [portFile,ne_eq,Sum.inr.injEq,reduceCtorEq,not_false_eq_true]

/-- A full physical edge, with every XOR and address move accounted for. -/
theorem edge_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) (e : Edge) (s : Machine q) (input : Inputs f P G S)
    (hfit : workspace+fileCount*CommonEdgeExecution.blocks q f P G S hV≤q.N^q.exponent)
    (hinput : InputView q f P G S workspace (CommonEdgeExecution.blocks q f P G S hV) s.disk input)
    (hprevious : EdgeView q f P G S workspace (CommonEdgeExecution.blocks q f P G S hV)
      (edgeEnumeration e).val s.disk input) :
    let K := CommonEdgeExecution.blocks q f P G S hV
    let result := executeRaw q (edgeCode q reader f P G S hV workspace e) s
    (∀ a,CommonPermutationPairs.readBit q result.1.disk (edgeBase workspace K e)
      (commonLayout f P G S a).val=idealWire f input e a) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<scratchBase workspace K ∨ scratchBase workspace K+K≤a.val) →
      (a.val<edgeBase workspace K e ∨ edgeBase workspace K e+K≤a.val) →
      result.1.disk a=s.disk a) := by
  let K := CommonEdgeExecution.blocks q f P G S hV
  let V := longVolume f P G S
  have hc : CommonPermutationPairs.count q V≤K := CommonEdgeExecution.count_le_blocks q f P G S hV
  have hscratch := base_fits q workspace K hfit (.inr (.inr ()))
  have ht : scratchBase workspace K+CommonPermutationPairs.count q V≤q.N^q.exponent := by
    change base workspace K (.inr (.inr ()))+_≤_; omega
  have hs : ∀ x∈portBases workspace K e,x+CommonPermutationPairs.count q V≤q.N^q.exponent := by
    intro x hx
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    have hf := base_fits q workspace K hfit (portFile e p)
    omega
  have hsep : ∀ x∈portBases workspace K e,CommonXorAccumulator.Separate q V (scratchBase workspace K) x := by
    intro x hx
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    have hz := base_separate workspace K (portFile e p) (.inr (.inr ())) (portFile_ne_scratch e p)
    rcases hz with hz|hz
    · left; exact (Nat.add_le_add_left hc _).trans hz
    · right; exact (Nat.add_le_add_left hc _).trans hz
  let mid := (executeRaw q (CommonXorAccumulator.code q reader V (scratchBase workspace K)
    (portBases workspace K e)) s).1
  obtain ⟨hm,ho,_⟩ := CommonXorAccumulator.raw_complete q reader V (scratchBase workspace K)
    (portBases workspace K e) s ht hs hsep
  have hports : ∀ p : Port e,∀ a,
      CommonPermutationPairs.readBit q s.disk (base workspace K (portFile e p))
        (commonLayout f P G S a).val=portValue f P G S input e p a := by
    intro p a
    cases p with
    | inl r => exact hinput r.val a
    | inr incoming =>
      exact hprevious incoming.val
        (edgeEnumeration_prior _ _ (incoming_index_lt e incoming.val incoming.property)) a
  have hsum : ∀ a,CommonPermutationPairs.readBit q mid.disk (scratchBase workspace K)
      (commonLayout f P G S a).val=
      ((ports e).map (fun p => portValue f P G S input e p a)).sum := by
    intro a
    rw [hm (commonLayout f P G S a)]
    simp only [portBases,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro p hp
    exact hports p a
  obtain ⟨he,heout,_⟩ := CommonEdgeExecution.raw_stream_outside q f P G S e hV
    (scratchBase workspace K) (edgeBase workspace K e) mid
    (fun a => ((ports e).map (fun p => portValue f P G S input e p a)).sum)
    hscratch (base_fits q workspace K hfit _) hsum
  dsimp only
  rw [edgeCode,CommonPermutationPairs.raw_append]
  refine ⟨?_,?_⟩
  · intro a
    exact (he a).trans (congrFun (portSum_transport f P G S input e) a)
  · intro a ha hb
    rw [heout a hb]
    apply ho a
    rcases ha with ha|ha
    · left; exact ha
    · right; exact (Nat.add_le_add_left hc _).trans ha


end
end CodedSorting.CommonResidentNetwork
end Network

section NetworkCost
/-! Exact instruction count and physical I/O charge for the complete
finite network program, including every accumulator initialization. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace CodedSorting.CommonResidentNetwork
open CommonSortingNormalization CommonStaticSchedule
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonNetworkInputs (ports)
noncomputable section
attribute [local irreducible] edgeCount CircuitProgram.globalProgram Parameters.W

def lengthBound (weight count edges blocks : ℕ) := 3*weight*count+edges*(3*blocks+1)
def costBound (weight count edges blocks : ℕ) := 3*weight*count+2*edges*blocks

theorem costBound_le (weight count edges blocks : ℕ) (h : count≤blocks) :
    costBound weight count edges blocks≤(3*weight+2*edges)*blocks := by
  unfold costBound
  nlinarith [Nat.mul_le_mul_left (3*weight) h]

theorem lengthBound_le (weight count edges blocks : ℕ) (h : count≤blocks) :
    lengthBound weight count edges blocks≤(3*weight+3*edges)*blocks+edges := by
  unfold lengthBound
  nlinarith [Nat.mul_le_mul_left (3*weight) h]

theorem prefixCode_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace n : ℕ) (hn : n≤edgeCount) :
    (prefixCode q reader f P G S hV workspace n hn).length=
      lengthBound (prefixWeight n hn) (CommonPermutationPairs.count q (longVolume f P G S))
      n (CommonEdgeExecution.blocks q f P G S hV) := by
  induction n with
  | zero =>
    change 0=3*0*CommonPermutationPairs.count q (longVolume f P G S)+0*(3*CommonEdgeExecution.blocks q f P G S hV+1)
    omega
  | succ n ih =>
    have hi := ih (Nat.le_of_succ_le hn)
    have he := edgeCode_length q reader f P G S hV workspace (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)
    change (prefixCode q reader f P G S hV workspace n (Nat.le_of_succ_le hn) ++
      edgeCode q reader f P G S hV workspace (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)).length=_
    rw [List.length_append,hi,he]
    change _=3*(prefixWeight n (Nat.le_of_succ_le hn)+
      (ports (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)).length+1)*CommonPermutationPairs.count q (longVolume f P G S)+
      (n+1)*(3*CommonEdgeExecution.blocks q f P G S hV+1)
    unfold lengthBound
    ring

theorem prefixCode_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace n : ℕ) (hn : n≤edgeCount)
    (hfit : workspace+fileCount*CommonEdgeExecution.blocks q f P G S hV≤q.N^q.exponent) :
    cost q (prefixCode q reader f P G S hV workspace n hn)=
      costBound (prefixWeight n hn) (CommonPermutationPairs.count q (longVolume f P G S))
      n (CommonEdgeExecution.blocks q f P G S hV) := by
  induction n with
  | zero =>
    change 0=3*0*CommonPermutationPairs.count q (longVolume f P G S)+2*0*CommonEdgeExecution.blocks q f P G S hV
    omega
  | succ n ih =>
    have hi := ih (Nat.le_of_succ_le hn)
    have he := edgeCode_cost q reader f P G S hV workspace (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩) hfit
    change cost q (prefixCode q reader f P G S hV workspace n (Nat.le_of_succ_le hn) ++
      edgeCode q reader f P G S hV workspace (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩))=_
    rw [CommonPermutationPairs.cost_append,hi,he]
    change _=3*(prefixWeight n (Nat.le_of_succ_le hn)+
      (ports (edgeEnumeration.symm ⟨n,Nat.lt_of_succ_le hn⟩)).length+1)*CommonPermutationPairs.count q (longVolume f P G S)+
      2*(n+1)*CommonEdgeExecution.blocks q f P G S hV
    unfold costBound
    ring

theorem prefixCode_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace n : ℕ) (hn : n≤edgeCount) :
    ∀ i∈prefixCode q reader f P G S hV workspace n hn,RespectsPC q i := by
  induction n with
  | zero => intro i hi; exact (List.not_mem_nil hi).elim
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact ih (Nat.le_of_succ_le hn) i hi
    · exact edgeCode_safe q reader f P G S hV workspace _ i hi

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) :
    (code q reader f P G S hV workspace).length=
      lengthBound weight (CommonPermutationPairs.count q (longVolume f P G S))
      edgeCount (CommonEdgeExecution.blocks q f P G S hV) := by
  dsimp only [code,weight]
  exact prefixCode_length q reader f P G S hV workspace edgeCount le_rfl

theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ)
    (hfit : workspace+fileCount*CommonEdgeExecution.blocks q f P G S hV≤q.N^q.exponent) :
    cost q (code q reader f P G S hV workspace)=
      costBound weight (CommonPermutationPairs.count q (longVolume f P G S))
      edgeCount (CommonEdgeExecution.blocks q f P G S hV) := by
  dsimp only [code,weight]
  exact prefixCode_cost q reader f P G S hV workspace edgeCount le_rfl hfit

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) :
    ∀ i∈code q reader f P G S hV workspace,RespectsPC q i :=
  prefixCode_safe q reader f P G S hV workspace edgeCount le_rfl

/-- The finite graph contributes only its fixed instruction/edge constants.
The scan variable is the actual rounded physical allocation K. -/
theorem code_cost_le (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ)
    (hfit : workspace+fileCount*CommonEdgeExecution.blocks q f P G S hV≤q.N^q.exponent) :
    cost q (code q reader f P G S hV workspace)≤
      (3*weight+2*edgeCount)*CommonEdgeExecution.blocks q f P G S hV := by
  rw [code_cost q reader f P G S hV workspace hfit]
  exact costBound_le _ _ _ _ (CommonEdgeExecution.count_le_blocks q f P G S hV)

theorem code_length_le (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) :
    (code q reader f P G S hV workspace).length≤
      (3*weight+3*edgeCount)*CommonEdgeExecution.blocks q f P G S hV+edgeCount := by
  rw [code_length]
  exact lengthBound_le _ _ _ _ (CommonEdgeExecution.count_le_blocks q f P G S hV)

end
end CodedSorting.CommonResidentNetwork
end NetworkCost

section NetworkRun
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
namespace CodedSorting.CommonResidentNetwork
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Disk Machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open PhysicalRecursiveExchange CodedSimulation Address Circuit CircuitProgram ProgramNetwork
open CommonNetworkInputs (ports)
noncomputable section

theorem bit_outside_file (q : Configuration) (V workspace stride : ℕ)
    (hcount : CommonPermutationPairs.count q V≤stride)
    (hfit : workspace+fileCount*stride≤q.N^q.exponent)
    (other written : File) (hne : other≠written) (i : Fin V) :
    (CommonColumnSplit.address q (base workspace stride other)
      (i.val/CommonPermutationPairs.width q)).val<base workspace stride written ∨
    base workspace stride written+stride≤(CommonColumnSplit.address q
      (base workspace stride other) (i.val/CommonPermutationPairs.width q)).val := by
  have hi := CommonPermutationPairs.bit_block_lt q i
  have hf := base_fits q workspace stride hfit other
  rw [CommonColumnSplit.address_val q _ _ (by omega)]
  rcases base_separate workspace stride other written hne with h|h
  · left; omega
  · right; exact h.trans (Nat.le_add_right _ _)

theorem outside_workspace (workspace stride : ℕ) (a : ℕ)
    (ha : a<workspace ∨ workspace+fileCount*stride≤a) (file : File) :
    a<base workspace stride file ∨ base workspace stride file+stride≤a := by
  rcases ha with ha|ha
  · left; exact ha.trans_le (Nat.le_add_right _ _)
  · right
    have hs := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt (slot_lt file))
    dsimp only [base]
    nlinarith

/-- The same execution retains original inputs and all completed edges.
The only destructive scratch is the explicitly allocated accumulator. -/
theorem prefix_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace n : ℕ) (hn : n≤edgeCount) (s : Machine q) (input : Inputs f P G S)
    (hfit : workspace+fileCount*CommonEdgeExecution.blocks q f P G S hV≤q.N^q.exponent)
    (hinput : InputView q f P G S workspace (CommonEdgeExecution.blocks q f P G S hV) s.disk input) :
    let K := CommonEdgeExecution.blocks q f P G S hV
    let result := executeRaw q (prefixCode q reader f P G S hV workspace n hn) s
    InputView q f P G S workspace K result.1.disk input ∧
    EdgeView q f P G S workspace K n result.1.disk input ∧
    (∀ a : Fin (q.N^q.exponent),a.val<workspace ∨ workspace+fileCount*K≤a.val →
      result.1.disk a=s.disk a) := by
  induction n with
  | zero => exact ⟨hinput,fun _ h => (Nat.not_lt_zero _ h).elim,fun _ _ => rfl⟩
  | succ n ih =>
    let K := CommonEdgeExecution.blocks q f P G S hV
    let e : Edge := edgeEnumeration.symm ⟨n,by omega⟩
    have he : (edgeEnumeration e).val=n := by simp only [e,Equiv.apply_symm_apply]
    let mid := (executeRaw q (prefixCode q reader f P G S hV workspace n (by omega)) s).1
    obtain ⟨hmi,hme,hmo⟩ := ih (by omega)
    have hprev : EdgeView q f P G S workspace K (edgeEnumeration e).val mid.disk input := by
      rw [he]; exact hme
    obtain ⟨hout,hframe⟩ := edge_raw q reader f P G S hV workspace e mid input hfit hmi hprev
    let final := (executeRaw q (edgeCode q reader f P G S hV workspace e) mid).1
    have hkeep : ∀ other : File,other≠.inr (.inr ()) → other≠.inr (.inl e) →
        ∀ i : Fin (longVolume f P G S),
        CommonPermutationPairs.readBit q final.disk (base workspace K other) i.val=
          CommonPermutationPairs.readBit q mid.disk (base workspace K other) i.val := by
      intro other hs he' i
      unfold CommonPermutationPairs.readBit
      rw [hframe]
      · exact bit_outside_file q _ workspace K (CommonEdgeExecution.count_le_blocks q f P G S hV)
          hfit other _ hs i
      · exact bit_outside_file q _ workspace K (CommonEdgeExecution.count_le_blocks q f P G S hV)
          hfit other _ he' i
    dsimp only
    have hrun : (executeRaw q (prefixCode q reader f P G S hV workspace (n+1) hn) s).1=final := by
      exact CommonPermutationPairs.raw_append q
        (prefixCode q reader f P G S hV workspace n (by omega))
        (edgeCode q reader f P G S hV workspace e) s
    rw [hrun]
    refine ⟨?_,?_,?_⟩
    · intro r a
      exact (hkeep (.inl r) (by simp) (by simp) (commonLayout f P G S a)).trans (hmi r a)
    · intro old hold a
      by_cases hold' : old=e
      · subst old; exact hout a
      · have henum : (edgeEnumeration old).val≠n := by
          intro h
          apply hold'
          apply edgeEnumeration.injective
          apply Fin.ext
          exact h.trans he.symm
        have hp : (edgeEnumeration old).val<n := by omega
        exact (hkeep (.inr (.inl old)) (by simp) (by simpa using hold')
          (commonLayout f P G S a)).trans (hme old hp a)
    · intro a ha
      exact (hframe a (outside_workspace workspace K a.val ha _) (outside_workspace workspace K a.val ha _)).trans
        (hmo a ha)

/-- Every edge of the fixed graph is realized by one chronological program
on a single finite disk and the common resident memory. -/
theorem raw_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) (s : Machine q) (input : Inputs f P G S)
    (hfit : workspace+fileCount*CommonEdgeExecution.blocks q f P G S hV≤q.N^q.exponent)
    (hinput : InputView q f P G S workspace (CommonEdgeExecution.blocks q f P G S hV) s.disk input) :
    let K := CommonEdgeExecution.blocks q f P G S hV
    let result := executeRaw q (code q reader f P G S hV workspace) s
    InputView q f P G S workspace K result.1.disk input ∧
    (∀ e a,CommonPermutationPairs.readBit q result.1.disk (edgeBase workspace K e)
      (commonLayout f P G S a).val=executePhysical f input e a) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<workspace ∨ workspace+fileCount*K≤a.val →
      result.1.disk a=s.disk a) := by
  obtain ⟨hi,he,ho⟩ := prefix_raw q reader f P G S hV workspace edgeCount le_rfl s input hfit hinput
  dsimp only [code]
  refine ⟨hi,?_,ho⟩
  intro e a
  rw [executePhysical_correct]
  exact he e (edgeEnumeration e).isLt a

/-- Reading the designated sinks gives the proved identity-matrix address
exchange, with all terminal edges included in the actual execution. -/
theorem raw_sink (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (workspace : ℕ) (s : Machine q) (input : Inputs f P G S)
    (hfit : workspace+fileCount*CommonEdgeExecution.blocks q f P G S hV≤q.N^q.exponent)
    (hinput : InputView q f P G S workspace (CommonEdgeExecution.blocks q f P G S hV) s.disk input)
    (r : Reg) (a : EdgeAddress f P G S) :
    CommonPermutationPairs.readBit q (executeRaw q (code q reader f P G S hV workspace) s).1.disk
      (edgeBase workspace (CommonEdgeExecution.blocks q f P G S hV)
        (sinkWire (globalProgram Parameters.d) (globalSwap r)))
      (commonLayout f P G S a).val=
      transport (matrixLocation (1 : Matrix Index Index (Scalar f))) (input r) a := by
  obtain ⟨_,he,_⟩ := raw_complete q reader f P G S hV workspace s input hfit hinput
  exact (he _ a).trans (congrFun (physicalOutput_correct f input r) a)

end
end CodedSorting.CommonResidentNetwork
end NetworkRun
