import CodedSorting.Interchange.OneLevel.Exchange

section CallAddress
/-! Disk-address and allocation boundaries for the next Construction exchange layer.
Every actual selected child already has a separated source and one temporary
copy. A further network layer needs the additional, explicit numerical
reservation stated below. No recursive program or execution premise is
assumed here. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.RecursiveCallAddress

open CommonSortingNormalization CommonPermutationPairs CommonAddressLayout
open ExchangeSpecialization OneLevelChildren OneLevelExchange

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs

variable {q : Configuration} {f rows G S source temporary : Nat}

/-- The selected scalar child occupies exactly its existing network file. -/
theorem child_volume_eq_local (a : Setup q f rows G S source temporary) (c : Child) :
    ExchangeInterface.volume radix (childCall a c) =
      OneLevelAssembly.localVolume q (radix^f) rows G S := by
  exact StreamSplitLayout.selectedCall_volume radix 512 f rows G (S*q.w)
    (childRow c) (childCol c) (edgeSource a.network c.1)
    a.network.buffer a.network.limit

/-- This boundary keeps the dependent edge index inside its network layout. -/
theorem edgeSource_after_workspace
    (layout : MachineNetworkActualEdges.NetworkLayout q f rows G (S*q.w)) (e : Edge) :
    layout.workspace ≤ edgeSource layout e := by
  exact Nat.le_add_right _ _

/-- Prove the source bound within the layout's own dependent interface. -/
theorem edgeSource_end_le
    (layout : MachineNetworkActualEdges.NetworkLayout q f rows G (S*q.w)) (e : Edge) :
    edgeSource layout e +
      count q (OneLevelAssembly.localVolume q (radix^f) rows G S) ≤ layout.buffer :=
  (Nat.add_le_add_left layout.count_le_stride _).trans
    (layout.base_end_le (MachineNetworkActualEdges.edgeFile e))

private theorem transportEndpoint {q : Configuration} {s b V V' : Nat}
    (hV : V = V') (h : s + count q V' ≤ b) : s + count q V ≤ b := by
  rw [hV]
  exact h

theorem child_source_end_le (a : Setup q f rows G S source temporary) (c : Child) :
    (childCall a c).source + count q (ExchangeInterface.volume radix (childCall a c)) ≤
      (childCall a c).buffer :=
  transportEndpoint (child_volume_eq_local a c) (edgeSource_end_le a.network c.1)

/-- Actual selected children remain inside their parent's disposable region. -/
theorem child_source_after_parent_buffer
    (a : Setup q f rows G S source temporary) (c : Child) :
    (parentCall a).buffer ≤ (childCall a c).source := by
  exact (Nat.le_add_right temporary _).trans
    (a.temporary_separate.trans (edgeSource_after_workspace a.network c.1))

/-- The existing single-layer room bound supplies every child with one
temporary copy. It does not assert room for another whole network layer. -/
def childAllocation (a : Setup q f rows G S source temporary)
    (hroom : a.network.buffer +
      count q (OneLevelAssembly.localVolume q (radix^f) rows G S) ≤ a.network.limit)
    (c : Child) : ExchangeInterface.Allocation q radix (childCall a c) where
  source_separate := child_source_end_le a c
  temporary_fits := by
    rw [child_volume_eq_local]
    exact hroom
  limit_fits := a.network.fit

/-- The exact extra-layer reservation: a parent temporary file, one file
for every physical input/edge, and a shared local buffer. The raw file-count
expression matches the dependent layout interface without expanding it. -/
private theorem zeroReserveIff {a t p x limit : Nat}
    (h : a = t + (p + x + 0)) : a ≤ limit ↔ t + (p + x) ≤ limit := by
  rw [h, Nat.add_zero]

theorem canonical_reserve_iff (q : Configuration)
    (Q rows G S temporary limit : Nat) :
    OneLevelAllocation.canonicalLimit q Q rows G S temporary 0 ≤ limit ↔
      temporary + (OneLevelAllocation.parentBlocks q Q rows G S +
        ((MachineNetworkAdapter.physicalInputs +
          MachineNetworkAdapter.nodes TensorFrameNetwork.program
            (inputs := MachineNetworkAdapter.physicalInputs))+1) *
          OneLevelAllocation.localBlocks q Q rows G S) ≤ limit :=
  zeroReserveIff (OneLevelAllocation.canonicalLimit_eq q Q rows G S temporary 0)

/-- Allocate the next layer with exactly the caller's upper workspace limit.
The only inputs beyond public dimensions are source separation, the exact
reservation, and the physical disk bound. Siblings may reuse this interval. -/
def atLimitSetup (q : Configuration) (Q rows G S source temporary limit : Nat)
    (hsource : source + OneLevelAllocation.parentBlocks q Q rows G S ≤ temporary)
    (hreserve : OneLevelAllocation.canonicalLimit q Q rows G S temporary 0 ≤ limit)
    (hfit : limit ≤ q.N^q.exponent) :
    OneLevelAssembly.Setup q Q rows G S source temporary where
  network :=
    { workspace := OneLevelAllocation.canonicalWorkspace q Q rows G S temporary
      stride := OneLevelAllocation.localBlocks q Q rows G S
      buffer := OneLevelAllocation.canonicalBuffer q Q rows G S temporary
      limit := limit
      count_le_stride := le_rfl
      files_le_buffer := le_rfl
      buffer_le_limit := by
        have hr : OneLevelAllocation.canonicalBuffer q Q rows G S temporary +
            OneLevelAllocation.localBlocks q Q rows G S ≤ limit := by
          simpa only [OneLevelAllocation.canonicalLimit, Nat.add_zero] using hreserve
        exact (Nat.le_add_right _ _).trans hr
      fit := hfit }
  source_separate := hsource
  temporary_separate := le_rfl

theorem atLimitSetup_limit (q : Configuration) (Q rows G S source temporary limit : Nat)
    (hsource : source + OneLevelAllocation.parentBlocks q Q rows G S ≤ temporary)
    (hreserve : OneLevelAllocation.canonicalLimit q Q rows G S temporary 0 ≤ limit)
    (hfit : limit ≤ q.N^q.exponent) :
    (atLimitSetup q Q rows G S source temporary limit hsource hreserve hfit).network.limit =
      limit := rfl

theorem atLimitSetup_room (q : Configuration) (Q rows G S source temporary limit : Nat)
    (hsource : source + OneLevelAllocation.parentBlocks q Q rows G S ≤ temporary)
    (hreserve : OneLevelAllocation.canonicalLimit q Q rows G S temporary 0 ≤ limit)
    (hfit : limit ≤ q.N^q.exponent) :
    (atLimitSetup q Q rows G S source temporary limit hsource hreserve hfit).network.buffer +
      count q (OneLevelAssembly.localVolume q Q rows G S) ≤
        (atLimitSetup q Q rows G S source temporary limit hsource hreserve hfit).network.limit := by
  change OneLevelAllocation.canonicalBuffer q Q rows G S temporary +
    OneLevelAllocation.localBlocks q Q rows G S ≤ limit
  simpa only [OneLevelAllocation.canonicalLimit, Nat.add_zero] using hreserve

#print axioms child_volume_eq_local
#print axioms child_source_end_le
#print axioms child_source_after_parent_buffer
#print axioms childAllocation
#print axioms canonical_reserve_iff
#print axioms atLimitSetup
#print axioms atLimitSetup_room

end
end CodedSorting.Construction.RecursiveCallAddress
end CallAddress

section CallShape
/-! Shape closure for the actual Construction children. A depth certificate retains
one factor of the width multiplier and the stream count per remaining
level. The regrouping below preserves the complete scalar call, including
its addresses; it neither allocates a next network nor moves any data. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.RecursiveCallShape

open CommonSortingNormalization CommonAddressLayout
open ExchangeSpecialization OneLevelChildren OneLevelExchange

noncomputable section

/-- Public arithmetic conditions for `k` further one-level splits. Disk
capacity is intentionally a separate allocation obligation. -/
structure ShapeDepth (q : Configuration) (k : Nat) (c : ExchangeInterface.Call) : Prop where
  width_divisible : ambientDimension^k ∣ c.fieldWidth
  prefix_divisible : streamCount^k ∣ c.prefixCount
  width_pos : 0 < c.fieldWidth
  gap_pos : 0 < c.gap
  suffix_words : ∃ S : Nat, 0 < S ∧ c.suffix = S*q.w

/-- A family with the required factors in its input dimensions. Prefix counts may be zero; the dimensions describe the array before disk allocation. 

-/
def depthCall (q : Configuration)
    (k widthUnit lanes G suffixUnit source buffer limit : Nat) : ExchangeInterface.Call :=
  ⟨ambientDimension^k*widthUnit, lanes*streamCount^k, G,
    suffixUnit*q.w, source, buffer, limit⟩

theorem depthCall_shape (q : Configuration)
    (k widthUnit lanes G suffixUnit source buffer limit : Nat)
    (hwidth : 0 < widthUnit) (hG : 0 < G) (hS : 0 < suffixUnit) :
    ShapeDepth q k (depthCall q k widthUnit lanes G suffixUnit source buffer limit) := by
  refine ⟨dvd_mul_right _ _, dvd_mul_left _ _, ?_, hG, ⟨suffixUnit, hS, rfl⟩⟩
  exact Nat.mul_pos (pow_pos (by rw [ambientDimension_eq]; omega) _) hwidth

theorem ShapeDepth.suffix_pos {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}
    (h : ShapeDepth q k c) : 0 < c.suffix := by
  obtain ⟨S, hS, hEq⟩ := h.suffix_words
  rw [hEq]
  exact Nat.mul_pos hS (by have := q.word_width; omega)

def shortWidth (c : ExchangeInterface.Call) : Nat := c.fieldWidth / ambientDimension
def rows (c : ExchangeInterface.Call) : Nat := c.prefixCount / streamCount
def suffixWords (q : Configuration) (c : ExchangeInterface.Call) : Nat := c.suffix / q.w

/-- The numerical parameters needed by the next parent constructor, with
exactly the original source and scratch interval. -/
def parentForm (q : Configuration) (c : ExchangeInterface.Call) : ExchangeInterface.Call :=
  ⟨ambientDimension*shortWidth c, rows c*streamCount, c.gap,
    suffixWords q c*q.w, c.source, c.buffer, c.limit⟩

theorem width_eq {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}
    (h : ShapeDepth q (k+1) c) : ambientDimension*shortWidth c = c.fieldWidth := by
  apply Nat.mul_div_cancel_left'
  apply dvd_trans _ h.width_divisible
  rw [pow_succ']
  exact dvd_mul_right _ _

theorem prefix_eq {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}
    (h : ShapeDepth q (k+1) c) : rows c*streamCount = c.prefixCount := by
  apply Nat.div_mul_cancel
  apply dvd_trans _ h.prefix_divisible
  rw [pow_succ']
  exact dvd_mul_right _ _

theorem suffix_eq {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}
    (h : ShapeDepth q k c) : suffixWords q c*q.w = c.suffix := by
  apply Nat.div_mul_cancel
  obtain ⟨S, _, hEq⟩ := h.suffix_words
  rw [hEq]
  exact dvd_mul_left _ _

theorem shortWidth_pos {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}
    (h : ShapeDepth q (k+1) c) : 0 < shortWidth c := by
  have hp : 0 < ambientDimension*shortWidth c := by rw [width_eq h]; exact h.width_pos
  exact Nat.pos_of_mul_pos_left hp

theorem suffixWords_pos {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}
    (h : ShapeDepth q k c) : 0 < suffixWords q c := by
  have hp : 0 < suffixWords q c*q.w := by rw [suffix_eq h]; exact h.suffix_pos
  exact Nat.pos_of_mul_pos_right hp

/-- Exact equality of all seven call fields, rather than only file volume. -/
theorem parentForm_eq {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}
    (h : ShapeDepth q (k+1) c) : parentForm q c = c := by
  unfold parentForm
  rw [width_eq h, prefix_eq h, suffix_eq h]

variable {q : Configuration} {f r G S source temporary k : Nat}

/-- Every actual child retains all shape factors required for the remaining
levels. The concrete rank-coordinate supports need no special case. -/
theorem actual_child_depth (a : Setup q f r G S source temporary)
    (h : ShapeDepth q (k+1) (parentCall a)) (c : Child) :
    ShapeDepth q k (childCall a c) := by
  have hm : 0 < ambientDimension := by rw [ambientDimension_eq]; omega
  have hW : 0 < streamCount := by rw [streamCount_eq]; omega
  have hfDiv : ambientDimension^k ∣ f := by
    have hd := h.width_divisible
    change ambientDimension^(k+1) ∣ ambientDimension*f at hd
    rw [pow_succ', Nat.mul_dvd_mul_iff_left hm] at hd
    exact hd
  have hrDiv : streamCount^k ∣ r := by
    have hd := h.prefix_divisible
    change streamCount^(k+1) ∣ r*streamCount at hd
    rw [pow_succ, Nat.mul_dvd_mul_iff_right hW] at hd
    exact hd
  have hf : 0 < f := by
    have hp := h.width_pos
    change 0 < ambientDimension*f at hp
    exact Nat.pos_of_mul_pos_left hp
  have hG : 0 < G := h.gap_pos
  have hS : 0 < S := by
    have hp := h.suffix_pos
    change 0 < S*q.w at hp
    exact Nat.pos_of_mul_pos_right hp
  have hQ : 0 < radix^f := pow_pos radix_prime.pos _
  have hBefore : ∀ i : Fin 512, 0 < BeforeCount (radix^f) i :=
    fun _ => pow_pos hQ _
  have hAfter : ∀ i : Fin 512, 0 < AfterCount (radix^f) i :=
    fun _ => pow_pos hQ _
  refine ⟨hfDiv, ?_, hf, ?_, ?_⟩
  · change streamCount^k ∣ r*BeforeCount (radix^f) (childRow c)
    exact dvd_mul_of_dvd_left hrDiv _
  · change 0 < AfterCount (radix^f) (childRow c) *
      (G*BeforeCount (radix^f) (childCol c))
    exact Nat.mul_pos (hAfter _) (Nat.mul_pos hG (hBefore _))
  · refine ⟨AfterCount (radix^f) (childCol c)*S, Nat.mul_pos (hAfter _) hS, ?_⟩
    change AfterCount (radix^f) (childCol c)*(S*q.w) =
      (AfterCount (radix^f) (childCol c)*S)*q.w
    exact (Nat.mul_assoc _ _ _).symm

/-- When another non-leaf level remains, an actual child is precisely a
parent-shaped call at the same physical addresses. No reordering is needed. -/
theorem next_parent_eq (a : Setup q f r G S source temporary)
    (h : ShapeDepth q (k+2) (parentCall a)) (c : Child) :
    parentForm q (childCall a c) = childCall a c :=
  parentForm_eq (actual_child_depth a h c)

/-- Width alone already prevents unrestricted repeated use of a one-level
constructor: a positive width below 512 cannot have a further split. -/
theorem no_depth_one_of_width_lt {q : Configuration} {c : ExchangeInterface.Call}
    (hpos : 0 < c.fieldWidth) (hlt : c.fieldWidth < ambientDimension) :
    ¬ ShapeDepth q 1 c := by
  intro h
  have hd : ambientDimension ∣ c.fieldWidth := by simpa only [pow_one] using h.width_divisible
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos hd)

#print axioms depthCall_shape
#print axioms parentForm_eq
#print axioms actual_child_depth
#print axioms next_parent_eq
#print axioms no_depth_one_of_width_lt

end
end CodedSorting.Construction.RecursiveCallShape
end CallShape

section CallBridge
/-! The actual Construction split and the next-level call adapter. Shape, source
separation and explicit numerical workspace capacity produce the next
concrete layout. The program adapter preserves instructions and charge.
No leaf or complete recursive family is constructed in this module. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveCallBridge

open CommonSortingNormalization CommonAddressLayout CommonPermutationPairs
open ExchangeSpecialization OneLevelChildren OneLevelExchange
open RecursiveCallShape RecursiveCallAddress

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

variable {q : Configuration} {f r G S source temporary k : Nat}

/-- The generic split is instantiated by the actual physical rank children,
using their certified bijection. It is not an arbitrary weak split. -/
def actualSplit (hf : 0 < f) (a : Setup q f r G S source temporary) :
    ExchangeInterface.Split radix (parentCall a) where
  shortWidth := f
  rows := r
  short_positive := hf
  parent_width := rfl
  parent_prefix := rfl
  child := fun i => childCall a (OneLevelChildren.enumeration.symm i)
  child_width := fun _ => child_width a _
  child_volume := fun _ => child_volume a _
  child_source := fun _ => child_source_after_parent_buffer a _
  child_limit := fun _ => Nat.le_refl _

theorem actualSplit_child (hf : 0 < f) (a : Setup q f r G S source temporary)
    (i : Fin rankBudget) :
    (actualSplit hf a).child i = childCall a (OneLevelChildren.enumeration.symm i) := rfl

/-- The extra-layer space requirement is a public number, not an execution
or correctness assumption. Its expanded formula is canonical_reserve_iff. -/
def requiredLimit (q : Configuration) (c : ExchangeInterface.Call) : Nat :=
  OneLevelAllocation.canonicalLimit q (radix^shortWidth c) (rows c) c.gap
    (suffixWords q c) c.buffer 0

theorem next_parent_volume {c : ExchangeInterface.Call}
    (h : ShapeDepth q (k+1) c) :
    OneLevelAssembly.parentVolume q (radix^shortWidth c) (rows c) c.gap
      (suffixWords q c) = ExchangeInterface.volume radix c := by
  calc
    OneLevelAssembly.parentVolume q (radix^shortWidth c) (rows c) c.gap
        (suffixWords q c) = ExchangeInterface.volume radix (parentForm q c) :=
      (StreamSplitLayout.packedVolume radix ambientDimension (shortWidth c)
        (rows c*streamCount) c.gap (suffixWords q c*q.w)).symm
    _ = ExchangeInterface.volume radix c :=
      congrArg (ExchangeInterface.volume radix) (parentForm_eq h)

theorem next_source_separate {c : ExchangeInterface.Call}
    (h : ShapeDepth q (k+1) c) (allocation : ExchangeInterface.Allocation q radix c) :
    c.source + OneLevelAllocation.parentBlocks q (radix^shortWidth c) (rows c) c.gap
      (suffixWords q c) ≤ c.buffer := by
  unfold OneLevelAllocation.parentBlocks
  rw [next_parent_volume h]
  exact allocation.source_separate

/-- A next-level setup with exactly the original scalar call's source and
scratch interval. Capacity is the only additional allocation premise. -/
def nextSetup {c : ExchangeInterface.Call} (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit) :
    Setup q (shortWidth c) (rows c) c.gap (suffixWords q c) c.source c.buffer :=
  atLimitSetup q (radix^shortWidth c) (rows c) c.gap (suffixWords q c)
    c.source c.buffer c.limit (next_source_separate h allocation) hreserve
    allocation.limit_fits

theorem nextSetup_parent_eq {c : ExchangeInterface.Call} (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit) :
    parentCall (nextSetup h allocation hreserve) = c :=
  parentForm_eq h

theorem nextSetup_room {c : ExchangeInterface.Call} (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit) :
    (nextSetup h allocation hreserve).network.buffer +
      count q (OneLevelAssembly.localVolume q (radix^shortWidth c) (rows c) c.gap
        (suffixWords q c)) ≤ (nextSetup h allocation hreserve).network.limit :=
  atLimitSetup_room q (radix^shortWidth c) (rows c) c.gap (suffixWords q c)
    c.source c.buffer c.limit (next_source_separate h allocation) hreserve
    allocation.limit_fits

/-- Exact call equality changes only the type of the already built code. -/
def castCall {c d : ExchangeInterface.Call} (h : c = d)
    (p : ExchangeInterface.Program q radix c) : ExchangeInterface.Program q radix d := h ▸ p

theorem castCall_instructions {c d : ExchangeInterface.Call} (h : c = d)
    (p : ExchangeInterface.Program q radix c) : (castCall h p).instructions = p.instructions := by
  cases h
  rfl

theorem castCall_charge {c d : ExchangeInterface.Call} (h : c = d)
    (p : ExchangeInterface.Program q radix c) : (castCall h p).charge = p.charge := by
  cases h
  rfl

/-- Given the actual smaller programs at the next node, this is an actual
program for the original call. No permutation adapter, scan or fee is added. -/
def nextProgram (reader : Fin q.inventory.readers) {c : ExchangeInterface.Call}
    (h : ShapeDepth q (k+1) c) (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit)
    (children : Children (nextSetup h allocation hreserve)) :
    ExchangeInterface.Program q radix c :=
  castCall (nextSetup_parent_eq h allocation hreserve)
    (program reader h.gap_pos (suffixWords_pos h) (nextSetup h allocation hreserve)
      (nextSetup_room h allocation hreserve) children)

theorem nextProgram_instructions (reader : Fin q.inventory.readers)
    {c : ExchangeInterface.Call} (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit)
    (children : Children (nextSetup h allocation hreserve)) :
    (nextProgram reader h allocation hreserve children).instructions =
      (program reader h.gap_pos (suffixWords_pos h) (nextSetup h allocation hreserve)
        (nextSetup_room h allocation hreserve) children).instructions :=
  castCall_instructions _ _

theorem nextProgram_charge (reader : Fin q.inventory.readers)
    {c : ExchangeInterface.Call} (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit)
    (children : Children (nextSetup h allocation hreserve)) :
    (nextProgram reader h allocation hreserve children).charge =
      (program reader h.gap_pos (suffixWords_pos h) (nextSetup h allocation hreserve)
        (nextSetup_room h allocation hreserve) children).charge :=
  castCall_charge _ _

/-- Instantiate the adapter at any actual rank child. The parent's depth
certificate and already verified layout supply all non-capacity premises. -/
def actualNextProgram (reader : Fin q.inventory.readers)
    (a : Setup q f r G S source temporary)
    (hdepth : ShapeDepth q (k+2) (parentCall a))
    (hroom : a.network.buffer +
      count q (OneLevelAssembly.localVolume q (radix^f) r G S) ≤ a.network.limit)
    (c : Child) (hreserve : requiredLimit q (childCall a c) ≤ (childCall a c).limit)
    (children : Children (nextSetup (actual_child_depth a hdepth c)
      (childAllocation a hroom c) hreserve)) :
    ExchangeInterface.Program q radix (childCall a c) :=
  nextProgram reader (actual_child_depth a hdepth c) (childAllocation a hroom c)
    hreserve children

#print axioms actualSplit
#print axioms nextSetup
#print axioms nextSetup_parent_eq
#print axioms nextSetup_room
#print axioms nextProgram
#print axioms nextProgram_instructions
#print axioms nextProgram_charge
#print axioms actualNextProgram

end
end CodedSorting.Construction.RecursiveCallBridge
end CallBridge
