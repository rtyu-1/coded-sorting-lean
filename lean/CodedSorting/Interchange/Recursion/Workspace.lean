import CodedSorting.Interchange.Recursion.Build

section Descent
/-! Descent for the actual children of the next concrete Construction node. Every
child loses one certified shape level and has strictly smaller field width.
These facts concern the actual calls, including their inherited addresses;
they do not assume execution, correctness, or an unconstructed child program.
The numerical workspace reserve remains explicit. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveDescent

open CommonSortingNormalization CommonAddressLayout
open ExchangeSpecialization OneLevelChildren OneLevelExchange
open RecursiveCallShape RecursiveCallBridge

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

variable {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}

/-- The actual children inherit exactly one fewer remaining shape level. -/
theorem next_child_depth (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit) (child : Child) :
    ShapeDepth q k (childCall (nextSetup h allocation hreserve) child) := by
  apply actual_child_depth
  rw [nextSetup_parent_eq]
  exact h

/-- The short width of every actual child is the same public integer. -/
theorem next_child_width_eq (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit) (child : Child) :
    (childCall (nextSetup h allocation hreserve) child).fieldWidth = shortWidth c :=
  child_width _ _

/-- Width decreases strictly at each actual recursive edge. Together with
the shape-level decrease, this excludes any recursive cycle. -/
theorem next_child_width_lt (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit) (child : Child) :
    (childCall (nextSetup h allocation hreserve) child).fieldWidth < c.fieldWidth := by
  have hs := child_smaller (shortWidth_pos h) (nextSetup h allocation hreserve) child
  rwa [nextSetup_parent_eq] at hs

/-- This is the actual child volume identity, with the original parent
call restored by its complete call equality. -/
theorem next_child_volume (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit) (child : Child) :
    streamCount * ExchangeInterface.volume radix
      (childCall (nextSetup h allocation hreserve) child) =
      ExchangeInterface.volume radix c := by
  have hv := child_volume (nextSetup h allocation hreserve) child
  rwa [nextSetup_parent_eq] at hv

theorem next_child_volume_div (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (hreserve : requiredLimit q c ≤ c.limit) (child : Child) :
    ExchangeInterface.volume radix (childCall (nextSetup h allocation hreserve) child) =
      ExchangeInterface.volume radix c / streamCount := by
  have hv := child_volume_div (nextSetup h allocation hreserve) child
  rwa [nextSetup_parent_eq] at hv

#print axioms next_child_depth
#print axioms next_child_width_eq
#print axioms next_child_width_lt
#print axioms next_child_volume
#print axioms next_child_volume_div

end
end CodedSorting.Construction.RecursiveDescent
end Descent

section WorkspaceBudget
/-! One shared recursive scratch tail, measured in physical disk blocks.
The terminal field width is fixed at `base`; a depth-k call has field width
512^k * base. At a node the retained parent and network slabs are followed
by ONE child's scratch reserve. This is not a sum over rank children. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveWorkspaceBudget

open CommonSortingNormalization CommonPermutationPairs
open ExchangeSpecialization

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs

local notation "files" => (MachineNetworkAdapter.physicalInputs +
  MachineNetworkAdapter.nodes TensorFrameNetwork.program
    (inputs := MachineNetworkAdapter.physicalInputs))

def buckets (base : Nat) : Nat := (radix^base)^2

def padding (cutoff base V : Nat) : Nat :=
  if V ≤ cutoff then 3 else buckets base

/-- Only leaf RAM/startup requirements remain as global numeric inputs. -/
structure LeafParameters (q : Configuration) (cutoff base : Nat) : Prop where
  resident : cutoff ≤ CommonExchangeLeaf.bankBits q
  bank : buckets base * q.block ≤ CommonExchangeLeaf.bankWords q
  startup : buckets base * width q ≤ cutoff + width q

/-- Exact sufficient reservation from the root buffer to the common limit. -/
def space (q : Configuration) (cutoff base : Nat) : Nat → Nat → Nat
  | 0, V => count q V + padding cutoff base V
  | k+1, V => if V ≤ cutoff then count q V + 3 else
      count q V + files * count q (V / streamCount) +
        space q cutoff base k (V / streamCount)

theorem space_zero (q : Configuration) (cutoff base V : Nat) :
    space q cutoff base 0 V = count q V + padding cutoff base V := rfl

theorem space_small (q : Configuration) (cutoff base k V : Nat) (hs : V ≤ cutoff) :
    space q cutoff base k V = count q V + 3 := by
  cases k <;> simp only [space, padding, if_pos hs]

theorem space_node (q : Configuration) (cutoff base k V : Nat) (hs : ¬ V ≤ cutoff) :
    space q cutoff base (k+1) V = count q V + files * count q (V / streamCount) +
      space q cutoff base k (V / streamCount) := by
  simp only [space, if_neg hs]

theorem space_ge_count (q : Configuration) (cutoff base k V : Nat) :
    count q V ≤ space q cutoff base k V := by
  cases k with
  | zero => exact Nat.le_add_right _ _
  | succ k =>
      simp only [space]
      split
      · exact Nat.le_add_right _ _
      · exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

theorem space_ge_node_reserve (q : Configuration) (cutoff base k V : Nat)
    (hs : ¬ V ≤ cutoff) :
    count q V + (files+1)*count q (V/streamCount) ≤
      space q cutoff base (k+1) V := by
  rw [space_node q cutoff base k V hs, Nat.add_mul, one_mul]
  have h := space_ge_count q cutoff base k (V/streamCount)
  omega

end
end CodedSorting.Construction.RecursiveWorkspaceBudget
end WorkspaceBudget

section WorkspaceAddress
/-! Exact addresses used by each recursive Construction layer. Every actual child
shares the same scratch start and upper limit; only its source file varies.
The formulas expose the public block counts needed for the global workspace
recurrence without reducing the concrete network's dependent index type. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.RecursiveWorkspaceAddress

open CommonSortingNormalization CommonAddressLayout CommonPermutationPairs
open ExchangeSpecialization OneLevelChildren OneLevelExchange
open RecursiveCallShape RecursiveCallAddress RecursiveCallBridge

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs

variable {q : Configuration} {k : Nat} {c : ExchangeInterface.Call}

/-- The next layer's file is exactly the parent volume divided by the
fixed number of parallel streams. -/
theorem next_local_volume (h : ShapeDepth q (k+1) c) :
    OneLevelAssembly.localVolume q (radix^shortWidth c) (rows c) c.gap
      (suffixWords q c) = ExchangeInterface.volume radix c / streamCount := by
  calc
    OneLevelAssembly.localVolume q (radix^shortWidth c) (rows c) c.gap
        (suffixWords q c) =
        (streamCount * OneLevelAssembly.localVolume q (radix^shortWidth c)
          (rows c) c.gap (suffixWords q c)) / streamCount :=
      (Nat.mul_div_cancel_left _ (by decide : 0 < streamCount)).symm
    _ = OneLevelAssembly.parentVolume q (radix^shortWidth c) (rows c) c.gap
        (suffixWords q c) / streamCount := by
      rw [OneLevelAllocation.parentVolume_eq_streams]
    _ = ExchangeInterface.volume radix c / streamCount := by
      rw [next_parent_volume h]

theorem next_parent_blocks (h : ShapeDepth q (k+1) c) :
    OneLevelAllocation.parentBlocks q (radix^shortWidth c) (rows c) c.gap
      (suffixWords q c) = count q (ExchangeInterface.volume radix c) :=
  congrArg (count q) (next_parent_volume h)

theorem next_local_blocks (h : ShapeDepth q (k+1) c) :
    OneLevelAllocation.localBlocks q (radix^shortWidth c) (rows c) c.gap
      (suffixWords q c) = count q (ExchangeInterface.volume radix c / streamCount) :=
  congrArg (count q) (next_local_volume h)

private theorem transportReserve {a t p p' F l l' : Nat}
    (ha : a = t + (p + (F+1)*l + 0)) (hp : p = p') (hl : l = l') :
    a = t + p' + (F+1)*l' := by
  rw [ha, hp, hl]
  simp only [Nat.add_zero, Nat.add_assoc]

/-- A single node reserves its parent copy, all network files, and one
local copy. Deeper recursive scratch is reserved separately. -/
theorem requiredLimit_eq (h : ShapeDepth q (k+1) c) :
    requiredLimit q c = c.buffer + count q (ExchangeInterface.volume radix c) +
      ((MachineNetworkAdapter.physicalInputs +
        MachineNetworkAdapter.nodes TensorFrameNetwork.program
          (inputs := MachineNetworkAdapter.physicalInputs))+1) *
        count q (ExchangeInterface.volume radix c / streamCount) :=
  transportReserve
    (OneLevelAllocation.canonicalLimit_eq q (radix^shortWidth c) (rows c) c.gap
      (suffixWords q c) c.buffer 0)
    (next_parent_blocks h) (next_local_blocks h)

/-- The next child starts scratch after the parent temporary copy and the
whole fixed network arena. This value is independent of the child index. -/
theorem next_child_buffer (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (reserve : requiredLimit q c ≤ c.limit) (child : Child) :
    (childCall (nextSetup h allocation reserve) child).buffer =
      c.buffer + count q (ExchangeInterface.volume radix c) +
        (MachineNetworkAdapter.physicalInputs +
          MachineNetworkAdapter.nodes TensorFrameNetwork.program
            (inputs := MachineNetworkAdapter.physicalInputs)) *
          count q (ExchangeInterface.volume radix c / streamCount) := by
  change OneLevelAllocation.canonicalBuffer q (radix^shortWidth c) (rows c)
    c.gap (suffixWords q c) c.buffer = _
  unfold OneLevelAllocation.canonicalBuffer OneLevelAllocation.canonicalWorkspace
  rw [next_parent_blocks h, next_local_blocks h]

theorem next_child_limit (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (reserve : requiredLimit q c ≤ c.limit) (child : Child) :
    (childCall (nextSetup h allocation reserve) child).limit = c.limit := rfl

theorem next_child_volume (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (reserve : requiredLimit q c ≤ c.limit) (child : Child) :
    ExchangeInterface.volume radix (childCall (nextSetup h allocation reserve) child) =
      ExchangeInterface.volume radix c / streamCount := by
  rw [child_volume_eq_local, next_local_volume h]

/-- Every child's complete source file ends before the shared scratch. -/
theorem next_child_source_separate (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (reserve : requiredLimit q c ≤ c.limit) (child : Child) :
    (childCall (nextSetup h allocation reserve) child).source +
      count q (ExchangeInterface.volume radix
        (childCall (nextSetup h allocation reserve) child)) ≤
      (childCall (nextSetup h allocation reserve) child).buffer :=
  child_source_end_le (nextSetup h allocation reserve) child

theorem next_child_source_after_buffer (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (reserve : requiredLimit q c ≤ c.limit) (child : Child) :
    c.buffer ≤ (childCall (nextSetup h allocation reserve) child).source := by
  have hs := child_source_after_parent_buffer (nextSetup h allocation reserve) child
  rw [nextSetup_parent_eq h allocation reserve] at hs
  exact hs

/-- Canonical construction supplies the one-copy child allocation, without
requiring a separate certificate for every physical child. -/
def next_child_allocation (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (reserve : requiredLimit q c ≤ c.limit) (child : Child) :
    ExchangeInterface.Allocation q radix (childCall (nextSetup h allocation reserve) child) :=
  childAllocation (nextSetup h allocation reserve) (nextSetup_room h allocation reserve) child

/-- Siblings reuse the same scratch interval instead of receiving disjoint
copies of the entire recursive workspace. -/
theorem sibling_buffer_eq (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (reserve : requiredLimit q c ≤ c.limit) (a b : Child) :
    (childCall (nextSetup h allocation reserve) a).buffer =
      (childCall (nextSetup h allocation reserve) b).buffer := rfl

theorem sibling_limit_eq (h : ShapeDepth q (k+1) c)
    (allocation : ExchangeInterface.Allocation q radix c)
    (reserve : requiredLimit q c ≤ c.limit) (a b : Child) :
    (childCall (nextSetup h allocation reserve) a).limit =
      (childCall (nextSetup h allocation reserve) b).limit := rfl

end
end CodedSorting.Construction.RecursiveWorkspaceAddress
end WorkspaceAddress

section BuildPath
/-! Paths in the concrete cutoff-controlled recursion. Every step follows
an actual child of the canonical next setup, and is available only at a
positive depth whose volume exceeds the cutoff. Thus the path relation
records precisely the builder's recursive-call rule, not an arbitrary tree.
The length and width results are independent of a global resource bound. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveBuildPath

open CommonSortingNormalization
open ExchangeInterface
open ExchangeSpecialization (radix)
open RecursiveBuildConditions RecursiveCallBridge

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

/-- The same actual call used by a large positive-depth recursive branch. -/
def nextCall {q : Configuration} {cutoff k : Nat} {c : Call}
    (h : Ready q cutoff (k+1) c) (hs : ¬ volume radix c ≤ cutoff)
    (child : OneLevelChildren.Child) : Call :=
  OneLevelExchange.childCall
    (nextSetup (large_node h hs).shape (large_node h hs).allocation
      (large_node h hs).reserve) child

theorem nextCall_width_lt {q : Configuration} {cutoff k : Nat} {c : Call}
    (h : Ready q cutoff (k+1) c) (hs : ¬ volume radix c ≤ cutoff)
    (child : OneLevelChildren.Child) : (nextCall h hs child).fieldWidth < c.fieldWidth :=
  RecursiveDescent.next_child_width_lt (large_node h hs).shape
    (large_node h hs).allocation (large_node h hs).reserve child

/-- A finite prefix of an actual recursion path. There is no positive step
from depth zero or from a volume at or below the cutoff. -/
inductive Path (q : Configuration) (cutoff : Nat) :
    Nat → Call → List OneLevelChildren.Child → Nat → Call → Prop
  | nil (k : Nat) (c : Call) : Path q cutoff k c [] k c
  | cons {k : Nat} {c : Call}
      (h : Ready q cutoff (k+1) c) (hs : ¬ volume radix c ≤ cutoff)
      (child : OneLevelChildren.Child)
      {rest : List OneLevelChildren.Child} {remaining : Nat} {endpoint : Call}
      (tail : Path q cutoff k (nextCall h hs child) rest remaining endpoint) :
      Path q cutoff (k+1) c (child :: rest) remaining endpoint

/-- Each traversed edge consumes exactly one unit of the starting depth. -/
theorem path_depth {q : Configuration} {cutoff k remaining : Nat}
    {c endpoint : Call} {choices : List OneLevelChildren.Child}
    (p : Path q cutoff k c choices remaining endpoint) :
    choices.length + remaining = k := by
  induction p with
  | nil => simp
  | cons h hs child tail ih =>
      simp only [List.length_cons]
      omega

theorem path_length_le {q : Configuration} {cutoff k remaining : Nat}
    {c endpoint : Call} {choices : List OneLevelChildren.Child}
    (p : Path q cutoff k c choices remaining endpoint) : choices.length ≤ k := by
  have hd := path_depth p
  omega

/-- The actual field width never increases along any finite path. -/
theorem path_width_le {q : Configuration} {cutoff k remaining : Nat}
    {c endpoint : Call} {choices : List OneLevelChildren.Child}
    (p : Path q cutoff k c choices remaining endpoint) :
    endpoint.fieldWidth ≤ c.fieldWidth := by
  induction p with
  | nil => exact Nat.le_refl _
  | cons h hs child tail ih =>
      exact ih.trans (Nat.le_of_lt (nextCall_width_lt h hs child))

/-- Every nonempty actual path strictly decreases the field width. -/
theorem path_width_lt_of_nonempty {q : Configuration} {cutoff k remaining : Nat}
    {c endpoint : Call} {choices : List OneLevelChildren.Child}
    (p : Path q cutoff k c choices remaining endpoint) (hne : choices ≠ []) :
    endpoint.fieldWidth < c.fieldWidth := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons h hs child tail =>
      exact (path_width_le tail).trans_lt (nextCall_width_lt h hs child)

/-- Zero remaining depth forces the path length to equal its starting depth. -/
theorem path_length_eq_of_zero {q : Configuration} {cutoff k : Nat}
    {c endpoint : Call} {choices : List OneLevelChildren.Child}
    (p : Path q cutoff k c choices 0 endpoint) : choices.length = k := by
  simpa only [Nat.add_zero] using path_depth p

#print axioms nextCall_width_lt
#print axioms path_depth
#print axioms path_length_le
#print axioms path_width_le
#print axioms path_width_lt_of_nonempty
#print axioms path_length_eq_of_zero

end
end CodedSorting.Construction.RecursiveBuildPath
end BuildPath

section CostNode
/-! The charge recurrence for the actual recursive Construction node. The one-level
bound is transported back to the original scalar call and applied to the
children generated by the same recursive builder. The child sum uses the
certified cardinality of the physical rank children, with no supplied tree
or arbitrary constructor family. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveCostNode

open CommonSortingNormalization CommonPermutationPairs
open ExchangeInterface ExchangeSpecialization
open RecursiveCallShape RecursiveCallBridge RecursiveBuildConditions
open scoped BigOperators

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

local notation "nodeCoefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)

private theorem transport_charge {a a' A p p' s : Nat}
    (ha : a = a') (hp : p' = p) (h : a' ≤ A*p'+s) : a ≤ A*p+s := by
  rw [ha, ←hp]
  exact h

/-- The concrete next-level adapter has the one-level charge bound for the
original parent's volume. No extra scan or fee comes from the adapter. -/
theorem nextProgram_charge_le {q : Configuration} (reader : Fin q.inventory.readers)
    {c : Call} {k : Nat} (shape : ShapeDepth q (k+1) c)
    (allocation : Allocation q radix c) (reserve : requiredLimit q c ≤ c.limit)
    (children : OneLevelExchange.Children (nextSetup shape allocation reserve)) :
    (nextProgram reader shape allocation reserve children).charge ≤
      nodeCoefficient * count q (volume radix c) +
        ∑ child : OneLevelChildren.Child, (children child).charge :=
  transport_charge
    (nextProgram_charge reader shape allocation reserve children)
    (congrArg (fun d : Call => count q (volume radix d))
      (nextSetup_parent_eq shape allocation reserve))
    (OneLevelExchange.charge_le reader shape.gap_pos (suffixWords_pos shape)
      (nextSetup shape allocation reserve) (nextSetup_room shape allocation reserve) children)

/-- The actual recursive node pays its local work and the sum of the
charges of precisely the recursively generated physical children. -/
theorem build_node_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff (k+1) c)
    (hs : ¬ volume radix c ≤ cutoff) :
    (RecursiveBuild.build q reader cutoff (k+1) c h).charge ≤
      nodeCoefficient * count q (volume radix c) +
        ∑ child : OneLevelChildren.Child,
          (RecursiveBuild.children q reader cutoff k c (large_node h hs) child).charge :=
  (congrArg (fun p : Program q radix c => p.charge)
    (RecursiveBuild.build_node q reader cutoff k c h hs)).trans_le
    (nextProgram_charge_le reader (large_node h hs).shape
      (large_node h hs).allocation (large_node h hs).reserve
      (RecursiveBuild.children q reader cutoff k c (large_node h hs)))

/-- A common bound on the actual physical children gives exactly the
certified rank budget times that bound. -/
theorem child_sum_le (cost : OneLevelChildren.Child → Nat) (B : Nat)
    (h : ∀ child, cost child ≤ B) :
    (∑ child : OneLevelChildren.Child, cost child) ≤ rankBudget * B := by
  calc
    (∑ child : OneLevelChildren.Child, cost child) ≤
        ∑ _child : OneLevelChildren.Child, B :=
      Finset.sum_le_sum (fun child _ => h child)
    _ = Fintype.card OneLevelChildren.Child * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ = rankBudget * B := congrArg (fun n => n*B) OneLevelChildren.child_count

/-- Uniformly bounding the generated child programs closes the local node
recurrence with the actual, already certified number of children. -/
theorem build_node_uniform_charge_le
    (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff (k+1) c)
    (hs : ¬ volume radix c ≤ cutoff) (B : Nat)
    (hchildren : ∀ child : OneLevelChildren.Child,
      (RecursiveBuild.children q reader cutoff k c (large_node h hs) child).charge ≤ B) :
    (RecursiveBuild.build q reader cutoff (k+1) c h).charge ≤
      nodeCoefficient * count q (volume radix c) + rankBudget * B :=
  (build_node_charge_le q reader cutoff k c h hs).trans
    (Nat.add_le_add_left (child_sum_le _ B hchildren) _)

end
end CodedSorting.Construction.RecursiveCostNode
end CostNode

section Parameters
/-! Uniform integer parameters for the actual Construction recursive implementation.
The cutoff is the existing common-machine leaf bank. The base width is the
largest power of the Construction dimension below floor(log_radix(bankWords/block)/8).
One fixed Construction normalization threshold supplies resident fit, buffered-bank
fit, startup and the stronger cutoff needed by the improved I/O rate.
Only generic integer parameter lemmas are reused; no old specialization
radix, dimension or stream count occurs in the chosen parameters. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveParameters

open CommonSortingNormalization CommonPermutationPairs
open ExchangeSpecialization
open PhysicalLeafParameters

noncomputable section

attribute [local irreducible] ExchangeSpecialization.uniform TensorFrameNetwork.program

def ratio (q : Configuration) : Nat := CommonExchangeLeaf.bankWords q / q.block

def cutoff (q : Configuration) : Nat := CommonExchangeLeaf.bankBits q

def chosenBase (q : Configuration) : Nat :=
  baseWidth ambientDimension radix (ratio q)

/-- A fixed threshold in the actual Construction radix and stream count. -/
def Normalized (q : Configuration) : Prop :=
  minimumRatio radix 1 streamCount ≤ ratio q

theorem minimumRatio_eq :
    minimumRatio radix 1 streamCount = max (radix^8) streamCount := by
  simp only [minimumRatio, Nat.log_one_right, Nat.zero_add, Nat.mul_one, Nat.one_mul]

/-- The selected positive power of 512 approximates the integer width limit
within the fixed dimension factor. -/
theorem chosenBase_bounds (q : Configuration) (hnormal : Normalized q) :
    0 < chosenBase q ∧ chosenBase q ≤ widthLimit radix (ratio q) ∧
      widthLimit radix (ratio q) < ambientDimension * chosenBase q :=
  baseWidth_bounds ambientDimension radix 1 streamCount (ratio q)
    (by rw [ambientDimension_eq]; omega) radix_prime.one_lt hnormal

theorem chosenBase_pos (q : Configuration) (hnormal : Normalized q) :
    0 < chosenBase q := (chosenBase_bounds q hnormal).1

/-- An exact integer logarithm sandwich for the selected Construction base width. -/
theorem chosenBase_log_sandwich (q : Configuration) (hnormal : Normalized q) :
    8 * chosenBase q ≤ Nat.log radix (ratio q) ∧
      Nat.log radix (ratio q) < 8 * ambientDimension * chosenBase q :=
  baseWidth_log_sandwich ambientDimension radix 1 streamCount (ratio q)
    (by rw [ambientDimension_eq]; omega) radix_prime.one_lt hnormal

/-- Every allowed width has enough actual leaf-bank words for all buckets. -/
theorem width_fit (q : Configuration) (hnormal : Normalized q) (e : Nat)
    (he : e ≤ widthLimit radix (ratio q)) :
    RecursiveWorkspaceBudget.buckets e * q.block ≤ CommonExchangeLeaf.bankWords q := by
  have h := bucket_words radix 1 streamCount (CommonExchangeLeaf.bankWords q)
    q.block e radix_prime.one_lt (by decide) hnormal he
  simpa only [RecursiveWorkspaceBudget.buckets, pow_two, Nat.div_one] using h

theorem chosenBase_fit (q : Configuration) (hnormal : Normalized q) :
    RecursiveWorkspaceBudget.buckets (chosenBase q) * q.block ≤
      CommonExchangeLeaf.bankWords q :=
  width_fit q hnormal (chosenBase q) (chosenBase_bounds q hnormal).2.1

/-- Word and bit bounds use the same machine word width. -/
theorem chosenBase_bits (q : Configuration) (hnormal : Normalized q) :
    RecursiveWorkspaceBudget.buckets (chosenBase q) * width q ≤ cutoff q := by
  simpa only [width, cutoff, CommonExchangeLeaf.bankBits, Nat.mul_assoc] using
    Nat.mul_le_mul_right q.w (chosenBase_fit q hnormal)

theorem chosenBase_startup (q : Configuration) (hnormal : Normalized q) :
    RecursiveWorkspaceBudget.buckets (chosenBase q) * width q ≤ cutoff q + width q :=
  (chosenBase_bits q hnormal).trans (Nat.le_add_right _ _)

/-- The selected cutoff also guarantees at least one physical block in
every child of an expanded node, as required by the improved rate theorem. -/
theorem cutoff_child (q : Configuration) (hnormal : Normalized q) :
    streamCount * width q ≤ cutoff q := by
  have h : streamCount * q.block ≤ CommonExchangeLeaf.bankWords q := by
    simpa only [Nat.div_one] using
      reserved_child_words radix 1 streamCount (CommonExchangeLeaf.bankWords q)
        q.block (by decide) hnormal
  simpa only [width, cutoff, CommonExchangeLeaf.bankBits, Nat.mul_assoc] using
    Nat.mul_le_mul_right q.w h

/-- The leaf package required by the real recursive workspace constructor,
now derived from the uniform integer parameter choice. -/
theorem leafParameters (q : Configuration) (hnormal : Normalized q) :
    RecursiveWorkspaceBudget.LeafParameters q (cutoff q) (chosenBase q) :=
  ⟨le_rfl, chosenBase_fit q hnormal, chosenBase_startup q hnormal⟩

/-- Choosing the common machine inventory ratio above the fixed Construction
threshold supplies normalization. No assertion is made for arbitrary
inventories that do not meet this numerical threshold. -/
theorem normalized_of_inventory (q : Configuration)
    (hthreshold : minimumRatio radix 1 streamCount ≤ q.inventory.ratio) :
    Normalized q := by
  apply (Nat.le_div_iff_mul_le (CommonLeafProgram.block_positive q)).2
  have h := Nat.mul_le_mul_right q.block hthreshold
  have hr := CommonSortingNormalization.normalized_ratio q
  have hb : q.height ≤ CommonExchangeLeaf.bankWords q := by
    unfold CommonExchangeLeaf.bankWords
    omega
  exact h.trans (hr.trans hb)

#print axioms minimumRatio_eq
#print axioms chosenBase_bounds
#print axioms chosenBase_log_sandwich
#print axioms chosenBase_fit
#print axioms cutoff_child
#print axioms leafParameters
#print axioms normalized_of_inventory

end
end CodedSorting.Construction.RecursiveParameters
end Parameters

section Workspace
/-! A single root reservation supplies the entire actual recursive tree.
Uniform leaf RAM/startup parameters, a public shape certificate and one
disk inequality generate every descendant's allocation and Ready proof.
No descendant program, workspace certificate or execution premise is an
input. The exact scalar reserve uses one shared recursive tail per layer. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveWorkspace

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface ExchangeSpecialization
open RecursiveCallShape RecursiveCallBridge RecursiveBuildConditions
open RecursiveWorkspaceBudget

noncomputable section

local notation "files" => (MachineNetworkAdapter.physicalInputs +
  MachineNetworkAdapter.nodes TensorFrameNetwork.program
    (inputs := MachineNetworkAdapter.physicalInputs))

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

theorem shortWidth_family {c : Call} {k base : Nat}
    (hwidth : c.fieldWidth = ambientDimension^(k+1)*base) :
    shortWidth c = ambientDimension^k*base := by
  rw [shortWidth, hwidth, pow_succ', Nat.mul_assoc]
  exact Nat.mul_div_cancel_left _ (by rw [ambientDimension_eq]; omega)

private theorem stop_fits (q : Configuration) (cutoff base k : Nat) (c : Call)
    (hp : LeafParameters q cutoff base) (hs : volume radix c ≤ cutoff) :
    LeafFits q radix cutoff k c := by
  simp only [LeafFits, if_pos hs]
  exact hs.trans hp.resident

private theorem zero_fits (q : Configuration) (cutoff base : Nat) (c : Call)
    (hp : LeafParameters q cutoff base) (hf : c.fieldWidth = base) :
    LeafFits q radix cutoff 0 c := by
  by_cases hs : volume radix c ≤ cutoff
  · exact stop_fits q cutoff base 0 c hp hs
  · simp only [LeafFits, if_neg hs, hf]
    exact ⟨True.intro, hp.bank, hp.startup⟩

private theorem zero_padding (cutoff base : Nat) (c : Call)
    (hf : c.fieldWidth = base) :
    RecursiveLeafProgram.padding cutoff c = padding cutoff base (volume radix c) := by
  unfold RecursiveLeafProgram.padding padding RecursiveBufferedLeaf.buckets buckets
  rw [hf, pow_two]

private theorem reserve_transport (r buffer C F F' L total limit : Nat)
    (hr : r = buffer+C+(F+1)*L) (hF : F = F')
    (ht : C+(F'+1)*L ≤ total) (hs : buffer+total ≤ limit) : r ≤ limit := by
  rw [hr, hF]
  omega

private theorem tail_transport (childBuffer buffer C F F' L tail limit : Nat)
    (hb : childBuffer = buffer+C+F*L) (hF : F = F')
    (h : buffer+(C+F'*L+tail) ≤ limit) : childBuffer+tail ≤ limit := by
  rw [hb, hF]
  omega

/-- All descendant allocations are consequences of a single root reserve. -/
theorem ready_of_space (q : Configuration) (cutoff base k : Nat) (c : Call)
    (hp : LeafParameters q cutoff base) (hshape : ShapeDepth q k c)
    (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + space q cutoff base k (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) : Ready q cutoff k c := by
  induction k generalizing c with
  | zero =>
      have hf : c.fieldWidth = base := by simpa only [pow_zero, one_mul] using hwidth
      refine of_zero_leaf ⟨⟨hsource, ?_, hdisk⟩, zero_fits q cutoff base c hp hf, ?_⟩
      · exact (Nat.add_le_add_left (space_ge_count q cutoff base 0 (volume radix c)) _).trans hspace
      · unfold RecursiveLeafProgram.Workspace
        rw [zero_padding cutoff base c hf]
        simpa only [space_zero, Nat.add_assoc] using hspace
  | succ k ih =>
      have ha : Allocation q radix c := ⟨hsource,
        (Nat.add_le_add_left (space_ge_count q cutoff base (k+1) (volume radix c)) _).trans hspace,
        hdisk⟩
      by_cases hs : volume radix c ≤ cutoff
      · refine of_small_leaf hs ⟨ha, stop_fits q cutoff base (k+1) c hp hs, ?_⟩
        unfold RecursiveLeafProgram.Workspace RecursiveLeafProgram.padding
        rw [if_pos hs]
        simpa only [space_small q cutoff base (k+1) (volume radix c) hs,
          Nat.add_assoc] using hspace
      · have hr : requiredLimit q c ≤ c.limit := by
          exact reserve_transport _ _ _ _ _ _ _ _
            (RecursiveWorkspaceAddress.requiredLimit_eq hshape) rfl
            (space_ge_node_reserve q cutoff base k (volume radix c) hs) hspace
        refine of_large_node hs ⟨hshape, ha, hr, ?_⟩
        intro child
        apply ih (OneLevelExchange.childCall (nextSetup hshape ha hr) child)
        · exact RecursiveDescent.next_child_depth hshape ha hr child
        · rw [RecursiveDescent.next_child_width_eq hshape ha hr child]
          exact shortWidth_family hwidth
        · exact RecursiveWorkspaceAddress.next_child_source_separate hshape ha hr child
        · rw [RecursiveWorkspaceAddress.next_child_volume hshape ha hr child,
            RecursiveWorkspaceAddress.next_child_limit hshape ha hr child]
          rw [space_node q cutoff base k (volume radix c) hs] at hspace
          exact tail_transport _ _ _ _ _ _ _ _
            (RecursiveWorkspaceAddress.next_child_buffer hshape ha hr child) rfl hspace
        · rw [RecursiveWorkspaceAddress.next_child_limit hshape ha hr child]
          exact hdisk

/-- Actual recursive instructions with no supplied per-child capacity proofs. -/
def program (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hshape : ShapeDepth q k c) (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + space q cutoff base k (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) : Program q radix c :=
  RecursiveBuild.build q reader cutoff k c
    (ready_of_space q cutoff base k c hp hshape hwidth hsource hspace hdisk)

theorem program_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hshape : ShapeDepth q k c) (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + space q cutoff base k (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) :
    (program q reader cutoff base k c hp hshape hwidth hsource hspace hdisk).instructions =
      (RecursiveBuild.build q reader cutoff k c
        (ready_of_space q cutoff base k c hp hshape hwidth hsource hspace hdisk)).instructions := rfl

theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff base k : Nat) (c : Call) (hp : LeafParameters q cutoff base)
    (hshape : ShapeDepth q k c) (hwidth : c.fieldWidth = ambientDimension^k*base)
    (hsource : c.source + count q (volume radix c) ≤ c.buffer)
    (hspace : c.buffer + space q cutoff base k (volume radix c) ≤ c.limit)
    (hdisk : c.limit ≤ q.N^q.exponent) (s : Machine q)
    (hsize : (program q reader cutoff base k c hp hshape hwidth hsource hspace hdisk).charge ≤
      q.N^q.exponent) (hpc : pc q s.ram = 0) :
    let p := program q reader cutoff base k c hp hshape hwidth hsource hspace hdisk
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q s.disk c.source (permutation radix c y).val) ∧
    (∀ z : Fin (q.N^q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) → result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧ result.2 ≤ p.charge ∧
    Fintype.card (ResidentIndex q) ≤ q.M :=
  CommonFinitePermutation.complete q
    (program q reader cutoff base k c hp hshape hwidth hsource hspace hdisk) s hsize hpc

end
end CodedSorting.Construction.RecursiveWorkspace
end Workspace
