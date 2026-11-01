import CodedSorting.Sorting.Radix.CodePolynomial

section Allocation
/-! One public arena size is used at every recursion depth. It is the
finite maximum of the actual generated workspace requirements for sizes
at most N. Parent directories occupy an earlier arena; a disk stack is
placed after every arena. The sole disk condition is an explicit numeric
end-address inequality, not a workspace or execution oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation
open CommonSortingNormalization CommonRecordProgram CodedSorting.Construction.RecursiveParameters
noncomputable section

def nodeWork (q : Configuration) (normal : Normalized q) (K n : ℕ) : ℕ :=
  max (CodedSorting.Construction.Sorting.CommonMSDChunks.space q normal n)
    (recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)+
      CodedSorting.CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q K)

def workSize (q : Configuration) (normal : Normalized q) (N K : ℕ) : ℕ :=
  (Finset.range (N+1)).sup (fun n => max (nodeWork q normal K n)
    (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q normal n))

def arenaSpan (q : Configuration) (normal : Normalized q) (N K : ℕ) : ℕ :=
  3*recordBlocks q N+workSize q normal N K+6

def arena (q : Configuration) (normal : Normalized q) (N K data depth : ℕ) : ℕ :=
  data+recordBlocks q N+2+depth*arenaSpan q normal N K

def buffer (q : Configuration) (normal : Normalized q) (N K data depth : ℕ) : ℕ :=
  arena q normal N K data depth+recordBlocks q N+2

def limit (q : Configuration) (normal : Normalized q) (N K data depth : ℕ) : ℕ :=
  buffer q normal N K data depth+workSize q normal N K

def target (q : Configuration) (normal : Normalized q) (N K data depth : ℕ) : ℕ :=
  limit q normal N K data depth+2

def stack (q : Configuration) (normal : Normalized q) (N K L data : ℕ) : ℕ :=
  arena q normal N K data (L+1)

def endAddress (q : Configuration) (normal : Normalized q) (N K L data : ℕ) : ℕ :=
  stack q normal N K L data+(L+1)*CommonMSDStack.frameBlocks q

structure Capacity (q : Configuration) (normal : Normalized q) (N K L data : ℕ) : Prop where
  input : N≤q.N
  exponent : 2≤q.exponent
  disk : endAddress q normal N K L data≤q.N^q.exponent

theorem recordBlocks_mono (q : Configuration) {n N : ℕ} (hn : n≤N) :
    recordBlocks q n≤recordBlocks q N := by
  rw [CommonRecordEncoding.recordBlocks_eq_words,CommonRecordEncoding.recordBlocks_eq_words]
  unfold PhysicalStreamCursor.blockCount
  apply Nat.div_le_div_right
  omega

theorem nodeWork_le (q : Configuration) (normal : Normalized q) (N K n : ℕ) (hn : n≤N) :
    nodeWork q normal K n≤workSize q normal N K := by
  exact (le_max_left _ _).trans (Finset.le_sup (f:=fun n => max (nodeWork q normal K n)
    (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q normal n)) (Finset.mem_range.mpr (by omega)))

theorem localWork_le (q : Configuration) (normal : Normalized q) (N K n : ℕ) (hn : n≤N) :
    CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q normal n≤workSize q normal N K := by
  exact (le_max_right _ _).trans (Finset.le_sup (f:=fun n => max (nodeWork q normal K n)
    (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q normal n)) (Finset.mem_range.mpr (by omega)))

theorem prepareWork_le (q : Configuration) (normal : Normalized q) (N K n : ℕ) (hn : n≤N) :
    CodedSorting.Construction.Sorting.CommonMSDChunks.space q normal n≤workSize q normal N K :=
  (le_max_left _ _).trans (nodeWork_le q normal N K n hn)

theorem directoryWork_le (q : Configuration) (normal : Normalized q) (N K n : ℕ) (hn : n≤N) :
    recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)+CodedSorting.CommonMSDChunks.chunkCount q n*
      CommonMSDDirectory.blocks q K≤workSize q normal N K :=
  (le_max_right _ _).trans (nodeWork_le q normal N K n hn)

theorem descriptor_capacity (q : Configuration) (n : ℕ) (hn : n≤q.N) (he : 2≤q.exponent) :
    3*CodedSorting.CommonMSDChunks.paddedSize q n<(2^q.w)^q.digits := by
  have hH := CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q
  have hs := CommonLocalDescriptorBounds.height_scaled_le_input q
  have hHN : q.height≤q.N := by omega
  have h96 : 96≤q.N := by nlinarith
  have h1 : 96*n≤q.N^2 := by nlinarith [Nat.mul_le_mul h96 hn]
  have h2 : 96*q.height^2≤q.N^2 := by nlinarith [Nat.mul_le_mul hs hHN]
  have hp := CodedSorting.CommonMSDChunks.padded_size_le q n
  change CodedSorting.CommonMSDChunks.paddedSize q n≤n+q.height^2 at hp
  have hbound : 3*CodedSorting.CommonMSDChunks.paddedSize q n≤q.N^2 := by nlinarith
  exact (hbound.trans (Nat.pow_le_pow_right (by have:=q.input_large;omega) he)).trans_lt
    (CommonStaticSchedule.pc_capacity q)

theorem counter_capacity (q : Configuration) (he : 2≤q.exponent) :
    recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)*q.block<(2^q.w)^q.digits := by
  have hb := CodedSorting.CommonMSDChunks.block_le_chunk q
  have hh := CommonLocalDescriptorBounds.capacity_of_height_squared q (CodedSorting.CommonMSDChunks.chunkSize q)
    le_rfl he
  have hC : recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)*q.block≤
      3*CodedSorting.CommonMSDChunks.chunkSize q+q.block := by
    rw [CommonRecordEncoding.recordBlocks_eq_words]
    exact LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) _
  omega

theorem arena_end (q : Configuration) (normal : Normalized q) (N K data depth : ℕ) :
    target q normal N K data depth+2*recordBlocks q N+2=
      arena q normal N K data (depth+1) := by
  unfold target limit buffer arena arenaSpan
  ring

theorem arena_mono (q : Configuration) (normal : Normalized q) (N K data d e : ℕ) (h : d≤e) :
    arena q normal N K data d≤arena q normal N K data e := by
  unfold arena
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem arena_capacity (q : Configuration) (normal : Normalized q) (N K L data depth : ℕ)
    (h : Capacity q normal N K L data) (hd : depth≤L) :
    arena q normal N K data (depth+1)≤q.N^q.exponent := by
  have hm := arena_mono q normal N K data (depth+1) (L+1) (by omega)
  have he : arena q normal N K data (L+1)≤endAddress q normal N K L data := by
    unfold endAddress stack
    omega
  exact (hm.trans he).trans h.disk

theorem limit_capacity (q : Configuration) (normal : Normalized q) (N K L data depth : ℕ)
    (h : Capacity q normal N K L data) (hd : depth≤L) :
    limit q normal N K data depth≤q.N^q.exponent := by
  have hc := arena_capacity q normal N K L data depth h hd
  rw [←arena_end] at hc
  unfold target at hc
  omega

/-- Every variable-size node receives a concrete resources value from
this one numerical arena allocation. -/
def resources (q : Configuration) (normal : Normalized q) (N K L data depth n : ℕ)
    (h : Capacity q normal N K L data) (hd : depth≤L) (hn : n≤N) :
    CodedSorting.Construction.Sorting.CommonMSDNodePass.Resources q normal n K where
  source := arena q normal N K data depth
  buffer := buffer q normal N K data depth
  limit := limit q normal N K data depth
  exponent := h.exponent
  source_before := by
    have hc := recordBlocks_mono q hn
    unfold buffer
    omega
  prepare_space := Nat.add_le_add_left (prepareWork_le q normal N K n hn) _
  directory_space := by
    have hc := directoryWork_le q normal N K n hn
    unfold CodedSorting.Construction.Sorting.CommonMSDNodePass.directory limit
    omega
  capacity := limit_capacity q normal N K L data depth h hd
  descriptors := descriptor_capacity q n (hn.trans h.input) h.exponent
  counters := counter_capacity q h.exponent

/-- A local bucket interval always lies before the current arena. -/
theorem local_source_before (q : Configuration) (normal : Normalized q) (N K data depth O n : ℕ)
    (hn : O+n≤N) :
    data+PhysicalStreamCursor.blockCount q.block (3*O+3*n)+2≤buffer q normal N K data depth := by
  have hb := recordBlocks_mono q hn
  rw [CommonRecordEncoding.recordBlocks_eq_words] at hb
  have he : 3*(O+n)=3*O+3*n := by ring
  rw [he] at hb
  unfold buffer arena
  omega

theorem local_work_fits (q : Configuration) (normal : Normalized q) (N K data depth n : ℕ)
    (hn : n≤N) :
    buffer q normal N K data depth+CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space q normal n≤
      limit q normal N K data depth := by
  have hc := localWork_le q normal N K n hn
  unfold limit
  omega

theorem gather_capacity (q : Configuration) (normal : Normalized q) (N K L data depth n : ℕ)
    (h : Capacity q normal N K L data) (hd : depth≤L) (hn : n≤N) :
    target q normal N K data depth+2*recordBlocks q n+2≤q.N^q.exponent := by
  have hc := arena_capacity q normal N K L data depth h hd
  have hb := recordBlocks_mono q hn
  rw [←arena_end] at hc
  omega

theorem stack_capacity (q : Configuration) (normal : Normalized q) (N K L data depth : ℕ)
    (h : Capacity q normal N K L data) (hd : depth≤L) :
    CommonMSDStack.frameBase q (stack q normal N K L data) depth+
      CommonMSDStack.frameBlocks q≤q.N^q.exponent := by
  have hm := Nat.mul_le_mul_right (CommonMSDStack.frameBlocks q) (show depth+1≤L+1 by omega)
  have hc := h.disk
  unfold CommonMSDStack.frameBase endAddress at *
  nlinarith

/-- A child arena starts after every byte of its parent's source,
workspace, stored row directories, and gathered output. -/
theorem parent_before_child (q : Configuration) (normal : Normalized q) (N K data depth : ℕ) :
    target q normal N K data depth+2*recordBlocks q N+2≤
      arena q normal N K data (depth+1) := le_of_eq (arena_end q normal N K data depth)

theorem arena_before_stack (q : Configuration) (normal : Normalized q) (N K L data depth : ℕ)
    (hd : depth≤L) :
    target q normal N K data depth+2*recordBlocks q N+2≤stack q normal N K L data := by
  rw [arena_end]
  exact arena_mono q normal N K data _ _ (by omega)

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation
end Allocation

section Control
/-! Compatibility names for the shared, proved controller. -/
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalControl
noncomputable instance : CodedSorting.RadixController.LocalSorter
    CodedSorting.Construction.RecursiveParameters.Normalized where
  space := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.space
  charge := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge
  program := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program
  program_charge := CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program_charge

abbrev Components := CodedSorting.RadixController.Components
  CodedSorting.Construction.RecursiveParameters.Normalized

export CodedSorting.RadixController (
  Job level offset records depth bounded
  Tag tagCount tagEquiv state visit nodeState
  counting pushing leaf returning halted child
  resume LeafFits leafCode body next leafCode_safe
  body_safe terminal terminal_empty routine)

export CodedSorting.RadixController (
  index routine_body routine_terminal routine_next node_body node_terminal
  node_raw node_next node_path node_trace_path node_done_body node_done_next
  node_return)
export CodedSorting.RadixController (
  path_of_one one_step count_body count_terminal counting_next count_next_loaded
  count_path count_done)
export CodedSorting.RadixController (
  bounded_val child_properties visit_node trace_terminal node_call root_halt)
export CodedSorting.RadixController (
  pushing_body pushing_terminal pushing_next push_path)
export CodedSorting.RadixController (
  pop_body pop_terminal pop_next_loaded pop_path)
end CodedSorting.Construction.Sorting.CommonMSDGlobalControl

namespace CodedSorting.Construction.Sorting.CommonMSDGlobalBase
export CodedSorting.RadixController.Base (
  one level_zero leaf_path small_path leafProgram leafProgram_code
  leafProgram_charge leaf_correct leaf_global)
end CodedSorting.Construction.Sorting.CommonMSDGlobalBase
end Control

section Components
/-! The actual global controller components, instantiated uniformly for
all public jobs. Every node uses charged extraction, the constructed row
sort/directory/gather routine, and charged restoration. Only public numeric
machine and allocation parameters occur in this program family. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalComponents
open CommonSortingNormalization CodedSorting.Construction.RecursiveParameters CommonRecordProgram
open CommonMSDRoutine CodedSorting.Construction.Sorting.CommonMSDGlobalControl CommonMSDParameters
open CommonLeafProgram (Machine)
noncomputable section

structure Parameters (q : Configuration) (L : ℕ) where
  reader : Fin q.inventory.readers
  normal : Normalized q
  source : ℕ
  capacity : CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal q.N (radix q) L source

variable {q : Configuration} {L : ℕ}

def resources (p : Parameters q L) (j : Job q.N L) :
    CodedSorting.Construction.Sorting.CommonMSDNodePass.Resources q p.normal (records j) (radix q) :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.resources q p.normal q.N (radix q) L p.source
    (depth j) (records j) p.capacity (by have:=j.2.2.2.isLt;unfold depth;omega)
    (by have:=j.2.2.1.isLt;unfold records;omega)

def target (p : Parameters q L) (j : Job q.N L) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target q p.normal q.N (radix q) p.source (depth j)

def layout (p : Parameters q L) (j : Job q.N L) :
    CommonMSDGatherController.Layout (radix q*CodedSorting.CommonMSDChunks.chunkCount q (records j)) :=
  CommonMSDNodeLayout.layout q (records j) (radix q) (resources p j).source
    (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer) (target p j)

def inner (p : Parameters q L) (j : Job q.N L) :
    Routine q (CodedSorting.Construction.Sorting.CommonMSDNodeController.tagCount
      (radix q*CodedSorting.CommonMSDChunks.chunkCount q (records j)) (3*records j)) :=
  CodedSorting.Construction.Sorting.CommonMSDNodeController.routine q p.reader (resources p j) (directory_fits q)
    (CommonMSDRecordDigits.wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
    (layout p j)

def interval (p : Parameters q L) (j : Job q.N L) :
    Routine q (CodedSorting.Construction.Sorting.CommonMSDNodeController.tagCount
      (radix q*CodedSorting.CommonMSDChunks.chunkCount q (records j)) (3*records j)+3) :=
  CommonMSDIntervalRoutine.routine q p.reader (records j) p.source (offset j)
    (resources p j).source (target p j) (inner p j)

def node (p : Parameters q L) (j : Job q.N L) : Routine q (CommonMSDNodeTagBound.bound q (radix q)) :=
  CommonMSDRoutinePad.extend (interval p j)
    (CommonMSDNodeTagBound.node_fits q (radix q) (records j)
      (by have:=j.2.2.1.isLt;unfold records;omega))

def directories (p : Parameters q L) (j : Job q.N L) : List ℕ :=
  List.ofFn (fun i : Fin (CodedSorting.CommonMSDChunks.chunkCount q (records j)) =>
    CommonMSDRowDirectoryBatch.target q (radix q)
      (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer) i.val)

def components (p : Parameters q L) : Components q L (CommonMSDNodeTagBound.bound q (radix q)) where
  reader := p.reader
  normal := p.normal
  exponent := p.capacity.exponent
  source := p.source
  stack := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack q p.normal q.N (radix q) L p.source
  buffer := fun j => (resources p j).buffer
  limit := fun j => (resources p j).limit
  directories := directories p
  node := node p

theorem leaf_fits (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (hn : records j≤q.height^2) :
    LeafFits (components p) j := by
  refine ⟨hn,?_,?_,?_⟩
  · exact CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.local_source_before q p.normal q.N (radix q) p.source
      (depth j) (offset j) (records j) hj
  · exact CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.local_work_fits q p.normal q.N (radix q) p.source
      (depth j) (records j) (by omega)
  · exact (resources p j).capacity

/-- Extraction needs the input's whole active interval to precede its
depth arena. The condition is numeric and follows from job containment. -/
theorem extract_fits (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) :
    CommonIntervalAdapter.Fits q (records j) p.source (offset j) (resources p j).source
      (resources p j).buffer (resources p j).limit := by
  refine ⟨?_,(resources p j).source_before,?_,(resources p j).capacity⟩
  · have h := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.recordBlocks_mono q hj
    rw [CommonRecordEncoding.recordBlocks_eq_words] at h
    have he : 3*(offset j+records j)=3*offset j+3*records j := by ring
    rw [he] at h
    change p.source+_+2≤CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j)
    unfold CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena
    omega
  · have h := (resources p j).prepare_space
    omega

theorem restore_fits (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) :
    CommonIntervalAdapter.Fits q (records j) p.source (offset j) (target p j)
      (target p j+recordBlocks q (records j)+2)
      (CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j+1)) := by
  have hn : records j≤q.N := by omega
  have hd : depth j≤L := by have:=j.2.2.2.isLt;unfold depth;omega
  have hc := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_capacity q p.normal q.N (radix q) L
    p.source (depth j) p.capacity hd
  have hb := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.recordBlocks_mono q hn
  have he := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_end q p.normal q.N (radix q) p.source (depth j)
  have hx := (extract_fits p j hj).source_before
  refine ⟨?_,le_rfl,?_,hc⟩
  · change p.source+_+2≤CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target q p.normal q.N (radix q) p.source (depth j)
    change p.source+_+2≤CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j) at hx
    unfold CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer
    omega
  · change CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target q p.normal q.N (radix q) p.source (depth j)+_+2≤_
    omega

def routine (p : Parameters q L) (root : Job q.N L) :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalControl.routine (components p) (K:=radix q) root

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalComponents
end Components

section Entry
/-! One input-independent whole-sort policy and its concrete initial job.
The finite instruction-space requirement is exposed as a numerical bound;
no successful run or sorting-correctness assumption is part of the policy. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalEntry
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CodedSorting.Construction.Sorting.CommonMSDGlobalControl
open CommonLeafProgram (Machine)
noncomputable section

abbrev levels (q : Configuration) := CommonMSDRadixCost.depth q
abbrev Parameters (q : Configuration) := CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.Parameters q (levels q)

def root (q : Configuration) (n : ℕ) (hn : n≤q.N) : Job q.N (levels q) :=
  (⟨levels q,by omega⟩,0,⟨n,by omega⟩,0)

def program (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p (root q n hn)

/-- A public stride shared by every finite control tag. -/
def stride (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) : ℕ :=
  (Finset.univ.sup (fun tag => ((program q p n hn).body tag).length))+1

def ControlCapacity (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) : Prop :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalControl.tagCount q.N (levels q)
    (CommonMSDNodeTagBound.bound q (CommonMSDParameters.radix q)) (CommonMSDParameters.radix q)*
    stride q p n hn≤q.N^q.exponent

theorem fits (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) : (program q p n hn).Fits (stride q p n hn) := by
  refine ⟨?_,hc⟩
  intro tag
  exact Nat.lt_succ_of_le (Finset.le_sup
    (f:=fun tag => ((program q p n hn).body tag).length) (Finset.mem_univ tag))

def initial (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (s : Machine q) : Machine q :=
  {s with ram:=setPC q ((program q p n hn).entry.val*stride q p n hn) s.ram}

@[simp] theorem initial_disk (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (s : Machine q) : (initial q p n hn s).disk=s.disk := rfl

@[simp] theorem initial_payload (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (s : Machine q) : erasePC q (initial q p n hn s)=erasePC q s := by
  simp only [initial,erasePC,setPC_setPC]

theorem initial_pc (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) (s : Machine q) :
    pc q (initial q p n hn s).ram=(program q p n hn).entry.val*stride q p n hn := by
  apply pc_setPC
  exact (program q p n hn).tag_capacity (stride q p n hn) (fits q p n hn hc) _

def policy (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) : SourcePolicy q :=
  (program q p n hn).policy (stride q p n hn)

theorem root_prefix (q : Configuration) (xs : List (KeyRecordWords.Record q.w))
    (ho : CommonMSDRecordDigits.OrdinaryList xs) :
    CommonMSDSemantics.Prefix CommonWordMSD.key (CommonMSDParameters.radix q) (levels q) 0 xs := by
  intro x hx
  exact Nat.div_eq_of_lt ((CommonMSDRecordDigits.ordinary_key_lt x (ho x hx)).trans_le
    (CommonMSDRadixCost.depth_covers q))

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalEntry
end Entry

section BodyBound
/-! Uniform instruction lengths for the entire global control table.
Every tag is covered, including unreachable jobs and unused padded tags.
The two scalar premises bound existing public code lengths; no execution,
directory, or control-capacity assumption occurs here. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalBodyBound
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CommonMSDParameters
noncomputable section
attribute [local irreducible] CodedSorting.Construction.RecursiveParameters.Normalized
  CodedSorting.Construction.Sorting.CommonMSDNodePass.code CodedSorting.Construction.Sorting.CommonMSDNodePass.chunks
  CodedSorting.Construction.Sorting.CommonLocalMachine.localProgram

variable {q : Configuration} {L : ℕ}

theorem height_le_input (q : Configuration) : q.height≤q.N := by
  have := CommonLocalDescriptorBounds.height_scaled_le_input q
  omega

theorem block_le_input (q : Configuration) : q.block≤q.N :=
  (CodedSorting.Construction.Sorting.CommonLocalRecursion.block_le_height q).trans (height_le_input q)

theorem digits_le_input (q : Configuration) : q.digits≤q.N :=
  (CommonMSDDirectoryBounds.digits_le_height q).trans (height_le_input q)

theorem records_le (j : Job q.N L) : records j≤q.N := by
  have := j.2.2.1.isLt
  unfold records
  omega

theorem copy_length_le (q : Configuration) (reader : Fin q.inventory.readers)
    (n O D source target : ℕ) (hn : n≤q.N) :
    (CommonIntervalCopy.code q reader O D (3*n) source target).length≤48*(q.N+1) := by
  rw [CommonIntervalCopy.code_length]
  have hp := CommonMSDGatherCapacity.copy_pages_le q D (3*n)
  have hb := block_le_input q
  omega

theorem inner_length_le (p : Parameters q L) (j : Job q.N L) (bNode : ℕ)
    (hn : CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q (records j) (radix q)≤bNode)
    (tag : Fin (CodedSorting.Construction.Sorting.CommonMSDNodeController.tagCount
      (radix q*CodedSorting.CommonMSDChunks.chunkCount q (records j)) (3*records j))) :
    ((inner p j).body tag).length≤bNode+48*(q.N+1) := by
  have hc := CodedSorting.Construction.Sorting.CommonMSDNodeController.code_length_lt q p.reader (resources p j)
    (directory_fits q)
    (CommonMSDRecordDigits.wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
    (layout p j) tag
  have hg := CommonMSDGatherCapacity.stride_le q (3*records j)
    (Nat.mul_le_mul_left 3 (records_le j))
  change ((inner p j).body tag).length<
    CodedSorting.Construction.Sorting.CommonMSDNodeController.chosenStride
      q (records j) (radix q) (3*records j) at hc
  unfold CodedSorting.Construction.Sorting.CommonMSDNodeController.chosenStride at hc
  have hm : max (CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q (records j) (radix q)+1)
      (CommonMSDGatherCapacity.chosenStride q (3*records j))≤bNode+48*(q.N+1) := by
    apply max_le <;> omega
  omega

theorem interval_length_le (p : Parameters q L) (j : Job q.N L) (bNode : ℕ)
    (hn : CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q (records j) (radix q)≤bNode)
    (tag : Fin (CodedSorting.Construction.Sorting.CommonMSDNodeController.tagCount
      (radix q*CodedSorting.CommonMSDChunks.chunkCount q (records j)) (3*records j)+3)) :
    ((interval p j).body tag).length≤bNode+48*(q.N+1) := by
  simp only [interval,CommonMSDIntervalRoutine.routine]
  split_ifs with ht he hr
  · exact inner_length_le p j bNode hn _
  · exact (copy_length_le q p.reader (records j) (3*offset j) 0 p.source
      (resources p j).source (records_le j)).trans (Nat.le_add_left _ _)
  · exact (copy_length_le q p.reader (records j) 0 (3*offset j) (target p j)
      p.source (records_le j)).trans (Nat.le_add_left _ _)
  · simp

theorem node_length_le (p : Parameters q L) (j : Job q.N L) (bNode : ℕ)
    (hn : CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q (records j) (radix q)≤bNode)
    (tag : Fin (CommonMSDNodeTagBound.bound q (radix q))) :
    ((node p j).body tag).length≤bNode+48*(q.N+1) := by
  simp only [node,CommonMSDRoutinePad.extend]
  split_ifs with ht
  · exact interval_length_le p j bNode hn _
  · simp

theorem count_length_le (p : Parameters q L) (j : Job q.N L) (key : ℕ) :
    (CommonMSDChildCount.code q (directories p j) key).length≤6*(q.N+1)^2 := by
  rw [CommonMSDChildCount.code_length]
  have hc := (CommonMSDChunkRows.count_le q (records j)).trans (records_le j)
  have hr := CommonMSDGatherCapacity.read_blocks_le q key
  have hb := block_le_input q
  have hd := digits_le_input q
  have hh : (directories p j).length=CodedSorting.CommonMSDChunks.chunkCount q (records j) := by
    simp only [directories,List.length_ofFn]
  rw [hh]
  have hm := Nat.mul_le_mul hc (show CommonMSDDirectoryRead.blocks q key+1≤4*q.N+1 by omega)
  nlinarith only [hm]

theorem frame_le (q : Configuration) : CommonMSDStack.frameBlocks q≤2*q.N := by
  have hd := digits_le_input q
  have hb := block_le_input q
  have hh := Nat.div_le_self (q.digits+q.block-1) q.block
  unfold CommonMSDStack.frameBlocks PhysicalStreamCursor.blockCount
  omega

theorem leaf_length_le (p : Parameters q L) (j : Job q.N L) (bLeaf : ℕ)
    (hl : ∀ n≤q.N,n≤q.height^2 → CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n≤bLeaf) :
    (leafCode (components p) j).length≤bLeaf := by
  unfold leafCode
  split
  · rename_i hf
    exact (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.program q (components p).reader (components p).normal
      (records j) hf.1 (components p).exponent (components p).source (offset j)
      ((components p).buffer j) ((components p).limit j) hf.2.1 hf.2.2.1 hf.2.2.2).length_le.trans
      (hl (records j) (records_le j) hf.1)
  · simp

def bound (q : Configuration) (bNode bLeaf : ℕ) : ℕ :=
  bNode+bLeaf+100*(q.N+1)^2

theorem body_length_le (p : Parameters q L) (bNode bLeaf : ℕ)
    (hn : ∀ n≤q.N,CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q n (radix q)≤bNode)
    (hl : ∀ n≤q.N,n≤q.height^2 → CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n≤bLeaf)
    (tag : Tag q.N L (CommonMSDNodeTagBound.bound q (radix q)) (radix q)) :
    (body (components p) tag).length≤bound q bNode bLeaf := by
  have hquadratic : 48*(q.N+1)≤100*(q.N+1)^2 := by nlinarith
  unfold body
  dsimp only
  split
  · have hh := node_length_le p tag.1 bNode (hn _ (records_le tag.1)) tag.2.2.1
    change ((node p tag.1).body tag.2.2.1).length≤_
    unfold bound
    omega
  · split
    · split
      · have hh := count_length_le p tag.1 tag.2.2.2.1.val
        change (CommonMSDChildCount.code q (directories p tag.1) _).length≤_
        unfold bound
        omega
      · simp only [List.length_nil];exact Nat.zero_le _
    · split
      · rw [CommonMSDStack.push_length]
        have hh := frame_le q
        unfold bound
        nlinarith
      · split
        · exact (leaf_length_le p tag.1 bLeaf hl).trans (by unfold bound;omega)
        · split
          · split
            · simp only [List.length_nil];exact Nat.zero_le _
            · rw [CommonMSDStack.pop_length]
              have hh := frame_le q
              unfold bound
              nlinarith
          · simp only [List.length_nil];exact Nat.zero_le _

theorem program_length_le (p : CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q)
    (n : ℕ) (hn : n≤q.N) (bNode bLeaf : ℕ)
    (hnode : ∀ m≤q.N,CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q m (radix q)≤bNode)
    (hleaf : ∀ m≤q.N,m≤q.height^2 → CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q m≤bLeaf)
    (tag : Fin (tagCount q.N (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
      (CommonMSDNodeTagBound.bound q (radix q)) (radix q))) :
    ((CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.program q p n hn).body tag).length≤bound q bNode bLeaf :=
  body_length_le p bNode bLeaf hnode hleaf _

theorem stride_le (p : CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q) (n : ℕ) (hn : n≤q.N)
    (bNode bLeaf : ℕ)
    (hnode : ∀ m≤q.N,CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q m (radix q)≤bNode)
    (hleaf : ∀ m≤q.N,m≤q.height^2 → CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q m≤bLeaf) :
    CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.stride q p n hn≤bound q bNode bLeaf+1 := by
  unfold CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.stride
  apply Nat.add_le_add_right
  apply Finset.sup_le
  intro tag _
  exact program_length_le p n hn bNode bLeaf hnode hleaf tag

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalBodyBound
end BodyBound

section Execution
/-! Compile the root job's actual returning path, including its final
return-to-halt instruction, into one run of the concrete fixed policy. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalExecution
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalEntry CodedSorting.Construction.Sorting.CommonMSDGlobalControl
open CommonLeafProgram (Machine)
noncomputable section

theorem tag_count_capacity (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) :
    CodedSorting.Construction.Sorting.CommonMSDGlobalControl.tagCount q.N (levels q)
      (CommonMSDNodeTagBound.bound q (CommonMSDParameters.radix q)) (CommonMSDParameters.radix q)
      <(2^q.w)^q.digits := by
  have hs : 0<stride q p n hn := by unfold stride;omega
  have hmul := Nat.le_mul_of_pos_right
    (CodedSorting.Construction.Sorting.CommonMSDGlobalControl.tagCount q.N (levels q)
      (CommonMSDNodeTagBound.bound q (CommonMSDParameters.radix q)) (CommonMSDParameters.radix q)) hs
  exact (hmul.trans hc).trans_lt (CommonStaticSchedule.pc_capacity q)

theorem finish (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) (s final : Machine q) (steps charge : ℕ)
    (hp : (program q p n hn).Path (program q p n hn).entry s
      (index (returning (K:=CommonMSDParameters.radix q)
        (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) (root q n hn))) final steps charge) :
    let out := ControlledNormalization.runLogical (policy q p n hn)
      (steps+1) (initial q p n hn s)
    out.1.disk=final.disk ∧ policy q p n hn out.1.ram=none ∧
      out.2=charge ∧ Fintype.card (ResidentIndex q)≤q.M := by
  let r := program q p n hn
  have hr := root_halt (K:=CommonMSDParameters.radix q)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) (root q n hn) (root q n hn)
    (by rfl) final
  have hpath := r.path_append hp (r.trace_toPath hr)
  have hterm : r.terminal (index (halted (K:=CommonMSDParameters.radix q)
      (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) (root q n hn)))=true := by
    change (CodedSorting.Construction.Sorting.CommonMSDGlobalControl.routine (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p)
      (root q n hn)).terminal (index (halted (K:=CommonMSDParameters.radix q)
        (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) (root q n hn)))=true
    rw [routine_terminal]
    rfl
  have ht := r.path_toTrace hpath hterm
  have hout := r.trace_run_from (stride q p n hn) (fits q p n hn hc) ht
    (initial q p n hn s) (initial_payload q p n hn s) (initial_pc q p n hn hc s)
  dsimp only
  have hd := congrArg (fun t : Machine q => t.disk) hout.1
  exact ⟨hd,hout.2.2.2,by simpa only [Nat.add_zero] using hout.2.1,resident_memory q⟩

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalExecution
end Execution

section ControlCapacity
/-! Eliminate the finite global control-table premise by fixed polynomial
bounds. The coefficient depends only on the fixed construction and the
public word-width constant, never on the input records or their run. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity
open CommonSortingNormalization CodedSorting.Construction.Sorting.CommonMSDGlobalEntry CommonMSDParameters
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension

def strideConstant : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.nodeConstant+CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.leafConstant+101

def controlConstant (κ : ℕ) : ℕ := 406*(κ+1)^2*strideConstant

/-- A fixed input threshold absorbs the fixed coefficient into N^17. -/
def threshold (κ : ℕ) : ℕ := 2^16*controlConstant κ

theorem stride_polynomial (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block) :
    stride q p n hn≤strideConstant*(q.N+1)^4 := by
  have h := CodedSorting.Construction.Sorting.CommonMSDGlobalBodyBound.stride_le p n hn
    (CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.nodeConstant*(q.N+1)^4)
    (CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.leafConstant*(q.N+1)^2)
    (fun m hm => CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.node_length q hnormal m hm)
    (fun m hm hs => CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.interval_charge q hnormal m hm hs)
  have h24 : (q.N+1)^2≤(q.N+1)^4 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤(q.N+1)^4 := Nat.one_le_pow _ _ (by omega)
  have hl := Nat.mul_le_mul_left CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.leafConstant h24
  unfold CodedSorting.Construction.Sorting.CommonMSDGlobalBodyBound.bound at h
  unfold strideConstant
  nlinarith only [h,hl,h24,h1]

/-- All tags, including unreachable states, fit a fixed degree 16 table. -/
theorem control_polynomial (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) :
    CodedSorting.Construction.Sorting.CommonMSDGlobalControl.tagCount q.N (levels q)
      (CommonMSDNodeTagBound.bound q (radix q)) (radix q)*stride q p n hn≤
      controlConstant κ*(q.N+1)^16 := by
  have ht := CommonMSDGlobalTagCapacity.tagCount_le q κ hw
  have hs := stride_polynomial q p n hn hnormal
  calc
    _ ≤ (406*(κ+1)^2*(q.N+1)^12)*(strideConstant*(q.N+1)^4) :=
      Nat.mul_le_mul ht hs
    _ = controlConstant κ*(q.N+1)^16 := by unfold controlConstant;ring

/-- No ControlCapacity assumption is retained: a fixed exponent and
fixed large-input threshold imply the exact original controller premise. -/
theorem capacity (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (hlarge : threshold κ≤q.N)
    (he : 17≤q.exponent) : ControlCapacity q p n hn := by
  have hN : 1≤q.N := by have := q.input_large;omega
  have hpow := Nat.pow_le_pow_left (show q.N+1≤2*q.N by omega) 16
  have hc := Nat.mul_le_mul_left (controlConstant κ) hpow
  have ht := Nat.mul_le_mul_right (q.N^16) hlarge
  unfold threshold at ht
  unfold ControlCapacity
  calc
    _ ≤ controlConstant κ*(q.N+1)^16 := control_polynomial q p n hn hnormal κ hw
    _ ≤ controlConstant κ*(2*q.N)^16 := hc
    _ = (2^16*controlConstant κ)*q.N^16 := by ring
    _ ≤ q.N*q.N^16 := ht
    _ = q.N^17 := by ring
    _ ≤ q.N^q.exponent := Nat.pow_le_pow_right hN he

theorem fits (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (hlarge : threshold κ≤q.N)
    (he : 17≤q.exponent) : (program q p n hn).Fits (stride q p n hn) :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.fits q p n hn (capacity q p n hn hnormal κ hw hlarge he)

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity
end ControlCapacity
