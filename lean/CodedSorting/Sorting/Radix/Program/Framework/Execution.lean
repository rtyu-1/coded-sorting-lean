import CodedSorting.Sorting.Radix.Partition.Framework.Pass
import CodedSorting.Sorting.Radix.LocalGroups.Framework.Local
import CodedSorting.Sorting.Radix.Program.Shared.Control
import CodedSorting.Sorting.Radix.LocalGroups.Framework.Routine
import CodedSorting.Sorting.Radix.Partition.Framework.Semantic

section Allocation
/-! One public arena size is used at every recursion depth. It is the
finite maximum of the actual generated workspace requirements for sizes
at most N. Parent directories occupy an earlier arena; a disk stack is
placed after every arena. The sole disk condition is an explicit numeric
end-address inequality, not a workspace or execution oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace CodedSorting.CommonMSDGlobalAllocation
open CommonSortingNormalization CommonRecordProgram CommonPrunedParameters
noncomputable section

def nodeWork (q : Configuration) (normal : Normalized q) (K n : ℕ) : ℕ :=
  max (CommonMSDChunks.space q normal n)
    (recordBlocks q (CommonMSDChunks.chunkSize q)+
      CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q K)

def workSize (q : Configuration) (normal : Normalized q) (N K : ℕ) : ℕ :=
  (Finset.range (N+1)).sup (fun n => max (nodeWork q normal K n)
    (CommonMSDIntervalLocal.space q normal n))

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
    (CommonMSDIntervalLocal.space q normal n)) (Finset.mem_range.mpr (by omega)))

theorem localWork_le (q : Configuration) (normal : Normalized q) (N K n : ℕ) (hn : n≤N) :
    CommonMSDIntervalLocal.space q normal n≤workSize q normal N K := by
  exact (le_max_right _ _).trans (Finset.le_sup (f:=fun n => max (nodeWork q normal K n)
    (CommonMSDIntervalLocal.space q normal n)) (Finset.mem_range.mpr (by omega)))

theorem prepareWork_le (q : Configuration) (normal : Normalized q) (N K n : ℕ) (hn : n≤N) :
    CommonMSDChunks.space q normal n≤workSize q normal N K :=
  (le_max_left _ _).trans (nodeWork_le q normal N K n hn)

theorem directoryWork_le (q : Configuration) (normal : Normalized q) (N K n : ℕ) (hn : n≤N) :
    recordBlocks q (CommonMSDChunks.chunkSize q)+CommonMSDChunks.chunkCount q n*
      CommonMSDDirectory.blocks q K≤workSize q normal N K :=
  (le_max_right _ _).trans (nodeWork_le q normal N K n hn)

theorem descriptor_capacity (q : Configuration) (n : ℕ) (hn : n≤q.N) (he : 2≤q.exponent) :
    3*CommonMSDChunks.paddedSize q n<(2^q.w)^q.digits := by
  have hH := CommonLocalRecursion.height_pos q
  have hs := CommonLocalDescriptorBounds.height_scaled_le_input q
  have hHN : q.height≤q.N := by omega
  have h96 : 96≤q.N := by nlinarith
  have h1 : 96*n≤q.N^2 := by nlinarith [Nat.mul_le_mul h96 hn]
  have h2 : 96*q.height^2≤q.N^2 := by nlinarith [Nat.mul_le_mul hs hHN]
  have hp := CommonMSDChunks.padded_size_le q n
  change CommonMSDChunks.paddedSize q n≤n+q.height^2 at hp
  have hbound : 3*CommonMSDChunks.paddedSize q n≤q.N^2 := by nlinarith
  exact (hbound.trans (Nat.pow_le_pow_right (by have:=q.input_large;omega) he)).trans_lt
    (CommonStaticSchedule.pc_capacity q)

theorem counter_capacity (q : Configuration) (he : 2≤q.exponent) :
    recordBlocks q (CommonMSDChunks.chunkSize q)*q.block<(2^q.w)^q.digits := by
  have hb := CommonMSDChunks.block_le_chunk q
  have hh := CommonLocalDescriptorBounds.capacity_of_height_squared q (CommonMSDChunks.chunkSize q)
    le_rfl he
  have hC : recordBlocks q (CommonMSDChunks.chunkSize q)*q.block≤
      3*CommonMSDChunks.chunkSize q+q.block := by
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
    CommonMSDNodePass.Resources q normal n K where
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
    unfold CommonMSDNodePass.directory limit
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
    buffer q normal N K data depth+CommonMSDIntervalLocal.space q normal n≤
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
end CodedSorting.CommonMSDGlobalAllocation
end Allocation

section Control
/-! Compatibility names for the shared, proved controller. -/
namespace CodedSorting.CommonMSDGlobalControl
noncomputable instance : CodedSorting.RadixController.LocalSorter
    CodedSorting.CommonPrunedParameters.Normalized where
  space := CodedSorting.CommonMSDIntervalLocal.space
  charge := CodedSorting.CommonMSDIntervalLocal.charge
  program := CodedSorting.CommonMSDIntervalLocal.program
  program_charge := CodedSorting.CommonMSDIntervalLocal.program_charge

abbrev Components := CodedSorting.RadixController.Components
  CodedSorting.CommonPrunedParameters.Normalized

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
end CodedSorting.CommonMSDGlobalControl

namespace CodedSorting.CommonMSDGlobalBase
export CodedSorting.RadixController.Base (
  one level_zero leaf_path small_path leafProgram leafProgram_code
  leafProgram_charge leaf_correct leaf_global)
end CodedSorting.CommonMSDGlobalBase
end Control

section Components
/-! The actual global controller components, instantiated uniformly for
all public jobs. Every node uses charged extraction, the constructed row
sort/directory/gather routine, and charged restoration. Only public numeric
machine and allocation parameters occur in this program family. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
namespace CodedSorting.CommonMSDGlobalComponents
open CommonSortingNormalization CommonPrunedParameters CommonRecordProgram
open CommonMSDRoutine CommonMSDGlobalControl CommonMSDParameters
open CommonLeafProgram (Machine)
noncomputable section

structure Parameters (q : Configuration) (L : ℕ) where
  reader : Fin q.inventory.readers
  normal : Normalized q
  source : ℕ
  capacity : CommonMSDGlobalAllocation.Capacity q normal q.N (radix q) L source

variable {q : Configuration} {L : ℕ}

def resources (p : Parameters q L) (j : Job q.N L) :
    CommonMSDNodePass.Resources q p.normal (records j) (radix q) :=
  CommonMSDGlobalAllocation.resources q p.normal q.N (radix q) L p.source
    (depth j) (records j) p.capacity (by have:=j.2.2.2.isLt;unfold depth;omega)
    (by have:=j.2.2.1.isLt;unfold records;omega)

def target (p : Parameters q L) (j : Job q.N L) : ℕ :=
  CommonMSDGlobalAllocation.target q p.normal q.N (radix q) p.source (depth j)

def layout (p : Parameters q L) (j : Job q.N L) :
    CommonMSDGatherController.Layout (radix q*CommonMSDChunks.chunkCount q (records j)) :=
  CommonMSDNodeLayout.layout q (records j) (radix q) (resources p j).source
    (CommonMSDNodePass.directory q (resources p j).buffer) (target p j)

def inner (p : Parameters q L) (j : Job q.N L) :
    Routine q (CommonMSDNodeController.tagCount
      (radix q*CommonMSDChunks.chunkCount q (records j)) (3*records j)) :=
  CommonMSDNodeController.routine q p.reader (resources p j) (directory_fits q)
    (CommonMSDRecordDigits.wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
    (layout p j)

def interval (p : Parameters q L) (j : Job q.N L) :
    Routine q (CommonMSDNodeController.tagCount
      (radix q*CommonMSDChunks.chunkCount q (records j)) (3*records j)+3) :=
  CommonMSDIntervalRoutine.routine q p.reader (records j) p.source (offset j)
    (resources p j).source (target p j) (inner p j)

def node (p : Parameters q L) (j : Job q.N L) : Routine q (CommonMSDNodeTagBound.bound q (radix q)) :=
  CommonMSDRoutinePad.extend (interval p j)
    (CommonMSDNodeTagBound.node_fits q (radix q) (records j)
      (by have:=j.2.2.1.isLt;unfold records;omega))

def directories (p : Parameters q L) (j : Job q.N L) : List ℕ :=
  List.ofFn (fun i : Fin (CommonMSDChunks.chunkCount q (records j)) =>
    CommonMSDRowDirectoryBatch.target q (radix q)
      (CommonMSDNodePass.directory q (resources p j).buffer) i.val)

def components (p : Parameters q L) : Components q L (CommonMSDNodeTagBound.bound q (radix q)) where
  reader := p.reader
  normal := p.normal
  exponent := p.capacity.exponent
  source := p.source
  stack := CommonMSDGlobalAllocation.stack q p.normal q.N (radix q) L p.source
  buffer := fun j => (resources p j).buffer
  limit := fun j => (resources p j).limit
  directories := directories p
  node := node p

theorem leaf_fits (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (hn : records j≤q.height^2) :
    LeafFits (components p) j := by
  refine ⟨hn,?_,?_,?_⟩
  · exact CommonMSDGlobalAllocation.local_source_before q p.normal q.N (radix q) p.source
      (depth j) (offset j) (records j) hj
  · exact CommonMSDGlobalAllocation.local_work_fits q p.normal q.N (radix q) p.source
      (depth j) (records j) (by omega)
  · exact (resources p j).capacity

/-- Extraction needs the input's whole active interval to precede its
depth arena. The condition is numeric and follows from job containment. -/
theorem extract_fits (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) :
    CommonIntervalAdapter.Fits q (records j) p.source (offset j) (resources p j).source
      (resources p j).buffer (resources p j).limit := by
  refine ⟨?_,(resources p j).source_before,?_,(resources p j).capacity⟩
  · have h := CommonMSDGlobalAllocation.recordBlocks_mono q hj
    rw [CommonRecordEncoding.recordBlocks_eq_words] at h
    have he : 3*(offset j+records j)=3*offset j+3*records j := by ring
    rw [he] at h
    change p.source+_+2≤CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j)
    unfold CommonMSDGlobalAllocation.arena
    omega
  · have h := (resources p j).prepare_space
    omega

theorem restore_fits (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) :
    CommonIntervalAdapter.Fits q (records j) p.source (offset j) (target p j)
      (target p j+recordBlocks q (records j)+2)
      (CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j+1)) := by
  have hn : records j≤q.N := by omega
  have hd : depth j≤L := by have:=j.2.2.2.isLt;unfold depth;omega
  have hc := CommonMSDGlobalAllocation.arena_capacity q p.normal q.N (radix q) L
    p.source (depth j) p.capacity hd
  have hb := CommonMSDGlobalAllocation.recordBlocks_mono q hn
  have he := CommonMSDGlobalAllocation.arena_end q p.normal q.N (radix q) p.source (depth j)
  have hx := (extract_fits p j hj).source_before
  refine ⟨?_,le_rfl,?_,hc⟩
  · change p.source+_+2≤CommonMSDGlobalAllocation.target q p.normal q.N (radix q) p.source (depth j)
    change p.source+_+2≤CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j) at hx
    unfold CommonMSDGlobalAllocation.target CommonMSDGlobalAllocation.limit CommonMSDGlobalAllocation.buffer
    omega
  · change CommonMSDGlobalAllocation.target q p.normal q.N (radix q) p.source (depth j)+_+2≤_
    omega

def routine (p : Parameters q L) (root : Job q.N L) :=
  CommonMSDGlobalControl.routine (components p) (K:=radix q) root

end
end CodedSorting.CommonMSDGlobalComponents
end Components

section TagCapacity
/-! Coarse public polynomial bounds for all global control tags, including
unreachable jobs.  An upper word-size condition is explicit: the existing
word convention supplies address capacity, not an upper bound on w. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.CommonMSDGlobalTagCapacity
open CommonSortingNormalization CommonMSDParameters
noncomputable section

theorem height_le_input (q : Configuration) : q.height≤q.N := by
  have h:=CommonLocalDescriptorBounds.height_scaled_le_input q
  omega

theorem radix_le_input (q : Configuration) : radix q≤q.N :=
  (radix_le_height q).trans (height_le_input q)

theorem digits_le_input (q : Configuration) : q.digits≤q.N :=
  (CommonMSDDirectoryBounds.digits_le_height q).trans (height_le_input q)

theorem block_le_input (q : Configuration) : q.block≤q.N :=
  (CommonLocalRecursion.block_le_height q).trans (height_le_input q)

theorem blocks_le_words (b n : ℕ) (hb : 0<b) : PhysicalStreamCursor.blockCount b n≤n := by
  apply LayoutConversion.blockCount_minimal _ _ _ hb
  have h:=Nat.mul_le_mul_left n hb
  simpa only [Nat.mul_one] using h

theorem frameBlocks_le_input (q : Configuration) : CommonMSDStack.frameBlocks q≤q.N :=
  (blocks_le_words q.block q.digits (CommonLeafProgram.block_positive q)).trans (digits_le_input q)

theorem directoryBlocks_le_input (q : Configuration) :
    CommonMSDDirectory.blocks q (radix q)≤q.N :=
  (blocks_le_words q.block ((radix q*2)*q.digits) (CommonLeafProgram.block_positive q)).trans
    ((radix_fields q).trans (height_le_input q))

theorem readBlocks_le_input (q : Configuration) (entry : ℕ) :
    CommonMSDDirectoryRead.blocks q entry≤3*q.N := by
  have h:=blocks_le_words q.block (CommonMSDDirectoryRead.total q entry)
    (CommonLeafProgram.block_positive q)
  have hl:=Nat.mod_lt (CommonMSDDirectoryRead.offset q entry) (CommonLeafProgram.block_positive q)
  have hb:=block_le_input q
  have hd:=digits_le_input q
  change CommonMSDDirectoryRead.blocks q entry≤CommonMSDDirectoryRead.total q entry at h
  unfold CommonMSDDirectoryRead.total CommonMSDDirectoryRead.lead at h
  omega

theorem directory_rows_le (q : Configuration) (n : ℕ) (hn : n≤q.N) :
    CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q (radix q)≤q.N^2 := by
  have h:=Nat.mul_le_mul ((CommonMSDChunkRows.count_le q n).trans hn) (directoryBlocks_le_input q)
  simpa only [pow_two] using h

/-- Base K≥2 never needs more than w radix digits for a w-bit key. -/
theorem levels_le_word (q : Configuration) : CommonMSDRadixCost.depth q≤q.w := by
  apply (Nat.le_pow_iff_clog_le (show 1<radix q by have:=radix_two q;omega)).1
  exact Nat.pow_le_pow_left (radix_two q) q.w

theorem levels_succ_le (q : Configuration) (κ : ℕ) (hw : q.w≤κ*q.N) :
    CommonMSDRadixCost.depth q+1≤(κ+1)*(q.N+1) := by
  have h:=levels_le_word q
  nlinarith

theorem stack_slots_le (q : Configuration) (κ : ℕ) (hw : q.w≤κ*q.N) :
    (CommonMSDRadixCost.depth q+1)*CommonMSDStack.frameBlocks q≤(κ+1)*(q.N+1)^2 := by
  have h:=Nat.mul_le_mul (levels_succ_le q κ hw)
    ((frameBlocks_le_input q).trans (Nat.le_succ q.N))
  simpa only [Nat.succ_eq_add_one,pow_two,Nat.mul_assoc] using h

/-- The padded node tag space is a polynomial even before restricting to
reachable row/gather states. -/
theorem nodeTagBound_le (q : Configuration) (K : ℕ) (hK : K≤q.N) :
    CommonMSDNodeTagBound.bound q K≤58*(q.N+1)^5 := by
  have hF : K*q.N+1≤(q.N+1)^2 := by
    have h:=Nat.mul_le_mul_right q.N hK
    nlinarith
  have hC : 3*q.N+1≤3*(q.N+1) := by omega
  have hm:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 hF) (Nat.pow_le_pow_left hC 3)
  have h1 : 1≤(q.N+1)^5 := Nat.one_le_pow _ _ (by omega)
  calc
    CommonMSDNodeTagBound.bound q K=4+2*(K*q.N+1)*(3*q.N+1)^3 := by
      rw [CommonMSDNodeTagBound.bound,CommonMSDNodeTagBound.card_formula]
      ring
    _ ≤ 4+2*(q.N+1)^2*(3*(q.N+1))^3 := Nat.add_le_add_left hm 4
    _ = 4+54*(q.N+1)^5 := by ring
    _ ≤ 58*(q.N+1)^5 := by omega

theorem card_formula (N L A K : ℕ) :
    CommonMSDGlobalControl.tagCount N L A K=7*A*(L+1)^2*(K+1)*(N+1)^4 := by
  simp only [CommonMSDGlobalControl.tagCount,CommonMSDGlobalControl.Tag,
    CommonMSDGlobalControl.Job,Fintype.card_prod,Fintype.card_fin]
  ring

/-- A fixed degree 12 suffices for the whole tagged DFS controller.
Only the public word-size constant enters the coefficient. -/
theorem tagCount_le (q : Configuration) (κ : ℕ) (hw : q.w≤κ*q.N) :
    CommonMSDGlobalControl.tagCount q.N (CommonMSDRadixCost.depth q)
      (CommonMSDNodeTagBound.bound q (radix q)) (radix q)≤
      406*(κ+1)^2*(q.N+1)^12 := by
  have hA:=nodeTagBound_le q (radix q) (radix_le_input q)
  have hL:=levels_succ_le q κ hw
  have hK : radix q+1≤q.N+1 := Nat.add_le_add_right (radix_le_input q) 1
  rw [card_formula]
  calc
    _ ≤ 7*(58*(q.N+1)^5)*((κ+1)*(q.N+1))^2*(q.N+1)*(q.N+1)^4 := by
      gcongr
    _ = 406*(κ+1)^2*(q.N+1)^12 := by ring

end
end CodedSorting.CommonMSDGlobalTagCapacity
end TagCapacity

section Entry
/-! One input-independent whole-sort policy and its concrete initial job.
The finite instruction-space requirement is exposed as a numerical bound;
no successful run or sorting-correctness assumption is part of the policy. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.CommonMSDGlobalEntry
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalComponents CommonMSDGlobalControl
open CommonLeafProgram (Machine)
noncomputable section

abbrev levels (q : Configuration) := CommonMSDRadixCost.depth q
abbrev Parameters (q : Configuration) := CommonMSDGlobalComponents.Parameters q (levels q)

def root (q : Configuration) (n : ℕ) (hn : n≤q.N) : Job q.N (levels q) :=
  (⟨levels q,by omega⟩,0,⟨n,by omega⟩,0)

def program (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) :=
  CommonMSDGlobalComponents.routine p (root q n hn)

/-- A public stride shared by every finite control tag. -/
def stride (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) : ℕ :=
  (Finset.univ.sup (fun tag => ((program q p n hn).body tag).length))+1

def ControlCapacity (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) : Prop :=
  CommonMSDGlobalControl.tagCount q.N (levels q)
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
end CodedSorting.CommonMSDGlobalEntry
end Entry

section Execution
/-! Compile the root job's actual returning path, including its final
return-to-halt instruction, into one run of the concrete fixed policy. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.CommonMSDGlobalExecution
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalEntry CommonMSDGlobalControl
open CommonLeafProgram (Machine)
noncomputable section

theorem tag_count_capacity (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) :
    CommonMSDGlobalControl.tagCount q.N (levels q)
      (CommonMSDNodeTagBound.bound q (CommonMSDParameters.radix q)) (CommonMSDParameters.radix q)
      <(2^q.w)^q.digits := by
  have hs : 0<stride q p n hn := by unfold stride;omega
  have hmul := Nat.le_mul_of_pos_right
    (CommonMSDGlobalControl.tagCount q.N (levels q)
      (CommonMSDNodeTagBound.bound q (CommonMSDParameters.radix q)) (CommonMSDParameters.radix q)) hs
  exact (hmul.trans hc).trans_lt (CommonStaticSchedule.pc_capacity q)

theorem finish (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) (s final : Machine q) (steps charge : ℕ)
    (hp : (program q p n hn).Path (program q p n hn).entry s
      (index (returning (K:=CommonMSDParameters.radix q)
        (CommonMSDGlobalComponents.components p) (root q n hn))) final steps charge) :
    let out := ControlledNormalization.runLogical (policy q p n hn)
      (steps+1) (initial q p n hn s)
    out.1.disk=final.disk ∧ policy q p n hn out.1.ram=none ∧
      out.2=charge ∧ Fintype.card (ResidentIndex q)≤q.M := by
  let r := program q p n hn
  have hr := root_halt (K:=CommonMSDParameters.radix q)
    (CommonMSDGlobalComponents.components p) (root q n hn) (root q n hn)
    (by rfl) final
  have hpath := r.path_append hp (r.trace_toPath hr)
  have hterm : r.terminal (index (halted (K:=CommonMSDParameters.radix q)
      (CommonMSDGlobalComponents.components p) (root q n hn)))=true := by
    change (CommonMSDGlobalControl.routine (CommonMSDGlobalComponents.components p)
      (root q n hn)).terminal (index (halted (K:=CommonMSDParameters.radix q)
        (CommonMSDGlobalComponents.components p) (root q n hn)))=true
    rw [routine_terminal]
    rfl
  have ht := r.path_toTrace hpath hterm
  have hout := r.trace_run_from (stride q p n hn) (fits q p n hn hc) ht
    (initial q p n hn s) (initial_payload q p n hn s) (initial_pc q p n hn hc s)
  dsimp only
  have hd := congrArg (fun t : Machine q => t.disk) hout.1
  exact ⟨hd,hout.2.2.2,by simpa only [Nat.add_zero] using hout.2.1,resident_memory q⟩

end
end CodedSorting.CommonMSDGlobalExecution
end Execution
