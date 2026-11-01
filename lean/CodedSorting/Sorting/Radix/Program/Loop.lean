import CodedSorting.Sorting.Radix.Program.Execution

section Frame
/-! Recursive frame invariants on the one finite disk.  Descendants may
use later arenas and later stack slots, but the interval between these
regions contains the saved ancestor continuations and is preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalFrame
open CommonSortingNormalization CommonRecordProgram CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents
open CommonLeafProgram (Disk Machine)
open CommonMarginTransform (wordAt)
noncomputable section
variable {q : Configuration} {L : ℕ}

def arena (p : Parameters q L) (j : Job q.N L) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j)

def stack (p : Parameters q L) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack q p.normal q.N (radix q) L p.source

def stackStart (p : Parameters q L) (j : Job q.N L) : ℕ :=
  CommonMSDStack.frameBase q (stack p) (depth j)

def endAddress (p : Parameters q L) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.endAddress q p.normal q.N (radix q) L p.source

/-- The main file is protected at word granularity.  All other disk
blocks are protected except the current/later arenas and current/later
stack slots.  In particular the two scratch regions are not merged. -/
structure Frame (p : Parameters q L) (j : Job q.N L) (before after : Disk q) : Prop where
  word_frame : ∀ w, w<3*q.N → (w<3*offset j ∨ 3*offset j+3*records j≤w) →
    wordAt q after p.source w=wordAt q before p.source w
  block_frame : ∀ a : Fin (q.N^q.exponent),
    (a.val<p.source ∨ p.source+recordBlocks q q.N≤a.val) →
    (a.val<arena p j ∨ stack p≤a.val) →
    (a.val<stackStart p j ∨ endAddress p≤a.val) → after a=before a

theorem depth_le (j : Job q.N L) : depth j≤L := by
  have:=j.2.2.2.isLt
  unfold depth
  omega

theorem file_before_arena (p : Parameters q L) (j : Job q.N L) :
    p.source+recordBlocks q q.N≤arena p j := by
  unfold arena CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena
  omega

theorem arena_before_stack (p : Parameters q L) (j : Job q.N L) : arena p j≤stack p := by
  exact CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_mono q p.normal q.N (radix q) p.source
    (depth j) (L+1) (by have:=depth_le j;omega)

theorem stack_before_start (p : Parameters q L) (j : Job q.N L) : stack p≤stackStart p j := by
  unfold stackStart CommonMSDStack.frameBase
  omega

theorem stack_slot_end (p : Parameters q L) (j : Job q.N L) :
    stackStart p j+CommonMSDStack.frameBlocks q≤endAddress p := by
  have hm:=Nat.mul_le_mul_right (CommonMSDStack.frameBlocks q)
    (show depth j+1≤L+1 by have:=depth_le j;omega)
  unfold stackStart CommonMSDStack.frameBase endAddress
    CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.endAddress stack
  nlinarith

theorem file_capacity (p : Parameters q L) : p.source+recordBlocks q q.N≤q.N^q.exponent := by
  have ha : p.source+recordBlocks q q.N≤stack p := by
    unfold stack CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena
    omega
  have he : stack p≤endAddress p := by
    unfold stack endAddress CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.endAddress
    omega
  exact (ha.trans he).trans p.capacity.disk

theorem word_page (p : Parameters q L) (w : ℕ) (hw : w<3*q.N) :
    p.source+w/q.block<p.source+recordBlocks q q.N := by
  have h := (PhysicalStreamCursor.cursor_live_iff q.block (3*q.N) (w/q.block)
    (CommonLeafProgram.block_positive q)).2 ((Nat.div_mul_le_self w q.block).trans_lt hw)
  rw [CommonRecordEncoding.recordBlocks_eq_words]
  omega

namespace Frame
variable {p : Parameters q L} {j parent child : Job q.N L} {a b c : Disk q}

theorem refl (p : Parameters q L) (j : Job q.N L) (a : Disk q) : Frame p j a a :=
  ⟨fun _ _ _=>rfl,fun _ _ _ _=>rfl⟩

theorem of_disk_eq (h : b=a) : Frame p j a b := by
  subst b
  exact refl p j a

theorem trans (hab : Frame p j a b) (hbc : Frame p j b c) : Frame p j a c := by
  exact ⟨fun w hw ho=>(hbc.word_frame w hw ho).trans (hab.word_frame w hw ho),
    fun x hf ha hs=>(hbc.block_frame x hf ha hs).trans (hab.block_frame x hf ha hs)⟩

/-- A child's changes are also allowed by its parent's frame. -/
theorem of_child (h : Frame p child a b)
    (hlo : offset parent≤offset child)
    (hhi : offset child+records child≤offset parent+records parent)
    (hd : depth parent≤depth child) : Frame p parent a b := by
  have ha : arena p parent≤arena p child :=
    CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_mono q p.normal q.N (radix q) p.source _ _ hd
  have hs : stackStart p parent≤stackStart p child := by
    have hm:=Nat.mul_le_mul_right (CommonMSDStack.frameBlocks q) hd
    unfold stackStart CommonMSDStack.frameBase
    omega
  refine ⟨?_,?_⟩
  · intro w hw ho
    apply h.word_frame w hw
    omega
  · intro x hf hx ht
    exact h.block_frame x hf (by omega) (by omega)

/-- Every earlier arena is unchanged; this is the ancestor-directory
invariant used while processing the next child. -/
theorem before_arena (h : Frame p j a b) (x : Fin (q.N^q.exponent))
    (hfile : p.source+recordBlocks q q.N≤x.val) (hx : x.val<arena p j) : b x=a x := by
  have ha:=arena_before_stack p j
  have hs:=stack_before_start p j
  exact h.block_frame x (Or.inr hfile) (Or.inl hx) (Or.inl (by omega))

theorem ancestor_arena (h : Frame p child a b)
    (hd : depth parent<depth child) (x : Fin (q.N^q.exponent))
    (hlo : arena p parent≤x.val)
    (hhi : x.val<CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth parent+1)) :
    b x=a x := by
  have ha:=CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_mono q p.normal q.N (radix q) p.source
    (depth parent+1) (depth child) (by omega)
  have hf:=file_before_arena p parent
  exact h.before_arena x (by omega) (by exact hhi.trans_le ha)

/-- Earlier continuation slots survive all descendant executions. -/
theorem stack_block (h : Frame p j a b) (slot : ℕ) (hd : slot<depth j)
    (x : Fin (q.N^q.exponent))
    (hx : CommonMSDStack.frameBase q (stack p) slot≤x.val ∧
      x.val<CommonMSDStack.frameBase q (stack p) slot+CommonMSDStack.frameBlocks q) :
    b x=a x := by
  have hf:=file_before_arena p j
  have ha:=arena_before_stack p j
  have hm:=Nat.mul_le_mul_right (CommonMSDStack.frameBlocks q)
    (show slot+1≤depth j by omega)
  have hxlo : stack p≤x.val := by
    unfold CommonMSDStack.frameBase at hx
    omega
  have hxhi : x.val<stackStart p j := by
    unfold stackStart CommonMSDStack.frameBase at *
    nlinarith
  exact h.block_frame x (Or.inr (by omega)) (Or.inr hxlo) (Or.inl hxhi)

theorem preserves_stack (h : Frame p j a b) (slot : ℕ) (hd : slot<depth j)
    (continuation : ℕ) (hs : CommonMSDStack.Frame q a (stack p) slot continuation) :
    CommonMSDStack.Frame q b (stack p) slot continuation := by
  have hc:=CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack_capacity q p.normal q.N (radix q) L p.source
    slot p.capacity (by have:=depth_le j;omega)
  unfold CommonMSDStack.Frame at *
  rw [CommonMSDStackFrames.storedWords_eq_of_blocks q a b (stack p) slot hc
    (fun x hx=>h.stack_block slot hd x hx)]
  exact hs

theorem preserves_saved (h : Frame p j a b) (values : Fin (depth j)→ℕ)
    (hs : CommonMSDStackFrames.Saved q a (stack p) (depth j) values) :
    CommonMSDStackFrames.Saved q b (stack p) (depth j) values := by
  intro slot
  exact h.preserves_stack slot.val slot.isLt (values slot) (hs slot)

/-- Any directory contained in an earlier arena retains both its
encoded starts and its encoded lengths. -/
theorem preserves_directory (h : Frame p child a b) {K base : ℕ}
    (hlo : p.source+recordBlocks q q.N≤base)
    (hhi : base+CommonMSDDirectory.blocks q K≤arena p child)
    (k : Fin K) (field : Fin 2) :
    CommonMSDDirectory.entry q b base k field=CommonMSDDirectory.entry q a base k field := by
  apply CommonMSDRowDirectoryBatch.entry_of_disk_eq q
  intro x hx ht
  exact h.before_arena x (by omega) (by omega)

end Frame

/-- Convert the literal interval-program frame to the recursive global
frame. The workspace lies in the arena bank, before the separate stack. -/
theorem of_interval_frames (p : Parameters q L) (j : Job q.N L)
    (before after : Disk q) (buffer limit : ℕ)
    (hj : offset j+records j≤q.N) (hb : arena p j≤buffer) (hl : limit≤stack p)
    (hw : ∀ w,p.source+w/q.block<q.N^q.exponent →
      (w<3*offset j ∨ 3*offset j+3*records j≤w) →
      (p.source+w/q.block<buffer ∨ limit≤p.source+w/q.block) →
      wordAt q after p.source w=wordAt q before p.source w)
    (hf : ∀ x : Fin (q.N^q.exponent),
      (x.val<p.source+3*offset j/q.block ∨
        p.source+PhysicalStreamCursor.blockCount q.block (3*offset j+3*records j)≤x.val) →
      (x.val<buffer ∨ limit≤x.val) →after x=before x) :
    Frame p j before after := by
  have hfile:=file_before_arena p j
  have hend : PhysicalStreamCursor.blockCount q.block (3*offset j+3*records j)≤
      recordBlocks q q.N := by
    have he : 3*(offset j+records j)=3*offset j+3*records j := by ring
    have h:=CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.recordBlocks_mono q hj
    rw [CommonRecordEncoding.recordBlocks_eq_words,he] at h
    exact h
  refine ⟨?_,?_⟩
  · intro w hw' ho
    have hp:=word_page p w hw'
    exact hw w (hp.trans_le (file_capacity p)) ho (Or.inl (by omega))
  · intro x hx ha _
    apply hf x
    · rcases hx with hx|hx
      · exact Or.inl (hx.trans_le (Nat.le_add_right _ _))
      · exact Or.inr (by omega)
    · omega

theorem of_interval_program (p : Parameters q L) (j : Job q.N L)
    {buffer limit : ℕ} {F : Records q (records j)→Records q (records j)}
    (program : CommonRecordInterval.Program q (records j) p.source (offset j) buffer limit F)
    (s : Machine q) (hj : offset j+records j≤q.N)
    (hb : arena p j≤buffer) (hl : limit≤stack p) :
    Frame p j s.disk (CommonStaticSchedule.executeRaw q program.instructions s).1.disk :=
  of_interval_frames p j _ _ buffer limit hj hb hl (program.word_frame s) (program.frame s)

/-- A push only writes the current depth's numeric continuation slot.
It is therefore a legal change for this job and preserves every ancestor. -/
theorem of_stack_write (p : Parameters q L) (j : Job q.N L) (before after : Disk q)
    (hout : ∀ x : Fin (q.N^q.exponent),x.val<stackStart p j ∨
      stackStart p j+CommonMSDStack.frameBlocks q≤x.val →after x=before x) :
    Frame p j before after := by
  have hf:=file_before_arena p j
  have ha:=arena_before_stack p j
  have hs:=stack_before_start p j
  have he:=stack_slot_end p j
  refine ⟨?_,?_⟩
  · intro w hw _
    have hp:=word_page p w hw
    have hc:=hp.trans_le (file_capacity p)
    apply CommonRecordInterval.word_congr q after before p.source w hc
    exact hout _ (Or.inl (by dsimp;omega))
  · intro x _ _ hx
    exact hout x (by omega)

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalFrame
end Frame

section ChildrenState
/-! The recursive disk invariant after each returned child. All offsets
are literal positions in one parent interval, and the actual child frame
preserves the prefix and all unvisited siblings. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalChildrenState
open CommonSortingNormalization CommonRecordIntervalList CommonMSDChildren
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CodedSorting.Construction.Sorting.CommonMSDGlobalFrame
open CommonLeafProgram (Disk)
noncomputable section
variable {q : Configuration} {L K : ℕ}

/-- The next child is already stored at the original prefix length. -/
theorem extract (disk : Disk q) (base O : ℕ)
    (before after : Fin K→List (KeyRecordWords.Record q.w))
    (hl : ∀ k,(after k).length=(before k).length) (k : Fin K)
    (h : EncodedListAt q disk base O (stage before after k.val)) :
    EncodedListAt q disk base (O+(front before k.val).length) (before k) := by
  have hc := current_context before after hl k
  rw [hc.1] at h
  have he := CommonRecordIntervalList.child q disk base O
    (front after k.val) (before k) (back before (k.val+1)) h
  simpa only [hc.2.2] using he

/-- Empty children require no disk change and no recursive call. -/
theorem empty_stage (before after : Fin K→List (KeyRecordWords.Record q.w))
    (hl : ∀ k,(after k).length=(before k).length) (k : Fin K)
    (hz : (before k).length=0) : stage before after k.val=stage before after (k.val+1) := by
  have hc := current_context before after hl k
  have hb : before k=[] := List.length_eq_zero.mp hz
  have ha : after k=[] := List.length_eq_zero.mp ((hl k).trans hz)
  rw [hc.1,hc.2.1,hb,ha]

/-- Splice one returned child into its parent using the actual global frame. -/
theorem returned (p : Parameters q L) (childJob : Job q.N L)
    (original current : Disk q) (O : ℕ)
    (before after : Fin K→List (KeyRecordWords.Record q.w))
    (hl : ∀ k,(after k).length=(before k).length) (k : Fin K)
    (hfit : O+((List.finRange K).flatMap before).length≤q.N)
    (hoff : offset childJob=O+(front before k.val).length)
    (hn : records childJob=(before k).length)
    (h : EncodedListAt q original p.source O (stage before after k.val))
    (hc : EncodedListAt q current p.source (offset childJob) (after k))
    (hf : Frame p childJob original current) :
    EncodedListAt q current p.source O (stage before after (k.val+1)) := by
  have ctx := current_context before after hl k
  have hlen := partial_length before after hl k.val
  rw [ctx.1] at h hlen
  rw [ctx.2.1]
  apply CommonRecordIntervalList.splice q original current p.source O
    (front after k.val) (before k) (back before (k.val+1)) (after k) (hl k) h
  · simpa only [hoff,ctx.2.2] using hc
  · intro w hw hw' ho
    apply hf.word_frame w
    · rw [hlen] at hw'
      omega
    · rw [hoff,hn]
      simpa only [ctx.2.2] using ho

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalChildrenState
end ChildrenState

section Directory
/-! The child's count is read from the persistent parent directory. These
lemmas protect that directory across deeper calls and stack writes, and
discharge the numeric bounds of the real counting scan. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalDirectory
open CommonSortingNormalization CommonRecordProgram CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CodedSorting.Construction.Sorting.CommonMSDGlobalFrame
open CommonLeafProgram (Disk)
noncomputable section
variable {q : Configuration} {L : ℕ}

def DirCounts (p : Parameters q L) (j : Job q.N L)
    (children : Fin (radix q)→List (KeyRecordWords.Record q.w)) (disk : Disk q) : Prop :=
  ∀ k : Fin (radix q),CommonMSDChildCount.totalCount q disk (directories p j) k.val=(children k).length

theorem directory_bounds (p : Parameters q L) (j : Job q.N L) (target : ℕ)
    (ht : target∈directories p j) :
    arena p j≤target ∧ target+CommonMSDDirectory.blocks q (radix q)≤(resources p j).limit := by
  obtain ⟨row,rfl⟩ := List.mem_ofFn.mp ht
  have he := CommonMSDRowDirectoryBatch.target_end q
    (K:=radix q) (base:=CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer) row
  refine ⟨?_,he.trans (resources p j).directory_space⟩
  unfold CommonMSDRowDirectoryBatch.target CodedSorting.Construction.Sorting.CommonMSDNodePass.directory
  change arena p j≤CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer q p.normal q.N (radix q) p.source (depth j)+_+_
  unfold CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer arena
  omega

theorem limit_before_next (p : Parameters q L) (j : Job q.N L) :
    (resources p j).limit≤CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j+1) := by
  have h := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_end q p.normal q.N (radix q) p.source (depth j)
  change CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit q p.normal q.N (radix q) p.source (depth j)≤_
  unfold CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target at h
  omega

theorem limit_before_stack (p : Parameters q L) (j : Job q.N L) :
    (resources p j).limit≤stack p :=
  (limit_before_next p j).trans (CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_mono q p.normal q.N
    (radix q) p.source (depth j+1) (L+1) (by have:=depth_le j;omega))

theorem count_congr (p : Parameters q L) (j : Job q.N L) (before after : Disk q)
    (h : ∀ target∈directories p j,∀ k : Fin (radix q),
      CommonMSDDirectory.entry q after target k 1=CommonMSDDirectory.entry q before target k 1)
    (k : Fin (radix q)) :
    CommonMSDChildCount.totalCount q after (directories p j) k.val=
      CommonMSDChildCount.totalCount q before (directories p j) k.val := by
  unfold CommonMSDChildCount.totalCount
  congr 1
  apply List.map_congr_left
  intro target ht
  simp only [CommonMSDDirectoryRead.stored_entry]
  exact h target ht k

theorem child_preserves (p : Parameters q L) (j child : Job q.N L)
    (before after : Disk q) (hf : Frame p child before after) (hd : depth j<depth child)
    (k : Fin (radix q)) :
    CommonMSDChildCount.totalCount q after (directories p j) k.val=
      CommonMSDChildCount.totalCount q before (directories p j) k.val := by
  apply count_congr p j before after
  intro target ht k
  have hb := directory_bounds p j target ht
  have hc := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_mono q p.normal q.N (radix q) p.source
    (depth j+1) (depth child) (by omega)
  apply hf.preserves_directory
  · exact (file_before_arena p j).trans hb.1
  · exact (hb.2.trans (limit_before_next p j)).trans hc

theorem stack_write_preserves (p : Parameters q L) (j : Job q.N L) (before after : Disk q)
    (hf : ∀ a : Fin (q.N^q.exponent),a.val<stack p → after a=before a)
    (k : Fin (radix q)) :
    CommonMSDChildCount.totalCount q after (directories p j) k.val=
      CommonMSDChildCount.totalCount q before (directories p j) k.val := by
  apply count_congr p j before after
  intro target ht k
  have hb := (directory_bounds p j target ht).2.trans (limit_before_stack p j)
  apply CommonMSDRowDirectoryBatch.entry_of_disk_eq q before after
  intro a _ ha
  exact hf a (ha.trans_le hb)

theorem DirCounts.child (p : Parameters q L) (j child : Job q.N L)
    (children : Fin (radix q)→List (KeyRecordWords.Record q.w)) (before after : Disk q)
    (hc : DirCounts p j children before) (hf : Frame p child before after)
    (hd : depth j<depth child) : DirCounts p j children after := by
  intro k
  rw [child_preserves p j child before after hf hd k]
  exact hc k

theorem DirCounts.stack_write (p : Parameters q L) (j : Job q.N L)
    (children : Fin (radix q)→List (KeyRecordWords.Record q.w)) (before after : Disk q)
    (hc : DirCounts p j children before)
    (hf : ∀ a : Fin (q.N^q.exponent),a.val<stack p → after a=before a) :
    DirCounts p j children after := by
  intro k
  rw [stack_write_preserves p j before after hf k]
  exact hc k

theorem scanner_fits (p : Parameters q L) (j : Job q.N L) (k : Fin (radix q)) :
    ∀ target∈directories p j,CommonMSDDirectoryRead.base q target k.val+
      CommonMSDDirectoryRead.blocks q k.val≤q.N^q.exponent := by
  intro target ht
  exact CommonMSDDirectoryBounds.read_inside_directory q target (radix q) k
    ((directory_bounds p j target ht).2.trans (resources p j).capacity)

theorem counter_fits (p : Parameters q L) (j : Job q.N L)
    (children : Fin (radix q)→List (KeyRecordWords.Record q.w)) (disk : Disk q)
    (hc : DirCounts p j children disk) (k : Fin (radix q)) (hn : (children k).length≤q.N) :
    CommonMSDChildCount.totalCount q disk (directories p j) k.val<(2^q.w)^q.digits := by
  rw [hc k]
  have hp : q.N≤q.N^q.exponent := by
    have h := Nat.pow_le_pow_right (show 0<q.N by have:=q.input_large;omega) q.exponent_pos
    simpa only [pow_one] using h
  exact (hn.trans hp).trans_lt (CommonStaticSchedule.pc_capacity q)

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalDirectory
end Directory

section Loop
/-! The actual DFS sibling loop. The inductive child-call premise is
instantiated by the strictly smaller digit-depth induction in GlobalSort;
it is never supplied to the controller or compiled into a CPU operation. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 12000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalLoop
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalFrame CodedSorting.Construction.Sorting.CommonMSDGlobalDirectory CommonMSDChildren
open CommonRecordIntervalList
open CommonLeafProgram (Machine Disk)
noncomputable section
variable {q : Configuration} {L : ℕ}

abbrev Children (q : Configuration) := Fin (radix q)→List (KeyRecordWords.Record q.w)

def cursor (before : Children q) (k : ℕ) : Fin (q.N+1) := bounded q.N (front before k).length

def childJob (j : Job q.N L) (before : Children q) (k : Fin (radix q)) : Job q.N L :=
  child j (cursor before k.val) (bounded q.N (before k).length)

def Result (p : Parameters q L) (root j : Job q.N L)
    (start finish : Tag q.N L (CommonMSDNodeTagBound.bound q (radix q)) (radix q))
    (s : Machine q) (ys : List (KeyRecordWords.Record q.w)) : Prop :=
  ∃ final steps charge,
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).Path (index start) s (index finish) final steps charge ∧
    EncodedListAt q final.disk p.source (offset j) ys ∧ Frame p j s.disk final.disk

def Call (p : Parameters q L) (root j : Job q.N L) (s : Machine q)
    (ys : List (KeyRecordWords.Record q.w)) : Prop :=
  Result p root j (visit (components p) j) (returning (components p) j) s ys

theorem prefix_le (before : Children q) (k : ℕ) :
    (front before k).length≤((List.finRange (radix q)).flatMap before).length := by
  have h := partial_length before before (fun _=>rfl) k
  simp only [stage,List.length_append] at h
  omega

theorem cursor_val (before : Children q) (k : ℕ)
    (h : ((List.finRange (radix q)).flatMap before).length≤q.N) :
    (cursor before k).val=(front before k).length := by
  exact bounded_val ((prefix_le before k).trans h)

theorem child_properties (j : Job q.N L) (before : Children q) (k : Fin (radix q))
    (hj : offset j+records j≤q.N) (hl : 0<level j) (hd : depth j+level j≤L)
    (hn : ((List.finRange (radix q)).flatMap before).length=records j) :
    level (childJob j before k)=level j-1 ∧
    offset (childJob j before k)=offset j+(front before k.val).length ∧
    records (childJob j before k)=(before k).length ∧
    depth (childJob j before k)=depth j+1 ∧
    offset (childJob j before k)+records (childJob j before k)≤q.N ∧
    depth (childJob j before k)+level (childJob j before k)≤L := by
  have hk:=child_fits before k
  rw [hn] at hk
  have hc : (before k).length≤q.N := by omega
  have hv := cursor_val before k.val (by omega)
  simpa only [childJob,hv,bounded_val hc] using
    CodedSorting.Construction.Sorting.CommonMSDGlobalControl.child_properties j (cursor before k.val) (bounded q.N (before k).length)
      hj hl hd (by rw [hv,bounded_val hc];exact hk)

/-- A stack write preserves every record, including the current job. -/
theorem stack_data (p : Parameters q L) (j : Job q.N L) (before after : Disk q)
    (hout : ∀ a : Fin (q.N^q.exponent),a.val<stackStart p j ∨
      stackStart p j+CommonMSDStack.frameBlocks q≤a.val →after a=before a)
    (O : ℕ) (xs : List (KeyRecordWords.Record q.w)) (hfit : O+xs.length≤q.N)
    (hx : EncodedListAt q before p.source O xs) : EncodedListAt q after p.source O xs := by
  apply CommonRecordIntervalList.congr q before after p.source O xs hx
  intro w hw he
  have hp:=word_page p w (by omega)
  have hc:=hp.trans_le (file_capacity p)
  have hf:=file_before_arena p j
  have ha:=arena_before_stack p j
  have hs:=stack_before_start p j
  apply CommonRecordInterval.word_congr q after before p.source w hc
  exact hout _ (Or.inl (by dsimp;omega))

/-- All siblings are processed by the same fixed controller. The only
recursive premise is the smaller-depth call proved by the outer induction. -/
theorem loop (p : Parameters q L) (root j : Job q.N L)
    (hj : offset j+records j≤q.N) (hl : 0<level j) (hd : depth j+level j≤L)
    (before after : Children q)
    (hlen : ∀ k,(after k).length=(before k).length)
    (hsize : ((List.finRange (radix q)).flatMap before).length=records j)
    (hdecode : tagCount q.N L (CommonMSDNodeTagBound.bound q (radix q)) (radix q)≤(2^q.w)^q.digits)
    (hchild : ∀ (k : Fin (radix q)) (s : Machine q),
      EncodedListAt q s.disk p.source (offset (childJob j before k)) (before k) →
      Call p root (childJob j before k) s (after k))
    (key : Fin (radix q+1)) (s : Machine q)
    (hs : EncodedListAt q s.disk p.source (offset j) (stage before after key.val))
    (hcounts : DirCounts p j before s.disk) :
    Result p root j (counting (components p) j key (cursor before key.val))
      (returning (components p) j) s ((List.finRange (radix q)).flatMap after) := by
  generalize he : radix q-key.val=remaining
  induction remaining using Nat.strong_induction_on generalizing key s with
  | h remaining ih =>
    by_cases hk : key.val=radix q
    · refine ⟨erasePC q s,1,0,?_,?_,Frame.refl p j s.disk⟩
      · exact count_done (components p) root j key (cursor before key.val) hk s
      · simpa only [hk,partial_done,erasePC] using hs
    · have hklt : key.val<radix q := by have:=key.isLt;omega
      let k : Fin (radix q) := ⟨key.val,hklt⟩
      have hfitChild:=child_fits before k
      rw [hsize] at hfitChild
      have hnN : (before k).length≤q.N := by omega
      let amount : Fin (q.N+1) := bounded q.N (before k).length
      have hv : amount.val=(before k).length := bounded_val hnN
      have hcursor := cursor_val before key.val (by omega)
      have hcount : CommonMSDChildCount.totalCount q s.disk (directories p j) key.val=(before k).length :=
        hcounts k
      obtain ⟨sc,hpc,hsc⟩ := count_path (components p) root j key (cursor before key.val) hklt s
        (scanner_fits p j k) (counter_fits p j before s.disk hcounts k hnN)
      change (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).Path _ _ _ _ _ _ at hpc
      simp only [show (components p).directories j=directories p j from rfl,hcount] at hpc
      change (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).Path _ _
        (index (if amount.val=0 then resume (components p) j key (cursor before key.val) amount
          else pushing (components p) j key (cursor before key.val) amount)) _ _ _ at hpc
      let nextKey : Fin (radix q+1) := ⟨key.val+1,by omega⟩
      have hspan : (cursor before key.val).val+amount.val≤q.N := by
        rw [hcursor,hv]
        exact hfitChild.trans (by omega)
      have hresume : resume (components p) j key (cursor before key.val) amount=
          counting (components p) j nextKey (cursor before nextKey.val) := by
        unfold resume
        congr 1
        · apply Fin.ext
          exact bounded_val (by omega)
        · apply Fin.ext
          have hpref := prefix_next before k
          have hprefLen := congrArg List.length hpref
          simp only [List.length_append] at hprefLen
          have hcNext := cursor_val before nextKey.val (by omega)
          rw [bounded_val hspan,
            hcursor,hv,hcNext]
          exact hprefLen.symm
      have hnext : radix q-nextKey.val<remaining := by dsimp only [nextKey];omega
      have hscStage : EncodedListAt q sc.disk p.source (offset j) (stage before after key.val) := by
        simpa only [hsc] using hs
      have hscCounts : DirCounts p j before sc.disk := by simpa only [hsc] using hcounts
      by_cases hz : amount.val=0
      · rw [if_pos hz,hresume] at hpc
        have hstage := CodedSorting.Construction.Sorting.CommonMSDGlobalChildrenState.empty_stage before after hlen k (by rw [←hv];exact hz)
        have hsNext : EncodedListAt q sc.disk p.source (offset j) (stage before after nextKey.val) := by
          rw [←hstage]
          exact hscStage
        obtain ⟨final,steps,charge,hpath,hencoded,hframe⟩ :=
          ih _ hnext nextKey sc hsNext hscCounts rfl
        refine ⟨final,_,_,(CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hpc hpath,hencoded,?_⟩
        exact (Frame.of_disk_eq hsc).trans hframe
      · rw [if_neg hz] at hpc
        have hstack : CommonMSDStack.frameBase q (components p).stack (depth j)+
            CommonMSDStack.frameBlocks q≤q.N^q.exponent := by
          exact CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.stack_capacity q p.normal q.N (radix q) L p.source
            (depth j) p.capacity (depth_le j)
        obtain ⟨sp,hpush,hsaved,houtside⟩ := push_path (components p) root j key
          (cursor before key.val) amount sc hstack
        have houtside : ∀ a : Fin (q.N^q.exponent),a.val<stackStart p j ∨
            stackStart p j+CommonMSDStack.frameBlocks q≤a.val →sp.disk a=sc.disk a := houtside
        have hpFrame : Frame p j sc.disk sp.disk := of_stack_write p j sc.disk sp.disk houtside
        have hpStage : EncodedListAt q sp.disk p.source (offset j) (stage before after key.val) :=
          stack_data p j sc.disk sp.disk houtside (offset j) _
            (by rw [partial_length before after hlen,hsize];exact hj) hscStage
        have hpCounts : DirCounts p j before sp.disk := DirCounts.stack_write p j before _ _ hscCounts (by
          intro a ha
          exact houtside a (Or.inl (ha.trans_le (stack_before_start p j))))
        have props:=child_properties j before k hj hl hd hsize
        have hchildEq : child j (cursor before key.val) amount=childJob j before k := rfl
        rw [hchildEq] at hpush
        have hchildEncoded : EncodedListAt q sp.disk p.source (offset (childJob j before k)) (before k) := by
          rw [props.2.1]
          exact CodedSorting.Construction.Sorting.CommonMSDGlobalChildrenState.extract sp.disk p.source (offset j) before after hlen k hpStage
        obtain ⟨st,childSteps,childCharge,hcall,hreturned,hchildFrame⟩ := hchild k sp hchildEncoded
        have hsaved' := hchildFrame.preserves_stack (depth j) (by rw [props.2.2.2.1];omega)
          (index (resume (components p) j key (cursor before key.val) amount)).val hsaved
        have hdep : depth (childJob j before k)-1=depth j := by rw [props.2.2.2.1];omega
        have hpopfit : CommonMSDStack.frameBase q (components p).stack (depth (childJob j before k)-1)+
            CommonMSDStack.frameBlocks q≤q.N^q.exponent := by rw [hdep];exact hstack
        have hsavedPop : CommonMSDStack.Frame q st.disk (components p).stack
            (depth (childJob j before k)-1) (index (resume (components p) j key (cursor before key.val) amount)).val := by
          rw [hdep];exact hsaved'
        obtain ⟨sr,hpop,hsr⟩ := pop_path (components p) root (childJob j before k)
          (resume (components p) j key (cursor before key.val) amount) st
          (by rw [props.2.2.2.1];omega) hpopfit hsavedPop
          ((index (resume (components p) j key (cursor before key.val) amount)).isLt.trans_le hdecode)
        rw [hresume] at hpop
        have htStage : EncodedListAt q st.disk p.source (offset j) (stage before after nextKey.val) := by
          exact CodedSorting.Construction.Sorting.CommonMSDGlobalChildrenState.returned p (childJob j before k) sp.disk st.disk
            (offset j) before after hlen k (by rw [hsize];exact hj) props.2.1 props.2.2.1
            hpStage hreturned hchildFrame
        have htCounts : DirCounts p j before st.disk := DirCounts.child p j (childJob j before k)
          before _ _ hpCounts hchildFrame (by rw [props.2.2.2.1];omega)
        have hrStage : EncodedListAt q sr.disk p.source (offset j) (stage before after nextKey.val) := by
          simpa only [hsr] using htStage
        have hrCounts : DirCounts p j before sr.disk := by simpa only [hsr] using htCounts
        obtain ⟨final,steps,charge,htail,hencoded,hframe⟩ := ih _ hnext nextKey sr hrStage hrCounts rfl
        have hparentFrame : Frame p j sp.disk st.disk := hchildFrame.of_child
          (by rw [props.2.1];omega)
          (by rw [props.2.1,props.2.2.1];omega)
          (by rw [props.2.2.2.1];omega)
        have whole := (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hpc
          ((CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hpush
            ((CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hcall
              ((CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hpop htail)))
        refine ⟨final,_,_,whole,hencoded,?_⟩
        exact (Frame.of_disk_eq hsc).trans (hpFrame.trans
          (hparentFrame.trans ((Frame.of_disk_eq hsr).trans hframe)))


end
end CodedSorting.Construction.Sorting.CommonMSDGlobalLoop
end Loop
