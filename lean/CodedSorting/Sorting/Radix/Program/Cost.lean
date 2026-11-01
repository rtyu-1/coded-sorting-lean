import CodedSorting.Sorting.Radix.Program.Loop
import CodedSorting.Sorting.Radix.Program.Framework.Recursion

section BaseList
/-! List-valued base cases for the global recursive correctness invariant. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalBaseList
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalBase CommonRecordIntervalList
open CommonLeafProgram (Machine)
open CommonMarginTransform (wordAt)
noncomputable section
variable {q : Configuration} {L A K : ℕ}

theorem leaf_list (c : Components q L A) (j : Job q.N L) (h : LeafFits c j)
    (s : Machine q) (xs : List (KeyRecordWords.Record q.w))
    (hlen : xs.length=records j) (hx : EncodedListAt q s.disk c.source (offset j) xs) :
    EncodedListAt q (erasePC q (executeRaw q (leafCode c j) s).1).disk
      c.source (offset j) (CommonWordMSD.localSort xs) := by
  let f := recordsOfList q (records j) xs hlen
  have hf : CommonRecordInterval.EncodedAt q s.disk c.source (offset j) f :=
    (encoded_records q s.disk c.source (offset j) (records j) xs hlen).2 hx
  have hc := (leaf_correct c j h s f hf).1
  have hl := (ofFn q _ c.source (offset j) (Columnsort.sortColumn f)).2 hc
  rw [←CommonWordMSD.localSort_ofFn] at hl
  simpa only [f,ofFn_records] using hl

theorem leaf_cost (c : Components q L A) (j : Job q.N L) (h : LeafFits c j) :
    cost q (leafCode c j)≤CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q (records j) := by
  simpa only [leafProgram_code,leafProgram_charge] using (leafProgram c j h).cost_le

theorem leaf_word_frame (c : Components q L A) (j : Job q.N L) (h : LeafFits c j)
    (s : Machine q) (w : ℕ) (hfit : c.source+w/q.block<q.N^q.exponent)
    (ho : w<3*offset j ∨ 3*offset j+3*records j≤w)
    (hw : c.source+w/q.block<c.buffer j ∨ c.limit j≤c.source+w/q.block) :
    wordAt q (erasePC q (executeRaw q (leafCode c j) s).1).disk c.source w=
      wordAt q s.disk c.source w := by
  simpa only [leafProgram_code,erasePC] using (leafProgram c j h).word_frame s w hfit ho hw

theorem leaf_frame (c : Components q L A) (j : Job q.N L) (h : LeafFits c j)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (ho : a.val<c.source+3*offset j/q.block ∨
      c.source+PhysicalStreamCursor.blockCount q.block (3*offset j+3*records j)≤a.val)
    (hw : a.val<c.buffer j ∨ c.limit j≤a.val) :
    (erasePC q (executeRaw q (leafCode c j) s).1).disk a=s.disk a := by
  simpa only [leafProgram_code,erasePC] using (leafProgram c j h).frame s a ho hw

/-- One actual path and its list semantics, suitable for the recursive base case. -/
theorem small_list (c : Components q L A) (root j : Job q.N L)
    (hj : level j≠0) (h : LeafFits c j)
    (s : Machine q) (xs : List (KeyRecordWords.Record q.w))
    (hlen : xs.length=records j) (hx : EncodedListAt q s.disk c.source (offset j) xs) :
    let out := erasePC q (executeRaw q (leafCode c j) s).1
    (routine (K:=K) c root).Path (tagEquiv q.N L A K (visit c j)) s
      (tagEquiv q.N L A K (returning c j)) out
      ((leafCode c j).length+2) (cost q (leafCode c j)) ∧
    EncodedListAt q out.disk c.source (offset j) (CommonWordMSD.localSort xs) ∧
    cost q (leafCode c j)≤CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q (records j) :=
  ⟨small_path c root j hj h.1 s,leaf_list c j h s xs hlen hx,leaf_cost c j h⟩

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalBaseList
end BaseList

section Cost
/-! Quantitative refinements of the already constructed global policy.
Budgets are proof-side natural numbers; they are not controller inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalCost
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalFrame CodedSorting.Construction.Sorting.CommonMSDGlobalLoop CommonRecordIntervalList
open CommonLeafProgram (Machine)
noncomputable section
variable {q : Configuration} {L : ℕ}

def CostResult (p : Parameters q L) (root j : Job q.N L)
    (start finish : Tag q.N L (CommonMSDNodeTagBound.bound q (radix q)) (radix q))
    (s : Machine q) (ys : List (KeyRecordWords.Record q.w)) (budget : ℕ) : Prop :=
  ∃ final steps charge,
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).Path (index start) s (index finish) final steps charge ∧
    EncodedListAt q final.disk p.source (offset j) ys ∧ Frame p j s.disk final.disk ∧ charge≤budget

def CostCall (p : Parameters q L) (root j : Job q.N L) (s : Machine q)
    (ys : List (KeyRecordWords.Record q.w)) (budget : ℕ) : Prop :=
  CostResult p root j (visit (components p) j) (returning (components p) j) s ys budget

def stepCharge (q : Configuration) (n : ℕ) (k : Fin (radix q)) : ℕ :=
  CodedSorting.CommonMSDChunks.chunkCount q n*CommonMSDDirectoryRead.blocks q k.val+2*CommonMSDStack.frameBlocks q

def siblingBudget (q : Configuration) (n : ℕ) (childBudget : Fin (radix q)→ℕ) (key : ℕ) : ℕ :=
  (((List.finRange (radix q)).drop key).map (fun k=>stepCharge q n k+childBudget k)).sum

@[simp] theorem siblingBudget_done (q : Configuration) (n : ℕ) (childBudget : Fin (radix q)→ℕ) :
    siblingBudget q n childBudget (radix q)=0 := by
  have h : (List.finRange (radix q)).drop (radix q)=[] := List.drop_eq_nil_of_le (by simp)
  simp only [siblingBudget,h,List.map_nil,List.sum_nil]

theorem siblingBudget_next (q : Configuration) (n : ℕ) (childBudget : Fin (radix q)→ℕ)
    (k : Fin (radix q)) :
    siblingBudget q n childBudget k.val=stepCharge q n k+childBudget k+
      siblingBudget q n childBudget (k.val+1) := by
  unfold siblingBudget
  rw [List.drop_eq_getElem_cons (show k.val<(List.finRange (radix q)).length by simpa using k.isLt)]
  simp

theorem siblingBudget_zero (q : Configuration) (n : ℕ) (childBudget : Fin (radix q)→ℕ) :
    siblingBudget q n childBudget 0=CommonMSDGlobalControlCost.controlCharge q n+
      ((List.finRange (radix q)).map childBudget).sum := by
  simp only [siblingBudget,List.drop_zero,List.sum_map_add]
  rfl

@[simp] theorem directories_length (p : Parameters q L) (j : Job q.N L) :
    (directories p j).length=CodedSorting.CommonMSDChunks.chunkCount q (records j) := by
  simp only [directories,List.length_ofFn]

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalCost
end Cost

section NodeRun
/-! A concrete depth-allocated node execution. The terminating inner trace
is constructed from the directory-reading controller, then transported
through actual interval copies and the uniform public tag embedding. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalNodeRun
open WordControl CommonSortingNormalization CodedSorting.Construction.RecursiveParameters CommonRecordProgram
open CommonStaticSchedule CommonMSDRoutine CodedSorting.Construction.Sorting.CommonMSDGlobalControl CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CommonMSDRecordDigits
open CommonLeafProgram (Machine Disk)
open CommonRecordInterval (EncodedAt)
open CommonMarginTransform (wordAt)
noncomputable section
attribute [local irreducible] CodedSorting.Construction.Sorting.CommonLocalRecursion.build CodedSorting.Construction.Sorting.CommonMSDChunks.program
  CodedSorting.Construction.Sorting.CommonMSDNodePass.chunks CodedSorting.Construction.Sorting.CommonMSDNodePass.code CommonMSDGatherRun.observe
  CodedSorting.Construction.RecursiveParameters.Normalized CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension
  
variable {q : Configuration} {L : ℕ}

def arenaEnd (p : Parameters q L) (j : Job q.N L) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j+1)

def output (p : Parameters q L) (j : Job q.N L) (f : Records q (records j)) : Records q (records j) :=
  CommonMSDNodeContents.gatherRecords q
    (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
    (CodedSorting.CommonMSDChunks.operation q (records j) f)

theorem source_target (p : Parameters q L) (j : Job q.N L) :
    (resources p j).source+recordBlocks q (records j)+2≤target p j := by
  have hs := (resources p j).source_before
  have hw := (resources p j).directory_space
  unfold CodedSorting.Construction.Sorting.CommonMSDNodePass.directory at hw
  have ht : (resources p j).limit+2=target p j := rfl
  omega

theorem target_end (p : Parameters q L) (j : Job q.N L) :
    target p j+recordBlocks q (records j)+2≤arenaEnd p j := by
  have hn : records j≤q.N := by have:=j.2.2.1.isLt;unfold records;omega
  have hm := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.recordBlocks_mono q hn
  have he := CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_end q p.normal q.N (radix q) p.source (depth j)
  change CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target q p.normal q.N (radix q) p.source (depth j)+_+2≤_
  unfold arenaEnd
  omega

theorem limit_end (p : Parameters q L) (j : Job q.N L) :
    (resources p j).limit≤arenaEnd p j := by
  have he := target_end p j
  have ht : (resources p j).limit+2=target p j := rfl
  omega

theorem extract_fits_end (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) :
    CommonIntervalAdapter.Fits q (records j) p.source (offset j) (resources p j).source
      (resources p j).buffer (arenaEnd p j) := by
  have h := extract_fits p j hj
  exact ⟨h.source_before,h.scratch_before,h.workspace.trans (limit_end p j),
    (restore_fits p j hj).capacity⟩

/-- Restoration changes only the main-file interval. The prepared rows
and their actual on-disk directories remain available to child counting. -/
theorem restore_ready (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (s : Machine q) (f : Records q (records j))
    (hr : CodedSorting.Construction.Sorting.CommonMSDNodePass.Ready q
      (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
      (resources p j).source (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer) s.disk f) :
    CodedSorting.Construction.Sorting.CommonMSDNodePass.Ready q
      (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
      (resources p j).source (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer)
      (CommonMSDIntervalRoutine.restored q p.reader (records j) p.source (offset j) (target p j) s).disk f := by
  have hf := restore_fits p j hj
  have hs := (extract_fits p j hj).source_before
  have hb := (resources p j).source_before
  have heq (a : Fin (q.N^q.exponent)) (ha : (resources p j).source≤a.val) :
      (CommonMSDIntervalRoutine.restored q p.reader (records j) p.source (offset j) (target p j) s).disk a=s.disk a :=
    CommonMSDIntervalRoutine.restored_frame q p.reader (records j) p.source (offset j) (target p j)
      hf s a (Or.inr (by omega))
  have hentry (c : Fin (CodedSorting.CommonMSDChunks.chunkCount q (records j)))
      (k : Fin (radix q)) (field : Fin 2) :
      CommonMSDDirectory.entry q
        (CommonMSDIntervalRoutine.restored q p.reader (records j) p.source (offset j) (target p j) s).disk
        (CommonMSDRowDirectoryBatch.target q (radix q)
          (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer) c.val) k field=
      CommonMSDDirectory.entry q s.disk
        (CommonMSDRowDirectoryBatch.target q (radix q)
          (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer) c.val) k field := by
    apply CommonMSDRowDirectoryBatch.entry_of_disk_eq q
    intro a ha _
    apply heq a
    unfold CommonMSDRowDirectoryBatch.target CodedSorting.Construction.Sorting.CommonMSDNodePass.directory at ha
    omega
  refine ⟨?_,fun c k=>(hentry c k 0).trans (hr.starts c k),
    fun c k=>(hentry c k 1).trans (hr.lengths c k)⟩
  apply CommonMSDRowDirectoryBatch.encoded_of_disk_eq q f s.disk _
    (CommonIntervalAdapter.scratch_fits q (extract_fits p j hj)) hr.input
  intro a ha _
  exact heq a ha


/-- A complete concrete node call, with no inner trace or directory oracle.
Its output is the exact ordered bucket concatenation. Both boundary words
and every other recursion depth's arena are preserved. -/
theorem complete (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (hl : 0<level j) (prefixValue : ℕ)
    (s : Machine q) (f : Records q (records j))
    (hf : EncodedAt q s.disk p.source (offset j) f)
    (ho : OrdinaryList (List.ofFn f))
    (hp : CommonMSDSemantics.Prefix CommonWordMSD.key (radix q) (level j) prefixValue (List.ofFn f)) :
    ∃ finalTag final steps charge,
      (node p j).Trace (node p j).entry s finalTag final steps charge ∧
      (node p j).terminal finalTag=true ∧
      EncodedAt q final.disk p.source (offset j) (output p j f) ∧
      CodedSorting.Construction.Sorting.CommonMSDNodePass.Ready q
        (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
        (resources p j).source (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer)
        final.disk (CodedSorting.CommonMSDChunks.operation q (records j) f) ∧
      (∀ a : Fin (q.N^q.exponent),
        (a.val<p.source+3*offset j/q.block ∨
          p.source+PhysicalStreamCursor.blockCount q.block (3*offset j+3*records j)≤a.val) →
        (a.val<(resources p j).source ∨ arenaEnd p j≤a.val) → final.disk a=s.disk a) ∧
      (∀ z : ℕ,(hz : p.source+z/q.block<q.N^q.exponent) →
        (z<3*offset j ∨ 3*offset j+3*records j≤z) →
        (p.source+z/q.block<(resources p j).source ∨ arenaEnd p j≤p.source+z/q.block) →
        wordAt q final.disk p.source z=wordAt q s.disk p.source z) := by
  let sx := CommonMSDIntervalRoutine.extracted q p.reader (records j) p.source (offset j)
    (resources p j).source s
  have hsx : Encoded q sx.disk (resources p j).source f :=
    CommonMSDIntervalRoutine.extracted_correct q p.reader (records j) p.source (offset j)
      (resources p j).source (extract_fits p j hj) s f hf
  have hsep : (resources p j).limit≤target p j := by
    change (resources p j).limit≤(resources p j).limit+2
    omega
  have hcap : target p j+2*PhysicalStreamCursor.blockCount q.block (3*records j)+2≤q.N^q.exponent := by
    rw [←CommonRecordEncoding.recordBlocks_eq_words]
    exact CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.gather_capacity q p.normal q.N (radix q) L p.source
      (depth j) (records j) p.capacity (by have:=j.2.2.2.isLt;unfold depth;omega) (by omega)
  have hp' : CommonMSDSemantics.Prefix CommonWordMSD.key (radix q)
      (level j-1+1) prefixValue (List.ofFn f) := by
    simpa only [Nat.sub_add_cancel (show 1≤level j by omega)] using hp
  obtain ⟨tag,t,steps,charge,ht,hout,hready,hframe⟩ :=
    CodedSorting.Construction.Sorting.CommonMSDNodeComplete.complete q p.reader (resources p j) (directory_fits q)
      (CommonMSDRadixCost.radixPositive q) (level j-1) prefixValue (target p j) 1 sx f hsx ho hp' hsep hcap
  change (inner p j).Trace (inner p j).entry sx tag t steps charge at ht
  have hw := CommonMSDIntervalRoutine.trace q p.reader (records j) p.source (offset j)
    (resources p j).source (target p j) (inner p j) ht
  have htpad := CommonMSDRoutinePad.trace (interval p j)
    (CommonMSDNodeTagBound.node_fits q (radix q) (records j) (by omega)) hw
  have hframe' (a : Fin (q.N^q.exponent))
      (ha : a.val<(resources p j).source ∨ arenaEnd p j≤a.val) : t.disk a=sx.disk a := by
    apply hframe a
    have he := target_end p j
    omega
  refine ⟨_,CommonMSDIntervalRoutine.restored q p.reader (records j) p.source (offset j)
    (target p j) t,_,_,htpad,?_,?_,?_,?_,?_⟩
  · simp only [node,CommonMSDRoutinePad.terminal_embed,interval,CommonMSDIntervalRoutine.terminal_done]
  · exact CommonMSDIntervalRoutine.restored_correct q p.reader (records j) p.source (offset j)
      (target p j) (restore_fits p j hj) t (output p j f) hout
  · exact restore_ready p j hj t _ hready
  · intro a ha hw
    exact CommonMSDIntervalRoutine.frame q p.reader (records j) p.source (offset j)
      (resources p j).source (target p j) (extract_fits_end p j hj)
      (restore_fits p j hj) s t hframe' a ha hw
  · intro z hz ho hw
    exact CommonMSDIntervalRoutine.word_frame q p.reader (records j) p.source (offset j)
      (resources p j).source (target p j) (extract_fits_end p j hj)
      (restore_fits p j hj) s t hframe' z hz ho hw


/-- The count subsequently read by the global controller is exactly the
length of the semantic child; no external histogram is supplied. -/
theorem stored_counts (p : Parameters q L) (j : Job q.N L)
    (disk : Disk q) (f : Records q (records j)) (ho : OrdinaryList (List.ofFn f))
    (hr : CodedSorting.Construction.Sorting.CommonMSDNodePass.Ready q
      (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
      (resources p j).source (CodedSorting.Construction.Sorting.CommonMSDNodePass.directory q (resources p j).buffer)
      disk (CodedSorting.CommonMSDChunks.operation q (records j) f)) (k : Fin (radix q)) :
    CommonMSDChildCount.totalCount q disk (directories p j) k.val=
      (CommonMSDNodeSemantic.children q (radix q) (CommonMSDRadixCost.radixPositive q)
        (level j-1) f k).length := by
  unfold CommonMSDChildCount.totalCount directories
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,CommonMSDDirectoryRead.stored_entry,hr.lengths]
  exact CommonMSDNodeSemantic.child_count q (radix q) (CommonMSDRadixCost.radixPositive q)
    (level j-1) f ho k


/-- List-level node interface for the global recursion. The children and
their lengths are the existing MSD semantics; all counts come from the
persisted directories written during this very execution. -/
theorem complete_list (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (hl : 0<level j) (prefixValue : ℕ)
    (s : Machine q) (xs : List (KeyRecordWords.Record q.w))
    (hlen : xs.length=records j)
    (hx : CommonRecordIntervalList.EncodedListAt q s.disk p.source (offset j) xs)
    (ho : OrdinaryList xs)
    (hp : CommonMSDSemantics.Prefix CommonWordMSD.key (radix q) (level j) prefixValue xs) :
    let children := CommonMSDChildren.nodeChildren CommonWordMSD.key (radix q)
      (CommonMSDRadixCost.radixPositive q) q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort (level j-1) xs
    ∃ finalTag final steps charge,
      (node p j).Trace (node p j).entry s finalTag final steps charge ∧
      (node p j).terminal finalTag=true ∧
      CommonRecordIntervalList.EncodedListAt q final.disk p.source (offset j)
        ((List.finRange (radix q)).flatMap children) ∧
      (∀ k : Fin (radix q),CommonMSDChildCount.totalCount q final.disk (directories p j) k.val=
        (children k).length) ∧
      CodedSorting.Construction.Sorting.CommonMSDGlobalFrame.Frame p j s.disk final.disk := by
  let f := CommonRecordIntervalList.recordsOfList q (records j) xs hlen
  have he : List.ofFn f=xs := CommonRecordIntervalList.ofFn_records q (records j) xs hlen
  have hf : EncodedAt q s.disk p.source (offset j) f :=
    (CommonRecordIntervalList.encoded_records q s.disk p.source (offset j) (records j) xs hlen).2 hx
  have ho' : OrdinaryList (List.ofFn f) := by rw [he];exact ho
  have hp' : CommonMSDSemantics.Prefix CommonWordMSD.key (radix q) (level j) prefixValue (List.ofFn f) := by
    rw [he];exact hp
  obtain ⟨tag,t,steps,charge,ht,hterm,hout,hready,hblock,hword⟩ :=
    complete p j hj hl prefixValue s f hf ho' hp'
  refine ⟨tag,t,steps,charge,ht,hterm,?_,?_,?_⟩
  · have hout' := (CommonRecordIntervalList.ofFn q t.disk p.source (offset j) (output p j f)).2 hout
    unfold output at hout'
    rw [CommonMSDNodeSemantic.output_list q (radix q) (CommonMSDRadixCost.radixPositive q)
      (level j-1) f ho'] at hout'
    simpa only [CommonMSDNodeSemantic.children,he] using hout'
  · intro k
    simpa only [CommonMSDNodeSemantic.children,he] using stored_counts p j t.disk f ho' hready k
  · apply CodedSorting.Construction.Sorting.CommonMSDGlobalFrame.of_interval_frames p j s.disk t.disk
      (resources p j).source (arenaEnd p j) hj le_rfl _ hword hblock
    exact CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_mono q p.normal q.N (radix q) p.source
      (depth j+1) (L+1) (by have:=j.2.2.2.isLt;unfold depth;omega)

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalNodeRun
end NodeRun

section LeafFrame
/-! The actual leaf-sort execution satisfies the recursive disk frame;
all required allocation inequalities are discharged concretely. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalLeafFrame
open CommonSortingNormalization CommonStaticSchedule CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CodedSorting.Construction.Sorting.CommonMSDGlobalFrame
open CommonLeafProgram (Machine)
noncomputable section
variable {q : Configuration} {L : ℕ}

theorem buffer_after_arena (p : Parameters q L) (j : Job q.N L) :
    arena p j≤(components p).buffer j := by
  change CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j)≤
    CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer q p.normal q.N (radix q) p.source (depth j)
  unfold CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.buffer
  omega

theorem limit_before_stack (p : Parameters q L) (j : Job q.N L) :
    (components p).limit j≤stack p := by
  have h:=CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.arena_before_stack q p.normal q.N (radix q) L
    p.source (depth j) (depth_le j)
  change CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.limit q p.normal q.N (radix q) p.source (depth j)≤_
  unfold CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.target at h
  exact le_trans (by omega) h

theorem leaf_frame (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (hn : records j≤q.height^2) (s : Machine q) :
    Frame p j s.disk (erasePC q (executeRaw q (leafCode (components p) j) s).1).disk := by
  have h:=leaf_fits p j hj hn
  exact of_interval_frames p j s.disk _ ((components p).buffer j) ((components p).limit j)
    hj (buffer_after_arena p j) (limit_before_stack p j)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalBaseList.leaf_word_frame (components p) j h s)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalBaseList.leaf_frame (components p) j h s)

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalLeafFrame
end LeafFrame

section CostLoop
/-! The same physical sibling loop, retaining the exact Path charge and
bounding it by the sum of scans, disk-stack transfers, and child budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 12000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalCostLoop
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalFrame CodedSorting.Construction.Sorting.CommonMSDGlobalDirectory CommonMSDChildren
open CommonRecordIntervalList CodedSorting.Construction.Sorting.CommonMSDGlobalLoop CodedSorting.Construction.Sorting.CommonMSDGlobalCost
open CommonLeafProgram (Machine Disk)
noncomputable section
variable {q : Configuration} {L : ℕ}
/-- All siblings are processed by the same fixed controller. The only
recursive premise is the smaller-depth call proved by the outer induction. -/
theorem loop (p : Parameters q L) (root j : Job q.N L)
    (hj : offset j+records j≤q.N) (hl : 0<level j) (hd : depth j+level j≤L)
    (before after : Children q)
    (hlen : ∀ k,(after k).length=(before k).length)
    (hsize : ((List.finRange (radix q)).flatMap before).length=records j)
    (hdecode : tagCount q.N L (CommonMSDNodeTagBound.bound q (radix q)) (radix q)≤(2^q.w)^q.digits)
    (childBudget : Fin (radix q)→ℕ)
    (hchild : ∀ (k : Fin (radix q)) (s : Machine q),
      EncodedListAt q s.disk p.source (offset (childJob j before k)) (before k) →
      CostCall p root (childJob j before k) s (after k) (childBudget k))
    (key : Fin (radix q+1)) (s : Machine q)
    (hs : EncodedListAt q s.disk p.source (offset j) (stage before after key.val))
    (hcounts : DirCounts p j before s.disk) :
    CostResult p root j (counting (components p) j key (cursor before key.val))
      (returning (components p) j) s ((List.finRange (radix q)).flatMap after)
      (siblingBudget q (records j) childBudget key.val) := by
  generalize he : radix q-key.val=remaining
  induction remaining using Nat.strong_induction_on generalizing key s with
  | h remaining ih =>
    by_cases hk : key.val=radix q
    · refine ⟨erasePC q s,1,0,?_,?_,Frame.refl p j s.disk,by omega⟩
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
        obtain ⟨final,steps,charge,hpath,hencoded,hframe,hcost⟩ :=
          ih _ hnext nextKey sc hsNext hscCounts rfl
        have whole := (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hpc hpath
        refine ⟨final,_,_,whole,hencoded,(Frame.of_disk_eq hsc).trans hframe,?_⟩
        have hb := siblingBudget_next q (records j) childBudget k
        change (directories p j).length*CommonMSDDirectoryRead.blocks q key.val+charge≤_
        rw [directories_length]
        dsimp only [stepCharge] at hb
        change siblingBudget q (records j) childBudget key.val=
          CodedSorting.CommonMSDChunks.chunkCount q (records j)*CommonMSDDirectoryRead.blocks q key.val+
            2*CommonMSDStack.frameBlocks q+childBudget k+
            siblingBudget q (records j) childBudget nextKey.val at hb
        omega
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
        obtain ⟨st,childSteps,childCharge,hcall,hreturned,hchildFrame,hchildCost⟩ := hchild k sp hchildEncoded
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
        obtain ⟨final,steps,charge,htail,hencoded,hframe,hcost⟩ := ih _ hnext nextKey sr hrStage hrCounts rfl
        have hparentFrame : Frame p j sp.disk st.disk := hchildFrame.of_child
          (by rw [props.2.1];omega)
          (by rw [props.2.1,props.2.2.1];omega)
          (by rw [props.2.2.2.1];omega)
        have whole := (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hpc
          ((CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hpush
            ((CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hcall
              ((CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hpop htail)))
        refine ⟨final,_,_,whole,hencoded,?_,?_⟩
        · exact (Frame.of_disk_eq hsc).trans (hpFrame.trans
            (hparentFrame.trans ((Frame.of_disk_eq hsr).trans hframe)))
        · have hb := siblingBudget_next q (records j) childBudget k
          change (directories p j).length*CommonMSDDirectoryRead.blocks q key.val+
            (CommonMSDStack.frameBlocks q+(childCharge+(CommonMSDStack.frameBlocks q+charge)))≤_
          rw [directories_length]
          dsimp only [stepCharge] at hb
          change siblingBudget q (records j) childBudget key.val=
            CodedSorting.CommonMSDChunks.chunkCount q (records j)*CommonMSDDirectoryRead.blocks q key.val+
              2*CommonMSDStack.frameBlocks q+childBudget k+
              siblingBudget q (records j) childBudget nextKey.val at hb
          omega


end
end CodedSorting.Construction.Sorting.CommonMSDGlobalCostLoop
end CostLoop

section NodeCostRun
/-! Exact costs for the already proved, concrete interval node routine.
Determinism attaches these costs to the semantic trace used by recursion. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalNodeCostRun
open WordControl CommonSortingNormalization CodedSorting.Construction.RecursiveParameters CommonRecordProgram
open CommonStaticSchedule CommonMSDRoutine CodedSorting.Construction.Sorting.CommonMSDGlobalControl CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CommonMSDRecordDigits
open CommonLeafProgram (Machine)
open CommonRecordInterval (EncodedAt)
noncomputable section
attribute [local irreducible] CodedSorting.Construction.Sorting.CommonLocalRecursion.build CodedSorting.Construction.Sorting.CommonMSDChunks.program
  CodedSorting.Construction.Sorting.CommonMSDNodePass.chunks CodedSorting.Construction.Sorting.CommonMSDNodePass.code CommonMSDGatherRun.observe
  CodedSorting.Construction.RecursiveParameters.Normalized CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension
  
variable {q : Configuration} {L : ℕ}

def exactBudget (p : Parameters q L) (j : Job q.N L) (f : Records q (records j)) : ℕ :=
  CommonIntervalAdapter.charge q (records j) (offset j)
    (CodedSorting.Construction.Sorting.CommonMSDNodeChargeTrace.innerCharge q p.reader (resources p j) (directory_fits q)
      (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1)) (target p j) f)

/-- Construct the charged trace from the original encoded interval. The
intermediate row directories are produced by the real preparation code. -/
theorem cost_trace (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (s : Machine q) (f : Records q (records j))
    (hf : EncodedAt q s.disk p.source (offset j) f) :
    ∃ tag final steps charge,(node p j).Trace (node p j).entry s tag final steps charge ∧
      charge=exactBudget p j f := by
  let sx := CommonMSDIntervalRoutine.extracted q p.reader (records j) p.source (offset j)
    (resources p j).source s
  have hsx : Encoded q sx.disk (resources p j).source f :=
    CommonMSDIntervalRoutine.extracted_correct q p.reader (records j) p.source (offset j)
      (resources p j).source (extract_fits p j hj) s f hf
  have hsep : (resources p j).limit≤target p j := by
    change (resources p j).limit≤(resources p j).limit+2
    omega
  have hcap : target p j+2*PhysicalStreamCursor.blockCount q.block (3*records j)+2≤q.N^q.exponent := by
    rw [←CommonRecordEncoding.recordBlocks_eq_words]
    exact CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.gather_capacity q p.normal q.N (radix q) L p.source
      (depth j) (records j) p.capacity (by have:=j.2.2.2.isLt;unfold depth;omega) (by omega)
  obtain ⟨tag,t,steps,charge,ht,hcharge⟩ := CodedSorting.Construction.Sorting.CommonMSDNodeChargeTrace.complete q p.reader
    (resources p j) (directory_fits q)
    (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
    (target p j) 1 sx f hsx hsep hcap
  change (inner p j).Trace (inner p j).entry sx tag t steps charge at ht
  have hw := CommonMSDIntervalRoutine.trace q p.reader (records j) p.source (offset j)
    (resources p j).source (target p j) (inner p j) ht
  have htpad := CommonMSDRoutinePad.trace (interval p j)
    (CommonMSDNodeTagBound.node_fits q (radix q) (records j) (by omega)) hw
  refine ⟨_,_,_,_,htpad,?_⟩
  exact (CommonMSDIntervalRoutine.charge_eq q p.reader (records j) p.source (offset j)
    (resources p j).source (target p j) charge).trans
    (congrArg (CommonIntervalAdapter.charge q (records j) (offset j)) hcharge)

/-- Every terminating execution from this input has the stated I/O count. Its final state is the output used by the correctness theorem. 
-/
theorem trace_charge (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (s : Machine q) (f : Records q (records j))
    (hf : EncodedAt q s.disk p.source (offset j) f)
    {tag : Fin (CommonMSDNodeTagBound.bound q (radix q))} {final : Machine q}
    {steps charge : ℕ} (ht : (node p j).Trace (node p j).entry s tag final steps charge) :
    charge=exactBudget p j f := by
  obtain ⟨_,_,_,_,ht',hc⟩ := cost_trace p j hj s f hf
  exact (ht.charge_eq ht').trans hc


theorem exactBudget_le (p : Parameters q L) (j : Job q.N L)
    (f : Records q (records j)) (hn : q.height^2≤records j) :
    exactBudget p j f≤CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q (records j) :=
  CodedSorting.Construction.Sorting.CommonMSDNodeChargeRate.interval_le q p.reader (resources p j) (directory_fits q)
    (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
    (offset j) (target p j) f hn

/-- Quantitative bound for the same concrete trace, with the directories,
copy boundaries and both interval transports already included. -/
theorem trace_le (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (s : Machine q) (f : Records q (records j))
    (hf : EncodedAt q s.disk p.source (offset j) f)
    {tag : Fin (CommonMSDNodeTagBound.bound q (radix q))} {final : Machine q}
    {steps charge : ℕ} (ht : (node p j).Trace (node p j).entry s tag final steps charge)
    (hn : q.height^2≤records j) : charge≤CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q (records j) :=
  (trace_charge p j hj s f hf ht).le.trans (exactBudget_le p j f hn)

/-- Strengthen the existing semantic endpoint with its actual I/O bound.
The trace is selected by the original correctness theorem, and determinism
identifies its cost with the independently derived concrete budget. -/
theorem complete_list (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (hl : 0<level j) (prefixValue : ℕ)
    (s : Machine q) (xs : List (KeyRecordWords.Record q.w))
    (hlen : xs.length=records j)
    (hx : CommonRecordIntervalList.EncodedListAt q s.disk p.source (offset j) xs)
    (ho : OrdinaryList xs)
    (hp : CommonMSDSemantics.Prefix CommonWordMSD.key (radix q) (level j) prefixValue xs)
    (hlarge : q.height^2<records j) :
    let children := CommonMSDChildren.nodeChildren CommonWordMSD.key (radix q)
      (CommonMSDRadixCost.radixPositive q) q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort (level j-1) xs
    ∃ finalTag final steps charge,
      (node p j).Trace (node p j).entry s finalTag final steps charge ∧
      (node p j).terminal finalTag=true ∧
      CommonRecordIntervalList.EncodedListAt q final.disk p.source (offset j)
        ((List.finRange (radix q)).flatMap children) ∧
      (∀ k : Fin (radix q),CommonMSDChildCount.totalCount q final.disk (directories p j) k.val=
        (children k).length) ∧
      CodedSorting.Construction.Sorting.CommonMSDGlobalFrame.Frame p j s.disk final.disk ∧
      charge≤CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q (records j) := by
  obtain ⟨tag,t,steps,charge,ht,hterminal,hout,hcounts,hframe⟩ :=
    CodedSorting.Construction.Sorting.CommonMSDGlobalNodeRun.complete_list p j hj hl prefixValue s xs hlen hx ho hp
  refine ⟨tag,t,steps,charge,ht,hterminal,hout,hcounts,hframe,?_⟩
  exact trace_le p j hj s (CommonRecordIntervalList.recordsOfList q (records j) xs hlen)
    ((CommonRecordIntervalList.encoded_records q s.disk p.source (offset j) (records j) xs hlen).2 hx)
    ht hlarge.le

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalNodeCostRun
end NodeCostRun

section CostRecursion
/-! Quantitative well-founded correctness of the same single-policy DFS sort. The
induction decreases the number of remaining radix groups. Its child path
is executed between a real continuation push and the matching real pop;
no recursive sorting function is inserted into a machine instruction. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalControl CodedSorting.Construction.Sorting.CommonMSDGlobalComponents CommonMSDParameters
open CodedSorting.Construction.Sorting.CommonMSDGlobalFrame CodedSorting.Construction.Sorting.CommonMSDGlobalDirectory CommonMSDChildren
open CommonRecordIntervalList CodedSorting.Construction.Sorting.CommonMSDGlobalLoop CodedSorting.Construction.Sorting.CommonMSDGlobalCost
open CommonLeafProgram (Machine)
noncomputable section
variable {q : Configuration} {L : ℕ}

open CommonMSDGlobalRecursion

/-- The existing semantic ledger instantiated with all physical node,
leaf, and controller costs. -/
def budget (q : Configuration) (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDSemanticCost.budget CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
    (CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q)
    (fun n=>CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q n+CommonMSDGlobalControlCost.controlCharge q n) fuel xs

@[simp] theorem budget_zero (q : Configuration) (xs : List (KeyRecordWords.Record q.w)) :
    budget q 0 xs=0 := rfl

theorem budget_small (q : Configuration) (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w))
    (hl : 0<fuel) (hn : xs.length≤q.height^2) :
    budget q fuel xs=CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q xs.length := by
  cases fuel with
  | zero => omega
  | succ fuel => simp only [budget,CodedSorting.Construction.Sorting.CommonMSDSemanticCost.budget,if_pos hn]

theorem budget_large (q : Configuration) (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w))
    (hl : 0<fuel) (hn : q.height^2<xs.length) :
    budget q fuel xs=CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q xs.length+
      CommonMSDGlobalControlCost.controlCharge q xs.length+
      ((List.finRange (radix q)).map (fun k=>budget q (fuel-1) (children q (fuel-1) xs k))).sum := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [budget,CodedSorting.Construction.Sorting.CommonMSDSemanticCost.budget,if_neg (not_le.mpr hn),Nat.add_sub_cancel]
    rfl

/-- A complete recursive call of the constructed global controller.
The remaining hypotheses concern the input and finite numeric allocation;
there is no successful child-execution premise. -/
theorem complete (p : Parameters q L) (root j : Job q.N L)
    (hdecode : tagCount q.N L (CommonMSDNodeTagBound.bound q (radix q)) (radix q)≤(2^q.w)^q.digits)
    (hj : offset j+records j≤q.N) (hd : depth j+level j≤L)
    (prefixValue : ℕ) (s : Machine q) (xs : List (KeyRecordWords.Record q.w))
    (hlen : xs.length=records j) (hx : EncodedListAt q s.disk p.source (offset j) xs)
    (ho : CommonMSDRecordDigits.OrdinaryList xs)
    (hp : CommonMSDSemantics.Prefix CommonWordMSD.key (radix q) (level j) prefixValue xs) :
    CostCall p root j s (sort q (level j) xs) (budget q (level j) xs) := by
  have main : ∀ fuel,∀ (j : Job q.N L),level j=fuel →
      offset j+records j≤q.N → depth j+level j≤L →
      ∀ (prefixValue : ℕ) (s : Machine q) (xs : List (KeyRecordWords.Record q.w)),
      xs.length=records j → EncodedListAt q s.disk p.source (offset j) xs →
      CommonMSDRecordDigits.OrdinaryList xs →
      CommonMSDSemantics.Prefix CommonWordMSD.key (radix q) (level j) prefixValue xs →
      CostCall p root j s (sort q (level j) xs) (budget q (level j) xs) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro j hlevel hj hd prefixValue s xs hlen hx ho hp
      by_cases hz : level j=0
      · refine ⟨erasePC q s,1,0,?_,?_,Frame.refl p j s.disk,by omega⟩
        · exact CodedSorting.Construction.Sorting.CommonMSDGlobalBase.level_zero (components p) root j hz s
        · simpa only [hz,sort,CommonMSDSemantics.sort,erasePC] using hx
      · have hl : 0<level j := by omega
        by_cases hn : records j≤q.height^2
        · have hfit:=leaf_fits p j hj hn
          have hb:=CodedSorting.Construction.Sorting.CommonMSDGlobalBaseList.small_list (K:=radix q)
            (components p) root j hz hfit s xs hlen hx
          dsimp only at hb
          refine ⟨erasePC q (executeRaw q (leafCode (components p) j) s).1,
            (leafCode (components p) j).length+2,cost q (leafCode (components p) j),hb.1,?_,
            CodedSorting.Construction.Sorting.CommonMSDGlobalLeafFrame.leaf_frame p j hj hn s,?_⟩
          · have hsorteq : sort q (level j) xs=CommonWordMSD.localSort xs := by
              unfold sort
              simpa only [Nat.sub_add_cancel (show 1≤level j by omega)] using
                (parent_terminal CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
                  q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (level j-1) xs (by omega)).symm
            rw [hsorteq]
            exact hb.2.1
          · rw [budget_small q (level j) xs hl (by omega),hlen]
            exact hb.2.2
        · let before := children q (level j-1) xs
          let after : Children q := fun k=>sort q (level j-1) (before k)
          have hlength : ∀k,(after k).length=(before k).length := fun k=>length_sort _ _
          have hsize : ((List.finRange (radix q)).flatMap before).length=records j := by
            have h:=parent_size CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
              q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
              (CommonMSDSemantics.record_local_correct q.w) (level j-1) 0 xs
            simpa only [partial_zero,hlen] using h
          obtain ⟨nodeTag,nodeFinal,nodeSteps,nodeCharge,htrace,hterminal,hencoded,hcounts,hframe,hnodeCost⟩ :=
            CodedSorting.Construction.Sorting.CommonMSDGlobalNodeCostRun.complete_list p j hj hl prefixValue s xs hlen hx ho hp (by omega)
          change EncodedListAt q nodeFinal.disk p.source (offset j)
            ((List.finRange (radix q)).flatMap before) at hencoded
          change DirCounts p j before nodeFinal.disk at hcounts
          have hnode:=node_call (K:=radix q) (components p) root j hz (by omega)
            s nodeFinal nodeTag nodeSteps nodeCharge htrace
          have hchildren : ∀(k : Fin (radix q)) (st : Machine q),
              EncodedListAt q st.disk p.source (offset (childJob j before k)) (before k) →
              CostCall p root (childJob j before k) st (after k)
                (budget q (level j-1) (before k)) := by
            intro k st he
            have props:=CodedSorting.Construction.Sorting.CommonMSDGlobalLoop.child_properties j before k hj hl hd hsize
            have hlt : level (childJob j before k)<fuel := by rw [props.1];omega
            let f:=recordsOfList q (records j) xs hlen
            have hf : List.ofFn f=xs := ofFn_records q (records j) xs hlen
            have ho' : CommonMSDRecordDigits.OrdinaryList (List.ofFn f) := by rw [hf];exact ho
            have hp' : CommonMSDSemantics.Prefix CommonWordMSD.key (radix q)
                (level j-1+1) prefixValue (List.ofFn f) := by rw [hf];convert hp using 1 <;> omega
            have hco:=CommonMSDNodeSemantic.child_ordinary q (radix q)
              (CommonMSDRadixCost.radixPositive q) (level j-1) f ho' k
            have hcp:=CommonMSDNodeSemantic.child_prefix q (radix q)
              (CommonMSDRadixCost.radixPositive q) (level j-1) prefixValue f hp' k
            change CommonMSDRecordDigits.OrdinaryList
              (children q (level j-1) (List.ofFn f) k) at hco
            change CommonMSDSemantics.Prefix CommonWordMSD.key (radix q) (level j-1)
              (prefixValue*radix q+k.val) (children q (level j-1) (List.ofFn f) k) at hcp
            rw [hf] at hco hcp
            have hc:=ih (level (childJob j before k)) hlt (childJob j before k) rfl
              props.2.2.2.2.1 props.2.2.2.2.2 (prefixValue*radix q+k.val) st (before k)
              props.2.2.1.symm he hco (by simpa only [props.1] using hcp)
            simpa only [props.1] using hc
          have hstage : EncodedListAt q nodeFinal.disk p.source (offset j) (stage before after 0) := by
            simpa only [partial_zero] using hencoded
          obtain ⟨final,steps,charge,hloop,hout,hloopFrame,hloopCost⟩ :=
            CodedSorting.Construction.Sorting.CommonMSDGlobalCostLoop.loop p root j hj hl hd before after hlength hsize hdecode
              (fun k=>budget q (level j-1) (before k)) hchildren 0 nodeFinal hstage hcounts
          have hcursor : cursor before 0=0 := by
            apply Fin.ext
            simp only [cursor,front,List.take_zero,List.flatMap_nil,List.length_nil,bounded,Nat.zero_mod,Fin.val_zero]
          simp only [Fin.val_zero,hcursor] at hloop
          have hsort : ((List.finRange (radix q)).flatMap after)=sort q (level j) xs := by
            have h:=parent_done CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
              q.height (CodedSorting.Construction.Sorting.CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (level j-1) xs (by omega)
            simpa only [partial_done,returnedChildren,after,before,children,sort,
              Nat.sub_add_cancel (show 1≤level j by omega)] using h
          rw [hsort] at hout
          have whole := (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.routine p root).path_append hnode hloop
          refine ⟨final,_,_,whole,hout,hframe.trans hloopFrame,?_⟩
          change nodeCharge+charge≤_
          rw [budget_large q (level j) xs hl (by omega),hlen]
          simp only [Fin.val_zero,siblingBudget_zero] at hloopCost
          change charge≤CommonMSDGlobalControlCost.controlCharge q (records j)+
            ((List.finRange (radix q)).map (fun k=>budget q (level j-1) (before k))).sum at hloopCost
          change nodeCharge+charge≤CodedSorting.Construction.Sorting.CommonMSDNodeRate.nodeBudget q (records j)+
            CommonMSDGlobalControlCost.controlCharge q (records j)+
            ((List.finRange (radix q)).map (fun k=>budget q (level j-1) (before k))).sum
          omega
  exact main (level j) j rfl hj hd prefixValue s xs hlen hx ho hp

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion
end CostRecursion
