import CodedSorting.Sorting.Radix.Program.Framework.Cost

section BaseList
/-! List-valued base cases for the global recursive correctness invariant. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.CommonMSDGlobalBaseList
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalControl CommonMSDGlobalBase CommonRecordIntervalList
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
    cost q (leafCode c j)≤CommonMSDIntervalLocal.charge q (records j) := by
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
    cost q (leafCode c j)≤CommonMSDIntervalLocal.charge q (records j) :=
  ⟨small_path c root j hj h.1 s,leaf_list c j h s xs hlen hx,leaf_cost c j h⟩

end
end CodedSorting.CommonMSDGlobalBaseList
end BaseList

section NodeRun
/-! A concrete depth-allocated node execution. The terminating inner trace
is constructed from the directory-reading controller, then transported
through actual interval copies and the uniform public tag embedding. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDGlobalNodeRun
open WordControl CommonSortingNormalization CommonPrunedParameters CommonRecordProgram
open CommonStaticSchedule CommonMSDRoutine CommonMSDGlobalControl CommonMSDParameters
open CommonMSDGlobalComponents CommonMSDRecordDigits
open CommonLeafProgram (Machine Disk)
open CommonRecordInterval (EncodedAt)
open CommonMarginTransform (wordAt)
noncomputable section
attribute [local irreducible] CommonLocalRecursion.build CommonMSDChunks.program
  CommonMSDNodePass.chunks CommonMSDNodePass.code CommonMSDGatherRun.observe
  CommonPrunedParameters.Normalized CodedSorting.Parameters.W CodedSorting.Parameters.m
  RecursiveExchange.radix
variable {q : Configuration} {L : ℕ}

def arenaEnd (p : Parameters q L) (j : Job q.N L) : ℕ :=
  CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j+1)

def output (p : Parameters q L) (j : Job q.N L) (f : Records q (records j)) : Records q (records j) :=
  CommonMSDNodeContents.gatherRecords q
    (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
    (CommonMSDChunks.operation q (records j) f)

theorem source_target (p : Parameters q L) (j : Job q.N L) :
    (resources p j).source+recordBlocks q (records j)+2≤target p j := by
  have hs := (resources p j).source_before
  have hw := (resources p j).directory_space
  unfold CommonMSDNodePass.directory at hw
  have ht : (resources p j).limit+2=target p j := rfl
  omega

theorem target_end (p : Parameters q L) (j : Job q.N L) :
    target p j+recordBlocks q (records j)+2≤arenaEnd p j := by
  have hn : records j≤q.N := by have:=j.2.2.1.isLt;unfold records;omega
  have hm := CommonMSDGlobalAllocation.recordBlocks_mono q hn
  have he := CommonMSDGlobalAllocation.arena_end q p.normal q.N (radix q) p.source (depth j)
  change CommonMSDGlobalAllocation.target q p.normal q.N (radix q) p.source (depth j)+_+2≤_
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
    (hr : CommonMSDNodePass.Ready q
      (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
      (resources p j).source (CommonMSDNodePass.directory q (resources p j).buffer) s.disk f) :
    CommonMSDNodePass.Ready q
      (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
      (resources p j).source (CommonMSDNodePass.directory q (resources p j).buffer)
      (CommonMSDIntervalRoutine.restored q p.reader (records j) p.source (offset j) (target p j) s).disk f := by
  have hf := restore_fits p j hj
  have hs := (extract_fits p j hj).source_before
  have hb := (resources p j).source_before
  have heq (a : Fin (q.N^q.exponent)) (ha : (resources p j).source≤a.val) :
      (CommonMSDIntervalRoutine.restored q p.reader (records j) p.source (offset j) (target p j) s).disk a=s.disk a :=
    CommonMSDIntervalRoutine.restored_frame q p.reader (records j) p.source (offset j) (target p j)
      hf s a (Or.inr (by omega))
  have hentry (c : Fin (CommonMSDChunks.chunkCount q (records j)))
      (k : Fin (radix q)) (field : Fin 2) :
      CommonMSDDirectory.entry q
        (CommonMSDIntervalRoutine.restored q p.reader (records j) p.source (offset j) (target p j) s).disk
        (CommonMSDRowDirectoryBatch.target q (radix q)
          (CommonMSDNodePass.directory q (resources p j).buffer) c.val) k field=
      CommonMSDDirectory.entry q s.disk
        (CommonMSDRowDirectoryBatch.target q (radix q)
          (CommonMSDNodePass.directory q (resources p j).buffer) c.val) k field := by
    apply CommonMSDRowDirectoryBatch.entry_of_disk_eq q
    intro a ha _
    apply heq a
    unfold CommonMSDRowDirectoryBatch.target CommonMSDNodePass.directory at ha
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
      CommonMSDNodePass.Ready q
        (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
        (resources p j).source (CommonMSDNodePass.directory q (resources p j).buffer)
        final.disk (CommonMSDChunks.operation q (records j) f) ∧
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
    exact CommonMSDGlobalAllocation.gather_capacity q p.normal q.N (radix q) L p.source
      (depth j) (records j) p.capacity (by have:=j.2.2.2.isLt;unfold depth;omega) (by omega)
  have hp' : CommonMSDSemantics.Prefix CommonWordMSD.key (radix q)
      (level j-1+1) prefixValue (List.ofFn f) := by
    simpa only [Nat.sub_add_cancel (show 1≤level j by omega)] using hp
  obtain ⟨tag,t,steps,charge,ht,hout,hready,hframe⟩ :=
    CommonMSDNodeComplete.complete q p.reader (resources p j) (directory_fits q)
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
    (hr : CommonMSDNodePass.Ready q
      (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
      (resources p j).source (CommonMSDNodePass.directory q (resources p j).buffer)
      disk (CommonMSDChunks.operation q (records j) f)) (k : Fin (radix q)) :
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
      (CommonMSDRadixCost.radixPositive q) q.height (CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort (level j-1) xs
    ∃ finalTag final steps charge,
      (node p j).Trace (node p j).entry s finalTag final steps charge ∧
      (node p j).terminal finalTag=true ∧
      CommonRecordIntervalList.EncodedListAt q final.disk p.source (offset j)
        ((List.finRange (radix q)).flatMap children) ∧
      (∀ k : Fin (radix q),CommonMSDChildCount.totalCount q final.disk (directories p j) k.val=
        (children k).length) ∧
      CommonMSDGlobalFrame.Frame p j s.disk final.disk := by
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
  · apply CommonMSDGlobalFrame.of_interval_frames p j s.disk t.disk
      (resources p j).source (arenaEnd p j) hj le_rfl _ hword hblock
    exact CommonMSDGlobalAllocation.arena_mono q p.normal q.N (radix q) p.source
      (depth j+1) (L+1) (by have:=j.2.2.2.isLt;unfold depth;omega)

end
end CodedSorting.CommonMSDGlobalNodeRun
end NodeRun

section LeafFrame
/-! The actual leaf-sort execution satisfies the recursive disk frame;
all required allocation inequalities are discharged concretely. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDGlobalLeafFrame
open CommonSortingNormalization CommonStaticSchedule CommonMSDParameters
open CommonMSDGlobalControl CommonMSDGlobalComponents CommonMSDGlobalFrame
open CommonLeafProgram (Machine)
noncomputable section
variable {q : Configuration} {L : ℕ}

theorem buffer_after_arena (p : Parameters q L) (j : Job q.N L) :
    arena p j≤(components p).buffer j := by
  change CommonMSDGlobalAllocation.arena q p.normal q.N (radix q) p.source (depth j)≤
    CommonMSDGlobalAllocation.buffer q p.normal q.N (radix q) p.source (depth j)
  unfold CommonMSDGlobalAllocation.buffer
  omega

theorem limit_before_stack (p : Parameters q L) (j : Job q.N L) :
    (components p).limit j≤stack p := by
  have h:=CommonMSDGlobalAllocation.arena_before_stack q p.normal q.N (radix q) L
    p.source (depth j) (depth_le j)
  change CommonMSDGlobalAllocation.limit q p.normal q.N (radix q) p.source (depth j)≤_
  unfold CommonMSDGlobalAllocation.target at h
  exact le_trans (by omega) h

theorem leaf_frame (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (hn : records j≤q.height^2) (s : Machine q) :
    Frame p j s.disk (erasePC q (executeRaw q (leafCode (components p) j) s).1).disk := by
  have h:=leaf_fits p j hj hn
  exact of_interval_frames p j s.disk _ ((components p).buffer j) ((components p).limit j)
    hj (buffer_after_arena p j) (limit_before_stack p j)
    (CommonMSDGlobalBaseList.leaf_word_frame (components p) j h s)
    (CommonMSDGlobalBaseList.leaf_frame (components p) j h s)

end
end CodedSorting.CommonMSDGlobalLeafFrame
end LeafFrame

section NodeCostRun
/-! Exact costs for the already proved, concrete interval node routine.
Determinism attaches these costs to the semantic trace used by recursion. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDGlobalNodeCostRun
open WordControl CommonSortingNormalization CommonPrunedParameters CommonRecordProgram
open CommonStaticSchedule CommonMSDRoutine CommonMSDGlobalControl CommonMSDParameters
open CommonMSDGlobalComponents CommonMSDRecordDigits
open CommonLeafProgram (Machine)
open CommonRecordInterval (EncodedAt)
noncomputable section
attribute [local irreducible] CommonLocalRecursion.build CommonMSDChunks.program
  CommonMSDNodePass.chunks CommonMSDNodePass.code CommonMSDGatherRun.observe
  CommonPrunedParameters.Normalized CodedSorting.Parameters.W CodedSorting.Parameters.m
  RecursiveExchange.radix
variable {q : Configuration} {L : ℕ}

def exactBudget (p : Parameters q L) (j : Job q.N L) (f : Records q (records j)) : ℕ :=
  CommonIntervalAdapter.charge q (records j) (offset j)
    (CommonMSDNodeChargeTrace.innerCharge q p.reader (resources p j) (directory_fits q)
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
    exact CommonMSDGlobalAllocation.gather_capacity q p.normal q.N (radix q) L p.source
      (depth j) (records j) p.capacity (by have:=j.2.2.2.isLt;unfold depth;omega) (by omega)
  obtain ⟨tag,t,steps,charge,ht,hcharge⟩ := CommonMSDNodeChargeTrace.complete q p.reader
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
    exactBudget p j f≤CommonMSDNodeRate.nodeBudget q (records j) :=
  CommonMSDNodeChargeRate.interval_le q p.reader (resources p j) (directory_fits q)
    (wordDigit q (radix q) (CommonMSDRadixCost.radixPositive q) (level j-1))
    (offset j) (target p j) f hn

/-- Quantitative bound for the same concrete trace, with the directories,
copy boundaries and both interval transports already included. -/
theorem trace_le (p : Parameters q L) (j : Job q.N L)
    (hj : offset j+records j≤q.N) (s : Machine q) (f : Records q (records j))
    (hf : EncodedAt q s.disk p.source (offset j) f)
    {tag : Fin (CommonMSDNodeTagBound.bound q (radix q))} {final : Machine q}
    {steps charge : ℕ} (ht : (node p j).Trace (node p j).entry s tag final steps charge)
    (hn : q.height^2≤records j) : charge≤CommonMSDNodeRate.nodeBudget q (records j) :=
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
      (CommonMSDRadixCost.radixPositive q) q.height (CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort (level j-1) xs
    ∃ finalTag final steps charge,
      (node p j).Trace (node p j).entry s finalTag final steps charge ∧
      (node p j).terminal finalTag=true ∧
      CommonRecordIntervalList.EncodedListAt q final.disk p.source (offset j)
        ((List.finRange (radix q)).flatMap children) ∧
      (∀ k : Fin (radix q),CommonMSDChildCount.totalCount q final.disk (directories p j) k.val=
        (children k).length) ∧
      CommonMSDGlobalFrame.Frame p j s.disk final.disk ∧
      charge≤CommonMSDNodeRate.nodeBudget q (records j) := by
  obtain ⟨tag,t,steps,charge,ht,hterminal,hout,hcounts,hframe⟩ :=
    CommonMSDGlobalNodeRun.complete_list p j hj hl prefixValue s xs hlen hx ho hp
  refine ⟨tag,t,steps,charge,ht,hterminal,hout,hcounts,hframe,?_⟩
  exact trace_le p j hj s (CommonRecordIntervalList.recordsOfList q (records j) xs hlen)
    ((CommonRecordIntervalList.encoded_records q s.disk p.source (offset j) (records j) xs hlen).2 hx)
    ht hlarge.le

end
end CodedSorting.CommonMSDGlobalNodeCostRun
end NodeCostRun

section Recursion
/-! Well-founded correctness of the actual single-policy DFS sort. The
induction decreases the number of remaining radix groups. Its child path
is executed between a real continuation push and the matching real pop;
no recursive sorting function is inserted into a machine instruction. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDGlobalRecursion
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalControl CommonMSDGlobalComponents CommonMSDParameters
open CommonMSDGlobalFrame CommonMSDGlobalDirectory CommonMSDChildren
open CommonRecordIntervalList CommonMSDGlobalLoop
open CommonLeafProgram (Machine)
noncomputable section
variable {q : Configuration} {L : ℕ}

abbrev sort (q : Configuration) (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) :=
  CommonMSDSemantics.sort CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort fuel xs

abbrev children (q : Configuration) (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) :=
  nodeChildren CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort fuel xs

theorem length_sort (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) :
    (sort q fuel xs).length=xs.length :=
  (CommonMSDSemantics.sort_perm CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
    (CommonMSDSemantics.record_local_correct q.w) fuel xs).length_eq

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
    Call p root j s (sort q (level j) xs) := by
  have main : ∀ fuel,∀ (j : Job q.N L),level j=fuel →
      offset j+records j≤q.N → depth j+level j≤L →
      ∀ (prefixValue : ℕ) (s : Machine q) (xs : List (KeyRecordWords.Record q.w)),
      xs.length=records j → EncodedListAt q s.disk p.source (offset j) xs →
      CommonMSDRecordDigits.OrdinaryList xs →
      CommonMSDSemantics.Prefix CommonWordMSD.key (radix q) (level j) prefixValue xs →
      Call p root j s (sort q (level j) xs) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro j hlevel hj hd prefixValue s xs hlen hx ho hp
      by_cases hz : level j=0
      · refine ⟨erasePC q s,1,0,?_,?_,Frame.refl p j s.disk⟩
        · exact CommonMSDGlobalBase.level_zero (components p) root j hz s
        · simpa only [hz,sort,CommonMSDSemantics.sort,erasePC] using hx
      · have hl : 0<level j := by omega
        by_cases hn : records j≤q.height^2
        · have hfit:=leaf_fits p j hj hn
          have hb:=CommonMSDGlobalBaseList.small_list (K:=radix q)
            (components p) root j hz hfit s xs hlen hx
          dsimp only at hb
          refine ⟨erasePC q (executeRaw q (leafCode (components p) j) s).1,
            (leafCode (components p) j).length+2,cost q (leafCode (components p) j),hb.1,?_,
            CommonMSDGlobalLeafFrame.leaf_frame p j hj hn s⟩
          have hsorteq : sort q (level j) xs=CommonWordMSD.localSort xs := by
            unfold sort
            simpa only [Nat.sub_add_cancel (show 1≤level j by omega)] using
              (parent_terminal CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
                q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (level j-1) xs (by omega)).symm
          rw [hsorteq]
          exact hb.2.1
        · let before := children q (level j-1) xs
          let after : Children q := fun k=>sort q (level j-1) (before k)
          have hlength : ∀k,(after k).length=(before k).length := fun k=>length_sort _ _
          have hsize : ((List.finRange (radix q)).flatMap before).length=records j := by
            have h:=parent_size CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
              q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
              (CommonMSDSemantics.record_local_correct q.w) (level j-1) 0 xs
            simpa only [partial_zero,hlen] using h
          obtain ⟨nodeTag,nodeFinal,nodeSteps,nodeCharge,htrace,hterminal,hencoded,hcounts,hframe⟩ :=
            CommonMSDGlobalNodeRun.complete_list p j hj hl prefixValue s xs hlen hx ho hp
          change EncodedListAt q nodeFinal.disk p.source (offset j)
            ((List.finRange (radix q)).flatMap before) at hencoded
          change DirCounts p j before nodeFinal.disk at hcounts
          have hnode:=node_call (K:=radix q) (components p) root j hz (by omega)
            s nodeFinal nodeTag nodeSteps nodeCharge htrace
          have hchildren : ∀(k : Fin (radix q)) (st : Machine q),
              EncodedListAt q st.disk p.source (offset (childJob j before k)) (before k) →
              Call p root (childJob j before k) st (after k) := by
            intro k st he
            have props:=CommonMSDGlobalLoop.child_properties j before k hj hl hd hsize
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
          obtain ⟨final,steps,charge,hloop,hout,hloopFrame⟩ :=
            CommonMSDGlobalLoop.loop p root j hj hl hd before after hlength hsize hdecode
              hchildren 0 nodeFinal hstage hcounts
          have hcursor : cursor before 0=0 := by
            apply Fin.ext
            simp only [cursor,front,List.take_zero,List.flatMap_nil,List.length_nil,bounded,Nat.zero_mod,Fin.val_zero]
          simp only [Fin.val_zero,hcursor] at hloop
          have hsort : ((List.finRange (radix q)).flatMap after)=sort q (level j) xs := by
            have h:=parent_done CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
              q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (level j-1) xs (by omega)
            simpa only [partial_done,returnedChildren,after,before,children,sort,
              Nat.sub_add_cancel (show 1≤level j by omega)] using h
          rw [hsort] at hout
          exact ⟨final,_,_,(CommonMSDGlobalComponents.routine p root).path_append hnode hloop,
            hout,hframe.trans hloopFrame⟩
  exact main (level j) j rfl hj hd prefixValue s xs hlen hx ho hp

end
end CodedSorting.CommonMSDGlobalRecursion
end Recursion

section CostRecursion
/-! Quantitative well-founded correctness of the same single-policy DFS sort. The
induction decreases the number of remaining radix groups. Its child path
is executed between a real continuation push and the matching real pop;
no recursive sorting function is inserted into a machine instruction. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDGlobalCostRecursion
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalControl CommonMSDGlobalComponents CommonMSDParameters
open CommonMSDGlobalFrame CommonMSDGlobalDirectory CommonMSDChildren
open CommonRecordIntervalList CommonMSDGlobalLoop CommonMSDGlobalCost
open CommonLeafProgram (Machine)
noncomputable section
variable {q : Configuration} {L : ℕ}

open CommonMSDGlobalRecursion

/-- The existing semantic ledger instantiated with all physical node,
leaf, and controller costs. -/
def budget (q : Configuration) (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) : ℕ :=
  CommonMSDSemanticCost.budget CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
    (CommonMSDIntervalLocal.charge q)
    (fun n=>CommonMSDNodeRate.nodeBudget q n+CommonMSDGlobalControlCost.controlCharge q n) fuel xs

@[simp] theorem budget_zero (q : Configuration) (xs : List (KeyRecordWords.Record q.w)) :
    budget q 0 xs=0 := rfl

theorem budget_small (q : Configuration) (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w))
    (hl : 0<fuel) (hn : xs.length≤q.height^2) :
    budget q fuel xs=CommonMSDIntervalLocal.charge q xs.length := by
  cases fuel with
  | zero => omega
  | succ fuel => simp only [budget,CommonMSDSemanticCost.budget,if_pos hn]

theorem budget_large (q : Configuration) (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w))
    (hl : 0<fuel) (hn : q.height^2<xs.length) :
    budget q fuel xs=CommonMSDNodeRate.nodeBudget q xs.length+
      CommonMSDGlobalControlCost.controlCharge q xs.length+
      ((List.finRange (radix q)).map (fun k=>budget q (fuel-1) (children q (fuel-1) xs k))).sum := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [budget,CommonMSDSemanticCost.budget,if_neg (not_le.mpr hn),Nat.add_sub_cancel]
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
        · exact CommonMSDGlobalBase.level_zero (components p) root j hz s
        · simpa only [hz,sort,CommonMSDSemantics.sort,erasePC] using hx
      · have hl : 0<level j := by omega
        by_cases hn : records j≤q.height^2
        · have hfit:=leaf_fits p j hj hn
          have hb:=CommonMSDGlobalBaseList.small_list (K:=radix q)
            (components p) root j hz hfit s xs hlen hx
          dsimp only at hb
          refine ⟨erasePC q (executeRaw q (leafCode (components p) j) s).1,
            (leafCode (components p) j).length+2,cost q (leafCode (components p) j),hb.1,?_,
            CommonMSDGlobalLeafFrame.leaf_frame p j hj hn s,?_⟩
          · have hsorteq : sort q (level j) xs=CommonWordMSD.localSort xs := by
              unfold sort
              simpa only [Nat.sub_add_cancel (show 1≤level j by omega)] using
                (parent_terminal CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
                  q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (level j-1) xs (by omega)).symm
            rw [hsorteq]
            exact hb.2.1
          · rw [budget_small q (level j) xs hl (by omega),hlen]
            exact hb.2.2
        · let before := children q (level j-1) xs
          let after : Children q := fun k=>sort q (level j-1) (before k)
          have hlength : ∀k,(after k).length=(before k).length := fun k=>length_sort _ _
          have hsize : ((List.finRange (radix q)).flatMap before).length=records j := by
            have h:=parent_size CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
              q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
              (CommonMSDSemantics.record_local_correct q.w) (level j-1) 0 xs
            simpa only [partial_zero,hlen] using h
          obtain ⟨nodeTag,nodeFinal,nodeSteps,nodeCharge,htrace,hterminal,hencoded,hcounts,hframe,hnodeCost⟩ :=
            CommonMSDGlobalNodeCostRun.complete_list p j hj hl prefixValue s xs hlen hx ho hp (by omega)
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
            have props:=CommonMSDGlobalLoop.child_properties j before k hj hl hd hsize
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
            CommonMSDGlobalCostLoop.loop p root j hj hl hd before after hlength hsize hdecode
              (fun k=>budget q (level j-1) (before k)) hchildren 0 nodeFinal hstage hcounts
          have hcursor : cursor before 0=0 := by
            apply Fin.ext
            simp only [cursor,front,List.take_zero,List.flatMap_nil,List.length_nil,bounded,Nat.zero_mod,Fin.val_zero]
          simp only [Fin.val_zero,hcursor] at hloop
          have hsort : ((List.finRange (radix q)).flatMap after)=sort q (level j) xs := by
            have h:=parent_done CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
              q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (level j-1) xs (by omega)
            simpa only [partial_done,returnedChildren,after,before,children,sort,
              Nat.sub_add_cancel (show 1≤level j by omega)] using h
          rw [hsort] at hout
          have whole := (CommonMSDGlobalComponents.routine p root).path_append hnode hloop
          refine ⟨final,_,_,whole,hout,hframe.trans hloopFrame,?_⟩
          change nodeCharge+charge≤_
          rw [budget_large q (level j) xs hl (by omega),hlen]
          simp only [Fin.val_zero,siblingBudget_zero] at hloopCost
          change charge≤CommonMSDGlobalControlCost.controlCharge q (records j)+
            ((List.finRange (radix q)).map (fun k=>budget q (level j-1) (before k))).sum at hloopCost
          change nodeCharge+charge≤CommonMSDNodeRate.nodeBudget q (records j)+
            CommonMSDGlobalControlCost.controlCharge q (records j)+
            ((List.finRange (radix q)).map (fun k=>budget q (level j-1) (before k))).sum
          omega
  exact main (level j) j rfl hj hd prefixValue s xs hlen hx ho hp

end
end CodedSorting.CommonMSDGlobalCostRecursion
end CostRecursion
