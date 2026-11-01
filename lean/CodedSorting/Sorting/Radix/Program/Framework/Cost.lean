import CodedSorting.Sorting.Radix.Program.Framework.Loop
import CodedSorting.Sorting.Radix.Partition.Framework.Cost

section ControlCost
/-! Charged control traffic of the actual global DFS. Each of K buckets
scans F row-directory entries and at most once pushes and pops a numeric
continuation. The per-entry bound counts its two d-word fields and block
rounding; it does not charge a whole K-entry directory for every bucket. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDGlobalControlCost
open CommonSortingNormalization CommonMSDParameters CommonStaticSchedule
noncomputable section

/-- The actual count scan plus a conservative push/pop pair per bucket.
Empty buckets skip the pair, so this also bounds their execution. -/
def controlCharge (q : Configuration) (n : ℕ) : ℕ :=
  ((List.finRange (radix q)).map (fun k =>
    CommonMSDChunks.chunkCount q n*CommonMSDDirectoryRead.blocks q k.val+
      2*CommonMSDStack.frameBlocks q)).sum

def entryCharge (q : Configuration) : ℕ :=
  ((List.finRange (radix q)).map (fun k =>CommonMSDDirectoryRead.blocks q k.val)).sum

def countCharge (q : Configuration) (n : ℕ) : ℕ :=
  CommonMSDChunks.chunkCount q n*entryCharge q

def stackCharge (q : Configuration) : ℕ :=
  2*radix q*CommonMSDStack.frameBlocks q

theorem controlCharge_eq (q : Configuration) (n : ℕ) :
    controlCharge q n=countCharge q n+stackCharge q := by
  unfold controlCharge countCharge entryCharge stackCharge
  rw [←List.ofFn_eq_map,←List.ofFn_eq_map,List.sum_ofFn,List.sum_ofFn,
    Finset.sum_add_distrib,←Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

/-- Reading one entry covers exactly its two fields and at most two
rounding blocks, independently of the radix and the number of rows. -/
theorem entry_words_le (q : Configuration) (k : ℕ) :
    CommonMSDDirectoryRead.blocks q k*q.block≤2*q.digits+2*q.block := by
  have hc:=LocalSortingCost.blockCount_capacity q.block
    (CommonLeafProgram.block_positive q) (CommonMSDDirectoryRead.total q k)
  have hl:=Nat.mod_lt (CommonMSDDirectoryRead.offset q k) (CommonLeafProgram.block_positive q)
  change CommonMSDDirectoryRead.blocks q k*q.block≤
    CommonMSDDirectoryRead.total q k+q.block at hc
  unfold CommonMSDDirectoryRead.total CommonMSDDirectoryRead.lead at hc
  omega

theorem frame_words_le (q : Configuration) :
    CommonMSDStack.frameBlocks q*q.block≤q.digits+q.block :=
  LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) q.digits

theorem height_le_square (q : Configuration) : q.height≤q.height^2 := by
  have hh:=CommonLocalRecursion.height_pos q
  nlinarith

/-- K entries occupy O(H²) rounded words even when d exceeds one block.
The descriptor-width condition contributes K*(2d)≤H, not K²*d. -/
theorem entryCharge_words_le (q : Configuration) :
    entryCharge q*q.block≤3*q.height^2 := by
  have hf:=radix_fields q
  have hb:=radix_block q
  have hh:=height_le_square q
  calc
    entryCharge q*q.block = ∑ k : Fin (radix q),CommonMSDDirectoryRead.blocks q k.val*q.block := by
      unfold entryCharge
      rw [←List.ofFn_eq_map,List.sum_ofFn,Finset.sum_mul]
    _ ≤ ∑ _k : Fin (radix q),(2*q.digits+2*q.block) :=
      Finset.sum_le_sum (fun k _=>entry_words_le q k.val)
    _ = radix q*(2*q.digits+2*q.block) := by simp
    _ ≤ 3*q.height^2 := by nlinarith

theorem stackCharge_words_le (q : Configuration) :
    stackCharge q*q.block≤3*q.height^2 := by
  have hf:=radix_fields q
  have hb:=radix_block q
  have hh:=height_le_square q
  have hc:=Nat.mul_le_mul_left (2*radix q) (frame_words_le q)
  unfold stackCharge
  nlinarith

theorem chunks_words_le (q : Configuration) (n : ℕ) (hn : q.height^2<n) :
    CommonMSDChunks.chunkCount q n*q.height^2≤2*n := by
  have hc:=LocalSortingCost.blockCount_capacity (q.height^2)
    (CommonMSDChunks.chunk_positive q) n
  change CommonMSDChunks.chunkCount q n*q.height^2≤n+q.height^2 at hc
  omega

theorem countCharge_words_le (q : Configuration) (n : ℕ) (hn : q.height^2<n) :
    countCharge q n*q.block≤6*n := by
  have hc:=Nat.mul_le_mul_left (CommonMSDChunks.chunkCount q n) (entryCharge_words_le q)
  have hr:=chunks_words_le q n hn
  unfold countCharge
  nlinarith

/-- The genuine global-control overhead is a scan bound at every
non-leaf node. Directory scans cost at most 6n/b and stack traffic 3n/b. -/
theorem controlCharge_words_le (q : Configuration) (n : ℕ) (hn : q.height^2<n) :
    controlCharge q n*q.block≤9*n := by
  have hc:=countCharge_words_le q n hn
  have hs:=stackCharge_words_le q
  rw [controlCharge_eq,Nat.add_mul]
  omega

/-- Link the directory component to the cost of the existing real
read-and-accumulate instructions, rather than an abstract histogram. -/
theorem actual_count_cost (q : Configuration) (n : ℕ) (directories : List ℕ)
    (hlen : directories.length=CommonMSDChunks.chunkCount q n)
    (hfit : ∀ (k : Fin (radix q)),∀ target∈directories,
      CommonMSDDirectoryRead.base q target k.val+CommonMSDDirectoryRead.blocks q k.val≤q.N^q.exponent) :
    ((List.finRange (radix q)).map (fun k =>
      cost q (CommonMSDChildCount.code q directories k.val))).sum=countCharge q n := by
  unfold countCharge entryCharge
  calc
    _ = ((List.finRange (radix q)).map (fun k =>
        CommonMSDChunks.chunkCount q n*CommonMSDDirectoryRead.blocks q k.val)).sum := by
      congr 1
      apply List.map_congr_left
      intro k _
      rw [CommonMSDChildCount.code_cost q directories k.val (hfit k),hlen]
    _ = _ := by
      rw [←List.ofFn_eq_map,←List.ofFn_eq_map,List.sum_ofFn,List.sum_ofFn,Finset.mul_sum]

end
end CodedSorting.CommonMSDGlobalControlCost
end ControlCost

section Cost
/-! Quantitative refinements of the already constructed global policy.
Budgets are proof-side natural numbers; they are not controller inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonMSDGlobalCost
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalControl CommonMSDGlobalComponents CommonMSDParameters
open CommonMSDGlobalFrame CommonMSDGlobalLoop CommonRecordIntervalList
open CommonLeafProgram (Machine)
noncomputable section
variable {q : Configuration} {L : ℕ}

def CostResult (p : Parameters q L) (root j : Job q.N L)
    (start finish : Tag q.N L (CommonMSDNodeTagBound.bound q (radix q)) (radix q))
    (s : Machine q) (ys : List (KeyRecordWords.Record q.w)) (budget : ℕ) : Prop :=
  ∃ final steps charge,
    (CommonMSDGlobalComponents.routine p root).Path (index start) s (index finish) final steps charge ∧
    EncodedListAt q final.disk p.source (offset j) ys ∧ Frame p j s.disk final.disk ∧ charge≤budget

def CostCall (p : Parameters q L) (root j : Job q.N L) (s : Machine q)
    (ys : List (KeyRecordWords.Record q.w)) (budget : ℕ) : Prop :=
  CostResult p root j (visit (components p) j) (returning (components p) j) s ys budget

def stepCharge (q : Configuration) (n : ℕ) (k : Fin (radix q)) : ℕ :=
  CommonMSDChunks.chunkCount q n*CommonMSDDirectoryRead.blocks q k.val+2*CommonMSDStack.frameBlocks q

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
    (directories p j).length=CommonMSDChunks.chunkCount q (records j) := by
  simp only [directories,List.length_ofFn]

end
end CodedSorting.CommonMSDGlobalCost
end Cost

section TreeCost
/-! Summation of the actual local, partition, directory, and stack
budgets over the MSD recursion. Per-child startup costs are absorbed
at their parent using radix*block<=height^2; no leaf-count oracle is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDGlobalTreeCost
open CommonSortingNormalization CommonMSDParameters CommonMSDSemanticCost
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m RecursiveExchange.radix

def budget (q : Configuration) : ℕ→List (KeyRecordWords.Record q.w)→ℕ :=
  CommonMSDSemanticCost.budget CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
    (CommonMSDIntervalLocal.charge q)
    (fun n=>CommonMSDNodeRate.nodeBudget q n+CommonMSDGlobalControlCost.controlCharge q n)

theorem node_scaled (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (n : ℕ) (hn : q.height^2<n) :
    (CommonMSDNodeRate.nodeBudget q n+CommonMSDGlobalControlCost.controlCharge q n)*q.block≤
      (4*localRate q+297)*n := by
  have hn' := CommonMSDNodeRate.nodeBudget_scaled q n hn.le hnormal
  have hc := CommonMSDGlobalControlCost.controlCharge_words_le q n hn
  nlinarith only [hn',hc]

/-- Exact tree-level ledger, including one startup allowance per child. -/
theorem budget_scaled (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) :
    budget q fuel xs*q.block≤
      ((5*localRate q+333)*fuel+(localRate q+36))*xs.length+(localRate q+36)*q.block := by
  have h := budget_depth_bound CommonWordMSD.key (radix q) (CommonMSDRadixCost.radixPositive q)
    q.block q.height (CommonLocalRecursion.height_pos q)
    (CommonLocalRecursion.block_le_height q) (radix_le_height q) CommonWordMSD.localSort
    (CommonMSDSemantics.record_local_correct q.w) (CommonMSDIntervalLocal.charge q)
    (fun n=>CommonMSDNodeRate.nodeBudget q n+CommonMSDGlobalControlCost.controlCharge q n)
    (localRate q+36) (4*localRate q+297)
    (CommonMSDNodeRate.local_scaled q hnormal) (node_scaled q hnormal) fuel xs
  have he : 4*localRate q+297+(localRate q+36)=5*localRate q+333 := by ring
  simpa only [budget,he] using h

theorem localRate_large (q : Configuration) : 333≤localRate q := by
  unfold localRate
  omega

/-- A scan-sized input absorbs the sole root startup term. -/
theorem absorb (q : Configuration) (charge fuel n : ℕ) (hn : q.block≤n)
    (hc : charge*q.block≤((5*localRate q+333)*fuel+(localRate q+36))*n+
      (localRate q+36)*q.block) :
    charge*q.block≤6*localRate q*(fuel+1)*n := by
  have hl := localRate_large q
  have hroot := Nat.mul_le_mul_left (localRate q+36) hn
  have hco : (5*localRate q+333)*fuel+(localRate q+36)+(localRate q+36)≤
      6*localRate q*(fuel+1) := by nlinarith
  have hm := Nat.mul_le_mul_right n hco
  nlinarith only [hc,hroot,hm]

theorem budget_scan_scaled (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) (hn : q.block≤xs.length) :
    budget q fuel xs*q.block≤6*localRate q*(fuel+1)*xs.length :=
  absorb q (budget q fuel xs) fuel xs.length hn (budget_scaled q hnormal fuel xs)

end
end CodedSorting.CommonMSDGlobalTreeCost
end TreeCost

section CostLoop
/-! The same physical sibling loop, retaining the exact Path charge and
bounding it by the sum of scans, disk-stack transfers, and child budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDGlobalCostLoop
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalControl CommonMSDGlobalComponents CommonMSDParameters
open CommonMSDGlobalFrame CommonMSDGlobalDirectory CommonMSDChildren
open CommonRecordIntervalList CommonMSDGlobalLoop CommonMSDGlobalCost
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
      change (CommonMSDGlobalComponents.routine p root).Path _ _ _ _ _ _ at hpc
      simp only [show (components p).directories j=directories p j from rfl,hcount] at hpc
      change (CommonMSDGlobalComponents.routine p root).Path _ _
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
        have hstage := CommonMSDGlobalChildrenState.empty_stage before after hlen k (by rw [←hv];exact hz)
        have hsNext : EncodedListAt q sc.disk p.source (offset j) (stage before after nextKey.val) := by
          rw [←hstage]
          exact hscStage
        obtain ⟨final,steps,charge,hpath,hencoded,hframe,hcost⟩ :=
          ih _ hnext nextKey sc hsNext hscCounts rfl
        have whole := (CommonMSDGlobalComponents.routine p root).path_append hpc hpath
        refine ⟨final,_,_,whole,hencoded,(Frame.of_disk_eq hsc).trans hframe,?_⟩
        have hb := siblingBudget_next q (records j) childBudget k
        change (directories p j).length*CommonMSDDirectoryRead.blocks q key.val+charge≤_
        rw [directories_length]
        dsimp only [stepCharge] at hb
        change siblingBudget q (records j) childBudget key.val=
          CommonMSDChunks.chunkCount q (records j)*CommonMSDDirectoryRead.blocks q key.val+
            2*CommonMSDStack.frameBlocks q+childBudget k+
            siblingBudget q (records j) childBudget nextKey.val at hb
        omega
      · rw [if_neg hz] at hpc
        have hstack : CommonMSDStack.frameBase q (components p).stack (depth j)+
            CommonMSDStack.frameBlocks q≤q.N^q.exponent := by
          exact CommonMSDGlobalAllocation.stack_capacity q p.normal q.N (radix q) L p.source
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
          exact CommonMSDGlobalChildrenState.extract sp.disk p.source (offset j) before after hlen k hpStage
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
          exact CommonMSDGlobalChildrenState.returned p (childJob j before k) sp.disk st.disk
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
        have whole := (CommonMSDGlobalComponents.routine p root).path_append hpc
          ((CommonMSDGlobalComponents.routine p root).path_append hpush
            ((CommonMSDGlobalComponents.routine p root).path_append hcall
              ((CommonMSDGlobalComponents.routine p root).path_append hpop htail)))
        refine ⟨final,_,_,whole,hencoded,?_,?_⟩
        · exact (Frame.of_disk_eq hsc).trans (hpFrame.trans
            (hparentFrame.trans ((Frame.of_disk_eq hsr).trans hframe)))
        · have hb := siblingBudget_next q (records j) childBudget k
          change (directories p j).length*CommonMSDDirectoryRead.blocks q key.val+
            (CommonMSDStack.frameBlocks q+(childCharge+(CommonMSDStack.frameBlocks q+charge)))≤_
          rw [directories_length]
          dsimp only [stepCharge] at hb
          change siblingBudget q (records j) childBudget key.val=
            CommonMSDChunks.chunkCount q (records j)*CommonMSDDirectoryRead.blocks q key.val+
              2*CommonMSDStack.frameBlocks q+childBudget k+
              siblingBudget q (records j) childBudget nextKey.val at hb
          omega


end
end CodedSorting.CommonMSDGlobalCostLoop
end CostLoop

section Power
/-! The actual-radix integer ledger implies the improved logarithmic
sorting expression. The numeric conversion is separate so the same
physical run can supply its already proved charge without a cost oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonMSDGlobalPower
open CommonSortingNormalization CommonMSDSemanticCost CommonLocalBudgetRate
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m RecursiveExchange.radix

def coefficient (q : Configuration) (κ : ℝ) : ℝ :=
  12*22194000000*GlobalSortingBound.rateConstant K tau*(κ*CommonMSDRadixLogBounds.factor q+2)

theorem rate_constant_nonneg : 0≤GlobalSortingBound.rateConstant K tau := by
  have hk:=K_nonneg
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  unfold GlobalSortingBound.rateConstant
  positivity

theorem local_power (q : Configuration)
    (ha : 1≤Real.log ((q.height : ℝ)/q.block)) :
    (CommonMSDSemanticCost.localRate q : ℝ)≤
      22194000000*GlobalSortingBound.rateConstant K tau*
        (1+(Real.log (q.height : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau) := by
  have h := GlobalSortingBound.localRate_power_bound q.height (CommonMSDRadixLogBounds.height_two q)
    K (Real.log ((q.height : ℝ)/q.block)) tau K_nonneg ha tau_nonneg
  unfold CommonMSDSemanticCost.localRate
  push_cast
  nlinarith only [h]

/-- No algorithmic premise is hidden here: hc is the explicit integer
ledger supplied by the actual complete run. The descriptor-width factor
is part of the displayed constant, independent of the input payload. -/
theorem sorting_power (q : Configuration) (charge n : ℕ) (κ : ℝ)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (hκ : 0≤κ) (hn : q.height≤n)
    (hword : (q.w : ℝ)*Real.log 2≤κ*Real.log (n : ℝ))
    (hc : charge*q.block≤6*CommonMSDSemanticCost.localRate q*(CommonMSDRadixCost.depth q+1)*n) :
    (charge : ℝ)≤coefficient q κ*((n : ℝ)/q.block)*
      (1+Real.log (n : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
        Real.log (q.height : ℝ)^(1-tau))) := by
  have hb := CommonLeafProgram.block_positive q
  have hbR : (0:ℝ)<q.block := by exact_mod_cast hb
  have hH : (0:ℝ)<q.height := by
    exact_mod_cast (show 0<q.height by have:=CommonMSDRadixLogBounds.height_two q;omega)
  have hh : 0<Real.log (q.height : ℝ) :=
    Real.log_pos (by exact_mod_cast CommonMSDRadixLogBounds.height_two q)
  have ha := MainSortingParameters.normalized_log_one 1 q.height q.block hb hnormal
  have ha0 : 0<Real.log ((q.height : ℝ)/q.block) := by linarith
  have hlogB : 0≤Real.log (q.block : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤q.block by omega))
  have hah : Real.log ((q.height : ℝ)/q.block)≤Real.log (q.height : ℝ) := by
    rw [Real.log_div hH.ne' hbR.ne']
    linarith
  have hlogN : Real.log (q.height : ℝ)≤Real.log (n : ℝ) :=
    Real.log_le_log hH (by exact_mod_cast hn)
  have hD : 0≤CommonMSDRadixLogBounds.factor q := by
    linarith [CommonMSDRadixLogBounds.factor_one q]
  have hd := CommonMSDRadixLogBounds.depth_bound q κ (Real.log (n : ℝ)) hword
  have hl := local_power q ha
  have hC : 0≤22194000000*GlobalSortingBound.rateConstant K tau :=
    mul_nonneg (by norm_num) rate_constant_nonneg
  have hratio : 0≤(Real.log (q.height : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau :=
    Real.rpow_nonneg (div_nonneg hh.le ha0.le) _
  have hp := mul_le_mul hl hd
    (show (0:ℝ)≤(CommonMSDRadixCost.depth q : ℝ)+1 by positivity)
    (mul_nonneg hC (by linarith))
  have hcancel := GlobalSortingBound.depth_times_rate
    (Real.log (q.height : ℝ)) (Real.log ((q.height : ℝ)/q.block)) (Real.log (n : ℝ))
    tau (κ*CommonMSDRadixLogBounds.factor q) hh ha0 hah hlogN tau_nonneg (mul_nonneg hκ hD)
  have hproduct : (CommonMSDSemanticCost.localRate q : ℝ)*
      ((CommonMSDRadixCost.depth q : ℝ)+1)≤
      22194000000*GlobalSortingBound.rateConstant K tau*
        (2*(κ*CommonMSDRadixLogBounds.factor q+2)*
          (Real.log (n : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
            Real.log (q.height : ℝ)^(1-tau)))) := by
    calc
      _ ≤ _ := hp
      _ = (22194000000*GlobalSortingBound.rateConstant K tau)*
          ((1+(Real.log (q.height : ℝ)/Real.log ((q.height : ℝ)/q.block))^tau)*
            (2+(κ*CommonMSDRadixLogBounds.factor q)*Real.log (n : ℝ)/Real.log (q.height : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcancel hC
  have hcR : (charge : ℝ)*(q.block : ℝ)≤6*(CommonMSDSemanticCost.localRate q : ℝ)*
      ((CommonMSDRadixCost.depth q : ℝ)+1)*(n : ℝ) := by exact_mod_cast hc
  have hscaled := mul_le_mul_of_nonneg_left hproduct (show (0:ℝ)≤6*(n : ℝ) by positivity)
  have hcb : (charge : ℝ)*(q.block : ℝ)≤coefficient q κ*(n : ℝ)*
      (Real.log (n : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
        Real.log (q.height : ℝ)^(1-tau))) := by
    unfold coefficient
    nlinarith only [hcR,hscaled]
  apply (le_div_iff₀ hbR).2 at hcb
  have hnonnegative : 0≤coefficient q κ*((n : ℝ)/q.block) := by
    unfold coefficient
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) rate_constant_nonneg)
        (by have:=mul_nonneg hκ hD;linarith)) (by positivity)
  calc
    _ ≤ _ := hcb
    _ = (coefficient q κ*((n : ℝ)/q.block))*
        (Real.log (n : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
          Real.log (q.height : ℝ)^(1-tau))) := by ring
    _ ≤ _ := by rw [mul_add,mul_one];linarith

/-- The tree budget is concrete: local sorts, row preparation, gather,
all child directory scans, and both stack transfers are included. -/
theorem budget_power (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (xs : List (KeyRecordWords.Record q.w)) (κ : ℝ) (hκ : 0≤κ) (hn : q.height≤xs.length)
    (hword : (q.w : ℝ)*Real.log 2≤κ*Real.log (xs.length : ℝ)) :
    (CommonMSDGlobalTreeCost.budget q (CommonMSDRadixCost.depth q) xs : ℝ)≤
      coefficient q κ*((xs.length : ℝ)/q.block)*
        (1+Real.log (xs.length : ℝ)/(Real.log ((q.height : ℝ)/q.block)^tau*
          Real.log (q.height : ℝ)^(1-tau))) :=
  sorting_power q _ xs.length κ hnormal hκ hn hword
    (CommonMSDGlobalTreeCost.budget_scan_scaled q hnormal _ xs
      ((CommonLocalRecursion.block_le_height q).trans hn))

end
end CodedSorting.CommonMSDGlobalPower
end Power
