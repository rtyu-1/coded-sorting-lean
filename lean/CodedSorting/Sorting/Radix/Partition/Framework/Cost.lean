import CodedSorting.Sorting.Radix.Partition.Framework.Pass
import CodedSorting.Sorting.Radix.Partition.Framework.Semantic
import CodedSorting.Sorting.Radix.LocalGroups.Framework.Local

section PassCost
/-! The actual preparation and persisted metadata scans retain the
local sorting rate at every nonleaf MSD node. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDNodePass
open CommonSortingNormalization CommonMSDChunks CommonLocalBudgetRate
noncomputable section

theorem directory_charge_scaled (q : Configuration) (n : ℕ) (hn : q.height^2≤n) :
    directoryCharge q n (CommonMSDParameters.radix q)*q.block≤39*n := by
  have hv := CommonMSDChunkRows.volume_eq q n
  change ((List.finRange (chunkCount q n)).map (fun c => (CommonMSDChunkRows.row q n c).length)).sum=n at hv
  rw [←List.ofFn_eq_map,List.sum_ofFn] at hv
  have h := CommonMSDDirectoryCost.scan_bound q n hn
    (fun c => (CommonMSDChunkRows.row q n c).length) le_rfl hv.le
  have he : directoryCharge q n (CommonMSDParameters.radix q)=
      ∑ c : Fin (chunkCount q n),CommonMSDDirectoryCost.rowCharge q
        (CommonMSDParameters.radix q) (CommonMSDChunkRows.row q n c).length := by
    unfold directoryCharge CommonMSDRowDirectoryBatch.rowBlocks CommonMSDDirectoryCost.rowCharge
    rw [←List.ofFn_eq_map,List.sum_ofFn,Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    ring
  rw [he]
  exact h

theorem integer_charge_bound (q : Configuration) (n : ℕ) (hn : q.height^2≤n)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block) :
    charge q n (CommonMSDParameters.radix q)*q.block≤
      (4*(22194000000*(GlobalSortingBound.localRate q.height K
        (Real.log ((q.height : ℝ)/q.block)) tau+2))+168)*n := by
  have hp := CommonMSDChunks.integer_charge_bound q n hn hnormal
  have hd := directory_charge_scaled q n hn
  unfold charge
  nlinarith only [hp,hd]

end
end CodedSorting.CommonMSDNodePass
end PassCost

section Rate
/-! A size-only budget for the actual MSD node. It includes local row
sorting, persisted directories, the complete gather, and both interval
copies. The radix accounts for directory fields as well as data blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.CommonMSDNodeRate
open CommonSortingNormalization CommonRecordProgram WordControl
open CommonMSDSemanticCost
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m RecursiveExchange.radix

def nodeBudget (q : Configuration) (n : ℕ) : ℕ :=
  CommonMSDNodePass.charge q n (CommonMSDParameters.radix q)+48*n/q.block+
    12*(recordBlocks q n+1)

/-- The actual fragment enumeration has total payload exactly three words
per record; all its metadata reads are included in this bound. -/
theorem gather_scaled (q : Configuration) {n : ℕ}
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (f : Records q n) (source directory target D : ℕ) (hn : q.height^2≤n) :
    (CommonMSDGatherComparison.directoryCharge q
      (CommonMSDNodeLayout.layout q n (CommonMSDParameters.radix q) source directory target)
      (List.finRange (CommonMSDParameters.radix q*CommonMSDChunks.chunkCount q n))+
    CommonMSDGatherSequence.charge q (CommonMSDNodeLayout.count q key f) D
      (List.finRange (CommonMSDParameters.radix q*CommonMSDChunks.chunkCount q n)))*q.block≤48*n := by
  apply CommonMSDGatherEstimate.scan_bound q _ _ D _ n hn
  · simp only [List.length_finRange,CommonMSDChunks.chunkCount,CommonMSDChunks.chunkSize]
    exact Nat.le_of_eq (Nat.mul_comm _ _)
  · exact (CommonMSDNodeLayout.total_count q key f).le

theorem gather_le (q : Configuration) {n : ℕ}
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (f : Records q n) (source directory target D : ℕ) (hn : q.height^2≤n) :
    CommonMSDGatherComparison.directoryCharge q
      (CommonMSDNodeLayout.layout q n (CommonMSDParameters.radix q) source directory target)
      (List.finRange (CommonMSDParameters.radix q*CommonMSDChunks.chunkCount q n))+
    CommonMSDGatherSequence.charge q (CommonMSDNodeLayout.count q key f) D
      (List.finRange (CommonMSDParameters.radix q*CommonMSDChunks.chunkCount q n))≤48*n/q.block :=
  (Nat.le_div_iff_mul_le (CommonLeafProgram.block_positive q)).2
    (gather_scaled q key f source directory target D hn)

theorem prepare_scaled (q : Configuration) (n : ℕ) (hn : q.height^2≤n)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block) :
    CommonMSDNodePass.charge q n (CommonMSDParameters.radix q)*q.block≤
      (4*localRate q+168)*n :=
  CommonMSDNodePass.integer_charge_bound q n hn hnormal

theorem nodeBudget_scaled (q : Configuration) (n : ℕ) (hn : q.height^2≤n)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block) :
    nodeBudget q n*q.block≤(4*localRate q+288)*n := by
  have hp := prepare_scaled q n hn hnormal
  have hg := Nat.div_mul_le_self (48*n) q.block
  have ht := CommonMSDIntervalLocalRate.transport_scaled q n
  have hb : q.block≤n := (CommonMSDChunks.block_le_chunk q).trans hn
  unfold nodeBudget
  nlinarith only [hp,hg,ht,hb]

/-- The same coefficient works for every leaf, including the empty one. -/
theorem local_scaled (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (n : ℕ) (hn : n≤q.height^2) :
    CommonMSDIntervalLocal.charge q n*q.block≤(localRate q+36)*(n+q.block) := by
  have hl := actual_local_charge q hnormal n hn
  have ht := CommonMSDIntervalLocalRate.transport_scaled q n
  unfold CommonMSDIntervalLocal.charge
  nlinarith only [hl,ht]

/-- Any actual inner charge below the preparation and gather budgets
retains the public node budget after extraction and reinsertion. -/
theorem interval_le (q : Configuration) (n O inner : ℕ)
    (hi : inner≤CommonMSDNodePass.charge q n (CommonMSDParameters.radix q)+48*n/q.block) :
    CommonIntervalAdapter.charge q n O inner≤nodeBudget q n :=
  (CommonIntervalAdapter.charge_le q n O inner).trans
    (Nat.add_le_add_right hi _)

end
end CodedSorting.CommonMSDNodeRate
end Rate

section Complete
/-! A complete aligned MSD node: the public preparation body writes the
row directories, then the actual controller reads and gathers their
intervals. Neither a correct directory nor sorted rows are assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
namespace CodedSorting.RadixNode.Complete
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonRecordEncoding CommonMSDNodeLayout CommonMSDNodeContents
open CommonMSDRecordDigits CommonMSDRoutine RadixNode
open CommonLeafProgram (Machine Disk)
noncomputable section
variable {Normal : Configuration → Prop} [ChunkSorter Normal]
attribute [local irreducible] ControlledNormalization.runLogical RadixNode.Pass.chunks RadixNode.Pass.code
  CommonMSDGatherRun.observe CommonMSDGatherSequence.ghostFrom executeRaw

theorem ready_of_before (q : Configuration) {n K source dir target : ℕ}
    (key : Word q.w→Fin K) (f : Records q n) (before after : Disk q)
    (h : RadixNode.Pass.Ready q key source dir before f)
    (hs : source+recordBlocks q n≤target)
    (hd : dir+CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q K≤target)
    (ht : target≤q.N^q.exponent)
    (he : CommonMSDGatherComparison.Before q target after before) :
    RadixNode.Pass.Ready q key source dir after f := by
  have hentry (c : Fin (CommonMSDChunks.chunkCount q n)) (k : Fin K) (field : Fin 2) :
      CommonMSDDirectory.entry q after (CommonMSDRowDirectoryBatch.target q K dir c.val) k field=
        CommonMSDDirectory.entry q before (CommonMSDRowDirectoryBatch.target q K dir c.val) k field := by
    apply CommonMSDRowDirectoryBatch.entry_of_disk_eq q
    intro a _ ha
    exact he a (ha.trans_le ((CommonMSDRowDirectoryBatch.target_end q c).trans hd))
  exact ⟨CommonMSDRowDirectoryBatch.encoded_of_disk_eq q f before after (hs.trans ht)
    h.input (fun a _ ha=>he a (ha.trans_le hs)),
    fun c k=>(hentry c k 0).trans (h.starts c k),
    fun c k=>(hentry c k 1).trans (h.lengths c k)⟩

/-- Generic gather semantics, kept separate from record encodings. -/
theorem observed_correct (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (l : CommonMSDGatherController.Layout F) (stride : ℕ)
    (start count : Fin F→ℕ) (s : Machine q)
    (hp : CommonMSDGatherComparison.Plan q l C s.disk start count)
    (hv : CommonMSDGatherSequence.total count (List.finRange F)≤C) :
    let out := CommonMSDGatherRun.observe q reader l stride F 0 (0 : Fin (C+1)) s
    (∀ j,j<CommonMSDGatherSequence.total count (List.finRange F) →
      l.target+j/q.block<q.N^q.exponent →
      CommonMarginTransform.wordAt q out.machine.disk l.target j=
        CommonMSDGatherSequence.contents q l.source start count s.disk (List.finRange F) j) ∧
    CommonMSDGatherComparison.Before q l.target out.machine.disk s.disk ∧
    out.destination.val=CommonMSDGatherSequence.total count (List.finRange F) ∧
    out.charge=CommonMSDGatherComparison.directoryCharge q l (List.finRange F)+
      CommonMSDGatherSequence.charge q count 0 (List.finRange F) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<l.target ∨ l.target+PhysicalStreamCursor.blockCount q.block
        (CommonMSDGatherSequence.total count (List.finRange F))≤a.val) →
      out.machine.disk a=s.disk a) := by
  have hc := CommonMSDGatherComparison.compare_from q reader l stride s.disk start count hp
    F 0 (0 : Fin (C+1)) s (by simp) (fun _ _=>rfl) (by simpa using hv)
  simp only [Fin.val_zero,List.drop_zero,Nat.zero_add] at hc
  have hcap : l.target+2*PhysicalStreamCursor.blockCount q.block
      (0+CommonMSDGatherSequence.total count (List.finRange F))+2≤q.N^q.exponent := by
    have hm := CommonMSDGatherSequence.blockCount_mono q.block _ C hv
    have hh := hp.output_capacity
    simp only [Nat.zero_add]
    omega
  have hr := CommonMSDGatherSequence.raw q reader l.source l.target start count 0
    (List.finRange F) s (fun i _=>hp.source_before i) hcap
  refine ⟨?_,hc.2.1,hc.2.2.1,hc.2.2.2.2,
    CommonMSDGatherFrame.observe_frame q reader l stride start count s hp hv⟩
  intro j hj hfit
  rw [hc.1,hr.2 j hfit]
  simp only [Nat.zero_le,Nat.zero_add,hj,and_self,ite_true,Nat.sub_zero]

theorem gather_correct (q : Configuration) (reader : Fin q.inventory.readers)
    {n K : ℕ} (key : Word q.w→Fin K) (f : Records q n)
    (source dir target stride : ℕ) (s : Machine q)
    (hready : RadixNode.Pass.Ready q key source dir s.disk f)
    (horder : ∀ c : Fin (CommonMSDChunks.chunkCount q n),
      (List.ofFn (rowRecords q f c)).Pairwise
        (fun x y=>CommonMSDDirectorySemantics.recordKey q key x≤
          CommonMSDDirectorySemantics.recordKey q key y))
    (hs : source+recordBlocks q n+2≤target)
    (hd : dir+CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q K≤target)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (3*n)+2≤q.N^q.exponent) :
    let out := CommonMSDGatherRun.observe q reader (layout q n K source dir target) stride
      (K*CommonMSDChunks.chunkCount q n) 0 (0 : Fin (3*n+1)) s
    Encoded q out.machine.disk target (gatherRecords q key f) ∧
    RadixNode.Pass.Ready q key source dir out.machine.disk f ∧
    out.destination.val=3*n ∧
    out.charge=CommonMSDGatherComparison.directoryCharge q (layout q n K source dir target)
      (List.finRange (K*CommonMSDChunks.chunkCount q n))+
        CommonMSDGatherSequence.charge q (count q key f) 0
          (List.finRange (K*CommonMSDChunks.chunkCount q n)) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<target ∨ target+recordBlocks q n≤a.val) → out.machine.disk a=s.disk a) := by
  let l := layout q n K source dir target
  have hplan := plan q key f s.disk source dir target hready.starts hready.lengths hs hd hcap
  have hg := observed_correct q reader l stride (start q key f) (count q key f) s hplan
    (total_count q key f).le
  have ht : target+recordBlocks q n≤q.N^q.exponent := by
    rw [recordBlocks_eq_words]
    omega
  refine ⟨?_,ready_of_before q key f s.disk _ hready (by omega) hd (by omega) hg.2.1,
    hg.2.2.1.trans (total_count q key f),hg.2.2.2.1,?_⟩
  · apply encoded_gather q key f s.disk _ source dir target
      ((encoded_iff_words q s.disk source f (by omega)).1 hready.input) horder ht
    intro j hj
    exact hg.1 j (by simpa only [total_count] using hj) (word_fits q n target j ht hj)
  · intro a ha
    apply hg.2.2.2.2 a
    simpa only [total_count,←recordBlocks_eq_words] using ha

theorem gather_data (q : Configuration) (reader : Fin q.inventory.readers)
    {n K : ℕ} (key : Word q.w→Fin K) (f : Records q n)
    (source dir target stride : ℕ) (s : Machine q)
    (hready : RadixNode.Pass.Ready q key source dir s.disk f)
    (horder : ∀ c : Fin (CommonMSDChunks.chunkCount q n),
      (List.ofFn (rowRecords q f c)).Pairwise
        (fun x y=>CommonMSDDirectorySemantics.recordKey q key x≤
          CommonMSDDirectorySemantics.recordKey q key y))
    (hs : source+recordBlocks q n+2≤target)
    (hd : dir+CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q K≤target)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (3*n)+2≤q.N^q.exponent) :
    let out := CommonMSDGatherRun.observe q reader (layout q n K source dir target) stride
      (K*CommonMSDChunks.chunkCount q n) 0 (0 : Fin (3*n+1)) s
    Encoded q out.machine.disk target (gatherRecords q key f) ∧
    RadixNode.Pass.Ready q key source dir out.machine.disk f ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<target ∨ target+recordBlocks q n≤a.val) → out.machine.disk a=s.disk a) := by
  have h := gather_correct q reader key f source dir target stride s hready horder hs hd hcap
  exact ⟨h.1,h.2.1,h.2.2.2.2⟩

theorem encoded_erase (q : Configuration) {n source : ℕ} (s : Machine q)
    (g : Records q n) (h : Encoded q s.disk source g) :
    Encoded q (erasePC q s).disk source g := h

theorem ready_erase (q : Configuration) {n K source dir : ℕ} (key : Word q.w→Fin K)
    (s : Machine q) (g : Records q n)
    (h : RadixNode.Pass.Ready q key source dir s.disk g) :
    RadixNode.Pass.Ready q key source dir (erasePC q s).disk g := h

/-- Package an abstract terminal machine before instantiating the
instruction execution that produced it. -/
theorem package_result (q : Configuration) {A n K source dir target cap : ℕ}
    (key : Word q.w→Fin K) (g : Records q n) (nr : Routine q A)
    (finalTag : Fin A) (s t : Machine q) (steps charge : ℕ)
    (htrace : nr.Trace nr.entry s finalTag (erasePC q t) steps charge)
    (hencoded : Encoded q t.disk target (gatherRecords q key g))
    (hready : RadixNode.Pass.Ready q key source dir t.disk g)
    (hframe : ∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ cap≤a.val) → t.disk a=s.disk a) :
    ∃ finalTag final steps charge,
      nr.Trace nr.entry s finalTag final steps charge ∧
      Encoded q final.disk target (gatherRecords q key g) ∧
      RadixNode.Pass.Ready q key source dir final.disk g ∧
      (∀ a : Fin (q.N^q.exponent),
        (a.val<source ∨ cap≤a.val) → final.disk a=s.disk a) :=
  ⟨finalTag,erasePC q t,steps,charge,htrace,encoded_erase q t _ hencoded,
    ready_erase q key t _ hready,hframe⟩

/-- Semantic composition over an abstract preparation instruction list.
The concrete resource-dependent code is substituted only after this proof. -/
theorem compose (q : Configuration) (reader : Fin q.inventory.readers) {n base A : ℕ}
    (key : Word q.w→Fin base) (source buffer dir limit target stride : ℕ)
    (preCode : List (Instruction q)) (nr : Routine q A)
    (finish : Fin (3*n+1)→Fin A) (s : Machine q) (g : Records q n)
    (htrace :
      let mid := erasePC q (executeRaw q preCode s).1
      let out := CommonMSDGatherRun.observe q reader (layout q n base source dir target) stride
        (base*CommonMSDChunks.chunkCount q n) 0 (0 : Fin (3*n+1)) mid
      nr.Trace nr.entry s (finish out.destination) (erasePC q out.machine)
        (preCode.length+1+out.steps) (cost q preCode+out.charge))
    (hprep : RadixNode.Pass.Ready q key source dir (executeRaw q preCode s).1.disk g)
    (horder : ∀ c : Fin (CommonMSDChunks.chunkCount q n),
      (List.ofFn (rowRecords q g c)).Pairwise
        (fun x y=>CommonMSDDirectorySemantics.recordKey q key x≤
          CommonMSDDirectorySemantics.recordKey q key y))
    (hframe : ∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → (executeRaw q preCode s).1.disk a=s.disk a)
    (hsource_before : source+recordBlocks q n+2≤buffer)
    (hbuffer : buffer≤limit)
    (hdirectory : dir+CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q base≤limit)
    (hsep : limit≤target)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (3*n)+2≤q.N^q.exponent) :
    ∃ finalTag final steps charge,
      nr.Trace nr.entry s finalTag final steps charge ∧
      Encoded q final.disk target (gatherRecords q key g) ∧
      RadixNode.Pass.Ready q key source dir final.disk g ∧
      (∀ a : Fin (q.N^q.exponent),
        (a.val<source ∨ target+recordBlocks q n≤a.val) → final.disk a=s.disk a) := by
  let l := layout q n base source (dir) target
  generalize hmid : erasePC q (executeRaw q (preCode) s).1=mid
  have hmidDisk : mid.disk=(executeRaw q (preCode) s).1.disk := by
    rw [←hmid]
    rfl
  have hprepmid : RadixNode.Pass.Ready q key source (dir)
      mid.disk g := by
    rw [hmidDisk]
    exact hprep
  generalize hout : CommonMSDGatherRun.observe q reader l stride
    (base*CommonMSDChunks.chunkCount q n) 0 (0 : Fin (3*n+1)) mid=out
  have hsource : source+recordBlocks q n+2≤target :=
    hsource_before.trans (hbuffer.trans hsep)
  have hbase : source≤source+recordBlocks q n+2 :=
    (Nat.le_add_right source _).trans (Nat.le_add_right (source+recordBlocks q n) 2)
  have hst : source≤target := hbase.trans hsource
  have hsb : source≤buffer := hbase.trans hsource_before
  have hg := gather_data q reader key g
    source (dir) target stride mid hprepmid horder hsource
    (hdirectory.trans hsep) hcap
  change (Encoded q (CommonMSDGatherRun.observe q reader l stride
    (base*CommonMSDChunks.chunkCount q n) 0 (0 : Fin (3*n+1)) mid).machine.disk target _ ∧ _) at hg
  rw [hout] at hg
  have ht := htrace
  dsimp only at ht
  rw [hmid,hout] at ht
  apply package_result q key g nr (finish out.destination)
    s out.machine ((preCode).length+1+out.steps)
    (cost q (preCode)+out.charge) ht hg.1 hg.2.1
  intro a ha
  have hga : a.val<target ∨ target+recordBlocks q n≤a.val := by
    rcases ha with ha|ha
    · exact Or.inl (ha.trans_le hst)
    · exact Or.inr ha
  exact (hg.2.2 a hga).trans ((congrArg (fun d : Disk q=>d a) hmidDisk).trans (hframe a (by
    rcases ha with ha|ha
    · exact Or.inl ha
    · exact Or.inr ((Nat.add_le_add_right hst _).trans ha)) (by
    rcases ha with ha|ha
    · exact Or.inl (ha.trans_le hsb)
    · exact Or.inr (hsep.trans ((Nat.le_add_right target _).trans ha)))))


/-- Composition for abstract prepared records keeps the proof independent
of the internal recursive row sorter. -/
theorem complete_from_prepared (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n base : ℕ}
    (r : RadixNode.Pass.Resources q hnormal n base)
    (hfit : (base*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin base) (target stride : ℕ) (s : Machine q) (g : Records q n)
    (hprep : RadixNode.Pass.Ready q key r.source (RadixNode.Pass.directory q r.buffer)
      (executeRaw q (RadixNode.Pass.code q reader (hnormal:=hnormal) r hfit key) s).1.disk g)
    (horder : ∀ c : Fin (CommonMSDChunks.chunkCount q n),
      (List.ofFn (rowRecords q g c)).Pairwise
        (fun x y=>CommonMSDDirectorySemantics.recordKey q key x≤
          CommonMSDDirectorySemantics.recordKey q key y))
    (hframe : ∀ a : Fin (q.N^q.exponent),
      (a.val<r.source ∨ r.source+recordBlocks q n≤a.val) →
      (a.val<r.buffer ∨ r.limit≤a.val) →
      (executeRaw q (RadixNode.Pass.code q reader (hnormal:=hnormal) r hfit key) s).1.disk a=s.disk a)
    (hsep : r.limit≤target)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (3*n)+2≤q.N^q.exponent) :
    let l := layout q n base r.source (RadixNode.Pass.directory q r.buffer) target
    let nr := RadixNode.Controller.routine q reader (hnormal:=hnormal) r hfit key l (C:=3*n)
    ∃ finalTag final steps charge,
      nr.Trace nr.entry s finalTag final steps charge ∧
      Encoded q final.disk target (gatherRecords q key g) ∧
      RadixNode.Pass.Ready q key r.source (RadixNode.Pass.directory q r.buffer)
        final.disk g ∧
      (∀ a : Fin (q.N^q.exponent),
        (a.val<r.source ∨ target+recordBlocks q n≤a.val) → final.disk a=s.disk a) := by
  have hbuffer : r.buffer≤r.limit := by
    have hd := r.directory_space
    change r.buffer+recordBlocks q (CommonMSDChunks.chunkSize q)+
      CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q base≤r.limit at hd
    exact (Nat.le_add_right r.buffer _).trans ((Nat.le_add_right _ _).trans hd)
  exact compose q reader key r.source r.buffer (RadixNode.Pass.directory q r.buffer) r.limit
    target stride (RadixNode.Pass.code q reader (hnormal:=hnormal) r hfit key)
    (RadixNode.Controller.routine q reader (hnormal:=hnormal) r hfit key
      (layout q n base r.source (RadixNode.Pass.directory q r.buffer) target) (C:=3*n))
    (fun D=>RadixNode.Controller.tagEquiv (base*CommonMSDChunks.chunkCount q n) (3*n)
      (some (CommonMSDGatherController.ready
        ⟨base*CommonMSDChunks.chunkCount q n,Nat.lt_succ_self _⟩ D))) s g
    (RadixNode.Head.trace q reader (hnormal:=hnormal) r hfit key _ (C:=3*n) stride s)
    hprep horder hframe r.source_before hbuffer r.directory_space hsep hcap

/-- A real entry-to-terminal trace for the complete aligned node. The
directories and all output records are derived from the original input. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n base : ℕ}
    (r : RadixNode.Pass.Resources q hnormal n base)
    (hfit : (base*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (hb : 0<base) (fuel p target stride : ℕ) (s : Machine q) (f : Records q n)
    (hf : Encoded q s.disk r.source f) (ho : OrdinaryList (List.ofFn f))
    (hp : CommonMSDSemantics.Prefix CommonWordMSD.key base (fuel+1) p (List.ofFn f))
    (hsep : r.limit≤target)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (3*n)+2≤q.N^q.exponent) :
    let key := wordDigit q base hb fuel
    let l := layout q n base r.source (RadixNode.Pass.directory q r.buffer) target
    let nr := RadixNode.Controller.routine q reader (hnormal:=hnormal) r hfit key l (C:=3*n)
    ∃ finalTag final steps charge,
      nr.Trace nr.entry s finalTag final steps charge ∧
      Encoded q final.disk target (gatherRecords q key (CommonMSDChunks.operation q n f)) ∧
      RadixNode.Pass.Ready q key r.source (RadixNode.Pass.directory q r.buffer)
        final.disk (CommonMSDChunks.operation q n f) ∧
      (∀ a : Fin (q.N^q.exponent),
        (a.val<r.source ∨ target+recordBlocks q n≤a.val) → final.disk a=s.disk a) := by
  have hprep := RadixNode.Pass.raw_complete q reader (hnormal:=hnormal) r hfit (wordDigit q base hb fuel) s f hf
  exact complete_from_prepared q reader (hnormal:=hnormal) r hfit (wordDigit q base hb fuel) target stride s
    (CommonMSDChunks.operation q n f) hprep.1
    (CommonMSDNodeSemantic.row_order q base hb fuel p f ho hp) hprep.2 hsep hcap

end
end CodedSorting.RadixNode.Complete
end Complete

namespace CodedSorting.CommonMSDNodeComplete
export CodedSorting.RadixNode.Complete (
  ready_of_before observed_correct gather_correct gather_data encoded_erase ready_erase
  package_result compose complete_from_prepared complete)
end CodedSorting.CommonMSDNodeComplete

section ChargeTrace
/-! A second derivation of the actual node trace retains its exact I/O
charge. The preparation instructions are abstract in the composition
lemma, so the kernel never unfolds the large recursive sorting program. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace CodedSorting.RadixNode.ChargeTrace
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open RadixNode CommonMSDRoutine CommonMSDNodeLayout
open CommonLeafProgram (Machine)
noncomputable section
variable {Normal : Configuration → Prop} [ChunkSorter Normal]
attribute [local irreducible] RadixNode.Pass.code RadixNode.Pass.chunks CommonMSDGatherRun.observe executeRaw

def gatherCharge (q : Configuration) {n K : ℕ} (key : Word q.w→Fin K)
    (source dir target : ℕ) (g : Records q n) : ℕ :=
  CommonMSDGatherComparison.directoryCharge q (layout q n K source dir target)
    (List.finRange (K*CommonMSDChunks.chunkCount q n))+
  CommonMSDGatherSequence.charge q (count q key g) 0
    (List.finRange (K*CommonMSDChunks.chunkCount q n))

/-- Cost composition over an actual trace and an actual persisted directory.
The concrete caller below constructs both premises from the input. -/
theorem compose (q : Configuration) (reader : Fin q.inventory.readers) {n K A : ℕ}
    (key : Word q.w→Fin K) (source dir target stride : ℕ)
    (preCode : List (Instruction q)) (nr : Routine q A)
    (finish : Fin (3*n+1)→Fin A) (s : Machine q) (g : Records q n)
    (htrace :
      let mid := erasePC q (executeRaw q preCode s).1
      let out := CommonMSDGatherRun.observe q reader (layout q n K source dir target) stride
        (K*CommonMSDChunks.chunkCount q n) 0 (0 : Fin (3*n+1)) mid
      nr.Trace nr.entry s (finish out.destination) (erasePC q out.machine)
        (preCode.length+1+out.steps) (cost q preCode+out.charge))
    (hprep : RadixNode.Pass.Ready q key source dir (executeRaw q preCode s).1.disk g)
    (hs : source+recordBlocks q n+2≤target)
    (hd : dir+CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q K≤target)
    (hc : target+2*PhysicalStreamCursor.blockCount q.block (3*n)+2≤q.N^q.exponent) :
    ∃ tag final steps charge,
      nr.Trace nr.entry s tag final steps charge ∧
      charge=cost q preCode+gatherCharge q key source dir target g := by
  let l := layout q n K source dir target
  generalize hmid : erasePC q (executeRaw q preCode s).1=mid
  have hm : mid.disk=(executeRaw q preCode s).1.disk := by rw [←hmid];rfl
  have hp : RadixNode.Pass.Ready q key source dir mid.disk g := by rw [hm];exact hprep
  have hplan := plan q key g mid.disk source dir target hp.starts hp.lengths hs hd hc
  have hg := RadixNode.Complete.observed_correct q reader l stride (start q key g)
    (count q key g) mid hplan (total_count q key g).le
  generalize hout : CommonMSDGatherRun.observe q reader l stride
    (K*CommonMSDChunks.chunkCount q n) 0 (0 : Fin (3*n+1)) mid=out
  have hcost := hg.2.2.2.1
  change (CommonMSDGatherRun.observe q reader l stride
    (K*CommonMSDChunks.chunkCount q n) 0 (0 : Fin (3*n+1)) mid).charge=_ at hcost
  rw [hout] at hcost
  have ht := htrace
  dsimp only at ht
  rw [hmid,hout] at ht
  exact ⟨finish out.destination,erasePC q out.machine,preCode.length+1+out.steps,
    cost q preCode+out.charge,ht,congrArg (fun c=>cost q preCode+c) hcost⟩

def innerCharge (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (target : ℕ) (f : Records q n) : ℕ :=
  cost q (RadixNode.Pass.code q reader r hfit key)+
    gatherCharge q key r.source (RadixNode.Pass.directory q r.buffer) target
      (CommonMSDChunks.operation q n f)

/-- The cost trace is constructed from the encoded input; no successful
inner execution, directory, or sorting-order assumption is supplied. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (target stride : ℕ) (s : Machine q) (f : Records q n)
    (hf : Encoded q s.disk r.source f) (hsep : r.limit≤target)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (3*n)+2≤q.N^q.exponent) :
    let nr := RadixNode.Controller.routine q reader r hfit key
      (layout q n K r.source (RadixNode.Pass.directory q r.buffer) target) (C:=3*n)
    ∃ tag final steps charge,nr.Trace nr.entry s tag final steps charge ∧
      charge=innerCharge q reader r hfit key target f := by
  have hprep := RadixNode.Pass.raw_complete q reader (hnormal:=hnormal) r hfit key s f hf
  have hbuffer : r.buffer≤r.limit := by
    have h := r.directory_space
    unfold RadixNode.Pass.directory at h
    omega
  exact compose q reader key r.source (RadixNode.Pass.directory q r.buffer) target stride
    (RadixNode.Pass.code q reader (hnormal:=hnormal) r hfit key)
    (RadixNode.Controller.routine q reader (hnormal:=hnormal) r hfit key
      (layout q n K r.source (RadixNode.Pass.directory q r.buffer) target) (C:=3*n))
    (fun D=>RadixNode.Controller.tagEquiv (K*CommonMSDChunks.chunkCount q n) (3*n)
      (some (CommonMSDGatherController.ready ⟨K*CommonMSDChunks.chunkCount q n,Nat.lt_succ_self _⟩ D)))
    s (CommonMSDChunks.operation q n f)
    (RadixNode.Head.trace q reader (hnormal:=hnormal) r hfit key _ (C:=3*n) stride s)
    hprep.1 (r.source_before.trans (hbuffer.trans hsep)) (r.directory_space.trans hsep) hcap

end
end CodedSorting.RadixNode.ChargeTrace
end ChargeTrace

namespace CodedSorting.CommonMSDNodeChargeTrace
export CodedSorting.RadixNode.ChargeTrace (
  gatherCharge compose innerCharge complete)
end CodedSorting.CommonMSDNodeChargeTrace

section ChargeRate
/-! The exact charge of the constructed node trace is bounded by the
size-only budget used in the full recursion. No histogram or successful
execution is an input to these bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonMSDNodeChargeRate
open CommonSortingNormalization CommonRecordProgram WordControl CommonPrunedParameters
open CommonMSDNodeChargeTrace CommonMSDNodeRate
noncomputable section
attribute [local irreducible] CommonPrunedParameters.Normalized
  Parameters.W Parameters.m RecursiveExchange.radix
  CommonMSDNodePass.code CommonMSDChunks.operation

theorem gather_le (q : Configuration) {n : ℕ}
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (source directory target : ℕ) (f : Records q n) (hn : q.height^2≤n) :
    gatherCharge q key source directory target f≤48*n/q.block :=
  CommonMSDNodeRate.gather_le q key f source directory target 0 hn

theorem inner_le (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normalized q} {n : ℕ}
    (r : CommonMSDNodePass.Resources q hnormal n (CommonMSDParameters.radix q))
    (hfit : (CommonMSDParameters.radix q*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (target : ℕ) (f : Records q n) (hn : q.height^2≤n) :
    innerCharge q reader r hfit key target f≤
      CommonMSDNodePass.charge q n (CommonMSDParameters.radix q)+48*n/q.block :=
  Nat.add_le_add (CommonMSDNodePass.code_cost_le q reader r hfit key)
    (gather_le q key r.source (CommonMSDNodePass.directory q r.buffer) target
      (CommonMSDChunks.operation q n f) hn)

theorem interval_le (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normalized q} {n : ℕ}
    (r : CommonMSDNodePass.Resources q hnormal n (CommonMSDParameters.radix q))
    (hfit : (CommonMSDParameters.radix q*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin (CommonMSDParameters.radix q))
    (O target : ℕ) (f : Records q n) (hn : q.height^2≤n) :
    CommonIntervalAdapter.charge q n O (innerCharge q reader r hfit key target f)≤nodeBudget q n :=
  CommonMSDNodeRate.interval_le q n O _ (inner_le q reader r hfit key target f hn)

end
end CodedSorting.CommonMSDNodeChargeRate
end ChargeRate
