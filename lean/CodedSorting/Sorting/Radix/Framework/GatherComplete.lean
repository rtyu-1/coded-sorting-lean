import Mathlib.Data.List.FinRange
import CodedSorting.Sorting.Radix.Framework.GatherController

section DirectoryStable
/-! Persisted descriptors remain equal whenever the gather changes only
blocks after their directory. This connects each actual later read to
the original metadata, rather than assuming the observed lengths. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDDirectoryStable
open CommonSortingNormalization
open CommonLeafProgram (Disk)
open CommonMSDDirectoryRead

theorem stored_eq (q : Configuration) (a b : Disk q) (directory entry target : ℕ)
    (hdir : base q directory entry+blocks q entry≤target)
    (ht : target≤q.N^q.exponent)
    (heq : ∀ x : Fin (q.N^q.exponent),x.val<target → a x=b x)
    (which : Fin 2) :
    stored q a directory entry which=stored q b directory entry which := by
  unfold stored
  congr 1
  funext j
  rw [←stored_shift,←stored_shift]
  have hi : lead q entry+which.val*q.digits+j.val<total q entry := by
    have := which.isLt
    have := j.isLt
    unfold total
    nlinarith
  have hb : (lead q entry+which.val*q.digits+j.val)/q.block<blocks q entry := by
    apply (PhysicalStreamCursor.cursor_live_iff q.block (total q entry) _
      (CommonLeafProgram.block_positive q)).2
    exact (Nat.div_mul_le_self _ _).trans_lt hi
  have ha : base q directory entry+(lead q entry+which.val*q.digits+j.val)/q.block<q.N^q.exponent := by omega
  simp only [CommonLeafLoad.diskWord,ha,↓reduceDIte]
  rw [heq _ (by dsimp;omega)]

theorem remaining_cons {F : ℕ} (j : Fin (F+1)) (hj : j.val<F) :
    (List.finRange F).drop j.val=
      (⟨j.val,hj⟩ : Fin F)::(List.finRange F).drop (j.val+1) := by
  rw [List.drop_eq_getElem_cons (show j.val<(List.finRange F).length by simpa using hj)]
  simp

theorem remaining_nil {F : ℕ} (j : Fin (F+1)) (hj : j.val=F) :
    (List.finRange F).drop j.val=[] := by simp [hj]

end CodedSorting.CommonMSDDirectoryStable
end DirectoryStable

section GatherCost
/-! Reading one actual directory entry and copying its live words costs a
scan plus a constant boundary charge. Summing over all row/bucket pairs
absorbs those charges into a scan when the radix counts descriptor words. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDGatherCost
open CommonSortingNormalization

def fragmentCharge (q : Configuration) (entry destination words : ℕ) : ℕ :=
  CommonMSDDirectoryRead.blocks q entry+6*CommonIntervalCopy.pages q destination words

theorem fragment_scaled (q : Configuration) (entry destination words : ℕ) :
    fragmentCharge q entry destination words*q.block≤6*words+2*q.digits+14*q.block := by
  have hb := CommonLeafProgram.block_positive q
  have hr := LocalSortingCost.blockCount_capacity q.block hb
    (CommonMSDDirectoryRead.total q entry)
  have hc := LocalSortingCost.blockCount_capacity q.block hb (destination%q.block+words)
  have hl : CommonMSDDirectoryRead.lead q entry<q.block := Nat.mod_lt _ hb
  have hm := Nat.mod_lt destination hb
  change CommonMSDDirectoryRead.blocks q entry*q.block≤
    CommonMSDDirectoryRead.lead q entry+2*q.digits+q.block at hr
  change CommonIntervalCopy.pages q destination words*q.block≤destination%q.block+words+q.block at hc
  unfold fragmentCharge
  nlinarith

theorem total_scaled (q : Configuration) {F : ℕ} (entry destination words : Fin F→ℕ) :
    (∑ i,fragmentCharge q (entry i) (destination i) (words i))*q.block≤
      6*(∑ i,words i)+F*(2*q.digits+14*q.block) := by
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ i : Fin F,(6*words i+2*q.digits+14*q.block) :=
      Finset.sum_le_sum (fun i _=>fragment_scaled q (entry i) (destination i) (words i))
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]; ring

/-- The directory reads and all unaligned boundary blocks together cost
at most 48 n/B transfers, with no K simultaneous output buffers. -/
theorem scan_bound (q : Configuration) (n : ℕ) (hn : q.height^2≤n)
    {F : ℕ} (entry destination words : Fin F→ℕ)
    (hF : F≤PhysicalStreamCursor.blockCount (q.height^2) n*CommonMSDParameters.radix q)
    (hwords : (∑ i,words i)≤3*n) :
    (∑ i,fragmentCharge q (entry i) (destination i) (words i))*q.block≤48*n := by
  have hH : 0<q.height :=
    (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory; omega)).1
  have hsq : q.height≤q.height^2 := by nlinarith
  have hfields := CommonMSDParameters.radix_fields q
  have hblocks := CommonMSDParameters.radix_block q
  have hper : CommonMSDParameters.radix q*(2*q.digits+14*q.block)≤15*q.height^2 := by
    nlinarith
  have hrows := LocalSortingCost.blockCount_capacity (q.height^2)
    (Nat.pow_pos hH) n
  change PhysicalStreamCursor.blockCount (q.height^2) n*q.height^2≤n+q.height^2 at hrows
  have hJ := Nat.mul_le_mul_left (PhysicalStreamCursor.blockCount (q.height^2) n) hper
  have hcount := Nat.mul_le_mul_right (2*q.digits+14*q.block) hF
  have hboundary : F*(2*q.digits+14*q.block)≤30*n := by nlinarith
  have htotal := total_scaled q entry destination words
  omega

end CodedSorting.CommonMSDGatherCost
end GatherCost

section GatherComparison
/-! The directory-driven loop copies exactly the original listed
intervals. Source rows and directory pages precede the output allocation,
so each later real directory read sees the same stored descriptor. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
namespace CodedSorting.CommonMSDGatherComparison
open CommonSortingNormalization CommonStaticSchedule CommonMSDGatherController
open CommonMSDGatherRun CommonMSDGatherSequence
open CommonLeafProgram (Machine Disk)
noncomputable section

structure Plan (q : Configuration) {F : ℕ} (layout : Layout F) (C : ℕ)
    (original : Disk q) (start count : Fin F → ℕ) : Prop where
  start_stored : ∀ i,start i=layout.offset i+3*CommonMSDDirectoryRead.stored q original
    (layout.directory i) (layout.entry i) 0
  count_stored : ∀ i,count i=3*CommonMSDDirectoryRead.stored q original
    (layout.directory i) (layout.entry i) 1
  directory_before : ∀ i,CommonMSDDirectoryRead.base q (layout.directory i) (layout.entry i)+
    CommonMSDDirectoryRead.blocks q (layout.entry i)≤layout.target
  source_before : ∀ i,layout.source i+
    PhysicalStreamCursor.blockCount q.block (start i+count i)+2≤layout.target
  start_bounded : ∀ i,start i≤C
  output_capacity : layout.target+2*PhysicalStreamCursor.blockCount q.block C+2≤q.N^q.exponent

def Before (q : Configuration) (target : ℕ) (a b : Disk q) : Prop :=
  ∀ x : Fin (q.N^q.exponent),x.val<target → a x=b x

def directoryCharge (q : Configuration) {F : ℕ} (layout : Layout F) (is : List (Fin F)) : ℕ :=
  (is.map (fun i => CommonMSDDirectoryRead.blocks q (layout.entry i))).sum

theorem bounded_val (C n : ℕ) (hn : n≤C) : (bounded C n).val=n := by
  exact Nat.mod_eq_of_lt (by omega)

theorem observed_eq (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (original : Disk q) (start count : Fin F → ℕ)
    (plan : Plan q layout C original start count) (j : Fin F) (D : Fin (C+1)) (s : Machine q)
    (hb : Before q layout.target s.disk original) :
    observed q reader layout stride j D s=(bounded C (start j),bounded C (count j)) := by
  have ht : layout.target≤q.N^q.exponent := by have:=plan.output_capacity;omega
  have hh := (readBody_fields q reader layout stride j D s
    ((plan.directory_before j).trans ht) (CommonMSDDirectoryBounds.read_window_fits q _)).2
  rw [hh,CommonMSDDirectoryStable.stored_eq q s.disk original _ _ _
    (plan.directory_before j) ht hb 0,CommonMSDDirectoryStable.stored_eq q s.disk original _ _ _
    (plan.directory_before j) ht hb 1,←plan.start_stored j,←plan.count_stored j]

theorem compare_from (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (original : Disk q) (start count : Fin F → ℕ)
    (plan : Plan q layout C original start count)
    (fuel : ℕ) (j : Fin (F+1)) (D : Fin (C+1)) (s : Machine q)
    (hcount : j.val+fuel=F)
    (hb : Before q layout.target s.disk original)
    (hvolume : D.val+total count ((List.finRange F).drop j.val)≤C) :
    let is := (List.finRange F).drop j.val
    let out := observe q reader layout stride fuel j D s
    out.machine.disk=(executeRaw q (ghostFrom q reader layout.source layout.target start count D.val is) s).1.disk ∧
    Before q layout.target out.machine.disk original ∧
    out.destination.val=D.val+total count is ∧
    (out.fragments.map Fragment.words).sum=total count is ∧
    out.charge=directoryCharge q layout is+charge q count D.val is := by
  induction fuel generalizing j D s with
  | zero =>
      have he := CommonMSDDirectoryStable.remaining_nil j (by omega)
      simp only [he,observe,ghostFrom,executeRaw,total_nil,Nat.add_zero,
        List.map_nil,List.sum_nil,directoryCharge,charge]
      aesop
  | succ fuel ih =>
      have hj : j.val<F := by omega
      let i : Fin F := ⟨j.val,hj⟩
      let is := (List.finRange F).drop (j.val+1)
      have hlist : (List.finRange F).drop j.val=i::is :=
        CommonMSDDirectoryStable.remaining_cons j hj
      have hvol : D.val+count i+total count is≤C := by
        simpa only [hlist,total_cons,Nat.add_assoc] using hvolume
      have hN : count i≤C := by omega
      have hDN : D.val+count i≤C := by omega
      have ho := observed_eq q reader layout stride original start count plan i D s hb
      have hO : (observed q reader layout stride i D s).1.val=start i := by
        rw [ho];exact bounded_val C _ (plan.start_bounded i)
      have hL : (observed q reader layout stride i D s).2.val=count i := by
        rw [ho];exact bounded_val C _ hN
      have hD : (nextDest q reader layout stride i D s).val=D.val+count i := by
        unfold nextDest
        rw [hL]
        exact bounded_val C _ hDN
      have htarget : layout.target≤q.N^q.exponent := by have:=plan.output_capacity;omega
      have hs := (plan.directory_before i).trans htarget
      have hw := CommonMSDDirectoryBounds.read_window_fits q (layout.entry i)
      have hcycle := cycle_disk q reader layout stride i D s hs hw
      dsimp only at hcycle
      rw [hO,hL] at hcycle
      have hcopy := CommonIntervalCopy.raw q reader (start i) D.val (count i)
        (layout.source i) layout.target s
        (copy_target_fits q layout.target D.val (count i) C hDN plan.output_capacity)
        (CommonIntervalCopyBounds.readsOutside q (start i) D.val (count i)
          (layout.source i) layout.target ((plan.source_before i).trans htarget)
          (Or.inl ((plan.source_before i).trans (Nat.le_add_right layout.target (D.val/q.block)))))
      have hnext : Before q layout.target (afterCopy q reader layout stride i D s).disk original := by
        intro x hx
        rw [hcycle]
        exact (hcopy.outside x (Or.inl (hx.trans_le (Nat.le_add_right layout.target (D.val/q.block))))).trans (hb x hx)
      have hvolnext : (nextDest q reader layout stride i D s).val+
          total count ((List.finRange F).drop (nextIndex i).val)≤C := by
        rw [hD]
        exact hvol
      have ht := ih (nextIndex i) (nextDest q reader layout stride i D s)
        (afterCopy q reader layout stride i D s) (by dsimp only [nextIndex,i];omega) hnext hvolnext
      have htail : (List.finRange F).drop (nextIndex i).val=is := rfl
      simp only [htail] at ht
      have hcost : cycleCost q reader layout stride i D s=
          CommonMSDDirectoryRead.blocks q (layout.entry i)+6*CommonIntervalCopy.pages q D.val (count i) := by
        unfold cycleCost
        dsimp only
        rw [hO,hL,CommonMSDDirectoryRead.code_cost q _ _ hs,CommonIntervalCopy.code_cost]
      simp only [observe,dif_pos hj]
      refine ⟨?_,ht.2.1,?_,?_,?_⟩
      · calc
          _ = (executeRaw q (ghostFrom q reader layout.source layout.target start count
                (nextDest q reader layout stride i D s).val is)
                (afterCopy q reader layout stride i D s)).1.disk := ht.1
          _ = (executeRaw q (ghostFrom q reader layout.source layout.target start count
                (D.val+count i) is)
                (executeRaw q (CommonIntervalCopy.code q reader (start i) D.val (count i)
                  (layout.source i) layout.target) s).1).1.disk := by
                rw [hD]
                exact ghostFrom_disk_congr q reader layout.source layout.target start count _ is _ _ hcycle
          _ = _ := by rw [hlist,ghostFrom,CommonPermutationPairs.raw_append]
      · have hh := ht.2.2.1
        rw [hD] at hh
        simpa only [hlist,total_cons,Nat.add_assoc] using hh
      · change (observed q reader layout stride i D s).2.val+
          ((observe q reader layout stride fuel (nextIndex i)
            (nextDest q reader layout stride i D s) (afterCopy q reader layout stride i D s)).fragments.map
              Fragment.words).sum=total count ((List.finRange F).drop j.val)
        rw [hL,ht.2.2.2.1,hlist,total_cons]
      · change cycleCost q reader layout stride i D s+
          (observe q reader layout stride fuel (nextIndex i)
            (nextDest q reader layout stride i D s) (afterCopy q reader layout stride i D s)).charge=
          directoryCharge q layout ((List.finRange F).drop j.val)+
            charge q count D.val ((List.finRange F).drop j.val)
        rw [hcost,ht.2.2.2.2,hD,hlist,charge]
        simp only [directoryCharge,List.map_cons,List.sum_cons]
        omega

end
end CodedSorting.CommonMSDGatherComparison
end GatherComparison

section GatherEstimate
/-! Actual directory-read charges plus actual interval-copy charges for
an ordered fragment list. No destination-alignment assumption is needed. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDGatherEstimate
open CommonSortingNormalization CommonMSDGatherSequence
variable {F : ℕ}

def readCharge (q : Configuration) (entry : Fin F → ℕ) (is : List (Fin F)) : ℕ :=
  (is.map (fun i => CommonMSDDirectoryRead.blocks q (entry i))).sum

theorem scaled (q : Configuration) (entry count : Fin F → ℕ)
    (D : ℕ) (is : List (Fin F)) :
    (readCharge q entry is+charge q count D is)*q.block≤
      6*total count is+is.length*(2*q.digits+14*q.block) := by
  induction is generalizing D with
  | nil => simp [readCharge,charge,total]
  | cons i is ih =>
    simp only [readCharge,List.map_cons,List.sum_cons,charge,total_cons,List.length_cons]
    have hh := CommonMSDGatherCost.fragment_scaled q (entry i) D (count i)
    unfold CommonMSDGatherCost.fragmentCharge at hh
    have ht := ih (D+count i)
    unfold readCharge at ht
    nlinarith

/-- The complete gather is a scan when descriptor volume is included in
the radix choice. The coefficient includes every directory and payload I/O. -/
theorem scan_bound (q : Configuration) (entry count : Fin F → ℕ)
    (D : ℕ) (is : List (Fin F)) (n : ℕ) (hn : q.height^2≤n)
    (hF : is.length≤PhysicalStreamCursor.blockCount (q.height^2) n*CommonMSDParameters.radix q)
    (hwords : total count is≤3*n) :
    (readCharge q entry is+charge q count D is)*q.block≤48*n := by
  have hH : 0<q.height :=
    (SortingResourceBudget.normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory;omega)).1
  have hsq : q.height≤q.height^2 := by nlinarith
  have hfields := CommonMSDParameters.radix_fields q
  have hblocks := CommonMSDParameters.radix_block q
  have hper : CommonMSDParameters.radix q*(2*q.digits+14*q.block)≤15*q.height^2 := by
    nlinarith
  have hrows := LocalSortingCost.blockCount_capacity (q.height^2) (Nat.pow_pos hH) n
  change PhysicalStreamCursor.blockCount (q.height^2) n*q.height^2≤n+q.height^2 at hrows
  have hJ := Nat.mul_le_mul_left (PhysicalStreamCursor.blockCount (q.height^2) n) hper
  have hcount := Nat.mul_le_mul_right (2*q.digits+14*q.block) hF
  have hboundary : is.length*(2*q.digits+14*q.block)≤30*n := by nlinarith
  have htotal := scaled q entry count D is
  omega

end CodedSorting.CommonMSDGatherEstimate
end GatherEstimate

section GatherFrame
/-! Gathering preserves the entire disk outside its packed output file,
including addresses after the file. Boundary words are recovered from the
already verified literal word-copy equation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDGatherFrame
open CommonSortingNormalization CommonStaticSchedule CommonMSDGatherSequence
open CommonLeafProgram (Machine Disk)
open CommonMarginTransform (wordAt)
noncomputable section

theorem word_at_block (q : Configuration) (disk : Disk q) (base : ℕ)
    (a : Fin (q.N^q.exponent)) (ha : base≤a.val) (i : Fin q.block) :
    wordAt q disk base ((a.val-base)*q.block+i.val)=disk a i := by
  rw [CommonRecordEncoding.wordAt_eq_diskWord,
    CommonLeafLoad.diskWord_block q disk base (a.val-base) (by have:=a.isLt;omega) i]
  congr 2
  omega

theorem ghost_frame (q : Configuration) (reader : Fin q.inventory.readers) {F : ℕ}
    (source : Fin F→ℕ) (target : ℕ) (start count : Fin F→ℕ) (is : List (Fin F)) (s : Machine q)
    (hs : SourcesBefore q source start count target is)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (total count is)+2≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<target ∨ target+PhysicalStreamCursor.blockCount q.block (total count is)≤a.val) :
    (executeRaw q (ghostFrom q reader source target start count 0 is) s).1.disk a=s.disk a := by
  obtain ⟨hbefore,hwords⟩ := raw q reader source target start count 0 is s hs (by simpa using hcap)
  rcases ha with ha|ha
  · exact hbefore a ha
  · have htarget : target≤a.val := by omega
    funext i
    let j := (a.val-target)*q.block+i.val
    have hj : target+j/q.block<q.N^q.exponent := by
      dsimp only [j]
      rw [Nat.add_comm ((a.val-target)*q.block) i.val,
        Nat.add_mul_div_right _ _ (CommonLeafProgram.block_positive q),Nat.div_eq_of_lt i.isLt]
      have:=a.isLt
      omega
    have hlo : total count is≤j := by
      have hb := LayoutConversion.blockCount_covers (total count is) q.block (CommonLeafProgram.block_positive q)
      change total count is≤PhysicalStreamCursor.blockCount q.block (total count is)*q.block at hb
      have hm := Nat.mul_le_mul_right q.block
        (show PhysicalStreamCursor.blockCount q.block (total count is)≤a.val-target by omega)
      dsimp only [j]
      omega
    have h := hwords j hj
    simp only [Nat.zero_add,Nat.sub_zero,show ¬(0≤j ∧ j<total count is) by omega,if_false] at h
    rw [word_at_block q _ target a htarget i,word_at_block q _ target a htarget i] at h
    exact h

theorem observe_frame (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : CommonMSDGatherController.Layout F) (stride : ℕ)
    (start count : Fin F→ℕ) (s : Machine q)
    (plan : CommonMSDGatherComparison.Plan q layout C s.disk start count)
    (hvolume : total count (List.finRange F)≤C)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<layout.target ∨
      layout.target+PhysicalStreamCursor.blockCount q.block (total count (List.finRange F))≤a.val) :
    (CommonMSDGatherRun.observe q reader layout stride F 0 (0 : Fin (C+1)) s).machine.disk a=s.disk a := by
  have hc := CommonMSDGatherComparison.compare_from q reader layout stride s.disk start count plan
    F 0 (0 : Fin (C+1)) s (by simp) (fun _ _=>rfl) (by simpa using hvolume)
  simp only [Fin.val_zero,List.drop_zero,Nat.zero_add] at hc
  rw [hc.1]
  apply ghost_frame q reader layout.source layout.target start count (List.finRange F) s
    (fun i _=>plan.source_before i) _ a ha
  have hm := blockCount_mono q.block (total count (List.finRange F)) C hvolume
  have := plan.output_capacity
  omega

end
end CodedSorting.CommonMSDGatherFrame
end GatherFrame

section GatherComplete
/-! Complete directory-driven gathering on one actual common machine.
The policy reads the persisted descriptors, copies all their intervals,
concatenates them in order, halts, and pays the scan bound in that same run.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDGatherComplete
open CommonSortingNormalization CommonStaticSchedule CommonMSDGatherController
open CommonMSDGatherRun CommonMSDGatherSequence CommonMSDGatherComparison
open CommonLeafProgram (Machine)
open CommonMarginTransform (wordAt)
noncomputable section

/-- No successful-execution premise is supplied: directory values are
read by the fixed controller, and source/metadata preservation is proved. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (hcontrol : Fits q reader (C:=C) layout stride)
    (start count : Fin F → ℕ) (D : Fin (C+1)) (s : Machine q)
    (plan : Plan q layout C s.disk start count)
    (hvolume : D.val+total count (List.finRange F)≤C)
    (hpc : pc q s.ram=(tagEquiv F C (ready (0 : Fin (F+1)) D)).val*stride)
    (n : ℕ) (hn : q.height^2≤n)
    (hF : F≤PhysicalStreamCursor.blockCount (q.height^2) n*CommonMSDParameters.radix q)
    (hwords : total count (List.finRange F)≤3*n) :
    let observedRun := observe q reader layout stride F 0 D s
    let result := ControlledNormalization.runLogical (policy q reader (C:=C) layout stride) observedRun.steps s
    (∀ j,layout.target+j/q.block<q.N^q.exponent →
      wordAt q result.1.disk layout.target j=
        if D.val≤j ∧ j<D.val+total count (List.finRange F) then
          contents q layout.source start count s.disk (List.finRange F) (j-D.val)
        else wordAt q s.disk layout.target j) ∧
    Before q layout.target result.1.disk s.disk ∧
    policy q reader (C:=C) layout stride result.1.ram=none ∧
    result.2=CommonMSDGatherEstimate.readCharge q layout.entry (List.finRange F)+
      charge q count D.val (List.finRange F) ∧
    result.2*q.block≤48*n ∧
    observedRun.destination.val=D.val+total count (List.finRange F) ∧
    observedRun.fragments.length=F ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have hc := compare_from q reader layout stride s.disk start count plan F 0 D s
    (by simp) (fun _ _ => rfl) (by simpa using hvolume)
  simp only [Fin.val_zero,List.drop_zero] at hc
  have hmono := blockCount_mono q.block (D.val+total count (List.finRange F)) C hvolume
  have hcap : layout.target+2*PhysicalStreamCursor.blockCount q.block
      (D.val+total count (List.finRange F))+2≤q.N^q.exponent := by
    have := plan.output_capacity
    omega
  have hg := CommonMSDGatherSequence.raw q reader layout.source layout.target start count
    D.val (List.finRange F) s (fun i _ => plan.source_before i) hcap
  obtain ⟨hr,hhalt,hflen,hmem⟩ := CommonMSDGatherRun.complete q reader layout stride hcontrol D s hpc
  rw [←CommonMSDGatherRun.observed_charge] at hr
  have hscan := CommonMSDGatherEstimate.scan_bound q layout.entry count D.val (List.finRange F)
    n hn (by simpa using hF) hwords
  dsimp only
  rw [hr]
  refine ⟨?_,hc.2.1,hhalt,?_,?_,hc.2.2.1,hflen,hmem⟩
  · intro j hj
    rw [hc.1]
    exact hg.2 j hj
  · exact hc.2.2.2.2
  · rw [hc.2.2.2.2]
    exact hscan

end
end CodedSorting.CommonMSDGatherComplete
end GatherComplete
