import CodedSorting.Sorting.Radix.Framework.Directory

section Stack
/-! A disk stack of bounded continuation numbers on the same common
machine. A frame has d words, placed at a public block-aligned slot. The
controller selects the push program from its current bounded control tag;
its payload instructions never inspect the compiler counter. Pop performs
real reads and exposes the saved continuation in the existing leaf bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDStack
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store Machine machine Disk)
noncomputable section

def frameBlocks (q : Configuration) : ℕ := PhysicalStreamCursor.blockCount q.block q.digits

def frameBase (q : Configuration) (stack depth : ℕ) : ℕ := stack+depth*frameBlocks q

def stage (q : Configuration) (continuation : ℕ) (s : Store q) : Store q :=
  {s with leaf:=(ResidentLeafBank.putBlock 0 q.digits
    (PhysicalStreamCursor.encodeNat q.digits q.w continuation) s.leaf)}

def stageInstruction (q : Configuration) (continuation : ℕ) : Instruction q :=
  ⟨.localOp (fun ram => pack (stage q continuation (unpack ram))),id⟩

def pushCode (q : Configuration) (stack depth continuation : ℕ) : List (Instruction q) :=
  stageInstruction q continuation ::
    CommonStaticLeaf.writeCode q (frameBase q stack depth) q.digits (frameBlocks q)

def popCode (q : Configuration) (stack depth : ℕ) : List (Instruction q) :=
  CommonStaticLeaf.readCode q (frameBase q stack depth) q.digits (frameBlocks q)

def loadedWords (q : Configuration) (s : Store q) : Words q.digits q.w :=
  fun j => ResidentLeafBank.getWord s.leaf j.val

def loaded (q : Configuration) (s : Store q) : ℕ := decodeWords (loadedWords q s)

def storedWords (q : Configuration) (disk : Disk q) (stack depth : ℕ) : Words q.digits q.w :=
  fun j => CommonLeafLoad.diskWord q disk (frameBase q stack depth) j.val

def stored (q : Configuration) (disk : Disk q) (stack depth : ℕ) : ℕ :=
  decodeWords (storedWords q disk stack depth)

def Frame (q : Configuration) (disk : Disk q) (stack depth continuation : ℕ) : Prop :=
  storedWords q disk stack depth=PhysicalStreamCursor.encodeNat q.digits q.w continuation

theorem frame_fits (q : Configuration) : q.digits≤CommonExchangeLeaf.bankWords q := by
  have h := CommonMSDDirectoryBounds.digits_le_height q
  unfold CommonExchangeLeaf.bankWords
  omega

theorem stage_step (q : Configuration) (continuation : ℕ) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (stageInstruction q continuation) (machine q s disk)=
      machine q (stage q continuation s) disk := by
  simp only [stageInstruction,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem stage_words (q : Configuration) (continuation : ℕ) (s : Store q) :
    loadedWords q (stage q continuation s)=PhysicalStreamCursor.encodeNat q.digits q.w continuation := by
  funext j
  have hj : j.val<512*q.height*3 := j.isLt.trans_le (frame_fits q)
  unfold loadedWords stage
  dsimp only
  rw [ResidentLeafBank.getWord,dif_pos hj]
  rw [ResidentLeafBank.raw_putBlock_inside 0 q.digits _ _ _ (by omega) (by simpa using j.isLt) le_rfl]
  simp only [Nat.sub_zero,Fin.eta]

theorem push_raw (q : Configuration) (stack depth continuation : ℕ)
    (s : Store q) (disk : Disk q)
    (hs : frameBase q stack depth+frameBlocks q≤q.N^q.exponent) :
    ∃ (final : Store q) (out : Disk q),
      executeRaw q (pushCode q stack depth continuation) (machine q s disk)=
        (machine q final out,frameBlocks q) ∧
      Frame q out stack depth continuation ∧
      (∀ a : Fin (q.N^q.exponent),a.val<frameBase q stack depth ∨
        frameBase q stack depth+frameBlocks q≤a.val → out a=disk a) := by
  let changed := stage q continuation s
  obtain ⟨final,hw,hbank,hframe⟩ := CommonStaticLeaf.write_prefix q (frameBase q stack depth)
    q.digits (frameBlocks q) changed disk hs
  let out := CommonLeafDisk.writePrefix (frameBase q stack depth)
    (fun j => CommonStaticLeaf.outputBlock q q.digits j changed.leaf) (frameBlocks q) disk
  refine ⟨final,out,?_,?_,?_⟩
  · rw [pushCode,executeRaw,stage_step]
    simp only [stageInstruction,Normalization.transferCost,Nat.zero_add]
    exact hw
  · unfold Frame
    rw [←stage_words q continuation s]
    funext j
    have hj : j.val<512*q.height*3 := j.isLt.trans_le (frame_fits q)
    have hword := CommonStaticLeaf.written_word q changed.leaf disk (frameBase q stack depth)
      q.digits hs ⟨j.val,hj⟩ j.isLt
    change CommonLeafLoad.diskWord q out (frameBase q stack depth) j.val=
      ResidentLeafBank.getWord changed.leaf j.val
    rw [ResidentLeafBank.getWord,dif_pos hj]
    exact hword
  · intro a ha
    exact CommonLeafDisk.prefix_outside _ _ _ disk a ha

theorem pop_raw (q : Configuration) (stack depth : ℕ) (s : Store q) (disk : Disk q)
    (hs : frameBase q stack depth+frameBlocks q≤q.N^q.exponent) :
    ∃ final : Store q,
      executeRaw q (popCode q stack depth) (machine q s disk)=(machine q final disk,frameBlocks q) ∧
      loadedWords q final=storedWords q disk stack depth ∧
      loaded q final=stored q disk stack depth := by
  obtain ⟨final,hr,hwords,hframe,hheader⟩ := CommonStaticLeaf.read_prefix q (frameBase q stack depth)
    q.digits (frameBlocks q) s disk hs le_rfl
  have hcover : q.digits≤frameBlocks q*q.block :=
    LayoutConversion.blockCount_covers _ _ (CommonLeafProgram.block_positive q)
  have hw : loadedWords q final=storedWords q disk stack depth := by
    funext j
    have hj : j.val<512*q.height*3 := j.isLt.trans_le (frame_fits q)
    unfold loadedWords storedWords
    rw [ResidentLeafBank.getWord,dif_pos hj]
    exact hwords _ (by simpa only [Nat.min_eq_left hcover] using j.isLt)
  exact ⟨final,hr,hw,congrArg decodeWords hw⟩

theorem frame_decodes (q : Configuration) (disk : Disk q) (stack depth continuation : ℕ)
    (h : Frame q disk stack depth continuation)
    (hc : continuation<(2^q.w)^q.digits) : stored q disk stack depth=continuation := by
  unfold stored
  rw [h]
  exact PhysicalStreamCursor.decodeNat_encode _ _ _ hc

theorem stage_safe (q : Configuration) (continuation : ℕ) :
    RespectsPC q (stageInstruction q continuation) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [stage_step,CommonBlockPair.erasePC_machine]
  rfl

theorem push_safe (q : Configuration) (stack depth continuation : ℕ) :
    ∀ i ∈ pushCode q stack depth continuation,RespectsPC q i := by
  intro i hi
  simp only [pushCode,List.mem_cons] at hi
  rcases hi with rfl | hi
  · exact stage_safe q continuation
  · obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl
    · exact CommonStaticLeaf.stage_safe q _ j
    · exact CommonStaticLeaf.writeAt_safe q _ j

theorem pop_safe (q : Configuration) (stack depth : ℕ) :
    ∀ i ∈ popCode q stack depth,RespectsPC q i := by
  intro i hi
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  exact CommonStaticLeaf.readAt_safe q _ _ j

theorem push_length (q : Configuration) (stack depth continuation : ℕ) :
    (pushCode q stack depth continuation).length=2*frameBlocks q+1 := by
  simp only [pushCode,List.length_cons,CommonStaticLeaf.writeCode_length]

theorem pop_length (q : Configuration) (stack depth : ℕ) :
    (popCode q stack depth).length=frameBlocks q := CommonStaticLeaf.readCode_length q _ _ _

theorem push_cost (q : Configuration) (stack depth continuation : ℕ)
    (hs : frameBase q stack depth+frameBlocks q≤q.N^q.exponent) :
    cost q (pushCode q stack depth continuation)=frameBlocks q := by
  simp only [pushCode,cost,stageInstruction,Normalization.transferCost,Nat.zero_add]
  exact CommonStaticLeaf.writeCode_cost q _ _ _ hs

theorem pop_cost (q : Configuration) (stack depth : ℕ)
    (hs : frameBase q stack depth+frameBlocks q≤q.N^q.exponent) :
    cost q (popCode q stack depth)=frameBlocks q := CommonStaticLeaf.readCode_cost q _ _ _ hs

theorem loaded_eq_of_erasePC (q : Configuration) (s t : Machine q)
    (h : erasePC q s=erasePC q t) : loaded q (unpack s.ram)=loaded q (unpack t.ram) := by
  have hh := congrArg (fun m : Machine q => (unpack m.ram : Store q).leaf) h
  simp only [erasePC,setPC,unpack_pack] at hh
  exact congrArg (fun bank => decodeWords (fun j : Fin q.digits => ResidentLeafBank.getWord bank j.val)) hh

theorem push_tagged (q : Configuration) (stride tag pcOffset stack depth continuation : ℕ)
    (s : Machine q)
    (hs : frameBase q stack depth+frameBlocks q≤q.N^q.exponent) :
    let result := CommonTaggedSchedule.execute q stride tag pcOffset
      (pushCode q stack depth continuation) s
    Frame q result.1.disk stack depth continuation ∧ result.2=frameBlocks q ∧
    (∀ a : Fin (q.N^q.exponent),a.val<frameBase q stack depth ∨
      frameBase q stack depth+frameBlocks q≤a.val → result.1.disk a=s.disk a) := by
  obtain ⟨final,out,hraw,hwords,hframe⟩ := push_raw q stack depth continuation (unpack s.ram) s.disk hs
  rw [CommonBlockPair.machine_eta] at hraw
  have he := CommonTaggedSchedule.execute_payload q stride tag pcOffset (pushCode q stack depth continuation)
    (push_safe q stack depth continuation) s s rfl
  rw [hraw] at he
  have hd := congrArg (fun t : Machine q => t.disk) he
  simp only [erasePC,machine] at hd
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simpa only [hd] using hwords
  · rw [CommonTaggedSchedule.execute_cost,push_cost q stack depth continuation hs]
  · simpa only [hd] using hframe

theorem pop_tagged (q : Configuration) (stride tag pcOffset stack depth : ℕ)
    (s : Machine q)
    (hs : frameBase q stack depth+frameBlocks q≤q.N^q.exponent) :
    let result := CommonTaggedSchedule.execute q stride tag pcOffset (popCode q stack depth) s
    result.1.disk=s.disk ∧ result.2=frameBlocks q ∧
      loaded q (unpack result.1.ram)=stored q s.disk stack depth := by
  obtain ⟨final,hraw,hwords,hload⟩ := pop_raw q stack depth (unpack s.ram) s.disk hs
  rw [CommonBlockPair.machine_eta] at hraw
  have he := CommonTaggedSchedule.execute_payload q stride tag pcOffset (popCode q stack depth)
    (pop_safe q stack depth) s s rfl
  rw [hraw] at he
  dsimp only at he ⊢
  refine ⟨?_,?_,?_⟩
  · simpa only [erasePC,machine] using congrArg (fun t : Machine q => t.disk) he
  · rw [CommonTaggedSchedule.execute_cost,pop_cost q stack depth hs]
  · exact (loaded_eq_of_erasePC q _ _ he).trans (by simpa only [machine,unpack_pack] using hload)

end
end CodedSorting.CommonMSDStack
end Stack

section StackFrames
/-! Stack invariants concern the same finite disk as payload processing.
Saved continuations are proof-side observations of its disjoint slots,
not an additional resident array or an unbounded machine stack. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDStackFrames
open CommonSortingNormalization CommonMSDStack
open CommonLeafProgram (Disk Machine)
noncomputable section

theorem storedWords_eq_of_blocks (q : Configuration) (before after : Disk q)
    (stack depth : ℕ)
    (hs : frameBase q stack depth+frameBlocks q≤q.N^q.exponent)
    (heq : ∀ a : Fin (q.N^q.exponent),frameBase q stack depth≤a.val ∧
      a.val<frameBase q stack depth+frameBlocks q → after a=before a) :
    storedWords q after stack depth=storedWords q before stack depth := by
  funext j
  have hj : j.val/q.block<frameBlocks q :=
    (PhysicalStreamCursor.cursor_live_iff q.block q.digits (j.val/q.block)
      (CommonLeafProgram.block_positive q)).2
        ((Nat.div_mul_le_self j.val q.block).trans_lt j.isLt)
  have ha : frameBase q stack depth+j.val/q.block<q.N^q.exponent := by omega
  unfold storedWords CommonLeafLoad.diskWord
  simp only [ha,↓reduceDIte]
  rw [heq _ ⟨Nat.le_add_right _ _,Nat.add_lt_add_left hj _⟩]

theorem stored_eq_of_blocks (q : Configuration) (before after : Disk q)
    (stack depth : ℕ)
    (hs : frameBase q stack depth+frameBlocks q≤q.N^q.exponent)
    (heq : ∀ a : Fin (q.N^q.exponent),frameBase q stack depth≤a.val ∧
      a.val<frameBase q stack depth+frameBlocks q → after a=before a) :
    stored q after stack depth=stored q before stack depth :=
  congrArg WordControl.decodeWords (storedWords_eq_of_blocks q before after stack depth hs heq)

theorem other_slot_outside (q : Configuration) (stack written kept : ℕ)
    (hne : kept≠written) (a : ℕ)
    (ha : frameBase q stack kept≤a ∧ a<frameBase q stack kept+frameBlocks q) :
    a<frameBase q stack written ∨ frameBase q stack written+frameBlocks q≤a := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Nat.mul_le_mul_right (frameBlocks q) (show kept+1≤written by omega)
    unfold frameBase at *
    rw [Nat.add_mul] at hm
    omega
  · have hm := Nat.mul_le_mul_right (frameBlocks q) (show written+1≤kept by omega)
    unfold frameBase at *
    rw [Nat.add_mul] at hm
    omega

theorem frame_preserved (q : Configuration) (before after : Disk q)
    (stack written kept continuation : ℕ) (hne : kept≠written)
    (hs : frameBase q stack kept+frameBlocks q≤q.N^q.exponent)
    (hframe : Frame q before stack kept continuation)
    (hout : ∀ a : Fin (q.N^q.exponent),a.val<frameBase q stack written ∨
      frameBase q stack written+frameBlocks q≤a.val → after a=before a) :
    Frame q after stack kept continuation := by
  unfold Frame at *
  rw [storedWords_eq_of_blocks q before after stack kept hs]
  · exact hframe
  · intro a ha
    exact hout a (other_slot_outside q stack written kept hne a.val ha)

def Saved (q : Configuration) (disk : Disk q) (stack depth : ℕ)
    (values : Fin depth → ℕ) : Prop :=
  ∀ j : Fin depth,Frame q disk stack j.val (values j)

def appendValue {depth : ℕ} (values : Fin depth → ℕ) (last : ℕ) : Fin (depth+1) → ℕ :=
  fun j => if h : j.val<depth then values ⟨j.val,h⟩ else last

theorem saved_push (q : Configuration) (before after : Disk q) (stack depth continuation : ℕ)
    (values : Fin depth → ℕ)
    (hs : stack+(depth+1)*frameBlocks q≤q.N^q.exponent)
    (hold : Saved q before stack depth values)
    (hnew : Frame q after stack depth continuation)
    (hout : ∀ a : Fin (q.N^q.exponent),a.val<frameBase q stack depth ∨
      frameBase q stack depth+frameBlocks q≤a.val → after a=before a) :
    Saved q after stack (depth+1) (appendValue values continuation) := by
  intro j
  by_cases hj : j.val<depth
  · simp only [appendValue,hj,↓reduceDIte]
    apply frame_preserved q before after stack depth j.val _ (by omega) _ (hold ⟨j.val,hj⟩) hout
    unfold frameBase
    have hm := Nat.mul_le_mul_right (frameBlocks q) (show j.val+1≤depth+1 by omega)
    rw [Nat.add_mul] at hm
    omega
  · have he : j.val=depth := by have:=j.isLt; omega
    simpa [appendValue,he] using hnew

/-- A real tagged push extends all previously stored continuation slots. -/
theorem tagged_push_saved (q : Configuration) (stride tag pcOffset stack depth continuation : ℕ)
    (s : Machine q) (values : Fin depth → ℕ)
    (hs : stack+(depth+1)*frameBlocks q≤q.N^q.exponent)
    (hold : Saved q s.disk stack depth values) :
    let result := CommonTaggedSchedule.execute q stride tag pcOffset
      (pushCode q stack depth continuation) s
    Saved q result.1.disk stack (depth+1) (appendValue values continuation) ∧
      result.2=frameBlocks q := by
  have hfit : frameBase q stack depth+frameBlocks q≤q.N^q.exponent := by
    unfold frameBase
    nlinarith [hs]
  obtain ⟨hn,hc,hout⟩ := push_tagged q stride tag pcOffset stack depth continuation s hfit
  exact ⟨saved_push q s.disk _ stack depth continuation values hs hold hn hout,hc⟩


/-- Pop recovers the last saved continuation from the disk and leaves all
older frames available.  The value is never supplied as a machine input. -/
theorem tagged_pop_saved (q : Configuration) (stride tag pcOffset stack depth : ℕ)
    (s : Machine q) (values : Fin (depth+1) → ℕ)
    (hs : stack+(depth+1)*frameBlocks q≤q.N^q.exponent)
    (hold : Saved q s.disk stack (depth+1) values)
    (hc : values (Fin.last depth)<(2^q.w)^q.digits) :
    let result := CommonTaggedSchedule.execute q stride tag pcOffset (popCode q stack depth) s
    result.1.disk=s.disk ∧ result.2=frameBlocks q ∧
      loaded q (unpack result.1.ram)=values (Fin.last depth) ∧
      Saved q result.1.disk stack depth (fun j => values j.castSucc) := by
  have hfit : frameBase q stack depth+frameBlocks q≤q.N^q.exponent := by
    unfold frameBase
    nlinarith [hs]
  obtain ⟨hd,hcost,hload⟩ := pop_tagged q stride tag pcOffset stack depth s hfit
  refine ⟨hd,hcost,?_,?_⟩
  · rw [hload]
    exact frame_decodes q s.disk stack depth _ (hold (Fin.last depth)) hc
  · intro j
    rw [hd]
    exact hold j.castSucc

end
end CodedSorting.CommonMSDStackFrames
end StackFrames
