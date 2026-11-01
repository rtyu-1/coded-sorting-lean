import CodedSorting.Shared.Memory.IntervalAdapter
import CodedSorting.Sorting.Radix.Framework.Routine

/-! Embed an actual finite control routine between charged interval copies.
The inner routine can return its records at a different aligned location.
The wrapper inspects only current RAM, and its tag set has A+3 elements. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDIntervalRoutine
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonMSDRoutine CommonIntervalAdapter
open CommonLeafProgram (Machine RAM Disk)
open CommonRecordInterval (EncodedAt)
open CommonMarginTransform (wordAt)
noncomputable section

def embed {A : ℕ} (tag : Fin A) : Fin (A+3) := ⟨tag.val,by omega⟩
def extractTag (A : ℕ) : Fin (A+3) := ⟨A,by omega⟩
def restoreTag (A : ℕ) : Fin (A+3) := ⟨A+1,by omega⟩
def doneTag (A : ℕ) : Fin (A+3) := ⟨A+2,by omega⟩

def routine (q : Configuration) (reader : Fin q.inventory.readers)
    (n base O input target : ℕ) {A : ℕ} (r : Routine q A) : Routine q (A+3) where
  entry := extractTag A
  body := fun tag => if ht : tag.val<A then r.body ⟨tag.val,ht⟩
    else if tag.val=A then extract q reader n base O input
    else if tag.val=A+1 then restore q reader n base O target else []
  next := fun tag ram => if ht : tag.val<A then
      if r.terminal ⟨tag.val,ht⟩ then restoreTag A else embed (r.next ⟨tag.val,ht⟩ ram)
    else if tag.val=A then embed r.entry else doneTag A
  terminal := fun tag => decide (tag.val=A+2)
  safe := by
    intro tag i hi
    split_ifs at hi with ht he hr
    · exact r.safe ⟨tag.val,ht⟩ i hi
    · exact CommonIntervalCopy.code_safe q reader _ _ _ _ _ i hi
    · exact CommonIntervalCopy.code_safe q reader _ _ _ _ _ i hi
    · simp at hi
  terminal_empty := by
    intro tag ht
    simp only [decide_eq_true_eq] at ht
    simp only [ht,show ¬A+2<A by omega,↓reduceDIte,show ¬A+2=A by omega,
      show ¬A+2=A+1 by omega,↓reduceIte]

variable (q : Configuration) (reader : Fin q.inventory.readers)
  (n base O input target : ℕ) {A : ℕ} (r : Routine q A)

@[simp] theorem body_embed (tag : Fin A) :
    (routine q reader n base O input target r).body (embed tag)=r.body tag := by
  simp only [routine,embed,tag.isLt,↓reduceDIte]

@[simp] theorem terminal_embed (tag : Fin A) :
    (routine q reader n base O input target r).terminal (embed tag)=false := by
  simp only [routine,embed,decide_eq_false_iff_not]
  have := tag.isLt
  omega

@[simp] theorem body_extract :
    (routine q reader n base O input target r).body (extractTag A)=extract q reader n base O input := by
  simp [routine,extractTag]

@[simp] theorem body_restore :
    (routine q reader n base O input target r).body (restoreTag A)=restore q reader n base O target := by
  simp [routine,restoreTag]

@[simp] theorem terminal_extract :
    (routine q reader n base O input target r).terminal (extractTag A)=false := by
  simp [routine,extractTag]

@[simp] theorem terminal_restore :
    (routine q reader n base O input target r).terminal (restoreTag A)=false := by
  simp [routine,restoreTag]

@[simp] theorem terminal_done :
    (routine q reader n base O input target r).terminal (doneTag A)=true := by
  simp [routine,doneTag]

@[simp] theorem rawBody_embed (tag : Fin A) (s : Machine q) :
    (routine q reader n base O input target r).rawBody (embed tag) s=r.rawBody tag s := by
  simp only [Routine.rawBody,body_embed]

@[simp] theorem nextTag_embed (tag : Fin A) (ht : r.terminal tag=false) (s : Machine q) :
    (routine q reader n base O input target r).nextTag (embed tag) s=embed (r.nextTag tag s) := by
  rw [Routine.nextTag,rawBody_embed]
  simp [Routine.successor,routine,embed,ht,Routine.nextTag]

@[simp] theorem nextTag_terminal (tag : Fin A) (ht : r.terminal tag=true) (s : Machine q) :
    (routine q reader n base O input target r).nextTag (embed tag) s=restoreTag A := by
  simp only [Routine.nextTag,Routine.successor,routine,embed,tag.isLt,↓reduceDIte,ht,↓reduceIte]

@[simp] theorem nextTag_extract (s : Machine q) :
    (routine q reader n base O input target r).nextTag (extractTag A) s=embed r.entry := by
  simp [Routine.nextTag,Routine.successor,routine,extractTag]

@[simp] theorem nextTag_restore (s : Machine q) :
    (routine q reader n base O input target r).nextTag (restoreTag A) s=doneTag A := by
  simp [Routine.nextTag,Routine.successor,routine,restoreTag]

def extracted (s : Machine q) : Machine q :=
  erasePC q (executeRaw q (extract q reader n base O input) s).1

def restored (s : Machine q) : Machine q :=
  erasePC q (executeRaw q (restore q reader n base O target) s).1

theorem restore_trace (s : Machine q) :
    (routine q reader n base O input target r).Trace (restoreTag A) s (doneTag A)
      (restored q reader n base O target s)
      ((restore q reader n base O target).length+1)
      (cost q (restore q reader n base O target)) := by
  have hd := Routine.Trace.done (r:=routine q reader n base O input target r)
    (doneTag A) (restored q reader n base O target s) (terminal_done q reader n base O input target r)
  have hs := Routine.Trace.step (r:=routine q reader n base O input target r)
    (restoreTag A) (doneTag A) s (restored q reader n base O target s) 0 0
    (terminal_restore q reader n base O input target r)
  simpa only [body_restore,Nat.add_zero] using hs (by
    simpa only [nextTag_restore,Routine.rawBody,body_restore,restored,erasePC,setPC_setPC] using hd)

/-- An inner terminating trace becomes a returning trace; its terminal tag
executes an empty transition before the real restoration copy. -/
theorem inner_trace {tag finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (ht : r.Trace tag s finalTag final steps charge) :
    (routine q reader n base O input target r).Trace (embed tag) s (doneTag A)
      (restored q reader n base O target final)
      (steps+((restore q reader n base O target).length+1)+1)
      (charge+cost q (restore q reader n base O target)) := by
  induction ht with
  | done tag s ht =>
      have hb := r.terminal_empty tag ht
      have tail := restore_trace q reader n base O input target r (erasePC q s)
      have hs := Routine.Trace.step (r:=routine q reader n base O input target r)
        (embed tag) (doneTag A) s (restored q reader n base O target (erasePC q s))
        ((restore q reader n base O target).length+1)
        (cost q (restore q reader n base O target))
        (terminal_embed q reader n base O input target r tag)
      simpa only [body_embed,hb,List.length_nil,Routine.rawBody,executeRaw,CommonStaticSchedule.cost,
        Nat.zero_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        hs (by simpa only [nextTag_terminal q reader n base O input target r tag ht,
          rawBody_embed,Routine.rawBody,body_embed,hb,executeRaw] using tail)
  | step tag finalTag s final steps charge ht tail ih =>
      have hs := Routine.Trace.step (r:=routine q reader n base O input target r)
        (embed tag) (doneTag A) s (restored q reader n base O target final)
        (steps+((restore q reader n base O target).length+1)+1)
        (charge+cost q (restore q reader n base O target))
        (terminal_embed q reader n base O input target r tag)
      simpa only [body_embed,Nat.add_assoc] using hs (by
        simpa only [nextTag_embed q reader n base O input target r tag ht,rawBody_embed] using ih)

theorem trace {finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (ht : r.Trace r.entry (extracted q reader n base O input s) finalTag final steps charge) :
    (routine q reader n base O input target r).Trace (extractTag A) s (doneTag A)
      (restored q reader n base O target final)
      ((extract q reader n base O input).length+steps+
        (restore q reader n base O target).length+3)
      (cost q (extract q reader n base O input)+charge+
        cost q (restore q reader n base O target)) := by
  have hi := inner_trace q reader n base O input target r ht
  have hs := Routine.Trace.step (r:=routine q reader n base O input target r)
    (extractTag A) (doneTag A) s (restored q reader n base O target final)
    (steps+((restore q reader n base O target).length+1)+1)
    (charge+cost q (restore q reader n base O target))
    (terminal_extract q reader n base O input target r)
  have hh := hs (by
    simpa only [nextTag_extract,Routine.rawBody,body_extract,extracted] using hi)
  convert hh using 1 <;> simp only [body_extract] <;> omega

theorem fits (stride : ℕ)
    (hi : ∀ tag,(r.body tag).length<stride)
    (he : (extract q reader n base O input).length<stride)
    (hr : (restore q reader n base O target).length<stride)
    (hc : (A+3)*stride≤q.N^q.exponent) :
    (routine q reader n base O input target r).Fits stride := by
  refine ⟨?_,hc⟩
  intro tag
  simp only [routine]
  split_ifs with ht hA hR
  · exact hi _
  · exact he
  · exact hr
  · simp only [List.length_nil]
    have := hi r.entry
    omega


/-- The actual extraction disk carries the original interval records. -/
theorem extracted_correct {work limit : ℕ}
    (h : CommonIntervalAdapter.Fits q n base O input work limit)
    (s : Machine q) (f : Records q n) (hf : EncodedAt q s.disk base O f) :
    Encoded q (extracted q reader n base O input s).disk input f :=
  CommonIntervalAdapter.extract_correct q reader h s f hf

/-- The actual restoration copy writes the inner routine's returned records
back to the same main-file interval, even when target differs from input. -/
theorem restored_correct {work limit : ℕ}
    (h : CommonIntervalAdapter.Fits q n base O target work limit)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk target f) :
    EncodedAt q (restored q reader n base O target s).disk base O f :=
  CommonIntervalAdapter.restore_correct q reader h s f hf

theorem extracted_frame {work limit : ℕ}
    (h : CommonIntervalAdapter.Fits q n base O input work limit)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val< input ∨ limit≤a.val) :
    (extracted q reader n base O input s).disk a=s.disk a := by
  have hi := h.scratch_before
  have hw := h.workspace
  exact (CommonIntervalAdapter.extract_raw q reader h s).outside a (by omega)

theorem restored_frame {work limit : ℕ}
    (h : CommonIntervalAdapter.Fits q n base O target work limit)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<base+3*O/q.block ∨
      base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)≤a.val) :
    (restored q reader n base O target s).disk a=s.disk a := by
  have he := CommonRecordInterval.interval_end q (3*O) (3*n)
  exact (CommonIntervalAdapter.restore_raw q reader h s).outside a (by omega)

theorem restored_word_frame {work limit : ℕ}
    (h : CommonIntervalAdapter.Fits q n base O target work limit)
    (s : Machine q) (j : ℕ) (hj : base+j/q.block<q.N^q.exponent)
    (ho : j<3*O ∨ 3*O+3*n≤j) :
    wordAt q (restored q reader n base O target s).disk base j=wordAt q s.disk base j := by
  have ht := CommonIntervalAdapter.main_end q h
  have hs : target+PhysicalStreamCursor.blockCount q.block (0+3*n)+2≤q.N^q.exponent := by
    rw [Nat.zero_add,←CommonRecordEncoding.recordBlocks_eq_words]
    exact h.scratch_before.trans (h.workspace.trans h.capacity)
  exact (CommonIntervalCopyBounds.raw_word q reader 0 (3*O) (3*n) target base s hs
    (ht.trans (by have:=CommonIntervalAdapter.scratch_fits q h;omega)) (Or.inr ht) j hj).trans
    (by rw [if_neg (by omega)])

/-- Composed disk frame: only the live main interval and the declared
scratch arena may change. The inner trace supplies its own actual frame. -/
theorem frame {work work' limit : ℕ}
    (hi : CommonIntervalAdapter.Fits q n base O input work limit)
    (hr : CommonIntervalAdapter.Fits q n base O target work' limit)
    (s t : Machine q)
    (hinner : ∀ a : Fin (q.N^q.exponent),(a.val< input ∨ limit≤a.val) →
      t.disk a=(extracted q reader n base O input s).disk a)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<base+3*O/q.block ∨
      base+PhysicalStreamCursor.blockCount q.block (3*O+3*n)≤a.val)
    (hw : a.val< input ∨ limit≤a.val) :
    (restored q reader n base O target t).disk a=s.disk a :=
  (restored_frame q reader n base O target hr t a ha).trans
    ((hinner a hw).trans (extracted_frame q reader n base O input hi s a hw))

/-- The two partially occupied boundary blocks retain all neighboring
words. This is stronger than preserving only disjoint disk blocks. -/
theorem word_frame {work work' limit : ℕ}
    (hi : CommonIntervalAdapter.Fits q n base O input work limit)
    (hr : CommonIntervalAdapter.Fits q n base O target work' limit)
    (s t : Machine q)
    (hinner : ∀ a : Fin (q.N^q.exponent),(a.val< input ∨ limit≤a.val) →
      t.disk a=(extracted q reader n base O input s).disk a)
    (j : ℕ) (hj : base+j/q.block<q.N^q.exponent)
    (ho : j<3*O ∨ 3*O+3*n≤j)
    (hw : base+j/q.block< input ∨ limit≤base+j/q.block) :
    wordAt q (restored q reader n base O target t).disk base j=wordAt q s.disk base j := by
  rw [restored_word_frame q reader n base O target hr t j hj ho]
  apply CommonRecordInterval.word_congr q t.disk s.disk base j hj
  exact (hinner ⟨base+j/q.block,hj⟩ hw).trans
    (extracted_frame q reader n base O input hi s ⟨base+j/q.block,hj⟩ hw)

theorem charge_eq (innerCharge : ℕ) :
    cost q (extract q reader n base O input)+innerCharge+
      cost q (restore q reader n base O target)=CommonIntervalAdapter.charge q n O innerCharge := by
  simp only [extract,restore,CommonIntervalCopy.code_cost,extract_pages,CommonIntervalAdapter.charge]


/-- End-to-end execution of the wrapper's one fixed policy. -/
theorem run_correct {work limit stride : ℕ}
    (hr : CommonIntervalAdapter.Fits q n base O target work limit)
    (hfit : (routine q reader n base O input target r).Fits stride)
    {finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (ht : r.Trace r.entry (extracted q reader n base O input s) finalTag final steps charge)
    (hpc : pc q s.ram=(extractTag A).val*stride)
    (f : Records q n) (hf : Encoded q final.disk target f) :
    let out := ControlledNormalization.runLogical
      ((routine q reader n base O input target r).policy stride)
      ((extract q reader n base O input).length+steps+
        (restore q reader n base O target).length+3) s
    EncodedAt q out.1.disk base O f ∧
      out.1.disk=(restored q reader n base O target final).disk ∧
      out.2=CommonIntervalAdapter.charge q n O charge ∧
      (routine q reader n base O input target r).policy stride out.1.ram=none := by
  have hh := (routine q reader n base O input target r).trace_run stride hfit
    (trace q reader n base O input target r ht) hpc
  have hd := congrArg (fun t : Machine q => t.disk) hh.1
  dsimp only [erasePC] at hd
  refine ⟨?_,hd,?_,hh.2.2.2⟩
  · rw [hd]
    exact restored_correct q reader n base O target hr final f hf
  · exact hh.2.1.trans (charge_eq q reader n base O input target charge)

end
end CodedSorting.CommonMSDIntervalRoutine
