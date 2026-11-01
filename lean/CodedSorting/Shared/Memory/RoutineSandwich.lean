import CodedSorting.Sorting.Radix.Framework.Routine

/-! Execute two public static instruction lists around an existing actual
routine. All three stages share the already counted top counter. The inner
tag numbers are unchanged; three additional tags select the prefix, suffix,
and final halt. No extra phase word or input-dependent program is added. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonRoutineSandwich
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonMSDRoutine
open CommonLeafProgram (Machine RAM Disk)
noncomputable section

def embed {A : ℕ} (tag : Fin A) : Fin (A+3) := ⟨tag.val,by omega⟩
def beginTag (A : ℕ) : Fin (A+3) := ⟨A,by omega⟩
def endTag (A : ℕ) : Fin (A+3) := ⟨A+1,by omega⟩
def doneTag (A : ℕ) : Fin (A+3) := ⟨A+2,by omega⟩

def routine (q : Configuration) (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i)
    {A : ℕ} (r : Routine q A) : Routine q (A+3) where
  entry := beginTag A
  body := fun tag => if ht : tag.val<A then r.body ⟨tag.val,ht⟩
    else if tag.val=A then pre
    else if tag.val=A+1 then post else []
  next := fun tag ram => if ht : tag.val<A then
      if r.terminal ⟨tag.val,ht⟩ then endTag A else embed (r.next ⟨tag.val,ht⟩ ram)
    else if tag.val=A then embed r.entry else doneTag A
  terminal := fun tag => decide (tag.val=A+2)
  safe := by
    intro tag i hi
    split_ifs at hi with ht he hr
    · exact r.safe ⟨tag.val,ht⟩ i hi
    · exact hpre i hi
    · exact hpost i hi
    · simp at hi
  terminal_empty := by
    intro tag ht
    simp only [decide_eq_true_eq] at ht
    simp only [ht,show ¬A+2<A by omega,↓reduceDIte,show ¬A+2=A by omega,
      show ¬A+2=A+1 by omega,↓reduceIte]

def before (q : Configuration) (pre : List (Instruction q)) (s : Machine q) : Machine q :=
  erasePC q (executeRaw q pre s).1

def after (q : Configuration) (post : List (Instruction q)) (s : Machine q) : Machine q :=
  erasePC q (executeRaw q post s).1

variable (q : Configuration) (pre post : List (Instruction q))
  (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i)
  {A : ℕ} (r : Routine q A)

@[simp] theorem body_embed (tag : Fin A) :
    (routine q pre post hpre hpost r).body (embed tag)=r.body tag := by
  simp only [routine,embed,tag.isLt,↓reduceDIte]

@[simp] theorem terminal_embed (tag : Fin A) :
    (routine q pre post hpre hpost r).terminal (embed tag)=false := by
  simp only [routine,embed,decide_eq_false_iff_not]
  have := tag.isLt
  omega

@[simp] theorem body_begin :
    (routine q pre post hpre hpost r).body (beginTag A)=pre := by
  simp [routine,beginTag]

@[simp] theorem body_end :
    (routine q pre post hpre hpost r).body (endTag A)=post := by
  simp [routine,endTag]

@[simp] theorem terminal_begin :
    (routine q pre post hpre hpost r).terminal (beginTag A)=false := by
  simp [routine,beginTag]

@[simp] theorem terminal_end :
    (routine q pre post hpre hpost r).terminal (endTag A)=false := by
  simp [routine,endTag]

@[simp] theorem terminal_done :
    (routine q pre post hpre hpost r).terminal (doneTag A)=true := by
  simp [routine,doneTag]

@[simp] theorem rawBody_embed (tag : Fin A) (s : Machine q) :
    (routine q pre post hpre hpost r).rawBody (embed tag) s=r.rawBody tag s := by
  simp only [Routine.rawBody,body_embed]

@[simp] theorem nextTag_embed (tag : Fin A) (ht : r.terminal tag=false) (s : Machine q) :
    (routine q pre post hpre hpost r).nextTag (embed tag) s=embed (r.nextTag tag s) := by
  rw [Routine.nextTag,rawBody_embed]
  simp [Routine.successor,routine,embed,ht,Routine.nextTag]

@[simp] theorem nextTag_terminal (tag : Fin A) (ht : r.terminal tag=true) (s : Machine q) :
    (routine q pre post hpre hpost r).nextTag (embed tag) s=endTag A := by
  simp only [Routine.nextTag,Routine.successor,routine,embed,tag.isLt,↓reduceDIte,ht,↓reduceIte]

@[simp] theorem nextTag_begin (s : Machine q) :
    (routine q pre post hpre hpost r).nextTag (beginTag A) s=embed r.entry := by
  simp [Routine.nextTag,Routine.successor,routine,beginTag]

@[simp] theorem nextTag_end (s : Machine q) :
    (routine q pre post hpre hpost r).nextTag (endTag A) s=doneTag A := by
  simp [Routine.nextTag,Routine.successor,routine,endTag]

theorem suffix_trace (s : Machine q) :
    (routine q pre post hpre hpost r).Trace (endTag A) s (doneTag A)
      (after q post s)
      ((post).length+1)
      (cost q (post)) := by
  have hd := Routine.Trace.done (r:=routine q pre post hpre hpost r)
    (doneTag A) (after q post s) (terminal_done q pre post hpre hpost r)
  have hs := Routine.Trace.step (r:=routine q pre post hpre hpost r)
    (endTag A) (doneTag A) s (after q post s) 0 0
    (terminal_end q pre post hpre hpost r)
  simpa only [body_end,Nat.add_zero] using hs (by
    simpa only [nextTag_end,Routine.rawBody,body_end,after,erasePC,setPC_setPC] using hd)

/-- An inner terminating trace becomes a returning trace; its terminal tag
executes an empty transition before the real suffix. -/
theorem inner_trace {tag finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (ht : r.Trace tag s finalTag final steps charge) :
    (routine q pre post hpre hpost r).Trace (embed tag) s (doneTag A)
      (after q post final)
      (steps+((post).length+1)+1)
      (charge+cost q (post)) := by
  induction ht with
  | done tag s ht =>
      have hb := r.terminal_empty tag ht
      have tail := suffix_trace q pre post hpre hpost r (erasePC q s)
      have hs := Routine.Trace.step (r:=routine q pre post hpre hpost r)
        (embed tag) (doneTag A) s (after q post (erasePC q s))
        ((post).length+1)
        (cost q (post))
        (terminal_embed q pre post hpre hpost r tag)
      simpa only [body_embed,hb,List.length_nil,Routine.rawBody,executeRaw,CommonStaticSchedule.cost,
        Nat.zero_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
        hs (by simpa only [nextTag_terminal q pre post hpre hpost r tag ht,
          rawBody_embed,Routine.rawBody,body_embed,hb,executeRaw] using tail)
  | step tag finalTag s final steps charge ht tail ih =>
      have hs := Routine.Trace.step (r:=routine q pre post hpre hpost r)
        (embed tag) (doneTag A) s (after q post final)
        (steps+((post).length+1)+1)
        (charge+cost q (post))
        (terminal_embed q pre post hpre hpost r tag)
      simpa only [body_embed,Nat.add_assoc] using hs (by
        simpa only [nextTag_embed q pre post hpre hpost r tag ht,rawBody_embed] using ih)

theorem trace {finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (ht : r.Trace r.entry (before q pre s) finalTag final steps charge) :
    (routine q pre post hpre hpost r).Trace (beginTag A) s (doneTag A)
      (after q post final)
      ((pre).length+steps+
        (post).length+3)
      (cost q (pre)+charge+
        cost q (post)) := by
  have hi := inner_trace q pre post hpre hpost r ht
  have hs := Routine.Trace.step (r:=routine q pre post hpre hpost r)
    (beginTag A) (doneTag A) s (after q post final)
    (steps+((post).length+1)+1)
    (charge+cost q (post))
    (terminal_begin q pre post hpre hpost r)
  have hh := hs (by
    simpa only [nextTag_begin,Routine.rawBody,body_begin,before] using hi)
  convert hh using 1 <;> simp only [body_begin] <;> omega

theorem fits (stride : ℕ)
    (hi : ∀ tag,(r.body tag).length<stride)
    (he : (pre).length<stride)
    (hr : (post).length<stride)
    (hc : (A+3)*stride≤q.N^q.exponent) :
    (routine q pre post hpre hpost r).Fits stride := by
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


end
end CodedSorting.CommonRoutineSandwich
