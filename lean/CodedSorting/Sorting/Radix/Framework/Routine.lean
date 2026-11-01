import CodedSorting.Shared.Memory.TaggedController

section Routine
/-! A finite public control family. Bodies are actual instruction lists;
transitions inspect only the currently resident RAM. Clearing the reserved
counter before a transition permits the same routine to be embedded in an
outer controller without changing its data-dependent decisions. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonMSDRoutine
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine RAM)
noncomputable section

structure Routine (q : Configuration) (A : ℕ) where
  entry : Fin A
  body : Fin A → List (Instruction q)
  next : Fin A → RAM q → Fin A
  terminal : Fin A → Bool
  safe : ∀ tag,∀ i∈body tag,RespectsPC q i
  terminal_empty : ∀ tag,terminal tag=true → body tag=[]

namespace Routine
variable {q : Configuration} {A : ℕ}

def successor (r : Routine q A) (tag : Fin A) (ram : RAM q) : Fin A :=
  r.next tag (setPC q 0 ram)

@[simp] theorem successor_setPC (r : Routine q A) (tag : Fin A) (ram : RAM q) (k : ℕ) :
    r.successor tag (setPC q k ram)=r.successor tag ram := by
  simp only [successor,setPC_setPC]

def transition (r : Routine q A) (stride : ℕ) (tag : Fin A) (ram : RAM q) : RAM q :=
  setPC q ((r.successor tag ram).val*stride) ram

def policy (r : Routine q A) (stride : ℕ) : SourcePolicy q :=
  CommonTaggedController.policy q stride r.body r.terminal (r.transition stride)

def Fits (r : Routine q A) (stride : ℕ) : Prop :=
  (∀ tag,(r.body tag).length<stride) ∧ A*stride≤q.N^q.exponent

def rawBody (r : Routine q A) (tag : Fin A) (s : Machine q) : Machine q :=
  erasePC q (executeRaw q (r.body tag) s).1

def nextTag (r : Routine q A) (tag : Fin A) (s : Machine q) : Fin A :=
  r.successor tag (r.rawBody tag s).ram

theorem rawBody_congr (r : Routine q A) (tag : Fin A) (s t : Machine q)
    (h : erasePC q s=erasePC q t) : r.rawBody tag s=r.rawBody tag t := by
  have hs := CommonStaticSchedule.execute_payload q (r.body tag) (r.safe tag) 0 s s rfl
  have ht := CommonStaticSchedule.execute_payload q (r.body tag) (r.safe tag) 0 s t h
  exact hs.symm.trans ht

theorem tag_capacity (r : Routine q A) (stride : ℕ) (h : r.Fits stride) (tag : Fin A) :
    tag.val*stride≤q.N^q.exponent :=
  (Nat.mul_le_mul_right stride (Nat.le_of_lt tag.isLt)).trans h.2

theorem body_capacity (r : Routine q A) (stride : ℕ) (h : r.Fits stride) (tag : Fin A) :
    tag.val*stride+(r.body tag).length≤q.N^q.exponent := by
  have ht := tag.isLt
  have hl := h.1 tag
  have hc := h.2
  nlinarith

theorem call (r : Routine q A) (stride : ℕ) (h : r.Fits stride)
    (tag : Fin A) (ht : r.terminal tag=false) (s : Machine q)
    (hpc : pc q s.ram=tag.val*stride) :
    let out := ControlledNormalization.runLogical (r.policy stride) ((r.body tag).length+1) s
    erasePC q out.1=r.rawBody tag s ∧
    pc q out.1.ram=(r.nextTag tag s).val*stride ∧
    out.2=cost q (r.body tag) := by
  have hc := CommonTaggedController.call q stride r.body r.terminal (r.transition stride)
    tag (h.1 tag) (r.body_capacity stride h tag) ht s hpc
  have hp := CommonTaggedSchedule.execute_payload q stride tag.val 0 (r.body tag)
    (r.safe tag) s s rfl
  dsimp only [policy]
  rw [hc]
  refine ⟨?_,?_,rfl⟩
  · simpa only [erasePC,transition,setPC_setPC,rawBody] using hp
  · change pc q (setPC q _ _)=_
    rw [pc_setPC q _ _ (r.tag_capacity stride h _)]
    congr 1
    unfold nextTag rawBody successor
    have hh := congrArg (fun t : Machine q => t.ram) hp
    simpa only [erasePC,setPC_setPC] using congrArg (fun ram => (r.next tag ram).val) hh

theorem halted (r : Routine q A) (stride : ℕ) (h : r.Fits stride)
    (tag : Fin A) (ht : r.terminal tag=true) (s : Machine q)
    (hpc : pc q s.ram=tag.val*stride) : r.policy stride s.ram=none := by
  apply CommonTaggedController.halted q stride r.body r.terminal (r.transition stride)
    tag (h.1 tag) ht s
  simpa only [r.terminal_empty tag ht,List.length_nil,Nat.add_zero] using hpc

/-- This inductive trace is proof instrumentation. Every edge is an
actual finite instruction execution, not a macro oracle. -/
inductive Trace (r : Routine q A) : Fin A → Machine q → Fin A → Machine q → ℕ → ℕ → Prop
  | done (tag : Fin A) (s : Machine q) (ht : r.terminal tag=true) :
      r.Trace tag s tag (erasePC q s) 0 0
  | step (tag finalTag : Fin A) (s final : Machine q) (steps charge : ℕ)
      (ht : r.terminal tag=false)
      (tail : r.Trace (r.nextTag tag s) (r.rawBody tag s) finalTag final steps charge) :
      r.Trace tag s finalTag final ((r.body tag).length+1+steps)
        (cost q (r.body tag)+charge)

theorem trace_congr (r : Routine q A) {tag finalTag : Fin A} {s final : Machine q}
    {steps charge : ℕ} (trace : r.Trace tag s finalTag final steps charge)
    (t : Machine q) (h : erasePC q t=erasePC q s) :
    r.Trace tag t finalTag final steps charge := by
  induction trace generalizing t with
  | done tag s ht =>
      rw [←h]
      exact Trace.done tag t ht
  | step tag finalTag s final steps charge ht tail ih =>
      have hh := r.rawBody_congr tag t s h
      apply Trace.step tag finalTag t final steps charge ht
      simpa only [nextTag,hh] using tail

/-- A finite body trace compiles to one complete run of the fixed policy,
with exactly the same charge and final disk. -/
theorem trace_run_from (r : Routine q A) (stride : ℕ) (h : r.Fits stride)
    {tag finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (trace : r.Trace tag s finalTag final steps charge)
    (t : Machine q) (heq : erasePC q t=erasePC q s)
    (hpc : pc q t.ram=tag.val*stride) :
    let out := ControlledNormalization.runLogical (r.policy stride) steps t
    erasePC q out.1=final ∧ out.2=charge ∧
      pc q out.1.ram=finalTag.val*stride ∧ r.policy stride out.1.ram=none := by
  induction trace generalizing t with
  | done tag s ht =>
      exact ⟨heq,rfl,hpc,r.halted stride h tag ht t hpc⟩
  | step tag finalTag s final steps charge ht tail ih =>
      have hc := r.call stride h tag ht t hpc
      have hb := r.rawBody_congr tag t s heq
      have hn : r.nextTag tag t=r.nextTag tag s := by simp only [nextTag,hb]
      let mid := (ControlledNormalization.runLogical (r.policy stride) ((r.body tag).length+1) t).1
      have hm : erasePC q mid=erasePC q (r.rawBody tag s) := by
        rw [show erasePC q (r.rawBody tag s)=r.rawBody tag s by
          simp only [rawBody,erasePC,setPC_setPC]]
        exact hc.1.trans hb
      have hi := ih mid hm (by rw [←hn];exact hc.2.1)
      dsimp only
      rw [CommonPolicyComposition.run_add]
      exact ⟨hi.1,by rw [hc.2.2,hi.2.1],hi.2.2.1,hi.2.2.2⟩

theorem trace_run (r : Routine q A) (stride : ℕ) (h : r.Fits stride)
    {tag finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (trace : r.Trace tag s finalTag final steps charge)
    (hpc : pc q s.ram=tag.val*stride) :
    let out := ControlledNormalization.runLogical (r.policy stride) steps s
    erasePC q out.1=final ∧ out.2=charge ∧
      pc q out.1.ram=finalTag.val*stride ∧ r.policy stride out.1.ram=none :=
  r.trace_run_from stride h trace s rfl hpc

end Routine
end
end CodedSorting.CommonMSDRoutine
end Routine

section RoutineDeterminism
/-! Terminating traces of the finite RAM-driven routine are deterministic.
Thus a cost derivation applies to the same execution as an existing semantic
endpoint, rather than selecting an unrelated successful run. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDRoutine.Routine
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine)

variable {q : Configuration} {A : ℕ} {r : Routine q A}

theorem Trace.unique {start finish₁ finish₂ : Fin A} {s t₁ t₂ : Machine q}
    {steps₁ steps₂ charge₁ charge₂ : ℕ}
    (h₁ : r.Trace start s finish₁ t₁ steps₁ charge₁)
    (h₂ : r.Trace start s finish₂ t₂ steps₂ charge₂) :
    finish₁=finish₂ ∧ t₁=t₂ ∧ steps₁=steps₂ ∧ charge₁=charge₂ := by
  induction h₁ generalizing finish₂ t₂ steps₂ charge₂ with
  | done tag s ht =>
    cases h₂ with
    | done => exact ⟨rfl,rfl,rfl,rfl⟩
    | step _ _ _ _ _ _ ht' _ => simp_all
  | step tag finish s final steps charge ht tail ih =>
    cases h₂ with
    | done _ _ ht' => simp_all
    | step _ finish₂ _ t₂ steps₂ charge₂ ht' tail₂ =>
      obtain ⟨hf,hm,hs,hc⟩ := ih tail₂
      exact ⟨hf,hm,congrArg (fun n=>(r.body tag).length+1+n) hs,
        congrArg (fun n=>cost q (r.body tag)+n) hc⟩

theorem Trace.charge_eq {start finish₁ finish₂ : Fin A} {s t₁ t₂ : Machine q}
    {steps₁ steps₂ charge₁ charge₂ : ℕ}
    (h₁ : r.Trace start s finish₁ t₁ steps₁ charge₁)
    (h₂ : r.Trace start s finish₂ t₂ steps₂ charge₂) : charge₁=charge₂ :=
  (h₁.unique h₂).2.2.2

end CodedSorting.CommonMSDRoutine.Routine
end RoutineDeterminism

section RoutinePad
/-! Extend a public routine to a common finite tag space. Unused tags halt;
reachable tags execute the original instructions and inspect the same RAM.
This permits one fixed global controller to contain routines for all public
subproblem sizes without including input data in its program description. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonMSDRoutinePad
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonLeafProgram (Machine)
noncomputable section

def embed {A B : ℕ} (h : A≤B) (tag : Fin A) : Fin B :=
  ⟨tag.val,tag.isLt.trans_le h⟩

def extend {q : Configuration} {A B : ℕ} (r : Routine q A) (h : A≤B) : Routine q B where
  entry := embed h r.entry
  body := fun tag => if ht : tag.val<A then r.body ⟨tag.val,ht⟩ else []
  next := fun tag ram => if ht : tag.val<A then embed h (r.next ⟨tag.val,ht⟩ ram) else tag
  terminal := fun tag => if ht : tag.val<A then r.terminal ⟨tag.val,ht⟩ else true
  safe := by
    intro tag i hi
    split_ifs at hi with ht
    · exact r.safe ⟨tag.val,ht⟩ i hi
    · simp at hi
  terminal_empty := by
    intro tag ht
    split_ifs at ht ⊢ with htag
    · exact r.terminal_empty ⟨tag.val,htag⟩ ht
    · rfl

@[simp] theorem body_embed {q : Configuration} {A B : ℕ} (r : Routine q A)
    (h : A≤B) (tag : Fin A) : (extend r h).body (embed h tag)=r.body tag := by
  simp only [extend,embed,tag.isLt,↓reduceDIte]

@[simp] theorem terminal_embed {q : Configuration} {A B : ℕ} (r : Routine q A)
    (h : A≤B) (tag : Fin A) : (extend r h).terminal (embed h tag)=r.terminal tag := by
  simp only [extend,embed,tag.isLt,↓reduceDIte]

@[simp] theorem successor_embed {q : Configuration} {A B : ℕ} (r : Routine q A)
    (h : A≤B) (tag : Fin A) (ram : CommonLeafProgram.RAM q) :
    (extend r h).successor (embed h tag) ram=embed h (r.successor tag ram) := by
  simp only [Routine.successor,extend,embed,tag.isLt,↓reduceDIte]

@[simp] theorem rawBody_embed {q : Configuration} {A B : ℕ} (r : Routine q A)
    (h : A≤B) (tag : Fin A) (s : Machine q) :
    (extend r h).rawBody (embed h tag) s=r.rawBody tag s := by
  simp only [Routine.rawBody,body_embed]

@[simp] theorem nextTag_embed {q : Configuration} {A B : ℕ} (r : Routine q A)
    (h : A≤B) (tag : Fin A) (s : Machine q) :
    (extend r h).nextTag (embed h tag) s=embed h (r.nextTag tag s) := by
  simp only [Routine.nextTag,rawBody_embed,successor_embed]

/-- Padding changes neither the execution trace nor its transfer charge. -/
theorem trace {q : Configuration} {A B : ℕ} (r : Routine q A) (h : A≤B)
    {tag finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (ht : r.Trace tag s finalTag final steps charge) :
    (extend r h).Trace (embed h tag) s (embed h finalTag) final steps charge := by
  induction ht with
  | done tag s ht =>
      exact Routine.Trace.done _ s (by simpa only [terminal_embed] using ht)
  | step tag finalTag s final steps charge ht tail ih =>
      simpa only [body_embed,nextTag_embed,rawBody_embed] using
        Routine.Trace.step (r:=extend r h) (embed h tag) (embed h finalTag)
          s final steps charge (by simpa only [terminal_embed] using ht)
          (by simpa only [nextTag_embed,rawBody_embed] using ih)

def idle (q : Configuration) : Routine q 1 where
  entry := 0
  body := fun _=>[]
  next := fun t _=>t
  terminal := fun _=>true
  safe := by simp
  terminal_empty := by simp

end
end CodedSorting.CommonMSDRoutinePad
end RoutinePad

section RoutinePath
/-! Finite execution paths may stop at a continuation before the whole
controller halts. They compose actual routine bodies and can be joined
across subroutine embeddings; terminal paths recover the existing Trace. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDRoutine
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine RAM)
noncomputable section
namespace Routine
variable {q : Configuration} {A B : ℕ}

inductive Path (r : Routine q A) : Fin A → Machine q → Fin A → Machine q → ℕ → ℕ → Prop
  | done (tag : Fin A) (s : Machine q) : r.Path tag s tag (erasePC q s) 0 0
  | step (tag finalTag : Fin A) (s final : Machine q) (steps charge : ℕ)
      (ht : r.terminal tag=false)
      (tail : r.Path (r.nextTag tag s) (r.rawBody tag s) finalTag final steps charge) :
      r.Path tag s finalTag final ((r.body tag).length+1+steps)
        (cost q (r.body tag)+charge)

theorem path_congr (r : Routine q A) {tag finalTag : Fin A} {s final : Machine q}
    {steps charge : ℕ} (path : r.Path tag s finalTag final steps charge)
    (t : Machine q) (h : erasePC q t=erasePC q s) :
    r.Path tag t finalTag final steps charge := by
  induction path generalizing t with
  | done tag s =>
      rw [←h]
      exact Path.done tag t
  | step tag finalTag s final steps charge ht tail ih =>
      have hh := r.rawBody_congr tag t s h
      apply Path.step tag finalTag t final steps charge ht
      simpa only [nextTag,hh] using tail

theorem path_final_erased (r : Routine q A) {tag finalTag : Fin A} {s final : Machine q}
    {steps charge : ℕ} (path : r.Path tag s finalTag final steps charge) :
    erasePC q final=final := by
  induction path with
  | done tag s => simp only [erasePC,setPC_setPC]
  | step tag finalTag s final steps charge ht tail ih => exact ih

theorem path_append (r : Routine q A) {tag midTag finalTag : Fin A}
    {s mid final : Machine q} {a b c d : ℕ}
    (first : r.Path tag s midTag mid a c) (second : r.Path midTag mid finalTag final b d) :
    r.Path tag s finalTag final (a+b) (c+d) := by
  induction first with
  | done tag s =>
      simpa only [Nat.zero_add] using r.path_congr second s
        (by simp only [erasePC,setPC_setPC])
  | step tag midTag s mid a c ht tail ih =>
      simpa only [Nat.add_assoc] using Path.step tag finalTag s final (a+b) (c+d) ht (ih second)

theorem path_toTrace (r : Routine q A) {tag finalTag : Fin A} {s final : Machine q}
    {steps charge : ℕ} (path : r.Path tag s finalTag final steps charge)
    (ht : r.terminal finalTag=true) : r.Trace tag s finalTag final steps charge := by
  induction path with
  | done tag s => exact Trace.done tag s ht
  | step tag finalTag s final steps charge hactive tail ih =>
      exact Trace.step tag finalTag s final steps charge hactive (ih ht)

theorem trace_toPath (r : Routine q A) {tag finalTag : Fin A} {s final : Machine q}
    {steps charge : ℕ} (trace : r.Trace tag s finalTag final steps charge) :
    r.Path tag s finalTag final steps charge := by
  induction trace with
  | done tag s ht => exact Path.done tag s
  | step tag finalTag s final steps charge ht tail ih =>
      exact Path.step tag finalTag s final steps charge ht ih

theorem path_run_from (r : Routine q A) (stride : ℕ) (h : r.Fits stride)
    {tag finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (path : r.Path tag s finalTag final steps charge)
    (t : Machine q) (heq : erasePC q t=erasePC q s)
    (hpc : pc q t.ram=tag.val*stride) :
    let out := ControlledNormalization.runLogical (r.policy stride) steps t
    erasePC q out.1=final ∧ out.2=charge ∧ pc q out.1.ram=finalTag.val*stride := by
  induction path generalizing t with
  | done tag s => exact ⟨heq,rfl,hpc⟩
  | step tag finalTag s final steps charge ht tail ih =>
      have hc := r.call stride h tag ht t hpc
      have hb := r.rawBody_congr tag t s heq
      have hn : r.nextTag tag t=r.nextTag tag s := by simp only [nextTag,hb]
      let mid := (ControlledNormalization.runLogical (r.policy stride) ((r.body tag).length+1) t).1
      have hm : erasePC q mid=erasePC q (r.rawBody tag s) := by
        rw [show erasePC q (r.rawBody tag s)=r.rawBody tag s by
          simp only [rawBody,erasePC,setPC_setPC]]
        exact hc.1.trans hb
      have hi := ih mid hm (by rw [←hn];exact hc.2.1)
      dsimp only
      rw [CommonPolicyComposition.run_add]
      exact ⟨hi.1,by rw [hc.2.2,hi.2.1],hi.2.2⟩

theorem path_run (r : Routine q A) (stride : ℕ) (h : r.Fits stride)
    {tag finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (path : r.Path tag s finalTag final steps charge)
    (hpc : pc q s.ram=tag.val*stride) :
    let out := ControlledNormalization.runLogical (r.policy stride) steps s
    erasePC q out.1=final ∧ out.2=charge ∧ pc q out.1.ram=finalTag.val*stride :=
  r.path_run_from stride h path s rfl hpc

/-- Embed actual bodies in a larger controller. The source terminal tag
may become an ordinary continuation in the target, since Path stops there. -/
theorem path_map (r : Routine q A) (outer : Routine q B) (embed : Fin A → Fin B)
    (hb : ∀ tag,r.terminal tag=false → outer.body (embed tag)=r.body tag)
    (hn : ∀ tag s,r.terminal tag=false → outer.nextTag (embed tag) s=embed (r.nextTag tag s))
    (ht : ∀ tag,r.terminal tag=false → outer.terminal (embed tag)=false)
    {tag finalTag : Fin A} {s final : Machine q} {steps charge : ℕ}
    (path : r.Path tag s finalTag final steps charge) :
    outer.Path (embed tag) s (embed finalTag) final steps charge := by
  induction path with
  | done tag s => exact Path.done (embed tag) s
  | step tag finalTag s final steps charge hactive tail ih =>
      have hh : outer.rawBody (embed tag) s=r.rawBody tag s := by
        simp only [rawBody,hb tag hactive]
      have hi : outer.Path (outer.nextTag (embed tag) s) (outer.rawBody (embed tag) s)
          (embed finalTag) final steps charge := by
        rw [hn tag s hactive,hh]
        exact ih
      simpa only [hb tag hactive] using Path.step (embed tag) (embed finalTag) s final steps charge
        (ht tag hactive) hi

end Routine
end
end CodedSorting.CommonMSDRoutine
end RoutinePath
