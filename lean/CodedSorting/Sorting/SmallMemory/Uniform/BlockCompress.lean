import CodedSorting.Sorting.SmallMemory.SmallSort

section BlockFormat
/-! Compact-to-sparse conversion with one fixed loop body. The cursor and
halt flag are actual external blocks; neither is an additional resident
register. The final halt test is a charged block read. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.TwoWordUniformBlockFormat
open TwoWordBlockLift TwoWordBlockFormat
variable {B w : ℕ}
abbrev Word (w : ℕ) := Fin (2^w)
def zero (w : ℕ) : Word w := ⟨0,by positivity⟩
def one {w : ℕ} (hw : 0<w) : Word w := ⟨1,by
  have h := Nat.pow_le_pow_right (by omega : 1≤2) hw
  exact lt_of_lt_of_le (by decide : 1<2) h⟩
def inc (x : Word w) : Word w := ⟨(x.val+1)%(2^w),Nat.mod_lt _ (by positivity)⟩
def cursor (base w : ℕ) : ℕ := base+10+6*2^w
def flag (base w : ℕ) : ℕ := cursor base w+1

structure LoopProgram (B : ℕ) (W : Type*) where
  flagAddress : ℕ
  halt : W
  body : List (Command B W)

def check {W : Type*} (p : LoopProgram B W) (s : State B W) : State B W :=
  step (.readLeft p.flagAddress) s
def next {W : Type*} (p : LoopProgram B W) (s : State B W) : State B W :=
  execute p.body (check p s)
inductive Executes {W : Type*} (hB : 0<B) (p : LoopProgram B W) :
    State B W → State B W → ℕ → Prop where
  | stop (s : State B W) (h : (check p s).left ⟨0,hB⟩=p.halt) :
      Executes hB p s (check p s) 1
  | more (s t : State B W) (cost : ℕ)
      (h : (check p s).left ⟨0,hB⟩≠p.halt)
      (rest : Executes hB p (next p s) t cost) :
      Executes hB p s t (1+transfers p.body+cost)

/-- A loop invariant indexed by proof-only progress. The program itself
has no fuel or input-length command list. -/
theorem loop_invariant {W : Type*} (hB : 0<B) (p : LoopProgram B W)
    (n : ℕ) (P : ℕ → State B W → Prop)
    (halt : ∀s,P n s → (check p s).left ⟨0,hB⟩=p.halt)
    (stop : ∀s,P n s → P n (check p s))
    (advance : ∀j s,j<n → P j s →
      (check p s).left ⟨0,hB⟩≠p.halt ∧ P (j+1) (next p s))
    (j : ℕ) (s : State B W) (hj : j≤n) (hs : P j s) :
    ∃t,Executes hB p s t ((1+transfers p.body)*(n-j)+1) ∧ P n t := by
  have aux : ∀ remaining j s,j+remaining=n → P j s →
      ∃t,Executes hB p s t ((1+transfers p.body)*remaining+1) ∧ P n t := by
    intro remaining
    induction remaining with
    | zero =>
      intro j s he hp
      have hjn : j=n := by omega
      subst j
      exact ⟨check p s,by simpa using Executes.stop s (halt s hp),stop s hp⟩
    | succ remaining ih =>
      intro j s he hp
      obtain ⟨hc,hn⟩ := advance j s (by omega) hp
      obtain ⟨t,ht,hp⟩ := ih (j+1) (next p s) (by omega) hn
      refine ⟨t,?_,hp⟩
      convert Executes.more s t _ hc ht using 1 <;> simp [Nat.mul_add] <;> omega
  exact aux (n-j) j s (by omega) hs

def setup (hB : 0<B) (hw : 0<w) (base n : ℕ) : List (Command B (Word w)) :=
  [.cpu (fun _ => (fun _ => zero w,fun _ => if n=0 then one hw else zero w)),
   .writeLeft (cursor base w),.writeRight (fun _ => flag base w)]

def Ready (hB : 0<B) (hw : 0<w) (base n j : ℕ) (s : State B (Word w)) : Prop :=
  (s.disk (cursor base w) ⟨0,hB⟩).val=j%(2^w) ∧
    s.disk (flag base w) ⟨0,hB⟩=(if j=n then one hw else zero w)

theorem setup_ready (hB : 0<B) (hw : 0<w) (base n : ℕ)
    (s : State B (Word w)) : Ready hB hw base n 0 (execute (setup hB hw base n) s) := by
  by_cases hn : n=0 <;> simp [Ready,setup,execute,step,flag,zero,Function.update_apply,hn,eq_comm]

theorem setup_disk (hB : 0<B) (hw : 0<w) (base n : ℕ)
    (s : State B (Word w)) (a : ℕ) (ha : a<cursor base w) :
    (execute (setup hB hw base n) s).disk a=s.disk a := by
  simp [setup,execute,step,Function.update_of_ne,show a≠cursor base w by omega,
    show a≠flag base w by unfold flag;omega]

theorem setup_cost (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    transfers (setup hB hw base n)=2 := rfl

/-- Seven fixed instructions: cursor read, compact read, local selection,
sparse write, local counter/flag update, cursor write, flag write. -/
def body (hB : 0<B) (hw : 0<w) (base n : ℕ) : List (Command B (Word w)) :=
  [.readLeft (cursor base w),
   .readRight (fun p => (p.1 ⟨0,hB⟩).val/B),
   .cpu (fun p => (p.1,fun _ => p.2 (cell hB (p.1 ⟨0,hB⟩).val))),
   .writeRight (fun p => base+5+(p.1 ⟨0,hB⟩).val),
   .cpu (fun p => (fun _ => inc (p.1 ⟨0,hB⟩),
     fun _ => if (p.1 ⟨0,hB⟩).val+1=n then one hw else zero w)),
   .writeLeft (cursor base w),.writeRight (fun _ => flag base w)]
def program (hB : 0<B) (hw : 0<w) (base n : ℕ) : LoopProgram B (Word w) :=
  ⟨flag base w,one hw,body hB hw base n⟩
theorem body_length (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    (program hB hw base n).body.length=7 := rfl
theorem body_cost (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    transfers (program hB hw base n).body=5 := rfl

/-- The exact disk effect includes both charged control-block writes. -/
theorem next_disk (hB : 0<B) (hw : 0<w) (base n : ℕ)
    (s : State B (Word w)) :
    (next (program hB hw base n) s).disk =
      Function.update (Function.update
        (Function.update s.disk (base+5+(s.disk (cursor base w) ⟨0,hB⟩).val)
          (fun _ => wordAt hB s.disk (s.disk (cursor base w) ⟨0,hB⟩).val))
        (cursor base w) (fun _ => inc (s.disk (cursor base w) ⟨0,hB⟩)))
        (flag base w) (fun _ =>
          if (s.disk (cursor base w) ⟨0,hB⟩).val+1=n then one hw else zero w) := rfl

def Below {W : Type*} (base w : ℕ) (s t : State B W) : Prop :=
  ∀a,a<cursor base w → s.disk a=t.disk a

theorem ready_cursor (hB : 0<B) (hw : 0<w) (base n j : ℕ)
    (s : State B (Word w)) (hN : n≤2^w) (hj : j<n)
    (hs : Ready hB hw base n j s) :
    (s.disk (cursor base w) ⟨0,hB⟩).val=j := by
  rw [hs.1,Nat.mod_eq_of_lt (by omega)]

theorem next_ready (hB : 0<B) (hw : 0<w) (base n j : ℕ)
    (s : State B (Word w)) (hN : n≤2^w) (hj : j<n)
    (hs : Ready hB hw base n j s) :
    Ready hB hw base n (j+1) (next (program hB hw base n) s) := by
  have hc := ready_cursor hB hw base n j s hN hj hs
  simp only [Ready,next_disk]
  constructor
  · simp [flag,Function.update_apply,inc,hc]
  · simp [Function.update_apply,hc]

theorem next_below (hB : 0<B) (hw : 0<w) (base n j : ℕ)
    (s t : State B (Word w)) (hN : n≤2^w) (hj : j<n)
    (hs : Ready hB hw base n j s) (hst : Below base w s t) :
    Below base w (next (program hB hw base n) s)
      (execute (expandOne hB base j) t) := by
  have hc := ready_cursor hB hw base n j s hN hj hs
  intro a ha
  rw [next_disk,expandOne_disk,hc]
  rw [Function.update_of_ne (by unfold flag;omega : a≠flag base w),
    Function.update_of_ne (by omega : a≠cursor base w)]
  by_cases he : a=base+5+j
  · subst a
    rw [Function.update_self,Function.update_self]
    funext i
    unfold wordAt
    rw [hst (j/B) (by have:=Nat.div_le_self j B;unfold cursor;omega)]
  · rw [Function.update_of_ne he,Function.update_of_ne he]
    exact hst a ha

/-- Execution refines the old scan's disk effect, but the actual program
has a fixed seven-instruction loop body for every input size. -/
theorem refines (hB : 0<B) (hw : 0<w) (base n : ℕ) (hN : n≤2^w)
    (s : State B (Word w)) :
    ∃t,Executes hB (program hB hw base n) (execute (setup hB hw base n) s) t (6*n+1) ∧
      Below base w t (execute (expand hB base n) s) := by
  let P : ℕ→State B (Word w)→Prop := fun j t =>
    Ready hB hw base n j t ∧ Below base w t (execute (expand hB base j) s)
  have hh : ∀t,P n t → (check (program hB hw base n) t).left ⟨0,hB⟩=
      (program hB hw base n).halt := by
    intro t ht
    change t.disk (flag base w) ⟨0,hB⟩=one hw
    simpa using ht.1.2
  have hs : ∀t,P n t → P n (check (program hB hw base n) t) := by
    intro t ht
    exact ht
  have ha : ∀j t,j<n → P j t →
      (check (program hB hw base n) t).left ⟨0,hB⟩≠(program hB hw base n).halt ∧
      P (j+1) (next (program hB hw base n) t) := by
    intro j t hj ht
    refine ⟨?_,next_ready hB hw base n j t hN hj ht.1,?_⟩
    · change t.disk (flag base w) ⟨0,hB⟩≠one hw
      rw [ht.1.2,if_neg (by omega)]
      intro he
      have hv := congrArg Fin.val he
      simp [zero,one] at hv
    · change Below base w _ (execute (expand hB base (j+1)) s)
      rw [expand,execute_append]
      exact next_below hB hw base n j t _ hN hj ht.1 ht.2
  have hi : P 0 (execute (setup hB hw base n) s) :=
    ⟨setup_ready hB hw base n s,fun a ha => setup_disk hB hw base n s a ha⟩
  obtain ⟨t,ht,hp⟩ := loop_invariant hB (program hB hw base n) n P hh hs ha 0 _
    (Nat.zero_le _) hi
  refine ⟨t,?_,hp.2⟩
  simpa only [body_cost,Nat.sub_zero] using ht

/-- Full compact-file expansion; the setup costs two further transfers. -/
theorem complete (hB : 0<B) (hw : 0<w) (base n : ℕ) (hN : n≤2^w)
    (hsep : n≤base) (s : State B (Word w)) (xs : List (Word w))
    (hlen : xs.length=n) (hin : File hB s.disk xs) :
    ∃t,Executes hB (program hB hw base n) (execute (setup hB hw base n) s) t (6*n+1) ∧
      (∀j : Fin xs.length,(observe hB base t).disk (5+j.val)=xs.get j) ∧
      Below base w t (execute (expand hB base n) s) := by
  obtain ⟨t,ht,hbelow⟩ := refines hB hw base n hN s
  refine ⟨t,ht,?_,hbelow⟩
  intro j
  change t.disk (base+(5+j.val)) ⟨0,hB⟩=xs.get j
  rw [hbelow _ (by have:=j.isLt;unfold cursor;omega)]
  exact expand_correct hB base n s xs hlen hsep hin j

def BoundedProgram {W : Type*} (L : ℕ) (p : LoopProgram B W) : Prop :=
  p.flagAddress<L ∧ TwoWordBlockFootprint.BoundedCode L p.body

theorem loop_frame {W : Type*} (hB : 0<B) (L : ℕ) (p : LoopProgram B W)
    (hb : BoundedProgram L p) {s t : State B W} {c : ℕ}
    (h : Executes hB p s t c) (a : ℕ) (ha : L≤a) : t.disk a=s.disk a := by
  classical
  induction h with
  | stop s h => rfl
  | more s t c h rest ih =>
    rw [ih]
    exact TwoWordBlockFootprint.execute_frame L p.body hb.2 (check p s) a ha

theorem setupBound (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    TwoWordBlockFootprint.BoundedCode (cursor base w+2) (setup hB hw base n) := by
  intro cmd hc
  simp only [setup,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl
  · trivial
  · change cursor base w<cursor base w+2;omega
  · intro r;change flag base w<cursor base w+2;unfold flag;omega

theorem bodyBound (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    BoundedProgram (cursor base w+2) (program hB hw base n) := by
  constructor
  · change flag base w<cursor base w+2;unfold flag;omega
  · intro cmd hc
    simp only [program,body,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change cursor base w<cursor base w+2;omega
    · intro r
      have hv := (r.1 ⟨0,hB⟩).isLt
      have hd := Nat.div_le_self (r.1 ⟨0,hB⟩).val B
      change (r.1 ⟨0,hB⟩).val/B<cursor base w+2
      unfold cursor;omega
    · trivial
    · intro r
      have hv := (r.1 ⟨0,hB⟩).isLt
      change base+5+(r.1 ⟨0,hB⟩).val<cursor base w+2
      unfold cursor;omega
    · trivial
    · change cursor base w<cursor base w+2;omega
    · intro r;change flag base w<cursor base w+2;unfold flag;omega

theorem setup_length (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    (setup hB hw base n).length=3 := rfl

end CodedSorting.TwoWordUniformBlockFormat
end BlockFormat

section BlockCompress
/-! Uniform sparse-to-compact conversion in the same two physical buffers.
When B≥2, the first buffer retains the data word and cursor in two cells
while the second buffer performs the compact read-modify-write. For B=1,
the destination is a complete block and needs no read-modify-write. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.TwoWordUniformBlockCompress
open TwoWordBlockLift TwoWordBlockFormat TwoWordRadixInsert
variable {B w : ℕ}

def smallBody (hB : 0<B) (base pointer : ℕ) : List (Command B (Word w)) :=
  [.readLeft pointer,
   .readRight (fun p => base+5+(p.1 ⟨0,hB⟩).val),
   .writeRight (fun p => (p.1 ⟨0,hB⟩).val/B)]

def largeBody (hB : 0<B) (h2 : 2≤B) (base pointer : ℕ) : List (Command B (Word w)) :=
  [.readLeft pointer,
   .readRight (fun p => base+5+(p.1 ⟨0,hB⟩).val),
   .cpu (fun p => ((fun i => if i.val=0 then p.2 ⟨0,hB⟩ else p.1 ⟨0,hB⟩),p.2)),
   .readRight (fun p => (p.1 ⟨1,by omega⟩).val/B),
   .cpu (fun p => (p.1,Function.update p.2 (cell hB (p.1 ⟨1,by omega⟩).val)
     (p.1 ⟨0,hB⟩))),
   .writeRight (fun p => (p.1 ⟨1,by omega⟩).val/B)]

def dataBody (hB : 0<B) (base pointer : ℕ) : List (Command B (Word w)) :=
  if h2 : 2≤B then largeBody hB h2 base pointer else smallBody hB base pointer

theorem largeBody_disk (hB : 0<B) (h2 : 2≤B) (base pointer k : ℕ)
    (s : State B (Word w)) (hc : (s.disk pointer ⟨0,hB⟩).val=k) :
    (execute (largeBody hB h2 base pointer) s).disk=
      (execute (compressOne hB base k) s).disk := by
  simp only [largeBody,execute,step,Fin.coe_ofNat_eq_mod,Nat.zero_mod,
    ↓reduceIte,Nat.one_ne_zero,hc,compressOne_disk]

theorem smallBody_disk (hB : 0<B) (h1 : B=1) (base pointer k : ℕ)
    (s : State B (Word w)) (hc : (s.disk pointer ⟨0,hB⟩).val=k) :
    (execute (smallBody hB base pointer) s).disk=
      (execute (compressOne hB base k) s).disk := by
  subst B
  have hv : s.disk (base+5+k)=
      Function.update (s.disk k) (cell hB k) (s.disk (base+5+k) ⟨0,hB⟩) := by
    funext i
    have hi : i=(⟨0,hB⟩ : Fin 1) := Subsingleton.elim _ _
    have hz : cell hB k=(⟨0,hB⟩ : Fin 1) := Subsingleton.elim _ _
    rw [hi,hz,Function.update_self]
  simpa only [smallBody,execute,step,hc,Nat.div_one,compressOne_disk] using
    congrArg (Function.update s.disk k) hv

theorem dataBody_disk (hB : 0<B) (base pointer k : ℕ) (s : State B (Word w))
    (hc : (s.disk pointer ⟨0,hB⟩).val=k) :
    (execute (dataBody hB base pointer) s).disk=
      (execute (compressOne hB base k) s).disk := by
  unfold dataBody
  split_ifs with h2
  · exact largeBody_disk hB h2 base pointer k s hc
  · exact smallBody_disk hB (by omega) base pointer k s hc

theorem dataBody_cost (hB : 0<B) (base pointer : ℕ) :
    transfers (dataBody (w:=w) hB base pointer)=(if 2≤B then 4 else 3) := by
  unfold dataBody
  split_ifs <;> rfl

theorem dataBody_length (hB : 0<B) (base pointer : ℕ) :
    (dataBody (w:=w) hB base pointer).length=(if 2≤B then 6 else 3) := by
  unfold dataBody
  split_ifs <;> rfl

open TwoWordUniformBlockFormat (LoopProgram Ready cursor flag zero one inc)

def advance (hB : 0<B) (hw : 0<w) (base n : ℕ) : List (Command B (Word w)) :=
  [.readLeft (cursor base w),
   .cpu (fun p => (fun _ => inc (p.1 ⟨0,hB⟩),
     fun _ => if (p.1 ⟨0,hB⟩).val+1=n then one hw else zero w)),
   .writeLeft (cursor base w),.writeRight (fun _ => flag base w)]

def body (hB : 0<B) (hw : 0<w) (base n : ℕ) : List (Command B (Word w)) :=
  dataBody hB base (cursor base w) ++ advance hB hw base n

def program (hB : 0<B) (hw : 0<w) (base n : ℕ) : LoopProgram B (Word w) :=
  ⟨flag base w,one hw,body hB hw base n⟩

theorem body_cost (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    transfers (program hB hw base n).body=(if 2≤B then 7 else 6) := by
  change transfers (dataBody hB base (cursor base w)++advance hB hw base n)=_
  rw [transfers_append,dataBody_cost]
  have ha : transfers (advance hB hw base n)=3 := rfl
  rw [ha]
  split_ifs <;> rfl

theorem body_length (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    (program hB hw base n).body.length=(if 2≤B then 10 else 7) := by
  change (dataBody hB base (cursor base w)++advance hB hw base n).length=_
  rw [List.length_append,dataBody_length]
  have ha : (advance hB hw base n).length=4 := rfl
  rw [ha]
  split_ifs <;> rfl

theorem advance_disk (hB : 0<B) (hw : 0<w) (base n : ℕ) (s : State B (Word w)) :
    (execute (advance hB hw base n) s).disk=
      Function.update (Function.update s.disk (cursor base w)
        (fun _ => inc (s.disk (cursor base w) ⟨0,hB⟩))) (flag base w)
        (fun _ => if (s.disk (cursor base w) ⟨0,hB⟩).val+1=n then one hw else zero w) := rfl

theorem next_disk (hB : 0<B) (hw : 0<w) (base n k : ℕ) (s : State B (Word w))
    (hk : k<n) (hsep : n≤base) (hc : (s.disk (cursor base w) ⟨0,hB⟩).val=k) :
    (TwoWordUniformBlockFormat.next (program hB hw base n) s).disk=
      Function.update (Function.update (execute (compressOne hB base k) s).disk
        (cursor base w) (fun _ => inc (s.disk (cursor base w) ⟨0,hB⟩)))
        (flag base w) (fun _ => if k+1=n then one hw else zero w) := by
  change (execute (dataBody hB base (cursor base w)++advance hB hw base n)
    (TwoWordUniformBlockFormat.check (program hB hw base n) s)).disk=_
  rw [execute_append,advance_disk]
  have hbody := dataBody_disk hB base (cursor base w) k
    (TwoWordUniformBlockFormat.check (program hB hw base n) s) hc
  rw [hbody]
  have hd : (execute (compressOne hB base k)
      (TwoWordUniformBlockFormat.check (program hB hw base n) s)).disk=
      (execute (compressOne hB base k) s).disk := rfl
  rw [hd]
  have hp : k/B<cursor base w := by have:=Nat.div_le_self k B;unfold cursor;omega
  have he : (execute (compressOne hB base k) s).disk (cursor base w)=s.disk (cursor base w) := by
    rw [compressOne_disk,Function.update_of_ne (by omega : cursor base w≠k/B)]
  rw [he,hc]

theorem next_ready (hB : 0<B) (hw : 0<w) (base n j : ℕ)
    (hsep : n≤base) (hN : n≤2^w) (hj : j<n) (s : State B (Word w))
    (hr : Ready hB hw base n j s) :
    Ready hB hw base n (j+1) (TwoWordUniformBlockFormat.next (program hB hw base n) s) := by
  have hc : (s.disk (cursor base w) ⟨0,hB⟩).val=j :=
    hr.1.trans (Nat.mod_eq_of_lt (by omega))
  unfold Ready
  rw [next_disk hB hw base n j s hj hsep hc]
  simp only [Function.update_self]
  rw [Function.update_of_ne (show cursor base w≠flag base w by unfold flag;omega),
    Function.update_self]
  exact ⟨by simp only [inc,hc],True.intro⟩

def cost (B n : ℕ) := (if 2≤B then 8 else 7)*n+3
def loopCost (B n : ℕ) := (if 2≤B then 8 else 7)*n+1

theorem complete_disk (hB : 0<B) (hw : 0<w) (base n : ℕ)
    (hsep : n≤base) (hN : n≤2^w) (s : State B (Word w)) :
    ∃ t, TwoWordUniformBlockFormat.Executes hB (program hB hw base n)
      (execute (TwoWordUniformBlockFormat.setup hB hw base n) s) t (loopCost B n) ∧
      ∀ a, a<cursor base w → t.disk a=(execute (compress hB base n) s).disk a := by
  let P : ℕ→State B (Word w)→Prop := fun j t => Ready hB hw base n j t ∧
    ∀ a, a<cursor base w → t.disk a=(execute (compress hB base j) s).disk a
  have hhalt (t : State B (Word w)) (ht : P n t) :
      (TwoWordUniformBlockFormat.check (program hB hw base n) t).left ⟨0,hB⟩=
        (program hB hw base n).halt := by
    exact ht.1.2.trans (if_pos rfl)
  have hstop (t : State B (Word w)) (ht : P n t) :
      P n (TwoWordUniformBlockFormat.check (program hB hw base n) t) := ht
  have hstep (j : ℕ) (t : State B (Word w)) (hj : j<n) (ht : P j t) :
      (TwoWordUniformBlockFormat.check (program hB hw base n) t).left ⟨0,hB⟩≠
        (program hB hw base n).halt ∧
      P (j+1) (TwoWordUniformBlockFormat.next (program hB hw base n) t) := by
    have hc : (t.disk (cursor base w) ⟨0,hB⟩).val=j :=
      ht.1.1.trans (Nat.mod_eq_of_lt (by omega))
    refine ⟨?_,next_ready hB hw base n j hsep hN hj t ht.1,?_⟩
    · change t.disk (flag base w) ⟨0,hB⟩≠one hw
      rw [ht.1.2,if_neg (by omega : j≠n)]
      intro he
      have := congrArg Fin.val he
      simp only [zero,one] at this
      omega
    · intro a ha
      rw [next_disk hB hw base n j t hj hsep hc,
        Function.update_of_ne (show a≠flag base w by unfold flag;omega),
        Function.update_of_ne (by omega : a≠cursor base w)]
      rw [compress,execute_append,compressOne_disk,compressOne_disk]
      have htar : j/B<cursor base w := by have:=Nat.div_le_self j B;unfold cursor;omega
      have hsrc : base+5+j<cursor base w := by unfold cursor;omega
      rw [ht.2 (j/B) htar,ht.2 (base+5+j) hsrc]
      by_cases he : a=j/B
      · subst a;rw [Function.update_self,Function.update_self]
      · rw [Function.update_of_ne he,Function.update_of_ne he,ht.2 a ha]
  have hinit : P 0 (execute (TwoWordUniformBlockFormat.setup hB hw base n) s) := by
    refine ⟨TwoWordUniformBlockFormat.setup_ready hB hw base n s,?_⟩
    intro a ha
    exact TwoWordUniformBlockFormat.setup_disk hB hw base n s a ha
  obtain ⟨t,ht,hp⟩ := TwoWordUniformBlockFormat.loop_invariant hB (program hB hw base n)
    n P hhalt hstop hstep 0 (execute (TwoWordUniformBlockFormat.setup hB hw base n) s)
    (by omega) hinit
  refine ⟨t,?_,hp.2⟩
  convert ht using 1
  rw [body_cost]
  unfold loopCost
  split_ifs <;> omega

theorem complete (hB : 0<B) (hw : 0<w) (base n : ℕ)
    (hsep : n≤base) (hN : n≤2^w) (s : State B (Word w))
    (xs : List (Word w)) (hlen : xs.length=n)
    (hin : ∀ j : Fin xs.length, (observe hB base s).disk (5+j.val)=xs.get j) :
    ∃ t, TwoWordUniformBlockFormat.Executes hB (program hB hw base n)
      (execute (TwoWordUniformBlockFormat.setup hB hw base n) s) t (loopCost B n) ∧
      File hB t.disk xs := by
  obtain ⟨t,ht,hd⟩ := complete_disk hB hw base n hsep hN s
  refine ⟨t,ht,?_⟩
  have hout := compress_correct hB base n s xs hlen hsep hin
  intro j
  unfold wordAt
  rw [hd (j.val/B) (by have:=Nat.div_le_self j.val B;have:=j.isLt;unfold cursor;omega)]
  exact hout j

theorem cost_le (B n : ℕ) : cost B n≤8*n+3 := by
  unfold cost
  split_ifs <;> omega

theorem cost_eq (B n : ℕ) : 2+loopCost B n=cost B n := by
  unfold cost loopCost
  omega

theorem smallBody_bound (hB : 0<B) (base : ℕ) :
    TwoWordBlockFootprint.BoundedCode (cursor base w+2)
      (smallBody (w:=w) hB base (cursor base w)) := by
  intro cmd hc
  simp only [smallBody,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl
  · change cursor base w<cursor base w+2;omega
  · intro r
    have hv := (r.1 ⟨0,hB⟩).isLt
    change base+5+(r.1 ⟨0,hB⟩).val<cursor base w+2
    unfold cursor;omega
  · intro r
    have hv := (r.1 ⟨0,hB⟩).isLt
    have hd := Nat.div_le_self (r.1 ⟨0,hB⟩).val B
    change (r.1 ⟨0,hB⟩).val/B<cursor base w+2
    unfold cursor;omega

theorem largeBody_bound (hB : 0<B) (h2 : 2≤B) (base : ℕ) :
    TwoWordBlockFootprint.BoundedCode (cursor base w+2)
      (largeBody (w:=w) hB h2 base (cursor base w)) := by
  intro cmd hc
  simp only [largeBody,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · change cursor base w<cursor base w+2;omega
  · intro r
    have hv := (r.1 ⟨0,hB⟩).isLt
    change base+5+(r.1 ⟨0,hB⟩).val<cursor base w+2
    unfold cursor;omega
  · trivial
  · intro r
    have hv := (r.1 ⟨1,by omega⟩).isLt
    have hd := Nat.div_le_self (r.1 ⟨1,by omega⟩).val B
    change (r.1 ⟨1,by omega⟩).val/B<cursor base w+2
    unfold cursor;omega
  · trivial
  · intro r
    have hv := (r.1 ⟨1,by omega⟩).isLt
    have hd := Nat.div_le_self (r.1 ⟨1,by omega⟩).val B
    change (r.1 ⟨1,by omega⟩).val/B<cursor base w+2
    unfold cursor;omega

theorem dataBody_bound (hB : 0<B) (base : ℕ) :
    TwoWordBlockFootprint.BoundedCode (cursor base w+2)
      (dataBody (w:=w) hB base (cursor base w)) := by
  unfold dataBody
  split_ifs with h2
  · exact largeBody_bound hB h2 base
  · exact smallBody_bound hB base

theorem advance_bound (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    TwoWordBlockFootprint.BoundedCode (cursor base w+2) (advance hB hw base n) := by
  intro cmd hc
  simp only [advance,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · change cursor base w<cursor base w+2;omega
  · trivial
  · change cursor base w<cursor base w+2;omega
  · intro r;change flag base w<cursor base w+2;unfold flag;omega

theorem bodyBound (hB : 0<B) (hw : 0<w) (base n : ℕ) :
    TwoWordUniformBlockFormat.BoundedProgram (cursor base w+2) (program hB hw base n) := by
  constructor
  · change flag base w<cursor base w+2;unfold flag;omega
  · intro cmd hc
    change cmd∈dataBody hB base (cursor base w)++advance hB hw base n at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact dataBody_bound hB base cmd hc
    · exact advance_bound hB hw base n cmd hc

end CodedSorting.TwoWordUniformBlockCompress
end BlockCompress
