import CodedSorting.Sorting.SmallMemory.SmallMemorySorting

section SmallMemoryFootprint
/-! A finite allocation for the entire compact-input/compact-output
execution, including both format cursors and halt flags. The syntactic
bound covers every read/write under arbitrary resident contents, and the
frame theorem applies to the same actual five-stage execution. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.TwoWordSmallMemoryFootprint
open TwoWordRadixInsert (Word)
open TwoWordSmallMemorySorting (Stage Executes)
open TwoWordBlockLift (State)

variable {B w : ℕ}

def space (n w : ℕ) : ℕ := TwoWordUniformBlockFormat.cursor (n+1) w+2

@[simp] theorem space_eq (n w : ℕ) : space n w=n+13+6*2^w := by
  unfold space TwoWordUniformBlockFormat.cursor
  omega

def BoundedStage (L : ℕ) : Stage B w → Prop
  | .straight body => TwoWordBlockFootprint.BoundedCode L body
  | .loop p => TwoWordUniformBlockFormat.BoundedProgram L p
  | .core base body => ∃ R, base+R≤L ∧ TwoWordRadixFootprint.BoundedCode R body

def BoundedCode (L : ℕ) (code : List (Stage B w)) : Prop := ∀st∈code,BoundedStage L st

/-- This includes the actual stop-test reads and all format control writes. -/
theorem code_bound (B w n c : ℕ) (hB : 0<B) (hw : 0<w)
    (hn : 2≤n) (hword : n≤2^w) :
    BoundedCode (space n w) (TwoWordSmallMemorySorting.code B w n c hB hw hn hword) := by
  intro st hs
  simp only [TwoWordSmallMemorySorting.code,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact TwoWordUniformBlockFormat.setupBound hB hw (n+1) n
  · exact TwoWordUniformBlockFormat.bodyBound hB hw (n+1) n
  · refine ⟨10+6*2^w,?_,TwoWordSmallMemoryCore.code_bound w n c hn hword⟩
    rw [space_eq]
    omega
  · exact TwoWordUniformBlockFormat.setupBound hB hw (n+1) n
  · exact TwoWordUniformBlockCompress.bodyBound hB hw (n+1) n

/-- No address outside the declared allocation changes on the actual run.
All reads are already covered by the stronger syntactic bound above. -/
theorem frame (hB : 0<B) (L : ℕ) (code : List (Stage B w))
    (hb : BoundedCode L code) {s t : State B (Word w)} {cost : ℕ}
    (h : Executes hB code s t cost) (a : ℕ) (ha : L≤a) : t.disk a=s.disk a := by
  induction h with
  | done s => rfl
  | straight body rest s t cost tail ih =>
    rw [ih (fun st hs=>hb st (List.mem_cons_of_mem _ hs))]
    exact TwoWordBlockFootprint.execute_frame L body (hb _ List.mem_cons_self) s a ha
  | loop p rest s mid t ca cb first tail ih =>
    rw [ih (fun st hs=>hb st (List.mem_cons_of_mem _ hs))]
    exact TwoWordUniformBlockFormat.loop_frame hB L p (hb _ List.mem_cons_self) first a ha
  | core base body rest s mid t ca cb first tail ih =>
    rw [ih (fun st hs=>hb st (List.mem_cons_of_mem _ hs))]
    obtain ⟨R,hR,hbody⟩ := hb _ List.mem_cons_self
    exact TwoWordBlockFootprint.stages_frame hB base R body hbody first a (by omega)

theorem code_frame (B w n c : ℕ) (hB : 0<B) (hw : 0<w)
    (hn : 2≤n) (hword : n≤2^w) {s t : State B (Word w)} {cost : ℕ}
    (h : Executes hB (TwoWordSmallMemorySorting.code B w n c hB hw hn hword) s t cost)
    (a : ℕ) (ha : space n w≤a) : t.disk a=s.disk a :=
  frame hB _ _ (code_bound B w n c hB hw hn hword) h a ha

/-- The allocation exponent depends only on the fixed upper word-width
constant c. This counts physical blocks; physical words multiply by B. -/
theorem polynomial (n c w : ℕ) (hn : 2≤n) (hw : w≤c*Nat.clog 2 n) :
    space n w≤n+13+6*n^(2*c) := by
  have h := TwoWordRadixFootprint.allocation_polynomial n c w hn hw
  rw [space_eq]
  omega

theorem polynomial_words (B n c w : ℕ) (hn : 2≤n) (hB : B≤n)
    (hw : w≤c*Nat.clog 2 n) :
    space n w*B≤(n+13+6*n^(2*c))*n :=
  Nat.mul_le_mul (polynomial n c w hn hw) hB

end CodedSorting.TwoWordSmallMemoryFootprint
end SmallMemoryFootprint

section PublicUnrolledBlockSort
/-! Compact-file lifting for a publicly unrolled word program.  The
immutable command list may depend on the public input length.  Its code
position is part of the Stage interpreter, not one of the two buffers.
This module does not identify that convention with a fixed-control RAM.
All data transfers, including expansion and compression, are charged. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.PublicUnrolledBlockSort
open TwoWordRadixInsert (Word)
open TwoWordBlockLift (State)
open TwoWordSmallMemorySorting (Stage Executes)
variable {B w : ℕ}

def code (hB : 0<B) (n offset : ℕ)
    (core : List (TwoWordRadixPreparedBuild.Stage (Word w))) : List (Stage B w) :=
  [.straight (TwoWordBlockFormat.expand hB (n+offset+1) n),
   .core (n+6) core,
   .straight (TwoWordBlockFormat.compress hB (n+offset+1) n)]

def space (n offset coreSpace : ℕ) : ℕ := 3*n+offset+coreSpace+12

private theorem bound_append (L : ℕ)
    (a b : List (TwoWordBlockLift.Command B (Word w)))
    (ha : TwoWordBlockFootprint.BoundedCode L a)
    (hb : TwoWordBlockFootprint.BoundedCode L b) :
    TwoWordBlockFootprint.BoundedCode L (a++b) := by
  intro cmd hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ha cmd hc
  · exact hb cmd hc

theorem expand_bound (hB : 0<B) (base n L : ℕ)
    (hsep : n≤base) (hL : base+5+n≤L) :
    TwoWordBlockFootprint.BoundedCode L
      (TwoWordBlockFormat.expand (W:=Word w) hB base n) := by
  induction n with
  | zero => intro cmd hc; simp [TwoWordBlockFormat.expand] at hc
  | succ n ih =>
    apply bound_append L _ _ (ih (by omega) (by omega))
    intro cmd hc
    simp only [TwoWordBlockFormat.expandOne,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · have := Nat.div_le_self n B
      change n/B<L
      omega
    · trivial
    · intro r
      change base+5+n<L
      omega

theorem compress_bound (hB : 0<B) (base n L : ℕ)
    (hsep : n≤base) (hL : base+5+n≤L) :
    TwoWordBlockFootprint.BoundedCode L
      (TwoWordBlockFormat.compress (W:=Word w) hB base n) := by
  induction n with
  | zero => intro cmd hc; simp [TwoWordBlockFormat.compress] at hc
  | succ n ih =>
    apply bound_append L _ _ (ih (by omega) (by omega))
    intro cmd hc
    simp only [TwoWordBlockFormat.compressOne,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · change base+5+n<L
      omega
    · intro r
      change n/B<L
      have := Nat.div_le_self n B
      omega
    · trivial
    · intro r
      change n/B<L
      have := Nat.div_le_self n B
      omega

theorem code_bound (hB : 0<B) (n offset coreSpace : ℕ)
    (core : List (TwoWordRadixPreparedBuild.Stage (Word w)))
    (hc : TwoWordRadixFootprint.BoundedCode coreSpace core) :
    TwoWordSmallMemoryFootprint.BoundedCode (space n offset coreSpace)
      (code hB n offset core) := by
  intro st hs
  simp only [code,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact expand_bound hB (n+offset+1) n _ (by omega) (by unfold space;omega)
  · exact ⟨coreSpace,by unfold space;omega,hc⟩
  · exact compress_bound hB (n+offset+1) n _ (by omega) (by unfold space;omega)

/-- A linear word-machine allocation remains polynomial after replacing
every word by a whole physical block, including the compact-file bridge. -/
theorem polynomial_words (n offset coreSpace A D B : ℕ)
    (hn : 2≤n) (hoffset : offset≤A*n) (hcore : coreSpace≤D*n)
    (hB : B≤n) : space n offset coreSpace*B≤(A+D+9)*n^2 := by
  have hspace : space n offset coreSpace≤(A+D+9)*n := by
    unfold space
    nlinarith
  have h := Nat.mul_le_mul hspace hB
  nlinarith only [h]

/-- This is a compositional lemma. A concrete sorter must discharge the
word-machine execution premise; it is not itself a sorting endpoint. -/
theorem complete (hB : 0<B) (n offset limit : ℕ)
    (core : List (TwoWordRadixPreparedBuild.Stage (Word w)))
    (output : List (Word w) → List (Word w))
    (hcore : ∀ (s : TwoWordPhysicalAddresses.State (Word w))
      (xs : List (Word w)), xs.length=n →
      (∀j : Fin xs.length,s.disk (offset+j.val)=xs.get j) →
      ∃t cost, TwoWordRadixPreparedBuild.Executes core s t cost ∧
        (∀j : Fin (output xs).length,t.disk (offset+j.val)=(output xs).get j) ∧
        (output xs).Perm xs ∧
        (output xs).Pairwise (fun x y=>x.val≤y.val) ∧ cost≤limit)
    (s : State B (Word w)) (xs : List (Word w)) (hlen : xs.length=n)
    (hin : TwoWordBlockFormat.File hB s.disk xs) :
    ∃t cost, Executes hB (code hB n offset core) s t cost ∧
      TwoWordBlockFormat.File hB t.disk (output xs) ∧
      (output xs).Perm xs ∧ (output xs).Pairwise (fun x y=>x.val≤y.val) ∧
      cost≤limit+5*n ∧ Fintype.card (Fin B ⊕ Fin B)=2*B := by
  let expanded := TwoWordBlockLift.execute
    (TwoWordBlockFormat.expand hB (n+offset+1) n) s
  have hexp := TwoWordBlockFormat.expand_correct hB (n+offset+1) n s xs hlen
    (by omega) hin
  have hi : ∀j : Fin xs.length,
      (TwoWordBlockLift.observe hB (n+6) expanded).disk (offset+j.val)=xs.get j := by
    intro j
    have hj := hexp j
    simpa only [TwoWordBlockLift.observe,Nat.add_assoc,Nat.add_left_comm,
      Nat.add_comm] using hj
  obtain ⟨wordResult,k,hword,hout,hperm,hsort,hk⟩ :=
    hcore (TwoWordBlockLift.observe hB (n+6) expanded) xs hlen hi
  obtain ⟨sorted,hrun,hobserve⟩ :=
    TwoWordBlockLift.lift_stages hB (n+6) hword expanded rfl
  have hsparse : ∀j : Fin (output xs).length,
      (TwoWordBlockLift.observe hB (n+offset+1) sorted).disk (5+j.val)=
        (output xs).get j := by
    intro j
    have hj := hout j
    rw [←hobserve] at hj
    simpa only [TwoWordBlockLift.observe,Nat.add_assoc,Nat.add_left_comm,
      Nat.add_comm] using hj
  let t := TwoWordBlockLift.execute
    (TwoWordBlockFormat.compress hB (n+offset+1) n) sorted
  have hlen' : (output xs).length=n := hperm.length_eq.trans hlen
  have hfile := TwoWordBlockFormat.compress_correct hB (n+offset+1) n sorted
    (output xs) hlen' (by omega) hsparse
  refine ⟨t,2*n+k+3*n,?_,hfile,hperm,hsort,by omega,TwoWordBlockLift.resident_card⟩
  have trace := Executes.straight
    (TwoWordBlockFormat.expand hB (n+offset+1) n) _ s t _
    (Executes.core (n+6) core _ expanded sorted t k _ hrun
      (Executes.straight (TwoWordBlockFormat.compress hB (n+offset+1) n) []
        sorted t 0 (Executes.done t)))
  simpa only [code,TwoWordBlockFormat.expand_cost,TwoWordBlockFormat.compress_cost,
    Nat.add_zero,Nat.add_assoc] using trace

end CodedSorting.PublicUnrolledBlockSort
end PublicUnrolledBlockSort
