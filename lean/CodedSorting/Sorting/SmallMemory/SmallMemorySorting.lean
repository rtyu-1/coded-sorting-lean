import CodedSorting.Sorting.SmallMemory.SmallSort
import CodedSorting.Sorting.SmallMemory.Uniform.BlockCompress
import CodedSorting.Sorting.SmallMemory.SmallMemoryPhysicalRate

/-! One fixed five-stage physical program for all standard-word small
memory instances. Each while loop stores its cursor and halt flag on
disk, and every format access, core access and halt check is charged.
The stage interpreter carries only a fixed finite phase, not an input
length cursor or an input-dependent schedule. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.TwoWordSmallMemorySorting
open TwoWordRadixInsert (Word)
open TwoWordBlockLift (State Command)
open TwoWordBlockFormat (File)

inductive Stage (B w : ℕ) where
  | straight (body : List (Command B (Word w)))
  | loop (p : TwoWordUniformBlockFormat.LoopProgram B (Word w))
  | core (base : ℕ) (body : List (TwoWordRadixPreparedBuild.Stage (Word w)))

inductive Executes {B w : ℕ} (hB : 0<B) :
    List (Stage B w) → State B (Word w) → State B (Word w) → ℕ → Prop where
  | done (s : State B (Word w)) : Executes hB [] s s 0
  | straight (body : List (Command B (Word w))) (rest : List (Stage B w))
      (s t : State B (Word w)) (cost : ℕ)
      (tail : Executes hB rest (TwoWordBlockLift.execute body s) t cost) :
      Executes hB (.straight body::rest) s t (TwoWordBlockLift.transfers body+cost)
  | loop (p : TwoWordUniformBlockFormat.LoopProgram B (Word w)) (rest : List (Stage B w))
      (s mid t : State B (Word w)) (ca cb : ℕ)
      (first : TwoWordUniformBlockFormat.Executes hB p s mid ca)
      (tail : Executes hB rest mid t cb) :
      Executes hB (.loop p::rest) s t (ca+cb)
  | core (base : ℕ) (body : List (TwoWordRadixPreparedBuild.Stage (Word w)))
      (rest : List (Stage B w)) (s mid t : State B (Word w)) (ca cb : ℕ)
      (first : TwoWordBlockLift.Executes hB base body s mid ca)
      (tail : Executes hB rest mid t cb) :
      Executes hB (.core base body::rest) s t (ca+cb)

noncomputable def code (B w n c : ℕ) (hB : 0<B) (hw : 0<w)
    (hn : 2≤n) (hword : n≤2^w) : List (Stage B w) :=
  [.straight (TwoWordUniformBlockFormat.setup hB hw (n+1) n),
   .loop (TwoWordUniformBlockFormat.program hB hw (n+1) n),
   .core (n+1) (TwoWordSmallMemoryCore.code w n c hn hword),
   .straight (TwoWordUniformBlockFormat.setup hB hw (n+1) n),
   .loop (TwoWordUniformBlockCompress.program hB hw (n+1) n)]

theorem code_length (B w n c : ℕ) (hB : 0<B) (hw : 0<w)
    (hn : 2≤n) (hword : n≤2^w) : (code B w n c hB hw hn hword).length=5 := rfl

theorem word_positive (n w : ℕ) (hn : 2≤n) (hlower : Nat.clog 2 n≤w) : 0<w :=
  (Nat.clog_pos (by decide) hn).trans_le hlower

def budget (c n : ℕ) : ℕ := TwoWordSmallMemoryCore.budget c n+14*n+6

theorem budget_linear (c n : ℕ) (hc : 1≤c) (hn : 2≤n) : budget c n≤4300*c*n := by
  have hcore:=TwoWordSmallMemoryCore.budget_linear c n (by omega)
  have hn':=Nat.mul_le_mul_right n hc
  unfold budget
  nlinarith only [hcore,hn',hn]

/-- One actual five-stage run, from a compact integer file back to a
compact sorted file. All scratch contents and both initial buffers are
arbitrary. The only word-size conditions are stated explicitly. -/
theorem complete (B w n c : ℕ) (hB : 0<B) (hn : 2≤n) (hc : 1≤c)
    (hlower : Nat.clog 2 n≤w) (hupper : w≤c*Nat.clog 2 n)
    (s : State B (Word w)) (xs : List (Word w)) (hlen : xs.length=n)
    (hin : File hB s.disk xs) :
    ∃ t cost, Executes hB
        (code B w n c hB (word_positive n w hn hlower) hn
          ((Nat.le_pow_iff_clog_le (by decide)).2 hlower)) s t cost ∧
      File hB t.disk (TwoWordSmallMemoryCore.output w n c hn xs) ∧
      (TwoWordSmallMemoryCore.output w n c hn xs).Perm xs ∧
      (TwoWordSmallMemoryCore.output w n c hn xs).Pairwise (fun x y=>x.val≤y.val) ∧
      cost≤budget c n ∧ cost≤4300*c*n ∧
      Fintype.card (Fin B ⊕ Fin B)=2*B := by
  let hw : 0<w := word_positive n w hn hlower
  have hword : n≤2^w := (Nat.le_pow_iff_clog_le (by decide)).2 hlower
  obtain ⟨expanded,hexpand,hinput,_⟩ :=
    TwoWordUniformBlockFormat.complete hB hw (n+1) n hword (by omega) s xs hlen hin
  obtain ⟨sorted,k,hcore,hk,hfile,hperm,hsorted⟩ :=
    TwoWordSmallMemoryCore.block_complete B w n c (n+1) hB hn hc hlower hupper
      expanded xs hlen hinput
  have hlen' : (TwoWordSmallMemoryCore.output w n c hn xs).length=n :=
    (TwoWordSmallMemoryCore.output_length w n c hn xs).trans hlen
  obtain ⟨t,hcompress,hout⟩ := TwoWordUniformBlockCompress.complete hB hw (n+1) n
    (by omega) hword sorted (TwoWordSmallMemoryCore.output w n c hn xs) hlen' hfile
  let total := 2+(6*n+1)+k+2+(TwoWordUniformBlockCompress.loopCost B n)
  have hcomp := TwoWordUniformBlockCompress.cost_le B n
  have hcompEq := TwoWordUniformBlockCompress.cost_eq B n
  have htotal : total≤budget c n := by
    unfold total budget
    omega
  refine ⟨t,total,?_,hout,hperm,hsorted,htotal,
    htotal.trans (budget_linear c n hc hn),TwoWordBlockLift.resident_card⟩
  have trace := Executes.straight (TwoWordUniformBlockFormat.setup hB hw (n+1) n) _ s t _
    (Executes.loop (TwoWordUniformBlockFormat.program hB hw (n+1) n) _ _ expanded t _ _
      hexpand (Executes.core (n+1) _ _ expanded sorted t k _ hcore
        (Executes.straight (TwoWordUniformBlockFormat.setup hB hw (n+1) n) _ sorted t _
          (Executes.loop (TwoWordUniformBlockCompress.program hB hw (n+1) n) [] _ t t _ 0
            hcompress (Executes.done t)))))
  simpa only [code,total,TwoWordUniformBlockFormat.setup_cost,Nat.add_zero,Nat.add_assoc] using trace

/-- The complete same-run cost has the paper's simplified factor for
all 2B≤M<M₀. The cutoff and word convention determine one fixed constant. -/
theorem complete_bound (B w n c M M₀ : ℕ) (τ ε : ℝ) (hB : 0<B)
    (hMB : 2*B≤M) (hMN : M≤n) (hM : M<M₀) (hc : 1≤c)
    (hlower : Nat.clog 2 n≤w) (hupper : w≤c*Nat.clog 2 n)
    (s : State B (Word w)) (xs : List (Word w)) (hlen : xs.length=n)
    (hin : File hB s.disk xs) :
    ∃ t cost, Executes hB
        (code B w n c hB (word_positive n w (by omega) hlower) (by omega)
          ((Nat.le_pow_iff_clog_le (by decide)).2 hlower)) s t cost ∧
      File hB t.disk (TwoWordSmallMemoryCore.output w n c (by omega) xs) ∧
      (TwoWordSmallMemoryCore.output w n c (by omega) xs).Perm xs ∧
      (TwoWordSmallMemoryCore.output w n c (by omega) xs).Pairwise (fun x y=>x.val≤y.val) ∧
      Fintype.card (Fin B ⊕ Fin B)≤M ∧
      (cost:ℝ)≤(4300*c*M₀:ℝ)*((n:ℝ)/B)*SmallMemorySortingRate.paperFactor n M B τ ε ∧
      (cost:ℝ)≤(4300*c*M₀:ℝ)*((n:ℝ)/B)*
        min (B:ℝ) (SmallMemorySortingRate.refinedFactor n M B τ ε) := by
  obtain ⟨t,cost,ht,hout,hperm,hsorted,_,hcost,hram⟩ :=
    complete B w n c hB (by omega) hc hlower hupper s xs hlen hin
  have hcostR : (cost:ℝ)≤(4300*c:ℝ)*n := by exact_mod_cast hcost
  refine ⟨t,cost,ht,hout,hperm,hsorted,by omega,?_,?_⟩
  · exact SmallMemoryPhysicalRate.linear_memory cost n M B M₀ (4300*c) τ ε
      (by positivity) hcostR (by omega) hB hMB hM
  · exact SmallMemoryPhysicalRate.linear_refined cost n M B M₀ (4300*c) τ ε
      (by positivity) hcostR hB hMB hMN hM

end CodedSorting.TwoWordSmallMemorySorting
