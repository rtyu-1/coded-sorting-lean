import CodedSorting.Sorting.SmallMemory.NarrowWords.PublicUnrolledComplete
import CodedSorting.Sorting.SmallMemory.PublicUnrolledBlockSort
import CodedSorting.Sorting.SmallMemory.SmallMemoryPhysicalRate

/-! Sorting when a word is shorter than the input-position address. Input and output words are stored consecutively. All working data occupy two B-word buffers or allocated disk space. The position in the predetermined instruction list is maintained by program control, as specified in Appendix D. 


-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.GeneralWordSmallSorting
open TwoWordRadixInsert (Word)
open TwoWordBlockLift (State)
noncomputable section

def code (B w n c : ℕ) (hB : 0<B) (hw : 0<w) :=
  PublicUnrolledBlockSort.code hB n (TwoWordGeneralHistogram.inputBase w (c+1))
    (TwoWordGeneralPublicUnrolled.code w hw (c+1) n)

def space (n w c : ℕ) : ℕ :=
  PublicUnrolledBlockSort.space n (TwoWordGeneralHistogram.inputBase w (c+1))
    (TwoWordGeneralFootprint.space w (c+1) n)

theorem code_bound (B w n c : ℕ) (hB : 0<B) (hw : 0<w) :
    TwoWordSmallMemoryFootprint.BoundedCode (space n w c) (code B w n c hB hw) :=
  PublicUnrolledBlockSort.code_bound hB n _ _ _
    (TwoWordGeneralFootprint.code_bound w hw (c+1) n)

theorem polynomial_words (B w n c : ℕ) (hn : 2≤n) (hB : B≤n)
    (hsmall : w<Nat.clog 2 n) : space n w c*B≤(2*c+16)*n^2 := by
  have hk := (TwoWordGeneralCapacity.alphabet_lt_length n w hsmall).le
  have h := PublicUnrolledBlockSort.polynomial_words n
    (TwoWordGeneralHistogram.inputBase w (c+1)) (TwoWordGeneralFootprint.space w (c+1) n)
    ((c+1)+2) ((c+1)+3) B hn
    (TwoWordGeneralFootprint.input_base_linear w (c+1) n hn hk)
    (TwoWordGeneralFootprint.space_linear w (c+1) n hn hk) hB
  convert h using 1 <;> ring

/-- The only input premise is the compact file. Initialization, key search,
sorting, compression and their charged transfers are one actual run. -/
theorem complete (B w n c : ℕ) (hB : 0<B) (hn : 2≤n)
    (hw : 0<w) (hc : WordConvention.Covers n w c)
    (hsmall : w<Nat.clog 2 n)
    (s : State B (Word w)) (xs : List (Word w)) (hlen : xs.length=n)
    (hin : TwoWordBlockFormat.File hB s.disk xs) :
    ∃t cost, TwoWordSmallMemorySorting.Executes hB (code B w n c hB hw) s t cost ∧
      TwoWordBlockFormat.File hB t.disk (TwoWordGeneralPublicUnrolled.output w xs) ∧
      (TwoWordGeneralPublicUnrolled.output w xs).Perm xs ∧
      (TwoWordGeneralPublicUnrolled.output w xs).Pairwise (fun x y=>x.val≤y.val) ∧
      cost≤305*(c+2)*n ∧ Fintype.card (Fin B ⊕ Fin B)=2*B := by
  have hword : ∀ (a : TwoWordPhysicalAddresses.State (Word w)) (ys : List (Word w)),
      ys.length=n →
      (∀j : Fin ys.length,a.disk (TwoWordGeneralHistogram.inputBase w (c+1)+j.val)=ys.get j) →
      ∃t cost, TwoWordRadixPreparedBuild.Executes
        (TwoWordGeneralPublicUnrolled.code w hw (c+1) n) a t cost ∧
        (∀j : Fin (TwoWordGeneralPublicUnrolled.output w ys).length,
          t.disk (TwoWordGeneralHistogram.inputBase w (c+1)+j.val)=
            (TwoWordGeneralPublicUnrolled.output w ys).get j) ∧
        (TwoWordGeneralPublicUnrolled.output w ys).Perm ys ∧
        (TwoWordGeneralPublicUnrolled.output w ys).Pairwise (fun x y=>x.val≤y.val) ∧
        cost≤300*(c+2)*n := by
    intro a ys hlen hin
    have hf : TwoWordGeneralHistogram.File a.disk (TwoWordGeneralHistogram.inputBase w (c+1)) ys := by
      intro i hi
      exact hin ⟨i,hi⟩
    obtain ⟨t,cost,hrun,hcost,hfile,hperm,hsorted⟩ :=
      TwoWordGeneralPublicUnrolled.complete w hw (c+1) n a ys hlen hf
        (TwoWordGeneralCapacity.counter_capacity n w c hw hc)
    refine ⟨t,cost,hrun,?_,hperm,hsorted,?_⟩
    · intro j
      exact hfile j.val j.isLt
    · have hk := TwoWordGeneralCapacity.alphabet_lt_length n w hsmall
      unfold TwoWordGeneralPublicUnrolled.budget at hcost
      nlinarith
  obtain ⟨t,cost,hrun,hfile,hperm,hsorted,hcost,hram⟩ :=
    PublicUnrolledBlockSort.complete hB n _ (300*(c+2)*n)
      (TwoWordGeneralPublicUnrolled.code w hw (c+1) n)
      (TwoWordGeneralPublicUnrolled.output w) hword s xs hlen hin
  exact ⟨t,cost,hrun,hfile,hperm,hsorted,by nlinarith,hram⟩

theorem complete_bound (B w n c M M₀ : ℕ) (τ ε : ℝ)
    (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤n) (hM : M<M₀)
    (hw : 0<w) (hc : WordConvention.Covers n w c) (hsmall : w<Nat.clog 2 n)
    (s : State B (Word w)) (xs : List (Word w)) (hlen : xs.length=n)
    (hin : TwoWordBlockFormat.File hB s.disk xs) :
    ∃t cost, TwoWordSmallMemorySorting.Executes hB (code B w n c hB hw) s t cost ∧
      TwoWordBlockFormat.File hB t.disk (TwoWordGeneralPublicUnrolled.output w xs) ∧
      (TwoWordGeneralPublicUnrolled.output w xs).Perm xs ∧
      (TwoWordGeneralPublicUnrolled.output w xs).Pairwise (fun x y=>x.val≤y.val) ∧
      Fintype.card (Fin B ⊕ Fin B)≤M ∧
      (cost : ℝ)≤(305*(c+2)*M₀ : ℝ)*((n : ℝ)/B)*
        SmallMemorySortingRate.paperFactor n M B τ ε := by
  obtain ⟨t,cost,hrun,hfile,hperm,hsorted,hcost,hram⟩ :=
    complete B w n c hB (by omega) hw hc hsmall s xs hlen hin
  have hcostR : (cost : ℝ)≤(305*(c+2) : ℝ)*n := by exact_mod_cast hcost
  exact ⟨t,cost,hrun,hfile,hperm,hsorted,by omega,
    SmallMemoryPhysicalRate.linear_memory cost n M B M₀ (305*(c+2)) τ ε
      (by positivity) hcostR (by omega) hB hBM hM⟩

end
end CodedSorting.GeneralWordSmallSorting
