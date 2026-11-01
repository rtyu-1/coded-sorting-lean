import CodedSorting.Sorting.Theorem31.LargeMemory
import CodedSorting.Sorting.Theorem31.SmallMemory

/-! Integer sorting for all allowed memory sizes.

The program is determined by the size parameters and sorts every input file.
Normal memory uses the recursive sorting controller; small memory uses two
block buffers. In the narrow-word small-memory case, the execution model
maintains the position in the predetermined instruction list outside the buffers.
Both cases have one common I/O coefficient, depending on the fixed construction
and word-width constants. Output, termination, and resource bounds describe
the same execution. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.Sorting.GeneralWordSorting
open CommonSortingNormalization WordControl
noncomputable section

def coefficient (c : ℕ) (κ : ℝ) : ℝ := max 1
  (max (GeneralWordNormalSorting.coefficient c κ)
    (max (5000*(SmallMemorySortingRate.wordFactor κ : ℝ)*GeneralWordNormalSorting.Mcut c κ)
      (305*((c : ℝ)+2)*GeneralWordNormalSorting.Mcut c κ)))

theorem coefficient_positive (c : ℕ) (κ : ℝ) : 0<coefficient c κ :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

def factor (N M B : ℕ) : ℝ := SmallMemorySortingRate.paperFactor N M B
  CommonLocalBudgetRate.tau (CodedSorting.Construction.epsilon : ℝ)

theorem factor_eq (N M B : ℕ) : factor N M B=GeneralWordNormalSorting.factor N M B := by
  simp only [factor,SmallMemorySortingRate.paperFactor,GeneralWordNormalSorting.factor,
    CommonLocalBudgetRate.tau,sub_sub_cancel]

private theorem increase_constant (c : ℕ) (κ K : ℝ) (cost N M B : ℕ)
    (hB : 0<B) (hBM : 2*B≤M) (hN : 0<N)
    (hK : K≤coefficient c κ)
    (hcost : (cost : ℝ)≤K*((N : ℝ)/B)*factor N M B) :
    (cost : ℝ)≤coefficient c κ*((N : ℝ)/B)*factor N M B := by
  have hf : 0≤factor N M B := (by norm_num : (0:ℝ)≤1).trans
    (SmallMemorySortingRate.paperFactor_one N M B _ _ hN hB hBM)
  exact hcost.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (by positivity)) hf)

/-- One coefficient works in every branch and depends only on the fixed
lower and upper word-width constants c and kappa. -/
def NormalGuarantee (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : GeneralWordNormalSorting.Mcut c κ≤M) (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) : Prop :=
  let q := GeneralWordNormalSorting.configuration c κ N M B w hN hB hBM hMN hM hw
  let p := GeneralWordNormalSorting.parameters c κ hκ N M B w hN hB hBM hMN hM hw hword
  ∀ (store : CommonLeafProgram.Store q)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word w)), xs.length=N → CommonIntegerPhysical.InputFile q disk xs →
    ∃ fuel,
      let prog := program q (CommonIntegerAllInputPhysical.algorithm q p)
      let s := CommonIntegerAllInputPhysical.start q p store disk
      let blocks := CommonIntegerPhysical.blocks q q.N
      let result := CommonNormalizationController.run prog (blocks+1+fuel+1+blocks+1) s
      (∀ i : Fin (CommonIntegerFile.output q xs).length,
        CommonNormalizationController.outputWord prog result.1 i.val=(CommonIntegerFile.output q xs).get i) ∧
      (CommonIntegerFile.output q xs).Perm xs ∧
      (CommonIntegerFile.output q xs).Pairwise (·≤·) ∧
      CommonNormalizationController.step prog result.1=(result.1,0) ∧
      Fintype.card (ResidentIndex q)≤M ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))≤
        N^(GeneralWordNormalSorting.exponent κ+2) ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))*B≤
        N^(GeneralWordNormalSorting.exponent κ+3) ∧
      (result.2 : ℝ)≤coefficient c κ*((N : ℝ)/B)*factor N M B

theorem normal_complete (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : GeneralWordNormalSorting.Mcut c κ≤M) (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    NormalGuarantee c κ hκ N M B w hN hB hBM hMN hM hw hword := by
  intro store disk xs hlen hin
  obtain ⟨fuel,hout,hperm,hsort,hhalt,hram,hdisk,hwords,hcost⟩ :=
    GeneralWordNormalSorting.complete c κ hκ N M B w hN hB hBM hMN hM hw hword
      store disk xs hlen hin
  refine ⟨fuel,hout,hperm,hsort,hhalt,hram,hdisk,hwords,?_⟩
  rw [←factor_eq] at hcost
  exact increase_constant c κ _ _ N M B hB hBM (by omega)
    ((le_max_left _ _).trans (le_max_right _ _)) hcost

def smallSpaceBound (c : ℕ) (κ : ℝ) (N : ℕ) : ℕ :=
  (N+13+6*N^(2*SmallMemorySortingRate.wordFactor κ))*N+(2*c+16)*N^2

/-- Choose the program, disk allocation, and output function from the size
parameters. The resulting execution sorts every input file from any initial
buffer and scratch contents, within the stated memory, disk, and I/O bounds. -/
def SmallGuarantee (c : ℕ) (κ : ℝ) (N M B w : ℕ) (hB : 0<B) : Prop :=
  ∃ (code : List (TwoWordSmallMemorySorting.Stage B w)) (allocation : ℕ)
    (output : List (Word w) → List (Word w)),
    TwoWordSmallMemoryFootprint.BoundedCode allocation code ∧
    allocation*B≤smallSpaceBound c κ N ∧
    ∀ (s : TwoWordBlockLift.State B (Word w)) (xs : List (Word w)),
      xs.length=N → TwoWordBlockFormat.File hB s.disk xs →
      ∃t cost, TwoWordSmallMemorySorting.Executes hB code s t cost ∧
        TwoWordBlockFormat.File hB t.disk (output xs) ∧
        (output xs).Perm xs ∧ (output xs).Pairwise (fun x y=>x.val≤y.val) ∧
        Fintype.card (Fin B ⊕ Fin B)≤M ∧
        (cost : ℝ)≤coefficient c κ*((N : ℝ)/B)*factor N M B

theorem small_complete (c : ℕ) (κ : ℝ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : M<GeneralWordNormalSorting.Mcut c κ) (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    SmallGuarantee c κ N M B w hB := by
  by_cases hs : Nat.clog 2 N≤w
  · let upper := SmallMemorySortingRate.wordFactor κ
    have hu : w≤upper*Nat.clog 2 N := SmallMemorySortingRate.word_upper N w κ (by omega) hword
    have hpositive := TwoWordSmallMemorySorting.word_positive N w hN hs
    have hcapacity : N≤2^w := (Nat.le_pow_iff_clog_le (by decide)).2 hs
    refine ⟨TwoWordSmallMemorySorting.code B w N upper hB hpositive hN hcapacity,
      TwoWordSmallMemoryFootprint.space N w,TwoWordSmallMemoryCore.output w N upper hN,
      TwoWordSmallMemoryFootprint.code_bound B w N upper hB hpositive hN hcapacity,?_,?_⟩
    · exact (TwoWordSmallMemoryFootprint.polynomial_words B N upper w hN (by omega) hu).trans
        (Nat.le_add_right _ _)
    · intro s xs hlen hin
      obtain ⟨t,cost,hrun,hfile,hperm,hsort,hram,hcost,_⟩ :=
        TwoWordSmallMemorySorting.complete_bound B w N upper M (GeneralWordNormalSorting.Mcut c κ)
          CommonLocalBudgetRate.tau (CodedSorting.Construction.epsilon : ℝ)
          hB hBM hMN hM (SmallMemorySortingRate.wordFactor_one κ) hs hu s xs hlen hin
      refine ⟨t,cost,hrun,hfile,hperm,hsort,hram,?_⟩
      have he : (4300*upper*GeneralWordNormalSorting.Mcut c κ : ℝ)≤
          5000*upper*GeneralWordNormalSorting.Mcut c κ := by
        have : (0:ℝ)≤(upper : ℝ)*GeneralWordNormalSorting.Mcut c κ := by positivity
        nlinarith
      exact increase_constant c κ _ cost N M B hB hBM (by omega)
        (he.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) hcost
  · have hnarrow : w<Nat.clog 2 N := by omega
    have hpositive : 0<w := (WordConvention.positive_words N w c hN hw).1
    refine ⟨GeneralWordSmallSorting.code B w N c hB hpositive,
      GeneralWordSmallSorting.space N w c,TwoWordGeneralPublicUnrolled.output w,
      GeneralWordSmallSorting.code_bound B w N c hB hpositive,?_,?_⟩
    · exact (GeneralWordSmallSorting.polynomial_words B w N c hN (by omega) hnarrow).trans
        (Nat.le_add_left _ _)
    · intro s xs hlen hin
      obtain ⟨t,cost,hrun,hfile,hperm,hsort,hram,hcost⟩ :=
        GeneralWordSmallSorting.complete_bound B w N c M (GeneralWordNormalSorting.Mcut c κ)
          CommonLocalBudgetRate.tau (CodedSorting.Construction.epsilon : ℝ)
          hB hBM hMN hM hpositive hw hnarrow s xs hlen hin
      exact ⟨t,cost,hrun,hfile,hperm,hsort,hram,
        increase_constant c κ _ cost N M B hB hBM (by omega)
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hcost⟩

/-- Combine the normal-memory and small-memory algorithms to cover every
allowed memory size, with the same output requirements and I/O coefficient. -/
theorem complete (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    (∃ hM : GeneralWordNormalSorting.Mcut c κ≤M,
      NormalGuarantee c κ hκ N M B w hN hB hBM hMN hM hw hword) ∨
    (M<GeneralWordNormalSorting.Mcut c κ ∧ SmallGuarantee c κ N M B w hB) := by
  by_cases hM : GeneralWordNormalSorting.Mcut c κ≤M
  · exact Or.inl ⟨hM,normal_complete c κ hκ N M B w hN hB hBM hMN hM hw hword⟩
  · exact Or.inr ⟨by omega,
      small_complete c κ N M B w hN hB hBM hMN (by omega) hw hword⟩

end
end CodedSorting.Construction.Sorting.GeneralWordSorting
