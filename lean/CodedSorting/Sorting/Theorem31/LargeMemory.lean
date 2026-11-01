import CodedSorting.Sorting.Execution.AllInputPhysical
import CodedSorting.Sorting.Radix.Framework.RadixCost

/-! Recursive integer sorting above a fixed memory threshold.

The word-width convention is ceil(log_2 N) <= c*w together with the upper
bound determined by kappa. The memory threshold and I/O coefficient depend
on these fixed constants and the finite circuit. The constructed program
runs on resident data and transfers whole physical blocks to and from disk. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.Sorting.GeneralWordNormalSorting
open CommonSortingNormalization CommonMSDPublicWordBounds WordControl
noncomputable section

/-- Fixed inventory for the actual Construction sorting controller. -/
def inventory : SortingResourceBudget.Inventory where
  readers := 1
  writers := 0
  keys := 0
  pc := 0
  ratio := PhysicalLeafParameters.minimumRatio Construction.ExchangeSpecialization.radix 1
    Construction.streamCount
def exponent (κ : ℝ) : ℕ := CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent (wordFactor κ)
def digits (c : ℕ) (κ : ℝ) : ℕ := SortingResourceBudget.digits c (exponent κ)
def reserveSize (c : ℕ) (κ : ℝ) : ℕ :=
  SortingResourceBudget.reserve inventory c (digits c κ)
def Mcut (c : ℕ) (κ : ℝ) : ℕ := reserveSize c κ ^ 2

def configuration (c : ℕ) (κ : ℝ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : Mcut c κ≤M) (hw : WordConvention.Covers N w c) : Configuration where
  inventory := inventory
  N := N
  M := M
  B := B
  w := w
  c := c
  exponent := exponent κ
  input_large := hN
  memory_input := hMN
  block_pos := hB
  block_memory := hBM
  exponent_pos := (by omega : 1≤17).trans
    (CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent_ge17 (wordFactor κ))
  word_convention := hw
  memory_large := hM

def parameters (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : Mcut c κ≤M) (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.Parameters
      (configuration c κ N M B w hN hB hBM hMN hM hw) where
  reader := ⟨0,by change 0<1;decide⟩
  ratio := le_rfl
  kappa := κ
  kappa_nonnegative := hκ
  word_bound := hword
  exponent := le_rfl

def coefficient (c : ℕ) (κ : ℝ) : ℝ :=
  (2*(reserveSize c κ : ℝ)^2)*
    (1+Real.log (2*(reserveSize c κ : ℝ))/Real.log 2)^2*
    (12*22194000000*
      GlobalSortingBound.rateConstant CodedSorting.Construction.Sorting.CommonLocalBudgetRate.K CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau*
      (κ*(1+Real.log (4*(digits c κ : ℝ))/Real.log 2)+2)+2*(16 : ℝ))

def factor (N M B : ℕ) : ℝ :=
  1+Real.log (N : ℝ)/
    (Real.log ((M : ℝ)/B)^(1-(CodedSorting.Construction.epsilon : ℝ))*
      Real.log (M : ℝ)^(CodedSorting.Construction.epsilon : ℝ))

theorem coefficient_eq (c : ℕ) (κ : ℝ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : Mcut c κ≤M) (hw : WordConvention.Covers N w c) :
    CodedSorting.Construction.Sorting.CommonIntegerSortingRate.coefficient
      (configuration c κ N M B w hN hB hBM hMN hM hw) κ=coefficient c κ := rfl

theorem Mcut_positive (c : ℕ) (κ : ℝ) : 0<Mcut c κ :=
  pow_pos (SortingResourceBudget.reserve_pos _ _ _) _

/-- The program is fixed from public parameters before the arbitrary input
and scratch state.  Sortedness, termination, memory, finite disk size, and
I/O cost all refer to the same constructed physical execution. -/
def Guarantee (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : Mcut c κ≤M) (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) : Prop :=
  let q := configuration c κ N M B w hN hB hBM hMN hM hw
  let p := parameters c κ hκ N M B w hN hB hBM hMN hM hw hword
  ∀ (store : CommonLeafProgram.Store q)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word w)), xs.length=N → CommonIntegerPhysical.InputFile q disk xs →
    ∃ fuel,
      let prog := program q (CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.algorithm q p)
      let s := CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.start q p store disk
      let blocks := CommonIntegerPhysical.blocks q q.N
      let result := CommonNormalizationController.run prog (blocks+1+fuel+1+blocks+1) s
      (∀ i : Fin (CommonIntegerFile.output q xs).length,
        CommonNormalizationController.outputWord prog result.1 i.val=
          (CommonIntegerFile.output q xs).get i) ∧
      (CommonIntegerFile.output q xs).Perm xs ∧
      (CommonIntegerFile.output q xs).Pairwise (·≤·) ∧
      CommonNormalizationController.step prog result.1=(result.1,0) ∧
      Fintype.card (ResidentIndex q)≤M ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))≤
        N^(exponent κ+2) ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))*B≤
        N^(exponent κ+3) ∧
      (result.2 : ℝ)≤coefficient c κ*((N : ℝ)/B)*factor N M B

/-- The lower word constant is arbitrary.  Covers and N>=2 already imply
c>0, so no logically redundant positivity assumption is required here. -/
theorem complete (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hM : Mcut c κ≤M) (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    Guarantee c κ hκ N M B w hN hB hBM hMN hM hw hword := by
  let q := configuration c κ N M B w hN hB hBM hMN hM hw
  let p := parameters c κ hκ N M B w hN hB hBM hMN hM hw hword
  intro store disk xs hlen hin
  obtain ⟨fuel,hout,hperm,hsort,hhalt,hram,hdisk,hcost⟩ :=
    CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical.complete q p store disk xs hlen hin
  refine ⟨fuel,hout,hperm,hsort,hhalt,hram,hdisk,?_,?_⟩
  · have hBN : B≤N := by omega
    have hh := Nat.mul_le_mul hdisk hBN
    change _≤N^(exponent κ+2)*N at hh
    simpa only [show exponent κ+3=(exponent κ+2)+1 by omega,pow_succ] using hh
  · have hfactor : CodedSorting.Construction.Sorting.CommonMSDPhysicalRate.paperFactor q q.N=factor N M B := by
      simp only [CodedSorting.Construction.Sorting.CommonMSDPhysicalRate.paperFactor,factor,CodedSorting.Construction.Sorting.CommonLocalBudgetRate.tau,
        sub_sub_cancel]
      rfl
    rw [show p.kappa=κ from rfl,
      show CodedSorting.Construction.Sorting.CommonIntegerSortingRate.coefficient q κ=coefficient c κ from rfl,
      hfactor] at hcost
    exact hcost

/-- A concrete infinite family outside the one-word address convention. -/
def familySize (k : ℕ) : ℕ := 2^(3*k)
def familyMemory (k : ℕ) : ℕ := 2^k

theorem family_size_ge_two (k : ℕ) (hk : 1≤k) : 2≤familySize k := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤3*k by omega)
  simpa only [familySize,pow_one] using h

theorem family_memory_ge_two (k : ℕ) (hk : 1≤k) : 2≤familyMemory k := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) hk
  simpa only [familyMemory,pow_one] using h

theorem family_memory_le_size (k : ℕ) : familyMemory k≤familySize k :=
  Nat.pow_le_pow_right (by decide : 0<2) (by omega)

theorem family_covers (k : ℕ) : WordConvention.Covers (familySize k) k 3 := by
  simp only [WordConvention.Covers,familySize,Nat.clog_pow 2 (3*k) (by decide)]
  exact le_refl _

theorem family_not_standard (k : ℕ) (hk : 1≤k) :
    ¬Nat.clog 2 (familySize k)≤k := by
  rw [familySize,Nat.clog_pow 2 (3*k) (by decide)]
  omega

theorem family_word_upper (k : ℕ) :
    (k : ℝ)*Real.log 2≤(1 : ℝ)*Real.log (familySize k : ℝ) := by
  simp only [familySize,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,
    Nat.cast_mul,one_mul]
  have hlog : 0≤Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hk : 0≤(k : ℝ) := Nat.cast_nonneg k
  nlinarith

def FamilyEndpoint (k : ℕ) : Prop :=
  ∃ hk : 1≤k, ∃ hM : Mcut 3 1≤familyMemory k,
    (¬Nat.clog 2 (familySize k)≤k) ∧
    Guarantee 3 1 (by norm_num) (familySize k) (familyMemory k) 1 k
      (family_size_ge_two k hk) (by decide) (by simpa using family_memory_ge_two k hk)
      (family_memory_le_size k) hM (family_covers k) (family_word_upper k)

/-- For every threshold there is a genuine normal-memory sorting endpoint
with w=k and log_2 N=3k, which the standard-word endpoint cannot accept. -/
theorem arbitrarily_large_nonstandard (threshold : ℕ) :
    ∃ k, threshold≤k ∧ FamilyEndpoint k := by
  let k := Mcut 3 1+threshold+1
  have hk : 1≤k := by dsimp [k];omega
  have hcut : Mcut 3 1≤k := by dsimp [k];omega
  have hM : Mcut 3 1≤familyMemory k :=
    hcut.trans (show k≤2^k from (show k<2^k from Nat.lt_two_pow_self).le)
  refine ⟨k,by dsimp [k];omega,hk,hM,family_not_standard k hk,?_⟩
  exact complete 3 1 (by norm_num) (familySize k) (familyMemory k) 1 k
    (family_size_ge_two k hk) (by decide) (by simpa using family_memory_ge_two k hk)
    (family_memory_le_size k) hM (family_covers k) (family_word_upper k)

end
end CodedSorting.Construction.Sorting.GeneralWordNormalSorting

