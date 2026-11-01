import CodedSorting.Sorting.Theorem31.Proof

/-! Paper Theorem 3.1 (`thm:sorting`).
The complete parameter list and guarantees are preserved from the Construction result.
-/
set_option autoImplicit false
namespace CodedSorting.Sorting.Theorem31
open CodedSorting Construction.Sorting GeneralWordSorting

theorem theorem_3_1 (c : ℕ) (κ : ℝ) (hκ : 0≤κ) (N M B w : ℕ)
    (hN : 2≤N) (hB : 0<B) (hBM : 2*B≤M) (hMN : M≤N)
    (hw : WordConvention.Covers N w c)
    (hword : (w : ℝ)*Real.log 2≤κ*Real.log (N : ℝ)) :
    (∃ hM : GeneralWordNormalSorting.Mcut c κ≤M,
      NormalGuarantee c κ hκ N M B w hN hB hBM hMN hM hw hword) ∨
    (M<GeneralWordNormalSorting.Mcut c κ ∧
      SmallGuarantee c κ N M B w hB) :=
  GeneralWordSorting.complete
    c κ hκ N M B w hN hB hBM hMN hw hword

end CodedSorting.Sorting.Theorem31
