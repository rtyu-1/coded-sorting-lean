import CodedSorting.Shared.Records.Transform
import CodedSorting.Sorting.Local.Framework.Program
import CodedSorting.Interchange.Framework.Memory.PaddedChunks

/-! Actual top-padding and prefix extraction around a record program.
Both scans are charged; padding is part of the disk contents consumed by
the intervening program. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace CodedSorting.CommonRecordTopPrefix
open CommonSortingNormalization CommonRecordProgram CommonRecordEncoding
open CommonRecordTransform CommonRecordReindex CommonLocalMarginsSemantic
open RecursiveColumnsort
noncomputable section

def operation {q : Configuration} {n m : ℕ} (hn : n≤m)
    (F : Records q m→Records q m) (f : Records q n) : Records q n :=
  trim hn (F (pad f))

def program (q : Configuration) (reader : Fin q.inventory.readers)
    {n m source buffer work limit : ℕ} {F : Records q m→Records q m}
    (hn : n≤m) (p : Program q m buffer work limit F)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+max 1 (recordBlocks q m)≤work)
    (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*m<(2^q.w)^q.digits) :
    Program q n source buffer limit (operation hn F) := by
  have hc : recordBlocks q n≤recordBlocks q m :=
    CommonFinitePadding.count_mono q (Nat.mul_le_mul_right _ hn)
  have hsc : source+recordBlocks q n≤q.N^q.exponent := by omega
  have hmc : buffer+recordBlocks q m≤q.N^q.exponent := by omega
  have hdesc : ∀ L N R O : ℕ,L≤m → N≤m → R≤m → O≤m →
      CommonStaticMargins.ShapeFits q (3*L) (3*N) (3*R) (3*O) := by
    intro L N R O hL hN hR hO
    exact ⟨by omega,by omega,by omega,by omega⟩
  let p0 := margins q reader 0 n (m-n) 0 source buffer source n buffer limit (by omega)
    (hdesc _ _ _ _ (by omega) hn (by omega) (by omega)) hsc
    (by simpa only [Nat.mul_zero,Nat.zero_add,←recordBlocks_eq_words] using
      (show source+max 1 (recordBlocks q n)≤q.N^q.exponent by omega))
    (by convert hmc using 1 <;> congr 2 <;> omega)
    (Or.inl (by simpa only [Nat.mul_zero,Nat.zero_add,←recordBlocks_eq_words] using hs))
    (by
      intro a _ ha
      rcases ha with ha|ha
      · exact Or.inl ha
      · exact Or.inr (by simp only [Nat.zero_add,Nat.add_sub_of_le hn]; omega))
  let padStage : Stage q n m source buffer source n buffer limit (pad (N:=m)) :=
    (p0.castOutput (by omega)).changeFunction (by
      funext f i
      exact congrFun (pad_margin hn f) i)
  let middle : Stage q m m buffer buffer source n buffer limit F :=
    workspaceProgram q p le_rfl (by omega) (by omega)
  let t0 := margins q reader 0 n 0 0 buffer source source n buffer limit (by omega)
    (hdesc _ _ _ _ (by omega) hn (by omega) (by omega)) hmc
    (by simpa only [Nat.mul_zero,Nat.zero_add,←recordBlocks_eq_words] using
      (show buffer+max 1 (recordBlocks q n)≤q.N^q.exponent by omega))
    (by simpa only [Nat.zero_add,Nat.add_zero] using hsc)
    (Or.inr (by simpa only [Nat.zero_add,Nat.add_zero] using
      (show source+recordBlocks q n≤buffer by omega)))
    (by intro a ha _; simpa only [Nat.zero_add,Nat.add_zero] using ha)
  let trimStage : Stage q m n buffer source source n buffer limit (trim hn) :=
    (t0.castOutput (by omega)).changeFunction (by
      funext f i
      exact congrFun (trim_margin hn f) i)
  let all := (padStage.append middle).append trimStage
  let done : Program q n source buffer limit (operation hn F) := all.toProgram
  have hcharge : done.charge=3*recordBlocks q m+p.charge+3*recordBlocks q n := by
    simp only [done,Stage.toProgram_charge,all,Stage.append_charge,padStage,trimStage,
      Stage.changeFunction_charge,Stage.castOutput_charge,middle,workspaceProgram_charge]
    change 3*recordBlocks q (0+n+(m-n))+p.charge+3*recordBlocks q (0+n+0)=_
    simp only [Nat.zero_add,Nat.add_zero,Nat.add_sub_of_le hn]
  exact {
    instructions:=done.instructions
    charge:=3*recordBlocks q m+p.charge+3*recordBlocks q n
    correct:=done.correct
    frame:=done.frame
    safe:=done.safe
    cost_le:=done.cost_le.trans_eq hcharge
    length_le:=done.length_le.trans_eq hcharge }

theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    {n m source buffer work limit : ℕ} {F : Records q m→Records q m}
    (hn : n≤m) (p : Program q m buffer work limit F)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+max 1 (recordBlocks q m)≤work)
    (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*m<(2^q.w)^q.digits) :
    (program q reader hn p hs hw hwl hl hshape).charge=
      3*recordBlocks q m+p.charge+3*recordBlocks q n := rfl

end
end CodedSorting.CommonRecordTopPrefix
