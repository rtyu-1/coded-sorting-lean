import CodedSorting.Shared.Memory.ScanProgram
import CodedSorting.Interchange.Framework.Memory.OuterExchangeProgram

/-! The full final outer transformation, compiled from the original scan
program. The two segment reversals and one addition for every coordinate
execute on one real disk. No intermediate file is created by the proof.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace CodedSorting.CommonOuterAfter
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open Address RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open OuterExchangeProgram ScanProgram CodedSimulation
noncomputable section

theorem reflectOne_length (f P G S : ℕ) (hS : 0<S) (i : Index) :
    (reflectOne f P G S hS i).length=3 := by
  simp [reflectOne,BlockDigitMove.castProgram,ScalarCoordinateProgram.after,
    ScanProgramLift.fieldReflections]

theorem afterProgram_length (f P G S : ℕ) (hS : 0<S) :
    (OuterExchangeProgram.afterProgram f P G S hS).length=3*Parameters.m := by
  have hh (is : List Index) :
      (is.flatMap (reflectOne f P G S hS)).length=3*is.length := by
    induction is with
    | nil => simp
    | cons i is ih =>
      rw [List.flatMap_cons,List.length_append,reflectOne_length,ih,List.length_cons]
      omega
  rw [OuterExchangeProgram.afterProgram,hh,coordinates_length]

private theorem finalBase_length {V : ℕ} (ps : List (Pass V)) (source target : ℕ) :
    CommonScanProgram.finalBase ps source target=
      (if ps.length%2=0 then source else target) := by
  induction ps generalizing source target with
  | nil => simp [CommonScanProgram.finalBase]
  | cons p ps ih =>
    rw [CommonScanProgram.finalBase,ih,List.length_cons]
    have hm : ps.length%2<2 := Nat.mod_lt _ (by omega)
    by_cases h : ps.length%2=0
    · have hn : (ps.length+1)%2≠0 := by omega
      simp only [if_pos h,if_neg hn]
    · have hn : (ps.length+1)%2=0 := by omega
      simp only [if_neg h,if_pos hn]

/-- Its even number of passes returns the transformed array to the source region. -/
theorem finalBase_after (f P G S : ℕ) (hS : 0<S) (source target : ℕ) :
    CommonScanProgram.finalBase (OuterExchangeProgram.afterProgram f P G S hS)
      source target=source := by
  rw [finalBase_length,afterProgram_length,Parameters.m_value]
  norm_num

/-- The chronological instruction program implements the original reflection
D←H−D on the real source array, including every vector coordinate. -/
theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (source target : ℕ) (s : Machine q)
    (hs : source+count q (longVolume f P G S)≤q.N^q.exponent)
    (ht : target+count q (longVolume f P G S)≤q.N^q.exponent)
    (hsep : source+count q (longVolume f P G S)≤target ∨
      target+count q (longVolume f P G S)≤source) (a : Addr f P G S) :
    readBit q (executeRaw q (CommonScanProgram.code q reader
      (OuterExchangeProgram.afterProgram f P G S hS) source target) s).1.disk source
        (commonLayout f P G S (mapPairEquiv lowerReflectEquiv a)).val=
      readBit q s.disk source (commonLayout f P G S a).val := by
  have h := CommonScanProgram.raw_correct q reader
    (OuterExchangeProgram.afterProgram f P G S hS) source target s hs ht hsep
    (destination (OuterExchangeProgram.afterProgram f P G S hS) (commonLayout f P G S a))
  rw [Equiv.symm_apply_apply,OuterExchangeProgram.after_destination,finalBase_after] at h
  exact h

/-- The final outer stage runs to completion with its actual charged I/O
and the same finite resident memory as all other common-machine operations. -/
theorem after_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hS : 0<S) (source target : ℕ) (s : Machine q)
    (hs : source+count q (longVolume f P G S)≤q.N^q.exponent)
    (ht : target+count q (longVolume f P G S)≤q.N^q.exponent)
    (hsep : source+count q (longVolume f P G S)≤target ∨
      target+count q (longVolume f P G S)≤source)
    (hsize : 60*Parameters.m*count q (longVolume f P G S)≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let program := CommonScanProgram.code q reader
      (OuterExchangeProgram.afterProgram f P G S hS) source target
    let result := ControlledNormalization.runLogical (policy q program) program.length s
    (∀ a : Addr f P G S,
      readBit q result.1.disk source
        (commonLayout f P G S (mapPairEquiv lowerReflectEquiv a)).val=
      readBit q s.disk source (commonLayout f P G S a).val) ∧
    policy q program result.1.ram=none ∧
    result.2≤60*Parameters.m*count q (longVolume f P G S) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have hb : 3*totalConstant (OuterExchangeProgram.afterProgram f P G S hS)*
      count q (longVolume f P G S)=60*Parameters.m*count q (longVolume f P G S) := by
    rw [OuterExchangeProgram.after_constant]
    ring
  have hc := CommonScanProgram.complete q reader
    (OuterExchangeProgram.afterProgram f P G S hS) source target s hs ht hsep
    (by rw [hb]; exact hsize) hpc
  dsimp only at hc ⊢
  refine ⟨?_,hc.2.1,?_,hc.2.2.2⟩
  · intro a
    have ha := hc.1 (destination (OuterExchangeProgram.afterProgram f P G S hS)
      (commonLayout f P G S a))
    rw [Equiv.symm_apply_apply,OuterExchangeProgram.after_destination,finalBase_after] at ha
    exact ha
  · rw [←hb]
    exact hc.2.2.1

end
end CodedSorting.CommonOuterAfter
