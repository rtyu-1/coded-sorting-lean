import CodedSorting.Interchange.Framework.Memory.Reflection
import CodedSorting.Shared.Programs.ScanProgramLift

/-! The original scan language compiled to one actual finite-disk policy.
Successive passes alternate two explicitly allocated regions. The output,
halt and I/O bound all concern this single instruction sequence. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonScanProgram
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs ScanProgram
open CommonLeafProgram (Machine Disk)
noncomputable section

def passCode (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (p : Pass V) (source target : ℕ) : List (Instruction q) :=
  match p with
  | .streams _ e key _ => CommonPermutationScan.program q reader e key source target
  | .reverse T L _ _ => CommonReflection.code q reader T L source target

theorem pass_safe (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (p : Pass V) (source target : ℕ) :
    ∀ i∈passCode q reader p source target,RespectsPC q i := by
  cases p with
  | streams K e key hi => exact CommonPermutationScan.program_safe q reader e key source target
  | reverse T L hL hV => exact CommonReflection.code_safe q reader T L source target

theorem pass_length (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (p : Pass V) (source target : ℕ) :
    (passCode q reader p source target).length≤3*p.constant*count q V := by
  cases p with
  | streams K e key hi =>
    have h := CommonPermutationScan.program_length q reader e key source target hi
    simp only [passCode,Pass.constant]
    nlinarith
  | reverse T L hL hV =>
    subst V
    simp only [passCode,CommonReflection.code_length,Pass.constant]
    omega

theorem pass_cost (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (p : Pass V) (source target : ℕ) :
    cost q (passCode q reader p source target)≤3*p.constant*count q V := by
  cases p with
  | streams K e key hi =>
    have h := CommonPermutationScan.program_cost q reader e key source target hi
    simp only [passCode,Pass.constant]
    nlinarith
  | reverse T L hL hV =>
    subst V
    simp only [passCode,CommonReflection.code_cost,Pass.constant]
    omega

theorem pass_raw (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (p : Pass V) (source target : ℕ) (s : Machine q)
    (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source) :
    (∀ y : Fin V,readBit q (executeRaw q (passCode q reader p source target) s).1.disk target y.val=
      readBit q s.disk source (p.permutation.symm y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q V≤a.val →
      (executeRaw q (passCode q reader p source target) s).1.disk a=s.disk a) := by
  cases p with
  | streams K e key hi =>
    exact CommonPermutationScan.raw_correct q reader e key source target hsource htarget hsep s
  | reverse T L hL hV =>
    subst V
    have hr := CommonReflection.raw_complete q reader T L source target hL s hsource htarget hsep
    refine ⟨?_,hr.2⟩
    intro y
    rw [Pass.permutation,ScanProgram.reversePerm_symm]
    simpa [ScanProgram.reversePerm] using hr.1 y

def code (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers) :
    List (Pass V)→ℕ→ℕ→List (Instruction q)
  | [],_,_ => []
  | p::ps,source,target => passCode q reader p source target++code q reader ps target source

def finalBase {V : ℕ} : List (Pass V)→ℕ→ℕ→ℕ
  | [],source,_ => source
  | _::ps,source,target => finalBase ps target source

theorem code_length (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) :
    (code q reader ps source target).length≤3*totalConstant ps*count q V := by
  induction ps generalizing source target with
  | nil => simp [code,totalConstant]
  | cons p ps ih =>
    have h := pass_length q reader p source target
    have ht := ih target source
    simp only [code,List.length_append,totalConstant,List.map_cons,List.sum_cons] at *
    nlinarith

theorem code_cost (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) :
    cost q (code q reader ps source target)≤3*totalConstant ps*count q V := by
  induction ps generalizing source target with
  | nil => simp [code,totalConstant,cost]
  | cons p ps ih =>
    have h := pass_cost q reader p source target
    have ht := ih target source
    rw [code,cost_append]
    simp only [totalConstant,List.map_cons,List.sum_cons] at *
    nlinarith

theorem code_safe (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) :
    ∀ i∈code q reader ps source target,RespectsPC q i := by
  induction ps generalizing source target with
  | nil => simp [code]
  | cons p ps ih =>
    intro i hi
    rcases List.mem_append.mp hi with h|h
    · exact pass_safe q reader p source target i h
    · exact ih target source i h

theorem raw_correct (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) (s : Machine q)
    (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source) :
    ∀ y : Fin V,readBit q (executeRaw q (code q reader ps source target) s).1.disk
      (finalBase ps source target) y.val=
      readBit q s.disk source ((destination ps).symm y).val := by
  induction ps generalizing source target s with
  | nil => intro y; rfl
  | cons p ps ih =>
    intro y
    rw [code,raw_append]
    change readBit q (executeRaw q (code q reader ps target source)
      (executeRaw q (passCode q reader p source target) s).1).1.disk (finalBase ps target source) y.val=_
    rw [ih target source _ htarget hsource hsep.symm]
    exact (pass_raw q reader p source target s hsource htarget hsep).1 ((destination ps).symm y)

theorem raw_outside (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) (s : Machine q)
    (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<source ∨ source+count q V≤a.val)
    (hb : a.val<target ∨ target+count q V≤a.val) :
    (executeRaw q (code q reader ps source target) s).1.disk a=s.disk a := by
  induction ps generalizing source target s with
  | nil => rfl
  | cons p ps ih =>
    rw [code,raw_append,ih target source _ htarget hsource hsep.symm hb ha]
    exact (pass_raw q reader p source target s hsource htarget hsep).2 a hb

theorem complete (q : Configuration) {V : ℕ} (reader : Fin q.inventory.readers)
    (ps : List (Pass V)) (source target : ℕ) (s : Machine q)
    (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source)
    (hsize : 3*totalConstant ps*count q V≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let program := code q reader ps source target
    let result := ControlledNormalization.runLogical (policy q program) program.length s
    (∀ y : Fin V,readBit q result.1.disk (finalBase ps source target) y.val=
      readBit q s.disk source ((destination ps).symm y).val) ∧
    policy q program result.1.ram=none ∧ result.2≤3*totalConstant ps*count q V ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (code q reader ps source target)
    ((code_length q reader ps source target).trans hsize) (code_safe q reader ps source target) s hpc
  exact ⟨by rw [hd]; exact raw_correct q reader ps source target s hsource htarget hsep,hh,
    hc.le.trans (code_cost q reader ps source target),hm⟩

end
end CodedSorting.CommonScanProgram
