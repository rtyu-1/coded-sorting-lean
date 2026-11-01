import CodedSorting.Sorting.Radix.Program.Cost
import CodedSorting.Sorting.Radix.Program.Execution
import CodedSorting.Sorting.Radix.Framework.SortingPower

/-! Expose the already constructed whole sorting execution before compiling
its counter to a policy. This permits static input/output scans to share
the same actual routine, with no successful-sort premise in the endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.Sorting.CommonMSDSortingTrace
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalEntry CodedSorting.Construction.Sorting.CommonMSDGlobalControl CommonRecordIntervalList
open CommonLeafProgram (Machine)
noncomputable section

theorem complete (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) (s : Machine q)
    (xs : List (KeyRecordWords.Record q.w)) (hlen : xs.length=n)
    (hx : EncodedListAt q s.disk p.source 0 xs)
    (ho : CommonMSDRecordDigits.OrdinaryList xs) :
    ∃ tag final steps charge,
      (program q p n hn).Trace (program q p n hn).entry s tag final steps charge ∧
      EncodedListAt q final.disk p.source 0 (CommonMSDSortingRun.output q xs) ∧
      charge≤CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.budget q (levels q) xs := by
  have hdecode := (CodedSorting.Construction.Sorting.CommonMSDGlobalExecution.tag_count_capacity q p n hn hc).le
  have hj : offset (root q n hn)+records (root q n hn)≤q.N := by
    simpa only [root,offset,records,Fin.val_zero,Nat.zero_add] using hn
  have hd : depth (root q n hn)+level (root q n hn)≤levels q := by
    simp only [root,depth,level,Fin.val_zero,Nat.zero_add,le_refl]
  have hl : xs.length=records (root q n hn) := hlen
  have hp : CommonMSDSemantics.Prefix CommonWordMSD.key (CommonMSDParameters.radix q)
      (level (root q n hn)) 0 xs := root_prefix q xs ho
  obtain ⟨final,steps,charge,hpath,hout,hframe,hcharge⟩ :=
    CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.complete p (root q n hn) (root q n hn)
      hdecode hj hd 0 s xs hl hx ho hp
  let r := program q p n hn
  have hr := root_halt (K:=CommonMSDParameters.radix q)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) (root q n hn) (root q n hn)
    (by rfl) final
  have hfull := r.path_append hpath (r.trace_toPath hr)
  have ht : r.terminal (index (halted (K:=CommonMSDParameters.radix q)
      (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) (root q n hn)))=true := by
    change (CodedSorting.Construction.Sorting.CommonMSDGlobalControl.routine (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p)
      (root q n hn)).terminal (index (halted (K:=CommonMSDParameters.radix q)
        (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) (root q n hn)))=true
    rw [routine_terminal]
    rfl
  refine ⟨index (halted (K:=CommonMSDParameters.radix q)
    (CodedSorting.Construction.Sorting.CommonMSDGlobalComponents.components p) (root q n hn)),
    erasePC q final,steps+1,charge,?_,hout,hcharge⟩
  simpa only [Nat.add_zero] using r.path_toTrace hfull ht

end
end CodedSorting.Construction.Sorting.CommonMSDSortingTrace
