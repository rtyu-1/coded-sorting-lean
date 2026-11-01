import CodedSorting.Sorting.Radix.Program.Framework.Recursion

section SortingRun
/-! Sorting on a finite RAM/disk machine. The program is determined by the size parameters. Its recursive execution uses the global controller and produces a sorted output followed by a stopped state. 



-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDSortingRun
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalEntry CommonMSDGlobalControl CommonRecordIntervalList
open CommonLeafProgram (Machine)
noncomputable section

def output (q : Configuration) (xs : List (KeyRecordWords.Record q.w)) :=
  CommonMSDSemantics.recordSort q.w (CommonMSDParameters.radix q)
    (CommonMSDRadixCost.radixPositive q) q.height (CommonLocalRecursion.height_pos q)
    (levels q) xs

/-- The entire MSD sort is one actual fixed-policy execution. Only public
numeric memory, disk and control-capacity conditions are assumed. -/
theorem complete (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) (s : Machine q)
    (xs : List (KeyRecordWords.Record q.w)) (hlen : xs.length=n)
    (hx : EncodedListAt q s.disk p.source 0 xs)
    (ho : CommonMSDRecordDigits.OrdinaryList xs) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (policy q p n hn)
        steps (initial q p n hn s)
      EncodedListAt q out.1.disk p.source 0 (output q xs) ∧
      (output q xs).Perm xs ∧
      (output q xs).Pairwise (fun x y=>CommonWordMSD.key x≤CommonWordMSD.key y) ∧
      policy q p n hn out.1.ram=none ∧ Fintype.card (ResidentIndex q)≤q.M := by
  have hdecode := (CommonMSDGlobalExecution.tag_count_capacity q p n hn hc).le
  have hj : offset (root q n hn)+records (root q n hn)≤q.N := by
    simpa only [root,offset,records,Fin.val_zero,Nat.zero_add] using hn
  have hd : depth (root q n hn)+level (root q n hn)≤levels q := by
    simp only [root,depth,level,Fin.val_zero,Nat.zero_add,le_refl]
  have hl : xs.length=records (root q n hn) := hlen
  have hp : CommonMSDSemantics.Prefix CommonWordMSD.key (CommonMSDParameters.radix q)
      (level (root q n hn)) 0 xs := root_prefix q xs ho
  obtain ⟨final,steps,charge,hpath,hout,hframe⟩ :=
    CommonMSDGlobalRecursion.complete p (root q n hn) (root q n hn) hdecode hj hd
      0 s xs hl hx ho hp
  have hrun := CommonMSDGlobalExecution.finish q p n hn hc s final steps charge hpath
  have hcorrect := CommonMSDRadixCost.semantic_correct q xs ho
  refine ⟨steps+1,?_,hcorrect.1,hcorrect.2,hrun.2.1,hrun.2.2.2⟩
  rw [hrun.1]
  exact hout

end
end CodedSorting.CommonMSDSortingRun
end SortingRun

section SortingCost
/-! The exact same fixed sorting policy now carries an actual I/O bound.
All directory reads, interval transfers and disk-stack operations occur
in the charged run; budgets are used only in its proof. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDSortingCost
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonMSDGlobalEntry CommonMSDGlobalControl CommonRecordIntervalList
open CommonLeafProgram (Machine)
noncomputable section

/-- Correctness, termination, and the recursive cost bound describe the same execution of the constructed program. 
-/
theorem complete_budget (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn) (s : Machine q)
    (xs : List (KeyRecordWords.Record q.w)) (hlen : xs.length=n)
    (hx : EncodedListAt q s.disk p.source 0 xs)
    (ho : CommonMSDRecordDigits.OrdinaryList xs) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (policy q p n hn)
        steps (initial q p n hn s)
      EncodedListAt q out.1.disk p.source 0 (CommonMSDSortingRun.output q xs) ∧
      (CommonMSDSortingRun.output q xs).Perm xs ∧
      (CommonMSDSortingRun.output q xs).Pairwise
        (fun x y=>CommonWordMSD.key x≤CommonWordMSD.key y) ∧
      policy q p n hn out.1.ram=none ∧ Fintype.card (ResidentIndex q)≤q.M ∧
      out.2≤CommonMSDGlobalCostRecursion.budget q (levels q) xs := by
  have hdecode := (CommonMSDGlobalExecution.tag_count_capacity q p n hn hc).le
  have hj : offset (root q n hn)+records (root q n hn)≤q.N := by
    simpa only [root,offset,records,Fin.val_zero,Nat.zero_add] using hn
  have hd : depth (root q n hn)+level (root q n hn)≤levels q := by
    simp only [root,depth,level,Fin.val_zero,Nat.zero_add,le_refl]
  have hl : xs.length=records (root q n hn) := hlen
  have hp : CommonMSDSemantics.Prefix CommonWordMSD.key (CommonMSDParameters.radix q)
      (level (root q n hn)) 0 xs := root_prefix q xs ho
  obtain ⟨final,steps,charge,hpath,hout,hframe,hcharge⟩ :=
    CommonMSDGlobalCostRecursion.complete p (root q n hn) (root q n hn)
      hdecode hj hd 0 s xs hl hx ho hp
  have hrun := CommonMSDGlobalExecution.finish q p n hn hc s final steps charge hpath
  have hcorrect := CommonMSDRadixCost.semantic_correct q xs ho
  refine ⟨steps+1,?_,hcorrect.1,hcorrect.2,hrun.2.1,hrun.2.2.2,?_⟩
  · rw [hrun.1]
    exact hout
  · rw [hrun.2.2.1]
    exact hcharge

/-- Every charged operation in the complete run is bounded, including
the one startup allowance for a possibly empty root input. -/
theorem complete_scaled (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1
      CodedSorting.Parameters.W≤q.height/q.block)
    (s : Machine q) (xs : List (KeyRecordWords.Record q.w)) (hlen : xs.length=n)
    (hx : EncodedListAt q s.disk p.source 0 xs)
    (ho : CommonMSDRecordDigits.OrdinaryList xs) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (policy q p n hn)
        steps (initial q p n hn s)
      EncodedListAt q out.1.disk p.source 0 (CommonMSDSortingRun.output q xs) ∧
      (CommonMSDSortingRun.output q xs).Perm xs ∧
      (CommonMSDSortingRun.output q xs).Pairwise
        (fun x y=>CommonWordMSD.key x≤CommonWordMSD.key y) ∧
      policy q p n hn out.1.ram=none ∧ Fintype.card (ResidentIndex q)≤q.M ∧
      out.2*q.block≤
        ((5*CommonMSDSemanticCost.localRate q+333)*levels q+
          (CommonMSDSemanticCost.localRate q+36))*n+
          (CommonMSDSemanticCost.localRate q+36)*q.block := by
  obtain ⟨steps,hout,hperm,hsorted,hhalt,hmemory,hcost⟩ :=
    complete_budget q p n hn hc s xs hlen hx ho
  refine ⟨steps,hout,hperm,hsorted,hhalt,hmemory,?_⟩
  have hb := CommonMSDGlobalTreeCost.budget_scaled q hnormal (levels q) xs
  change CommonMSDGlobalCostRecursion.budget q (levels q) xs*q.block≤_ at hb
  rw [hlen] at hb
  exact (Nat.mul_le_mul_right q.block hcost).trans hb

/-- For an input occupying at least one logical block, the root startup
is absorbed without discarding any directory, stack, or transfer charge. -/
theorem complete_scan (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1
      CodedSorting.Parameters.W≤q.height/q.block) (hbn : q.block≤n)
    (s : Machine q) (xs : List (KeyRecordWords.Record q.w)) (hlen : xs.length=n)
    (hx : EncodedListAt q s.disk p.source 0 xs)
    (ho : CommonMSDRecordDigits.OrdinaryList xs) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (policy q p n hn)
        steps (initial q p n hn s)
      EncodedListAt q out.1.disk p.source 0 (CommonMSDSortingRun.output q xs) ∧
      (CommonMSDSortingRun.output q xs).Perm xs ∧
      (CommonMSDSortingRun.output q xs).Pairwise
        (fun x y=>CommonWordMSD.key x≤CommonWordMSD.key y) ∧
      policy q p n hn out.1.ram=none ∧ Fintype.card (ResidentIndex q)≤q.M ∧
      out.2*q.block≤6*CommonMSDSemanticCost.localRate q*(levels q+1)*n := by
  obtain ⟨steps,hout,hperm,hsorted,hhalt,hmemory,hcost⟩ :=
    complete_scaled q p n hn hc hnormal s xs hlen hx ho
  exact ⟨steps,hout,hperm,hsorted,hhalt,hmemory,
    CommonMSDGlobalTreeCost.absorb q _ (levels q) n hbn hcost⟩

end
end CodedSorting.CommonMSDSortingCost
end SortingCost

section SortingPower
/-! The complete fixed-policy sorting run satisfies the improved
logarithmic I/O bound in the logical-block machine. Public workspace and
control capacities remain explicit; physical normalization is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDSortingPower
open CommonSortingNormalization CommonMSDGlobalEntry CommonRecordIntervalList
open CommonLeafProgram (Machine)
noncomputable section

/-- Correct output, termination, counted RAM and the target I/O rate all
refer to one actual run of the unchanged sorting policy. -/
theorem complete_power (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hc : ControlCapacity q p n hn)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1
      CodedSorting.Parameters.W≤q.height/q.block)
    (κ : ℝ) (hκ : 0≤κ) (hHn : q.height≤n)
    (hword : (q.w : ℝ)*Real.log 2≤κ*Real.log (n : ℝ))
    (s : Machine q) (xs : List (KeyRecordWords.Record q.w)) (hlen : xs.length=n)
    (hx : EncodedListAt q s.disk p.source 0 xs)
    (ho : CommonMSDRecordDigits.OrdinaryList xs) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (policy q p n hn)
        steps (initial q p n hn s)
      EncodedListAt q out.1.disk p.source 0 (CommonMSDSortingRun.output q xs) ∧
      (CommonMSDSortingRun.output q xs).Perm xs ∧
      (CommonMSDSortingRun.output q xs).Pairwise
        (fun x y=>CommonWordMSD.key x≤CommonWordMSD.key y) ∧
      policy q p n hn out.1.ram=none ∧
      Fintype.card (ResidentIndex q)≤q.M ∧
      (out.2 : ℝ)≤CommonMSDGlobalPower.coefficient q κ*((n : ℝ)/q.block)*
        (1+Real.log (n : ℝ)/
          (Real.log ((q.height : ℝ)/q.block)^(1-(CodedSorting.Parameters.epsilon : ℝ))*
            Real.log (q.height : ℝ)^(CodedSorting.Parameters.epsilon : ℝ))) := by
  obtain ⟨steps,hout,hperm,hsorted,hhalt,hmemory,hcost⟩ :=
    CommonMSDSortingCost.complete_scan q p n hn hc hnormal
      ((CommonLocalRecursion.block_le_height q).trans hHn) s xs hlen hx ho
  refine ⟨steps,hout,hperm,hsorted,hhalt,hmemory,?_⟩
  have hp := CommonMSDGlobalPower.sorting_power q _ n κ hnormal hκ hHn hword hcost
  have he : 1-CommonLocalBudgetRate.tau=(CodedSorting.Parameters.epsilon : ℝ) := by
    unfold CommonLocalBudgetRate.tau
    ring
  rw [he] at hp
  simpa only [CommonLocalBudgetRate.tau] using hp

end
end CodedSorting.CommonMSDSortingPower
end SortingPower
