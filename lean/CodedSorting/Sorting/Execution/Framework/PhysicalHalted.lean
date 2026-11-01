import CodedSorting.Sorting.Execution.Framework.File

section Physical
/-! One physical normalization around a completed raw-integer policy.
The original compact input and output are specified word for word; format
conversion, sorting and projection all belong inside the one logical run. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonIntegerPhysical
open WordControl CommonSortingNormalization CommonIntegerFile
open CommonLeafProgram (Store)
noncomputable section

def blocks (q : Configuration) (n : ℕ) := PhysicalStreamCursor.blockCount q.block n

def start (q : Configuration) (policy : SourcePolicy q) (store : Store q)
    (n : ℕ) (hn : blocks q n<q.N^q.exponent)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  initialState q policy store ⟨blocks q n,by omega⟩ ⟨blocks q n,hn⟩ disk

def inputWord (q : Configuration)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) (i : ℕ) : Word q.w :=
  if h : i/q.B<q.N^q.exponent then
    disk (.inl ⟨i/q.B,h⟩) ⟨i%q.B,Nat.mod_lt _ q.block_pos⟩
  else 0

def InputFile (q : Configuration)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word q.w)) : Prop := ∀ i : Fin xs.length,inputWord q disk i.val=xs.get i

theorem sizes (q : Configuration) (policy : SourcePolicy q) (store : Store q)
    (n : ℕ) (hn : blocks q n<q.N^q.exponent)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) :
    CommonNormalizationController.inputSize (start q policy store n hn disk)=blocks q n ∧
    CommonNormalizationController.outputSize (start q policy store n hn disk)=blocks q n :=
  ⟨(initialize_sizes q policy store _ _ disk).1,
    (initialize_sizes q policy store _ _ disk).2.1⟩

theorem expanded_input (q : Configuration) (policy : SourcePolicy q) (store : Store q)
    (n : ℕ) (hn : blocks q n<q.N^q.exponent)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word q.w)) (hlen : xs.length=n) (hx : InputFile q disk xs) :
    WordFile q (CommonNormalizationController.logicalInput (program q policy)
      (start q policy store n hn disk)).disk 0 0 xs := by
  intro i
  have hb := CommonLeafProgram.block_positive q
  have hi : i.val<n := by simpa only [hlen] using i.isLt
  have hk : i.val/q.block<blocks q n :=
    (PhysicalStreamCursor.cursor_live_iff q.block n (i.val/q.block) hb).2
      ((Nat.div_mul_le_self _ _).trans_lt hi)
  have ha : i.val/q.block<q.N^q.exponent := hk.trans hn
  have hcover : n≤blocks q n*q.block := LayoutConversion.blockCount_covers n q.block hb
  have hratio := (program q policy).block_ratio
  have hiB : i.val/q.B<q.N^q.exponent :=
    (Nat.div_lt_iff_lt_mul q.block_pos).2 (by nlinarith)
  let p := program q policy
  let s := start q policy store n hn disk
  let j : Fin (CommonNormalizationController.inputSize s) :=
    ⟨i.val/q.block,by rw [(sizes q policy store n hn disk).1];exact hk⟩
  let t : Fin q.block := ⟨i.val%q.block,Nat.mod_lt _ hb⟩
  have he := CommonNormalizationController.logicalInput_payload p s.ram
    s.inputCount s.outputCount disk j t
  have hd : j.val*q.block+t.val=i.val := by
    simpa only [j,t,Nat.mul_comm] using Nat.div_add_mod i.val q.block
  have hw : CommonMarginTransform.wordAt q
      (CommonNormalizationController.logicalInput p s).disk 0 i.val=
      (CommonNormalizationController.logicalInput p s).disk
        (j.castLE (Nat.min_le_right _ _)) t := by
    simp only [CommonMarginTransform.wordAt,CommonLeafBatchProgram.extendDisk,
      Nat.zero_add,ha,↓reduceDIte,j,t]
    rfl
  change CommonMarginTransform.wordAt q
    (CommonNormalizationController.logicalInput p s).disk 0 (0+i.val)=xs.get i
  rw [Nat.zero_add,hw]
  change (CommonNormalizationController.logicalInput p s).disk
    (j.castLE (Nat.min_le_right _ _)) t=_ at he
  rw [he,hd]
  have hs : PhysicalNormalizationLayout.sourceWord
      (CommonNormalizationController.inputProgram p s)
      (CommonNormalizationController.expandView disk) i.val=inputWord q disk i.val := by
    simp only [PhysicalNormalizationLayout.sourceWord,PhysicalNormalizationLayout.index,
      CommonNormalizationController.expandView,inputWord,hiB,↓reduceDIte,
      Nat.mod_eq_of_lt hiB]
  exact hs.trans (hx i)

/-- The physical endpoint uses the very same completed logical execution.
No sorting, permutation or runtime-success hypothesis is hidden in a codec. -/
theorem complete (q : Configuration) (policy : SourcePolicy q) (store : Store q)
    (n : ℕ) (hn : blocks q n<q.N^q.exponent)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (ys : List (Word q.w)) (hlen : ys.length=n) (T : ℕ)
    (hh : policy (ControlledNormalization.runLogical policy T
      (CommonNormalizationController.logicalInput (program q policy)
        (start q policy store n hn disk))).1.ram=none)
    (hout : WordFile q (ControlledNormalization.runLogical policy T
      (CommonNormalizationController.logicalInput (program q policy)
        (start q policy store n hn disk))).1.disk 0 0 ys) :
    ∃ fuel,fuel≤T ∧
      let p := program q policy
      let s := start q policy store n hn disk
      let result := CommonNormalizationController.run p
        (blocks q n+1+fuel+1+blocks q n) s
      (∀ i : Fin ys.length,CommonNormalizationController.outputWord p result.1 i.val=ys.get i) ∧
      result.2=(ControlledNormalization.runLogical policy T
        (CommonNormalizationController.logicalInput p s)).2+8*blocks q n ∧
      (let halted := CommonNormalizationController.run p
        (blocks q n+1+fuel+1+blocks q n+1) s
       CommonNormalizationController.step p halted.1=(halted.1,0)) ∧
      Fintype.card (ResidentIndex q)≤q.M ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))≤q.N^(q.exponent+2) := by
  let p := program q policy
  let s := start q policy store n hn disk
  have hc : decodeWords s.counter=0 := by
    change decodeWords (PhysicalNormalizationLayout.counterCode q.digits q.w 0)=0
    rw [PhysicalNormalizationLayout.decode_counterCode,Nat.zero_mod]
  obtain ⟨fuel,hfuel,hram,he,hcost,hstop⟩ :=
    CommonPolicyNormalized.simulate_at_halt q policy s hc rfl rfl T hh
  have hz := sizes q policy store n hn disk
  change CommonNormalizationController.inputSize s=blocks q n ∧
    CommonNormalizationController.outputSize s=blocks q n at hz
  rw [hz.1,hz.2] at hcost hstop
  refine ⟨fuel,hfuel,?_,?_,hstop,resident_memory q,disk_polynomial q⟩
  · intro i
    have hb := CommonLeafProgram.block_positive q
    have hi : i.val<n := by simpa only [hlen] using i.isLt
    have hk : i.val/q.block<blocks q n :=
      (PhysicalStreamCursor.cursor_live_iff q.block n (i.val/q.block) hb).2
        ((Nat.div_mul_le_self _ _).trans_lt hi)
    let j : Fin (CommonNormalizationController.outputSize s) :=
      ⟨i.val/q.block,by rw [hz.2];exact hk⟩
    let t : Fin q.block := ⟨i.val%q.block,Nat.mod_lt _ hb⟩
    have hx := he j t
    have hd : j.val*q.block+t.val=i.val := by
      simpa only [j,t,Nat.mul_comm] using Nat.div_add_mod i.val q.block
    rw [hd] at hx
    change CommonNormalizationController.outputWord (program q policy)
      (CommonNormalizationController.run (program q policy)
        (CommonNormalizationController.inputSize s+1+fuel+1+
          CommonNormalizationController.outputSize s) s).1 i.val=
      (ControlledNormalization.runLogical policy T
        (CommonNormalizationController.logicalInput (program q policy) s)).1.disk
          ⟨i.val/q.block,hk.trans hn⟩ t at hx
    rw [hz.1,hz.2] at hx
    rw [hx]
    have hf := hout i
    simpa only [CommonMarginTransform.wordAt,CommonLeafBatchProgram.extendDisk,
      Nat.zero_add,hk.trans hn,↓reduceDIte,j,t] using hf
  · calc
      _ = (ControlledNormalization.runLogical policy T
          (CommonNormalizationController.logicalInput (program q policy) s)).2+
          3*blocks q n+5*blocks q n := hcost
      _ = _ := by dsimp only [s];omega

end
end CodedSorting.CommonIntegerPhysical
end Physical

section Capacity
/-! Public format-scan and normalization bounds. No input contents, actual
execution, or successful allocation is assumed by these scalar facts. -/
set_option autoImplicit false
namespace CodedSorting.CommonIntegerCapacity
open CommonSortingNormalization

theorem input_ge_96 (q : Configuration) : 96≤q.N := by
  have h := CommonLocalDescriptorBounds.height_scaled_le_input q
  have hH := CommonLocalRecursion.height_pos q
  omega

theorem blocks_le (q : Configuration) (n : ℕ) :
    CommonIntegerPhysical.blocks q n≤n :=
  CommonMSDGlobalTagCapacity.blocks_le_words q.block n (CommonLeafProgram.block_positive q)

/-- Covers the three-block tail, five-instruction projection chunks, and
any other fixed scan coefficient at most 96, with room already public. -/
theorem scaled_blocks_le (q : Configuration) (n : ℕ) (hn : n≤q.N)
    (C : ℕ) (hC : C≤96) (he : 2≤q.exponent) :
    C*CommonIntegerPhysical.blocks q n≤q.N^q.exponent := by
  have hb := blocks_le q n
  have hN := input_ge_96 q
  have hp : q.N^2≤q.N^q.exponent :=
    Nat.pow_le_pow_right (by have:=q.input_large;omega) he
  have hprod := Nat.mul_le_mul (hC.trans hN) (hb.trans hn)
  exact hprod.trans (by simpa only [pow_two] using hp)

theorem format_blocks_fit (q : Configuration) (n : ℕ) (hn : n≤q.N)
    (he : 2≤q.exponent) :
    3*CommonIntegerPhysical.blocks q n≤q.N^q.exponent :=
  scaled_blocks_le q n hn 3 (by omega) he

theorem blocks_lt (q : Configuration) (n : ℕ) (hn : n≤q.N)
    (he : 2≤q.exponent) :
    CommonIntegerPhysical.blocks q n<q.N^q.exponent := by
  have hb := (blocks_le q n).trans hn
  have hN := q.input_large
  have hp : q.N^2≤q.N^q.exponent :=
    Nat.pow_le_pow_right (by omega) he
  have hs : q.N<q.N^2 := by nlinarith
  exact hb.trans_lt (hs.trans_le hp)

theorem leaf_words_fit (q : Configuration) :
    3*q.block≤CommonExchangeLeaf.bankWords q := by
  have hb := CommonLocalRecursion.block_le_height q
  unfold CommonExchangeLeaf.bankWords
  omega

theorem leaf_bits_fit (q : Configuration) :
    (3*q.block)*q.w≤CommonExchangeLeaf.bankBits q :=
  Nat.mul_le_mul_right q.w (leaf_words_fit q)

end CodedSorting.CommonIntegerCapacity
end Capacity

section PhysicalHalted
/-! Strengthens the physical endpoint so output, cost and halt are asserted
at exactly the same final observation.  The last step changes only the stage
register and performs no I/O. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonIntegerPhysicalHalted
open WordControl CommonSortingNormalization CommonIntegerFile CommonIntegerPhysical
open CommonLeafProgram (Store)
noncomputable section

section Controller
open CommonNormalizationController
variable {L R B b d w : ℕ}

/-- Entering the halt stage preserves every payload field and costs zero. -/
theorem pipeline_last (p : Program L R B b d w) (s : State L R B b d w)
    (hc : decodeWords s.counter=0) (hp : s.phase=code p 0)
    (hst : s.stage=code p 0) (fuel : ℕ)
    (hlive : CoreLive p fuel (coreInput p s))
    (hhalt : p.policy (coreRun p fuel (coreInput p s)).1.data.ram=none) :
    let before := run p (inputSize s+1+fuel+1+outputSize s) s
    run p (inputSize s+1+fuel+1+outputSize s+1) s =
      ({before.1 with stage := code p 3},before.2) := by
  dsimp only
  have ho := compaction_run p (compactInput p fuel s)
    (by simp [compactInput,enterCompact,PhysicalNormalizationLayout.decode_counterCode])
    rfl rfl (outputSize s) (le_refl _)
  have hoq : (run p (outputSize s) (compactInput p fuel s)).1=compacted p fuel s := ho.1
  have hcount : decodeWords (compacted p fuel s).counter=outputSize s := by
    rw [←hoq]; exact ho.2.1
  have hdone : step p (compacted p fuel s)=
      ({compacted p fuel s with stage:=code p 3},0) := by
    have hst' : (compacted p fuel s).stage=code p 2 := rfl
    have hsz : outputSize (compacted p fuel s)=outputSize s := rfl
    simp only [step,hst',code,hcount,hsz,lt_self_iff_false,if_false]
  rw [run_add,run_pipeline p s hc hp hst fuel hlive hhalt,run_one,hdone]
  simp only [Nat.add_zero]

end Controller

theorem simulate_at_halt (q : Configuration) (policy : SourcePolicy q)
    (s : MachineState q)
    (hc : decodeWords s.counter=0)
    (hp : s.phase=CommonNormalizationController.code (program q policy) 0)
    (hst : s.stage=CommonNormalizationController.code (program q policy) 0)
    (T : ℕ)
    (hT : policy (ControlledNormalization.runLogical policy T
      (CommonNormalizationController.logicalInput (program q policy) s)).1.ram=none) :
    ∃ fuel, fuel≤T ∧
      let p := program q policy
      let result := CommonNormalizationController.run p
        (CommonNormalizationController.inputSize s+1+fuel+1+
          CommonNormalizationController.outputSize s+1) s
      let logical := ControlledNormalization.runLogical policy T
        (CommonNormalizationController.logicalInput p s)
      result.1.ram=logical.1.ram ∧
      (∀ j : Fin (CommonNormalizationController.outputSize s),∀ i : Fin q.block,
        CommonNormalizationController.outputWord p result.1 (j.val*q.block+i.val)=
          logical.1.disk
            (j.castLE ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))) i) ∧
      result.2=logical.2+3*CommonNormalizationController.inputSize s+
        5*CommonNormalizationController.outputSize s ∧
      CommonNormalizationController.step p result.1=(result.1,0) := by
  let p := program q policy
  let start := CommonNormalizationController.logicalInput p s
  obtain ⟨fuel,hle,heq,hf,hlive⟩ :=
    CommonPolicyComposition.first_halt policy start T hT
  have hhalt : p.policy (CommonNormalizationController.coreRun p fuel
      (CommonNormalizationController.coreInput p s)).1.data.ram=none := by
    rw [←(CommonNormalizationController.core_logical_refinement p s fuel).1.1]
    exact hf
  have hl : CommonNormalizationController.CoreLive p fuel
      (CommonNormalizationController.coreInput p s) := by
    intro k hk
    rw [←(CommonNormalizationController.core_logical_refinement p s k).1.1]
    exact hlive k hk
  have hsim := CommonNormalizationController.simulation p s hc hp hst fuel hl hhalt
  have hhalts := CommonNormalizationController.pipeline_halts p s hc hp hst fuel hl hhalt
  have hram : (CommonNormalizationController.run p
      (CommonNormalizationController.inputSize s+1+fuel+1+
        CommonNormalizationController.outputSize s) s).1.ram=
      (ControlledNormalization.runLogical policy fuel start).1.ram := by
    rw [CommonNormalizationController.run_pipeline p s hc hp hst fuel hl hhalt]
    exact (CommonNormalizationController.core_logical_refinement p s fuel).1.1.symm
  refine ⟨fuel,hle,?_⟩
  dsimp only
  rw [←heq]
  have hlast := pipeline_last p s hc hp hst fuel hl hhalt
  refine ⟨?_,?_,?_,hhalts.2.1⟩
  · rw [hlast]
    exact hram
  · rw [hlast]
    exact hsim.1
  · rw [hlast]
    exact hsim.2


/-- The physical endpoint uses the very same completed logical execution.
No sorting, permutation or runtime-success hypothesis is hidden in a codec. -/
theorem complete (q : Configuration) (policy : SourcePolicy q) (store : Store q)
    (n : ℕ) (hn : blocks q n<q.N^q.exponent)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (ys : List (Word q.w)) (hlen : ys.length=n) (T : ℕ)
    (hh : policy (ControlledNormalization.runLogical policy T
      (CommonNormalizationController.logicalInput (program q policy)
        (start q policy store n hn disk))).1.ram=none)
    (hout : WordFile q (ControlledNormalization.runLogical policy T
      (CommonNormalizationController.logicalInput (program q policy)
        (start q policy store n hn disk))).1.disk 0 0 ys) :
    ∃ fuel,fuel≤T ∧
      let p := program q policy
      let s := start q policy store n hn disk
      let result := CommonNormalizationController.run p
        (blocks q n+1+fuel+1+blocks q n+1) s
      (∀ i : Fin ys.length,CommonNormalizationController.outputWord p result.1 i.val=ys.get i) ∧
      result.2=(ControlledNormalization.runLogical policy T
        (CommonNormalizationController.logicalInput p s)).2+8*blocks q n ∧
      CommonNormalizationController.step p result.1=(result.1,0) ∧
      Fintype.card (ResidentIndex q)≤q.M ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))≤q.N^(q.exponent+2) := by
  let p := program q policy
  let s := start q policy store n hn disk
  have hc : decodeWords s.counter=0 := by
    change decodeWords (PhysicalNormalizationLayout.counterCode q.digits q.w 0)=0
    rw [PhysicalNormalizationLayout.decode_counterCode,Nat.zero_mod]
  obtain ⟨fuel,hfuel,hram,he,hcost,hstop⟩ :=
    simulate_at_halt q policy s hc rfl rfl T hh
  have hz := sizes q policy store n hn disk
  change CommonNormalizationController.inputSize s=blocks q n ∧
    CommonNormalizationController.outputSize s=blocks q n at hz
  rw [hz.1,hz.2] at hcost hstop
  refine ⟨fuel,hfuel,?_,?_,hstop,resident_memory q,disk_polynomial q⟩
  · intro i
    have hb := CommonLeafProgram.block_positive q
    have hi : i.val<n := by simpa only [hlen] using i.isLt
    have hk : i.val/q.block<blocks q n :=
      (PhysicalStreamCursor.cursor_live_iff q.block n (i.val/q.block) hb).2
        ((Nat.div_mul_le_self _ _).trans_lt hi)
    let j : Fin (CommonNormalizationController.outputSize s) :=
      ⟨i.val/q.block,by rw [hz.2];exact hk⟩
    let t : Fin q.block := ⟨i.val%q.block,Nat.mod_lt _ hb⟩
    have hx := he j t
    have hd : j.val*q.block+t.val=i.val := by
      simpa only [j,t,Nat.mul_comm] using Nat.div_add_mod i.val q.block
    rw [hd] at hx
    change CommonNormalizationController.outputWord (program q policy)
      (CommonNormalizationController.run (program q policy)
        (CommonNormalizationController.inputSize s+1+fuel+1+
          CommonNormalizationController.outputSize s+1) s).1 i.val=
      (ControlledNormalization.runLogical policy T
        (CommonNormalizationController.logicalInput (program q policy) s)).1.disk
          ⟨i.val/q.block,hk.trans hn⟩ t at hx
    rw [hz.1,hz.2] at hx
    rw [hx]
    have hf := hout i
    simpa only [CommonMarginTransform.wordAt,CommonLeafBatchProgram.extendDisk,
      Nat.zero_add,hk.trans hn,↓reduceDIte,j,t] using hf
  · calc
      _ = (ControlledNormalization.runLogical policy T
          (CommonNormalizationController.logicalInput (program q policy) s)).2+
          3*blocks q n+5*blocks q n := hcost
      _ = _ := by dsimp only [s];omega


end
end CodedSorting.CommonIntegerPhysicalHalted
end PhysicalHalted
