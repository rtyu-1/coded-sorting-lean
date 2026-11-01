import CodedSorting.Sorting.Radix.PhysicalRate
import CodedSorting.Shared.Memory.RoutineSandwich
import CodedSorting.Sorting.Radix.SortingTrace
import CodedSorting.Sorting.Radix.Program.AllocatedCapacity
import CodedSorting.Sorting.Execution.Framework.PhysicalHalted

section SortingRate
/-! The final cost conversion charges both real format scans and the one
physical normalization around the entire integer sorting program. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.Construction.Sorting.CommonIntegerSortingRate
open CommonSortingNormalization CommonIntegerFile
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension 

def coefficient (q : Configuration) (κ : ℝ) : ℝ :=
  CodedSorting.Construction.Sorting.CommonMSDPhysicalRate.coefficient q (CodedSorting.Construction.Sorting.CommonMSDGlobalPower.coefficient q κ) 16

theorem logical_coefficient_nonneg (q : Configuration) (κ : ℝ) (hκ : 0≤κ) :
    0≤CodedSorting.Construction.Sorting.CommonMSDGlobalPower.coefficient q κ := by
  have hR := CodedSorting.Construction.Sorting.CommonMSDGlobalPower.rate_constant_nonneg
  have hF : 0≤CommonMSDRadixLogBounds.factor q :=
    (by norm_num : (0 : ℝ)≤1).trans (CommonMSDRadixLogBounds.factor_one q)
  unfold CodedSorting.Construction.Sorting.CommonMSDGlobalPower.coefficient
  positivity

/-- The natural budget is the concrete already-proved recursive ledger.
The extra 16 scans are 4 for expansion, 4 for projection, and 8 for the
single compact-layout normalization. -/
theorem complete_cost (q : Configuration) (κ : ℝ) (hκ : 0≤κ)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (hword : (q.w : ℝ)*Real.log 2≤κ*Real.log (q.N : ℝ))
    (xs : List (WordControl.Word q.w)) (hlen : xs.length=q.N)
    (cost : ℕ)
    (hcost : cost≤CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.budget q (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
      (input xs)+16*PhysicalStreamCursor.blockCount q.block q.N) :
    (cost : ℝ)≤coefficient q κ*((q.N : ℝ)/q.B)*
      CodedSorting.Construction.Sorting.CommonMSDPhysicalRate.paperFactor q q.N := by
  have hlen' : (input xs).length=q.N := by simpa only [input_length] using hlen
  have hpower := CodedSorting.Construction.Sorting.CommonMSDGlobalPower.budget_power q hnormal (input xs) κ hκ
    (by rw [hlen'];exact CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.height_le_input q)
    (by simpa only [hlen'] using hword)
  rw [hlen'] at hpower
  have hBN : q.B≤q.N := by have := q.block_memory;have := q.memory_input;omega
  exact CodedSorting.Construction.Sorting.CommonMSDPhysicalRate.with_scans q q.N _ cost 16
    (CodedSorting.Construction.Sorting.CommonMSDGlobalPower.coefficient q κ) hBN
    (logical_coefficient_nonneg q κ hκ) hpower hcost

end
end CodedSorting.Construction.Sorting.CommonIntegerSortingRate
end SortingRate

section Control
/-! Finite control for public integer input/output scans surrounding the
actual global sorter. The same counted top words select all three stages.
The enlarged control capacity follows from fixed numeric bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.Construction.Sorting.CommonIntegerControl
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalEntry CommonMSDParameters
open CommonLeafProgram (Machine)
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension

def routine (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i) :=
  CommonRoutineSandwich.routine q pre post hpre hpost (program q p n hn)

def stride (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i) : ℕ :=
  (Finset.univ.sup (fun tag => ((routine q p n hn pre post hpre hpost).body tag).length))+1

def threshold (κ : ℕ) : ℕ := 8*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.threshold κ

theorem stride_polynomial (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i)
    (hp : pre.length≤7*q.N) (ht : post.length≤7*q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block) :
    stride q p n hn pre post hpre hpost≤
      2*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.strideConstant*(q.N+1)^4 := by
  let S := CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.strideConstant
  have hS : 7≤S := by
    unfold S CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.strideConstant
      CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.nodeConstant CodedSorting.Construction.Sorting.CommonMSDCodePolynomial.leafConstant
    omega
  have hX : q.N+1≤(q.N+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0<q.N+1 by omega) (show 1≤4 by omega)
  have hscan : 7*q.N≤S*(q.N+1)^4 := by nlinarith
  have hold := CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.stride_polynomial q p n hn hnormal
  have hi : ∀ tag,((program q p n hn).body tag).length≤S*(q.N+1)^4 := by
    intro tag
    have hh := Finset.le_sup
      (f:=fun tag => ((program q p n hn).body tag).length) (Finset.mem_univ tag)
    change _≤CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.stride q p n hn-1 at hh
    change CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.stride q p n hn≤S*(q.N+1)^4 at hold
    exact hh.trans ((Nat.sub_le _ _).trans hold)
  have hbody : ∀ tag,((routine q p n hn pre post hpre hpost).body tag).length≤S*(q.N+1)^4 := by
    intro tag
    simp only [routine,CommonRoutineSandwich.routine]
    split_ifs with ha hb hc
    · exact hi _
    · exact hp.trans hscan
    · exact ht.trans hscan
    · simp
  have hs : stride q p n hn pre post hpre hpost≤S*(q.N+1)^4+1 := by
    unfold stride
    apply Nat.add_le_add_right
    exact Finset.sup_le (fun tag _ => hbody tag)
  change _≤2*S*(q.N+1)^4
  nlinarith only [hs,hS,hX]

theorem capacity (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i)
    (hp : pre.length≤7*q.N) (ht : post.length≤7*q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (hlarge : threshold κ≤q.N) (he : 17≤q.exponent) :
    (routine q p n hn pre post hpre hpost).Fits
      (stride q p n hn pre post hpre hpost) := by
  refine ⟨?_,?_⟩
  · intro tag
    exact Nat.lt_succ_of_le (Finset.le_sup
      (f:=fun tag => ((routine q p n hn pre post hpre hpost).body tag).length)
      (Finset.mem_univ tag))
  · let A := CodedSorting.Construction.Sorting.CommonMSDGlobalControl.tagCount q.N (levels q)
      (CommonMSDNodeTagBound.bound q (radix q)) (radix q)
    have hA : 1≤A := by
      have hh := (program q p n hn).entry.isLt
      change _<A at hh
      omega
    have htags := CommonMSDGlobalTagCapacity.tagCount_le q κ hw
    change A≤406*(κ+1)^2*(q.N+1)^12 at htags
    have hextra : A+3≤4*(406*(κ+1)^2*(q.N+1)^12) := by omega
    have hs := stride_polynomial q p n hn pre post hpre hpost hp ht hnormal
    have hm := Nat.mul_le_mul hextra hs
    have hpoly : (A+3)*stride q p n hn pre post hpre hpost≤
        8*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ*(q.N+1)^16 := by
      calc
        _ ≤ (4*(406*(κ+1)^2*(q.N+1)^12))*
            (2*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.strideConstant*(q.N+1)^4) := hm
        _ = _ := by unfold CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant;ring
    have hN : 1≤q.N := by have := q.input_large;omega
    have hpow := Nat.pow_le_pow_left (show q.N+1≤2*q.N by omega) 16
    have hscaled := Nat.mul_le_mul_left
      (8*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ) hpow
    have hth := Nat.mul_le_mul_right (q.N^16) hlarge
    unfold threshold CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.threshold at hth
    change (A+3)*stride q p n hn pre post hpre hpost≤_
    calc
      _ ≤ 8*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ*(q.N+1)^16 := hpoly
      _ ≤ 8*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ*(2*q.N)^16 := hscaled
      _ = (8*(2^16*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ))*q.N^16 := by ring
      _ ≤ q.N*q.N^16 := hth
      _ = q.N^17 := by ring
      _ ≤ q.N^q.exponent := Nat.pow_le_pow_right hN he

def initial (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i)
    (s : Machine q) : Machine q :=
  {s with ram:=setPC q ((routine q p n hn pre post hpre hpost).entry.val*
    stride q p n hn pre post hpre hpost) s.ram}

def policy (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i) : SourcePolicy q :=
  (routine q p n hn pre post hpre hpost).policy (stride q p n hn pre post hpre hpost)

end
end CodedSorting.Construction.Sorting.CommonIntegerControl
end Control

section SortingRun
/-! One fixed policy reads raw integer words, expands them in place, runs
the constructed global sorter, and projects its actual output back to words.
The public program never receives the input list or a successful-run oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace CodedSorting.Construction.Sorting.CommonIntegerSortingRun
open WordControl CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalEntry CommonRecordIntervalList CommonIntegerFile
open CommonLeafProgram (Machine Store)
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension
   CommonIntegerExpand.code CommonIntegerProjection.code

def pre (q : Configuration) (p : Parameters q) (n : ℕ) :=
  CommonIntegerExpand.code q p.reader n 0

def post (q : Configuration) (n : ℕ) := CommonIntegerProjection.code q n

def routine (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) :=
  CodedSorting.Construction.Sorting.CommonIntegerControl.routine q p n hn (pre q p n) (post q n)
    (CommonIntegerExpand.safe q p.reader n 0) (CommonIntegerProjection.safe q n)

def stride (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) :=
  CodedSorting.Construction.Sorting.CommonIntegerControl.stride q p n hn (pre q p n) (post q n)
    (CommonIntegerExpand.safe q p.reader n 0) (CommonIntegerProjection.safe q n)

def policy (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N) : SourcePolicy q :=
  (routine q p n hn).policy (stride q p n hn)

def initial (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (s : Machine q) : Machine q :=
  {s with ram:=setPC q ((routine q p n hn).entry.val*stride q p n hn) s.ram}

def initStore (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (store : Store q) : Store q :=
  {store with top:=(PhysicalStreamCursor.encodeNat q.digits q.w
    ((routine q p n hn).entry.val*stride q p n hn))}

theorem pack_initStore (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (store : Store q) :
    pack (initStore q p n hn store)=
      setPC q ((routine q p n hn).entry.val*stride q p n hn) (pack store) := by
  simp only [initStore,setPC,unpack_pack]

theorem initial_idempotent (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (s : Machine q) : initial q p n hn (initial q p n hn s)=initial q p n hn s := by
  simp only [initial,setPC_setPC]

theorem initial_packed (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (store : Store q) (disk : CommonLeafProgram.Disk q) :
    initial q p n hn (CommonLeafProgram.machine q store disk)=
      CommonLeafProgram.machine q (initStore q p n hn store) disk := by
  simp only [initial,CommonLeafProgram.machine,pack_initStore]

theorem fits (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (hlarge : CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ≤q.N)
    (he : 17≤q.exponent) : (routine q p n hn).Fits (stride q p n hn) := by
  have hcap := CommonIntegerProjection.capacity q n hn (by omega)
  have hB : PhysicalStreamCursor.blockCount q.block n≤n :=
    CommonLeafGrouping.blockCount_le_of_fits (CommonLeafProgram.block_positive q)
      (Nat.le_mul_of_pos_right _ (CommonLeafProgram.block_positive q))
  have hpre : (pre q p n).length≤7*q.N := by
    rw [pre,CommonIntegerExpand.length q p.reader n 0 (by simpa using hcap)]
    change 7*PhysicalStreamCursor.blockCount q.block n≤7*q.N
    omega
  have hpost : (post q n).length≤7*q.N := by
    rw [post,CommonIntegerProjection.length_code]
    change 5*PhysicalStreamCursor.blockCount q.block n≤7*q.N
    omega
  exact CodedSorting.Construction.Sorting.CommonIntegerControl.capacity q p n hn (pre q p n) (post q n)
    (CommonIntegerExpand.safe q p.reader n 0) (CommonIntegerProjection.safe q n)
    hpre hpost hnormal κ hw hlarge he

theorem initStore_pc (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (hlarge : CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ≤q.N)
    (he : 17≤q.exponent) (store : Store q) :
    pc q (pack (initStore q p n hn store))=(routine q p n hn).entry.val*stride q p n hn := by
  rw [pack_initStore]
  exact pc_setPC q _ _ ((routine q p n hn).tag_capacity (stride q p n hn)
    (fits q p n hn hnormal κ hw hlarge he) _)

/-- The caller may use already initialized RAM, as in the physical
normalization wrapper. The only input premise is the actual raw word file. -/
theorem complete_from_pc (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hsource : p.source=0)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (hlarge : CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ≤q.N)
    (he : 17≤q.exponent) (s : Machine q) (xs : List (Word q.w)) (hlen : xs.length=n)
    (hx : WordFile q s.disk 0 0 xs)
    (hpc : pc q s.ram=(routine q p n hn).entry.val*stride q p n hn) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (policy q p n hn) steps s
      WordFile q out.1.disk 0 0 (output q xs) ∧
      policy q p n hn out.1.ram=none ∧
      out.2≤CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.budget q (levels q) (input xs)+
        8*PhysicalStreamCursor.blockCount q.block n := by
  have hcap := CommonIntegerProjection.capacity q n hn (by omega)
  have hfit : 0+3*CommonIntegerExpand.blocks q n≤q.N^q.exponent := by simpa using hcap
  have hc : ControlCapacity q p n hn :=
    CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.capacity q p n hn hnormal κ hw
      (by unfold CodedSorting.Construction.Sorting.CommonIntegerControl.threshold at hlarge;omega) he
  have hbefore := CommonIntegerExpand.raw_correct q p.reader n 0 s xs hlen hx hfit
  change EncodedListAt q (CommonRoutineSandwich.before q (pre q p n) s).disk 0 0 (input xs) at hbefore
  have hbefore' : EncodedListAt q (CommonRoutineSandwich.before q (pre q p n) s).disk
      p.source 0 (input xs) := by simpa only [hsource] using hbefore
  obtain ⟨tag,final,steps,charge,htrace,hout,hcharge⟩ := CodedSorting.Construction.Sorting.CommonMSDSortingTrace.complete q p n hn hc
    (CommonRoutineSandwich.before q (pre q p n) s) (input xs)
    (by simpa only [input_length] using hlen) hbefore' (input_ordinary xs)
  have houtputlen : (CommonMSDSortingRun.output q (input xs)).length=n :=
    (CommonMSDRadixCost.semantic_correct q (input xs) (input_ordinary xs)).1.length_eq.trans
      ((input_length xs).trans hlen)
  have hproj := CommonIntegerProjection.raw_complete q (CommonMSDSortingRun.output q (input xs))
    final (by simpa only [hsource] using hout) (by simpa only [houtputlen] using hcap)
  rw [houtputlen] at hproj
  have hword : WordFile q (CommonRoutineSandwich.after q (post q n) final).disk 0 0 (output q xs) := hproj
  have hwrap := CommonRoutineSandwich.trace q (pre q p n) (post q n)
    (CommonIntegerExpand.safe q p.reader n 0) (CommonIntegerProjection.safe q n)
    (program q p n hn) htrace
  have hrun := (routine q p n hn).trace_run (stride q p n hn)
    (fits q p n hn hnormal κ hw hlarge he) hwrap hpc
  have hd := congrArg (fun t : Machine q => t.disk) hrun.1
  change (ControlledNormalization.runLogical ((routine q p n hn).policy (stride q p n hn))
    ((pre q p n).length+steps+(post q n).length+3) s).1.disk=
      (CommonRoutineSandwich.after q (post q n) final).disk at hd
  have hpreCost : cost q (pre q p n)=4*PhysicalStreamCursor.blockCount q.block n :=
    CommonIntegerExpand.cost_eq q p.reader n 0 hfit
  have hpostCost : cost q (post q n)=4*PhysicalStreamCursor.blockCount q.block n :=
    CommonIntegerProjection.cost_code q n hcap
  refine ⟨(pre q p n).length+steps+(post q n).length+3,?_,hrun.2.2.2,?_⟩
  · change WordFile q (ControlledNormalization.runLogical
      ((routine q p n hn).policy (stride q p n hn)) _ s).1.disk 0 0 _
    rw [hd]
    exact hword
  · change (ControlledNormalization.runLogical ((routine q p n hn).policy (stride q p n hn))
      ((pre q p n).length+steps+(post q n).length+3) s).2≤_
    rw [hrun.2.1,hpreCost,hpostCost]
    omega

theorem complete (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hsource : p.source=0)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (hlarge : CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ≤q.N)
    (he : 17≤q.exponent) (s : Machine q) (xs : List (Word q.w)) (hlen : xs.length=n)
    (hx : WordFile q s.disk 0 0 xs) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (policy q p n hn) steps (initial q p n hn s)
      WordFile q out.1.disk 0 0 (output q xs) ∧
      policy q p n hn out.1.ram=none ∧
      out.2≤CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.budget q (levels q) (input xs)+
        8*PhysicalStreamCursor.blockCount q.block n := by
  apply complete_from_pc q p n hn hsource hnormal κ hw hlarge he
    (initial q p n hn s) xs hlen hx
  exact pc_setPC q _ _ ((routine q p n hn).tag_capacity (stride q p n hn)
    (fits q p n hn hnormal κ hw hlarge he) _)

end
end CodedSorting.Construction.Sorting.CommonIntegerSortingRun
end SortingRun

section AllInputCapacity
/-! The fixed coefficients of the public disk and control polynomials can
be absorbed by a larger fixed address exponent, for every N at least two.
This constructs the same allocations and policies without a large-N
premise. The exponent depends only on the fixed word-width constant and
the new Construction coefficients: actual ExchangeSpace allocations on the disk
side and actual LocalBudget charges on the instruction side. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity
open CommonSortingNormalization CodedSorting.Construction.RecursiveParameters CodedSorting.Construction.Sorting.CommonMSDGlobalEntry
open CommonMSDParameters CommonMSDPublicWordBounds CommonStaticSchedule
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension

def allowance (κ : ℕ) : ℕ := max
  (CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.diskThreshold κ)
  (CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ)

def exponent (κ : ℕ) : ℕ := 17+Nat.clog 2 (allowance κ)

theorem exponent_ge17 (κ : ℕ) : 17≤exponent κ := by unfold exponent;omega

/-- Absorb a fixed coefficient rather than requiring the input length
to exceed it. No property of the input contents is involved. -/
theorem absorb (N A d E κ : ℕ) (hN : 2≤N)
    (hA : A*2^d≤allowance κ) (hd : d≤17) (hE : exponent κ≤E) :
    A*(N+1)^d≤N^E := by
  have hc : allowance κ≤N^(Nat.clog 2 (allowance κ)) :=
    (Nat.le_pow_clog (by omega : 1<(2 : ℕ)) _).trans (Nat.pow_le_pow_left hN _)
  have hbase : N+1≤2*N := by omega
  calc
    A*(N+1)^d ≤ A*(2*N)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = (A*2^d)*N^d := by rw [mul_pow];ring
    _ ≤ allowance κ*N^d := Nat.mul_le_mul_right _ hA
    _ ≤ N^(Nat.clog 2 (allowance κ))*N^d := Nat.mul_le_mul_right _ hc
    _ = N^(Nat.clog 2 (allowance κ)+d) := (pow_add _ _ _).symm
    _ ≤ N^E := Nat.pow_le_pow_right (by omega) (by unfold exponent at hE;omega)

def disk_capacity (q : Configuration) (normal : Normalized q) (κ : ℕ)
    (hw : q.w≤κ*q.N) (he : exponent κ≤q.exponent) :
    CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal q.N (radix q)
      (CommonMSDRadixCost.depth q) 0 where
  input := le_rfl
  exponent := (by have:=exponent_ge17 κ;omega)
  disk := by
    have hp := CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.endAddress_polynomial q normal
      (radix q) (CommonMSDRadixCost.depth q)
      CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.workspaceCoefficient 5 κ (by omega)
      (CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.work_le q normal)
      ((CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.depth_le_word q).trans hw)
    apply hp.trans
    apply absorb q.N _ 6 q.exponent κ q.input_large
      (by exact Nat.le_max_left _ _) (by omega) he

def parameters (q : Configuration) (reader : Fin q.inventory.readers)
    (hratio : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.inventory.ratio)
    (κ : ℝ) (hword : (q.w : ℝ)*Real.log 2≤κ*Real.log (q.N : ℝ))
    (he : exponent (wordFactor κ)≤q.exponent) : Parameters q where
  reader := reader
  normal := CodedSorting.Construction.RecursiveParameters.normalized_of_inventory q hratio
  source := 0
  capacity := disk_capacity q (CodedSorting.Construction.RecursiveParameters.normalized_of_inventory q hratio)
    (wordFactor κ) (word_linear q κ hword) he

theorem control (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (he : exponent κ≤q.exponent) :
    ControlCapacity q p n hn := by
  apply (CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.control_polynomial q p n hn hnormal κ hw).trans
  apply absorb q.N _ 16 q.exponent κ q.input_large ?_ (by omega) he
  have hh : CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.threshold κ≤CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ := by
    unfold CodedSorting.Construction.Sorting.CommonIntegerControl.threshold
    omega
  have h := hh.trans (Nat.le_max_right
    (CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.diskThreshold κ) (CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ))
  simpa only [CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.threshold,Nat.mul_comm] using h

theorem outer_polynomial (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i)
    (hp : pre.length≤7*q.N) (ht : post.length≤7*q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) :
    (CodedSorting.Construction.Sorting.CommonMSDGlobalControl.tagCount q.N (levels q)
      (CommonMSDNodeTagBound.bound q (radix q)) (radix q)+3)*
      CodedSorting.Construction.Sorting.CommonIntegerControl.stride q p n hn pre post hpre hpost≤
      8*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ*(q.N+1)^16 := by
  let A := CodedSorting.Construction.Sorting.CommonMSDGlobalControl.tagCount q.N (levels q)
    (CommonMSDNodeTagBound.bound q (radix q)) (radix q)
  have hA : 1≤A := by have h:=(program q p n hn).entry.isLt;change _<A at h;omega
  have htags := CommonMSDGlobalTagCapacity.tagCount_le q κ hw
  change A≤406*(κ+1)^2*(q.N+1)^12 at htags
  have hextra : A+3≤4*(406*(κ+1)^2*(q.N+1)^12) := by omega
  have hs := CodedSorting.Construction.Sorting.CommonIntegerControl.stride_polynomial q p n hn pre post hpre hpost hp ht hnormal
  have hm := Nat.mul_le_mul hextra hs
  calc
    _ ≤ (4*(406*(κ+1)^2*(q.N+1)^12))*
        (2*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.strideConstant*(q.N+1)^4) := hm
    _ = _ := by unfold CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant;ring

theorem outer_fits (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (pre post : List (Instruction q))
    (hpre : ∀ i∈pre,RespectsPC q i) (hpost : ∀ i∈post,RespectsPC q i)
    (hp : pre.length≤7*q.N) (ht : post.length≤7*q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (he : exponent κ≤q.exponent) :
    (CodedSorting.Construction.Sorting.CommonIntegerControl.routine q p n hn pre post hpre hpost).Fits
      (CodedSorting.Construction.Sorting.CommonIntegerControl.stride q p n hn pre post hpre hpost) := by
  refine ⟨?_,?_⟩
  · intro tag
    exact Nat.lt_succ_of_le (Finset.le_sup
      (f:=fun tag => ((CodedSorting.Construction.Sorting.CommonIntegerControl.routine q p n hn pre post hpre hpost).body tag).length)
      (Finset.mem_univ tag))
  · apply (outer_polynomial q p n hn pre post hpre hpost hp ht hnormal κ hw).trans
    apply absorb q.N _ 16 q.exponent κ q.input_large ?_ (by omega) he
    have h := Nat.le_max_right (CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity.diskThreshold κ)
      (CodedSorting.Construction.Sorting.CommonIntegerControl.threshold κ)
    unfold CodedSorting.Construction.Sorting.CommonIntegerControl.threshold CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.threshold at h
    change _≤allowance κ
    exact (show (8*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ)*2^16=
      8*(2^16*CodedSorting.Construction.Sorting.CommonMSDGlobalControlCapacity.controlConstant κ) by ring).le.trans h

theorem fits (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
      CodedSorting.Construction.streamCount≤q.height/q.block)
    (κ : ℕ) (hw : q.w≤κ*q.N) (he : exponent κ≤q.exponent) :
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).Fits (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn) := by
  have he2 : 2≤q.exponent := by have:=exponent_ge17 κ;omega
  have hcap := CommonIntegerCapacity.format_blocks_fit q n hn he2
  have hB := CommonIntegerCapacity.blocks_le q n
  have hpre : (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n).length≤7*q.N := by
    rw [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre,CommonIntegerExpand.length q p.reader n 0 (by simpa using hcap)]
    change 7*CommonIntegerPhysical.blocks q n≤7*q.N
    omega
  have hpost : (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n).length≤7*q.N := by
    rw [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post,CommonIntegerProjection.length_code]
    change 5*CommonIntegerPhysical.blocks q n≤7*q.N
    omega
  exact outer_fits q p n hn _ _ _ _ hpre hpost hnormal κ hw he

end
end CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity
end AllInputCapacity

section AllInputRun
/-! The same raw-integer CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy with exact finite-capacity premises.
The public all-input allocator discharges these scalar conditions using a
fixed larger address exponent instead of a lower threshold on N. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace CodedSorting.Construction.Sorting.CommonIntegerAllInputRun
open WordControl CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CodedSorting.Construction.Sorting.CommonMSDGlobalEntry CommonRecordIntervalList CommonIntegerFile CodedSorting.Construction.Sorting.CommonIntegerSortingRun
open CommonLeafProgram (Machine Store)
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension
   CommonIntegerExpand.code CommonIntegerProjection.code

theorem initStore_pc_of_fits (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hf : (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).Fits (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn)) (store : Store q) :
    pc q (pack (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initStore q p n hn store))=(CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).entry.val*CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn := by
  rw [CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pack_initStore]
  exact pc_setPC q _ _ ((CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).tag_capacity (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn) hf _)

/-- The caller may use already initialized RAM, as in the physical
normalization wrapper. The only input premise is the actual raw word file. -/
theorem complete_from_pc (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hsource : p.source=0)
    (hc : ControlCapacity q p n hn)
    (hf : (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).Fits (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn))
    (he : 2≤q.exponent) (s : Machine q) (xs : List (Word q.w)) (hlen : xs.length=n)
    (hx : WordFile q s.disk 0 0 xs)
    (hpc : pc q s.ram=(CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).entry.val*CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy q p n hn) steps s
      WordFile q out.1.disk 0 0 (output q xs) ∧
      CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy q p n hn out.1.ram=none ∧
      out.2≤CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.budget q (levels q) (input xs)+
        8*PhysicalStreamCursor.blockCount q.block n := by
  have hcap := CommonIntegerProjection.capacity q n hn (by omega)
  have hfit : 0+3*CommonIntegerExpand.blocks q n≤q.N^q.exponent := by simpa using hcap
  have hbefore := CommonIntegerExpand.raw_correct q p.reader n 0 s xs hlen hx hfit
  change EncodedListAt q (CommonRoutineSandwich.before q (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n) s).disk 0 0 (input xs) at hbefore
  have hbefore' : EncodedListAt q (CommonRoutineSandwich.before q (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n) s).disk
      p.source 0 (input xs) := by simpa only [hsource] using hbefore
  obtain ⟨tag,final,steps,charge,htrace,hout,hcharge⟩ := CodedSorting.Construction.Sorting.CommonMSDSortingTrace.complete q p n hn hc
    (CommonRoutineSandwich.before q (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n) s) (input xs)
    (by simpa only [input_length] using hlen) hbefore' (input_ordinary xs)
  have houtputlen : (CommonMSDSortingRun.output q (input xs)).length=n :=
    (CommonMSDRadixCost.semantic_correct q (input xs) (input_ordinary xs)).1.length_eq.trans
      ((input_length xs).trans hlen)
  have hproj := CommonIntegerProjection.raw_complete q (CommonMSDSortingRun.output q (input xs))
    final (by simpa only [hsource] using hout) (by simpa only [houtputlen] using hcap)
  rw [houtputlen] at hproj
  have hword : WordFile q (CommonRoutineSandwich.after q (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n) final).disk 0 0 (output q xs) := hproj
  have hwrap := CommonRoutineSandwich.trace q (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n) (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n)
    (CommonIntegerExpand.safe q p.reader n 0) (CommonIntegerProjection.safe q n)
    (program q p n hn) htrace
  have hrun := (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).trace_run (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn)
    hf hwrap hpc
  have hd := congrArg (fun t : Machine q => t.disk) hrun.1
  change (ControlledNormalization.runLogical ((CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).policy (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn))
    ((CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n).length+steps+(CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n).length+3) s).1.disk=
      (CommonRoutineSandwich.after q (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n) final).disk at hd
  have hpreCost : cost q (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n)=4*PhysicalStreamCursor.blockCount q.block n :=
    CommonIntegerExpand.cost_eq q p.reader n 0 hfit
  have hpostCost : cost q (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n)=4*PhysicalStreamCursor.blockCount q.block n :=
    CommonIntegerProjection.cost_code q n hcap
  refine ⟨(CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n).length+steps+(CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n).length+3,?_,hrun.2.2.2,?_⟩
  · change WordFile q (ControlledNormalization.runLogical
      ((CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).policy (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn)) _ s).1.disk 0 0 _
    rw [hd]
    exact hword
  · change (ControlledNormalization.runLogical ((CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).policy (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn))
      ((CodedSorting.Construction.Sorting.CommonIntegerSortingRun.pre q p n).length+steps+(CodedSorting.Construction.Sorting.CommonIntegerSortingRun.post q n).length+3) s).2≤_
    rw [hrun.2.1,hpreCost,hpostCost]
    omega

theorem complete (q : Configuration) (p : Parameters q) (n : ℕ) (hn : n≤q.N)
    (hsource : p.source=0) (hc : ControlCapacity q p n hn)
    (hf : (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).Fits (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn)) (he : 2≤q.exponent)
    (s : Machine q) (xs : List (Word q.w)) (hlen : xs.length=n)
    (hx : WordFile q s.disk 0 0 xs) :
    ∃ steps,
      let out := ControlledNormalization.runLogical (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy q p n hn) steps (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initial q p n hn s)
      WordFile q out.1.disk 0 0 (output q xs) ∧
      CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy q p n hn out.1.ram=none ∧
      out.2≤CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.budget q (levels q) (input xs)+
        8*PhysicalStreamCursor.blockCount q.block n := by
  apply complete_from_pc q p n hn hsource hc hf he (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initial q p n hn s) xs hlen hx
  exact pc_setPC q _ _ ((CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q p n hn).tag_capacity (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q p n hn) hf _)

end
end CodedSorting.Construction.Sorting.CommonIntegerAllInputRun
end AllInputRun

section AllInputPhysical
/-! A complete physical integer sorting run in the normal-memory range.
The public setup has no extra lower bound on input size. A single fixed
address exponent supplies disk and control space for every configuration.
The proof
constructs the allocation, controller, two format scans, full sorting run,
and one physical normalization, with their total I/O on that same run. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical
open WordControl CommonSortingNormalization CommonIntegerFile
open CommonLeafProgram (Store)
open CommonMSDPublicWordBounds
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension
  

/-- All fields are public numeric conditions, independent of input values.
Fix inventory, c, exponent, and kappa when interpreting the asymptotic bound.
The address exponent is fixed above the construction constant; there is no
additional lower threshold on N beyond Configuration's normal-memory range. -/
structure Parameters (q : Configuration) where
  reader : Fin q.inventory.readers
  ratio : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1
    CodedSorting.Construction.streamCount≤q.inventory.ratio
  kappa : ℝ
  kappa_nonnegative : 0≤kappa
  word_bound : (q.w : ℝ)*Real.log 2≤kappa*Real.log (q.N : ℝ)
  exponent : CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent (wordFactor kappa)≤q.exponent

def core (q : Configuration) (p : Parameters q) : CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.Parameters q :=
  CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.parameters q p.reader p.ratio p.kappa p.word_bound p.exponent

def algorithm (q : Configuration) (p : Parameters q) : SourcePolicy q :=
  CodedSorting.Construction.Sorting.CommonIntegerSortingRun.policy q (core q p) q.N le_rfl

def start (q : Configuration) (p : Parameters q) (store : Store q)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w) : MachineState q :=
  CommonIntegerPhysical.start q (algorithm q p)
    (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initStore q (core q p) q.N le_rfl store) q.N
    (CommonIntegerCapacity.blocks_lt q q.N le_rfl (by have:=CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent_ge17 (wordFactor p.kappa);have:=p.exponent;omega)) disk

/-- Raw compact integer input, raw compact sorted output, actual physical
execution and the paper's M,B I/O expression. No workspace, control, codec,
successful-run, or cost premise is supplied by the caller. -/
theorem complete (q : Configuration) (p : Parameters q) (store : Store q)
    (disk : CommonNormalizationController.Disk (q.N^q.exponent) q.B q.w)
    (xs : List (Word q.w)) (hlen : xs.length=q.N)
    (hx : CommonIntegerPhysical.InputFile q disk xs) :
    ∃ fuel,
      let prog := program q (algorithm q p)
      let s := start q p store disk
      let blocks := CommonIntegerPhysical.blocks q q.N
      let result := CommonNormalizationController.run prog (blocks+1+fuel+1+blocks+1) s
      (∀ i : Fin (output q xs).length,
        CommonNormalizationController.outputWord prog result.1 i.val=(output q xs).get i) ∧
      (output q xs).Perm xs ∧ (output q xs).Pairwise (·≤·) ∧
      CommonNormalizationController.step prog result.1=(result.1,0) ∧
      Fintype.card (ResidentIndex q)≤q.M ∧
      Fintype.card (CommonNormalizationController.Address (q.N^q.exponent))≤q.N^(q.exponent+2) ∧
      (result.2 : ℝ)≤CodedSorting.Construction.Sorting.CommonIntegerSortingRate.coefficient q p.kappa*
        ((q.N : ℝ)/q.B)*CodedSorting.Construction.Sorting.CommonMSDPhysicalRate.paperFactor q q.N := by
  let r := core q p
  let alg := algorithm q p
  let store' := CodedSorting.Construction.Sorting.CommonIntegerSortingRun.initStore q r q.N le_rfl store
  have hcap := CommonIntegerCapacity.blocks_lt q q.N le_rfl (by have:=CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent_ge17 (wordFactor p.kappa);have:=p.exponent;omega)
  let s := CommonIntegerPhysical.start q alg store' q.N hcap disk
  let logical := CommonNormalizationController.logicalInput (program q alg) s
  have hnormal := CodedSorting.Construction.Sorting.CommonSortingExchangeRate.normal_height_of_inventory q p.ratio
  have hw := word_linear q p.kappa p.word_bound
  have hc := CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.control q r q.N le_rfl hnormal
    (wordFactor p.kappa) hw p.exponent
  have hf := CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.fits q r q.N le_rfl hnormal
    (wordFactor p.kappa) hw p.exponent
  have he : 2≤q.exponent := by
    have:=CodedSorting.Construction.Sorting.CommonIntegerAllInputCapacity.exponent_ge17 (wordFactor p.kappa)
    have:=p.exponent
    omega
  have hinput := CommonIntegerPhysical.expanded_input q alg store' q.N hcap disk xs hlen hx
  have hpc : CommonStaticSchedule.pc q logical.ram=
      (CodedSorting.Construction.Sorting.CommonIntegerSortingRun.routine q r q.N le_rfl).entry.val*
        CodedSorting.Construction.Sorting.CommonIntegerSortingRun.stride q r q.N le_rfl :=
    CodedSorting.Construction.Sorting.CommonIntegerAllInputRun.initStore_pc_of_fits q r q.N le_rfl hf store
  obtain ⟨T,hout,hhalt,hcharge⟩ := CodedSorting.Construction.Sorting.CommonIntegerAllInputRun.complete_from_pc q r q.N le_rfl
    rfl hc hf he logical xs hlen hinput hpc
  have hcorrect := output_correct q xs
  have houtputlen : (output q xs).length=q.N := hcorrect.1.length_eq.trans hlen
  obtain ⟨fuel,hle,hwords,hcost,hstop,hmemory,hdisk⟩ :=
    CommonIntegerPhysicalHalted.complete q alg store' q.N hcap disk (output q xs)
      houtputlen T hhalt hout
  refine ⟨fuel,hwords,hcorrect.1,hcorrect.2,hstop,hmemory,hdisk,?_⟩
  apply CodedSorting.Construction.Sorting.CommonIntegerSortingRate.complete_cost q p.kappa p.kappa_nonnegative hnormal
    p.word_bound xs hlen
  change (CommonNormalizationController.run (program q alg)
    (CommonIntegerPhysical.blocks q q.N+1+fuel+1+CommonIntegerPhysical.blocks q q.N+1)
    (CommonIntegerPhysical.start q alg store' q.N hcap disk)).2≤_
  rw [hcost]
  change _≤CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.budget q (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
    (input xs)+16*CommonIntegerPhysical.blocks q q.N
  change (ControlledNormalization.runLogical alg T
    (CommonNormalizationController.logicalInput (program q alg)
      (CommonIntegerPhysical.start q alg store' q.N hcap disk))).2≤
    CodedSorting.Construction.Sorting.CommonMSDGlobalCostRecursion.budget q (CodedSorting.Construction.Sorting.CommonMSDGlobalEntry.levels q)
      (input xs)+8*CommonIntegerPhysical.blocks q q.N at hcharge
  omega

end
end CodedSorting.Construction.Sorting.CommonIntegerAllInputPhysical
end AllInputPhysical
