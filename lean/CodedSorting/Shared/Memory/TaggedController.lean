import CodedSorting.Shared.Programs.Static.Fusion

section PolicyComposition
/-! Sequential composition of RAM-controlled policies on the same machine.
The selector and boundary initializer are functions of existing RAM. Neither
the dispatcher nor the proof adds storage, captures a disk, or performs an
uncharged transfer. A first-halt argument removes idle fuel before starting
the next policy. -/

set_option autoImplicit false
namespace CodedSorting.CommonPolicyComposition
open Normalization (Words LogicalState)
open ControlledNormalization
variable {Word : Type*} {L b D : ℕ}

theorem run_add (p : Policy L b D Word) (n m : ℕ)
    (s : LogicalState L b D Word) :
    runLogical p (n+m) s =
      ((runLogical p m (runLogical p n s).1).1,
        (runLogical p n s).2+(runLogical p m (runLogical p n s).1).2) := by
  induction n generalizing s with
  | zero => simp [runLogical]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [runLogical]
    cases hp : p s.ram with
    | none => cases m <;> simp [runLogical,hp]
    | some i => simp only; rw [ih]; simp [Nat.add_assoc]

theorem run_halted (p : Policy L b D Word) (s : LogicalState L b D Word)
    (h : p s.ram=none) (n : ℕ) : runLogical p n s=(s,0) := by
  cases n <;> simp only [runLogical,h]

theorem run_after_halt (p : Policy L b D Word) (s : LogicalState L b D Word)
    (n k : ℕ) (h : p (runLogical p n s).1.ram=none) :
    runLogical p (n+k) s=runLogical p n s := by
  rw [run_add,run_halted p _ h k]
  simp only [Nat.add_zero,Prod.mk.eta]

/-- A known halting horizon contains a first halt with exactly the same
state and charge. No idle step is exported to the enclosing program. -/
theorem first_halt (p : Policy L b D Word) (s : LogicalState L b D Word)
    (T : ℕ) (hT : p (runLogical p T s).1.ram=none) :
    ∃ τ, τ≤T ∧ runLogical p τ s=runLogical p T s ∧
      p (runLogical p τ s).1.ram=none ∧
      ∀ k, k<τ → p (runLogical p k s).1.ram≠none := by
  classical
  have hex : ∃ n,p (runLogical p n s).1.ram=none := ⟨T,hT⟩
  let τ := Nat.find hex
  have ht : p (runLogical p τ s).1.ram=none := Nat.find_spec hex
  have hle : τ≤T := Nat.find_min' hex hT
  refine ⟨τ,hle,?_,ht,?_⟩
  · symm
    rw [←Nat.add_sub_of_le hle]
    exact run_after_halt p s τ (T-τ) ht
  · intro k hk
    exact Nat.find_min hex hk

/-- Policy equality is needed only at states actually reached before the
specified horizon. This includes equality of the RAM-only continuations. -/
theorem run_eq_of_agree (p q : Policy L b D Word) (s : LogicalState L b D Word)
    (n : ℕ) (h : ∀ k,k<n → q (runLogical p k s).1.ram=p (runLogical p k s).1.ram) :
    runLogical q n s=runLogical p n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (fun k hk => h k (by omega))
    rw [show n+1=n+1 from rfl,run_add q n 1,run_add p n 1,heq]
    have hp := h n (by omega)
    simp only [runLogical,hp]

/-- Any one-step state invariant also holds after every finite run. -/
theorem run_invariant (p : Policy L b D Word) (Q : LogicalState L b D Word → Prop)
    (hstep : ∀ s i,Q s → p s.ram=some i → Q (ControlledNormalization.logicalStep i s))
    (s : LogicalState L b D Word) (hs : Q s) (n : ℕ) :
    Q (runLogical p n s).1 := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    cases hp : p s.ram with
    | none => simpa only [runLogical,hp] using hs
    | some i => simpa only [runLogical,hp] using ih _ (hstep s i hs hp)

/-- `false` selects the first policy. Its stop is replaced by one local
boundary instruction. `true` selects the second policy, including its stop.
The caller chooses a selector already encoded in the existing RAM. -/
def sequential (mode : Words L Word → Bool) (init : Words L Word → Words L Word)
    (first second : Policy L b D Word) : Policy L b D Word := fun ram =>
  if mode ram then second ram else
    match first ram with
    | some i => some i
    | none => some ⟨.localOp init,id⟩

def boundary (init : Words L Word → Words L Word)
    (s : LogicalState L b D Word) : LogicalState L b D Word :=
  {s with ram:=init s.ram}

theorem sequential_first (mode : Words L Word → Bool) (init : Words L Word → Words L Word)
    (first second : Policy L b D Word) (s : LogicalState L b D Word) (τ : ℕ)
    (hm : ∀ k,k<τ → mode (runLogical first k s).1.ram=false)
    (hl : ∀ k,k<τ → first (runLogical first k s).1.ram≠none) :
    runLogical (sequential mode init first second) τ s=runLogical first τ s := by
  apply run_eq_of_agree
  intro k hk
  simp only [sequential,hm k hk,Bool.false_eq_true,↓reduceIte]
  cases hp : first (runLogical first k s).1.ram with
  | none => exact False.elim (hl k hk hp)
  | some i => rfl

theorem sequential_second (mode : Words L Word → Bool) (init : Words L Word → Words L Word)
    (first second : Policy L b D Word) (s : LogicalState L b D Word) (T : ℕ)
    (hm : ∀ k,k<T → mode (runLogical second k s).1.ram=true) :
    runLogical (sequential mode init first second) T s=runLogical second T s := by
  apply run_eq_of_agree
  intro k hk
  simp only [sequential,hm k hk,↓reduceIte]

theorem sequential_boundary (mode : Words L Word → Bool)
    (init : Words L Word → Words L Word) (first second : Policy L b D Word)
    (s : LogicalState L b D Word) (hm : mode s.ram=false) (hh : first s.ram=none) :
    runLogical (sequential mode init first second) 1 s=(boundary init s,0) := by
  simp only [runLogical,sequential,hm,Bool.false_eq_true,↓reduceIte,hh,
    ControlledNormalization.logicalStep,Normalization.logicalStep,
    Normalization.transferCost,Nat.zero_add]
  rfl

/-- Composition of two actual executions, with one charged-as-zero local
boundary. The whole result is one run of one fixed policy on one machine.
The first component's arbitrary horizon is shortened to its first halt. -/
theorem sequential_complete (mode : Words L Word → Bool)
    (init : Words L Word → Words L Word) (first second : Policy L b D Word)
    (s : LogicalState L b D Word) (T U : ℕ)
    (hfirst : first (runLogical first T s).1.ram=none)
    (hmfirst : ∀ k,k≤T → mode (runLogical first k s).1.ram=false)
    (hmsecond : ∀ k,k≤U → mode (runLogical second k
      (boundary init (runLogical first T s).1)).1.ram=true)
    (hsecond : second (runLogical second U
      (boundary init (runLogical first T s).1)).1.ram=none) :
    ∃ τ, τ≤T ∧
      runLogical (sequential mode init first second) (τ+1+U) s =
        ((runLogical second U (boundary init (runLogical first T s).1)).1,
          (runLogical first T s).2+
            (runLogical second U (boundary init (runLogical first T s).1)).2) ∧
      sequential mode init first second
        (runLogical (sequential mode init first second) (τ+1+U) s).1.ram=none := by
  obtain ⟨τ,hle,heq,hhalt,hlive⟩ := first_halt first s T hfirst
  have hprefix := sequential_first mode init first second s τ
    (fun k hk => hmfirst k (by omega)) hlive
  have hboundary := sequential_boundary mode init first second (runLogical first τ s).1
    (hmfirst τ hle) hhalt
  have hsuffix := sequential_second mode init first second
    (boundary init (runLogical first T s).1) U (fun k hk => hmsecond k (by omega))
  have hrun : runLogical (sequential mode init first second) (τ+1+U) s =
      ((runLogical second U (boundary init (runLogical first T s).1)).1,
        (runLogical first T s).2+
          (runLogical second U (boundary init (runLogical first T s).1)).2) := by
    rw [run_add _ (τ+1) U,run_add _ τ 1,hprefix,hboundary]
    dsimp only
    rw [heq,hsuffix]
    simp only [Nat.add_zero]
  refine ⟨τ,hle,hrun,?_⟩
  rw [hrun]
  simp only [sequential,hmsecond U (by omega),↓reduceIte,hsecond]

end CodedSorting.CommonPolicyComposition
end PolicyComposition

section PolicyNormalized
/-! One physical normalization around an arbitrary completed source policy.
The same physical execution realizes the logical output, total logical I/O,
both live-layout conversion charges, and an actual halted controller. -/

set_option autoImplicit false
namespace CodedSorting.CommonPolicyNormalized
open WordControl CommonSortingNormalization

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
          CommonNormalizationController.outputSize s) s
      let logical := ControlledNormalization.runLogical policy T
        (CommonNormalizationController.logicalInput p s)
      result.1.ram=logical.1.ram ∧
      (∀ j : Fin (CommonNormalizationController.outputSize s),∀ i : Fin q.block,
        CommonNormalizationController.outputWord p result.1 (j.val*q.block+i.val)=
          logical.1.disk
            (j.castLE ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))) i) ∧
      result.2=logical.2+3*CommonNormalizationController.inputSize s+
        5*CommonNormalizationController.outputSize s ∧
      let halted := CommonNormalizationController.run p
        (CommonNormalizationController.inputSize s+1+fuel+1+
          CommonNormalizationController.outputSize s+1) s
      CommonNormalizationController.step p halted.1=(halted.1,0) := by
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
  exact ⟨hram,hsim.1,hsim.2,hhalts.2.1⟩

end CodedSorting.CommonPolicyNormalized
end PolicyNormalized

section TaggedSchedule
/-! RAM-selected calls to public static programs on the common machine.
The existing counter stores `tag * stride + offset`.  The tag describes a
public subroutine, for example its input length and address; it is not a
stored payload.  Selection is made from RAM, and the policy receives no disk.
Every payload instruction already ignores the entire counter (`RespectsPC`),
so this compiler needs no new resident bank or preservation assumption.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonTaggedSchedule
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (RAM Machine)
noncomputable section

def instrument (q : Configuration) (stride tag offset : ℕ)
    (i : Instruction q) : Instruction q :=
  ⟨i.operation,fun ram => setPC q (tag*stride+(offset+1)) (i.resume ram)⟩

def policy (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) : SourcePolicy q := fun ram =>
  if h : pc q ram / stride < K then
    ((code ⟨pc q ram / stride,h⟩)[pc q ram % stride]?).map
      (instrument q stride (pc q ram / stride) (pc q ram % stride))
  else none

def execute (q : Configuration) (stride tag : ℕ) :
    ℕ → List (Instruction q) → Machine q → Machine q × ℕ
  | _,[],s => (s,0)
  | k,i::is,s =>
      let out := execute q stride tag (k+1) is
        (ControlledNormalization.logicalStep (instrument q stride tag k i) s)
      (out.1,Normalization.transferCost i.operation+out.2)

theorem decode (stride tag offset : ℕ) (hs : 0<stride) (ho : offset<stride) :
    (tag*stride+offset)/stride=tag ∧ (tag*stride+offset)%stride=offset := by
  constructor
  · simp [Nat.add_div,hs,Nat.div_eq_of_lt ho,Nat.mod_lt _ hs]
  · simp [Nat.add_mod,Nat.mod_eq_of_lt ho]

theorem at_counter (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (tag : Fin K) (offset : ℕ)
    (ram : RAM q) (hs : 0<stride) (ho : offset<stride)
    (hp : pc q ram=tag.val*stride+offset) :
    policy q stride code ram =
      ((code tag)[offset]?).map (instrument q stride tag.val offset) := by
  have hd := decode stride tag.val offset hs ho
  simp only [policy,hp,hd.1,hd.2,tag.isLt,↓reduceDIte]

theorem instrument_counter (q : Configuration) (stride tag offset : ℕ)
    (i : Instruction q) (s : Machine q)
    (h : tag*stride+(offset+1)≤q.N^q.exponent) :
    pc q (ControlledNormalization.logicalStep (instrument q stride tag offset i) s).ram=
      tag*stride+(offset+1) := pc_setPC q _ _ h

theorem instrument_erases (q : Configuration) (stride tag offset : ℕ)
    (i : Instruction q) (s : Machine q) :
    erasePC q (ControlledNormalization.logicalStep (instrument q stride tag offset i) s)=
      erasePC q (ControlledNormalization.logicalStep i s) := by
  change {ControlledNormalization.logicalStep i s with
    ram:=setPC q 0 (setPC q (tag*stride+(offset+1))
      (ControlledNormalization.logicalStep i s).ram)} = _
  simp only [setPC_setPC,erasePC]

@[simp] theorem execute_cost (q : Configuration) (stride tag offset : ℕ)
    (code : List (Instruction q)) (s : Machine q) :
    (execute q stride tag offset code s).2=cost q code := by
  induction code generalizing offset s with
  | nil => rfl
  | cons i is ih => simp only [execute,cost,ih]

theorem execute_counter (q : Configuration) (stride tag offset : ℕ)
    (code : List (Instruction q)) (s : Machine q)
    (hpc : pc q s.ram=tag*stride+offset)
    (hsize : tag*stride+(offset+code.length)≤q.N^q.exponent) :
    pc q (execute q stride tag offset code s).1.ram=tag*stride+(offset+code.length) := by
  induction code generalizing offset s with
  | nil => simpa only [execute,List.length_nil,Nat.add_zero] using hpc
  | cons i is ih =>
      have hk : tag*stride+(offset+1)≤q.N^q.exponent := by
        simp only [List.length_cons] at hsize
        omega
      have hs : tag*stride+(offset+1+is.length)≤q.N^q.exponent := by
        simp only [List.length_cons] at hsize
        omega
      have hh := ih (offset+1)
        (ControlledNormalization.logicalStep (instrument q stride tag offset i) s)
        (instrument_counter q stride tag offset i s hk) hs
      simpa only [execute,List.length_cons,Nat.add_assoc,Nat.add_comm 1 is.length] using hh

theorem execute_payload (q : Configuration) (stride tag offset : ℕ)
    (code : List (Instruction q)) (hsafe : ∀ i∈code,RespectsPC q i)
    (s t : Machine q) (hst : erasePC q s=erasePC q t) :
    erasePC q (execute q stride tag offset code s).1=
      erasePC q (executeRaw q code t).1 := by
  induction code generalizing offset s t with
  | nil => exact hst
  | cons i is ih =>
      have hi := hsafe i (List.mem_cons_self ..)
      have ht : ∀ j∈is,RespectsPC q j := fun j hj => hsafe j (List.mem_cons_of_mem _ hj)
      exact ih (offset+1) ht _ _
        ((instrument_erases q stride tag offset i s).trans (hi s t hst))

theorem run_from (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (tag : Fin K)
    (pref tail : List (Instruction q)) (hcode : code tag=pref++tail)
    (hstride : (code tag).length<stride)
    (hsize : tag.val*stride+(code tag).length≤q.N^q.exponent)
    (s : Machine q) (hpc : pc q s.ram=tag.val*stride+pref.length) :
    ControlledNormalization.runLogical (policy q stride code) tail.length s=
      execute q stride tag.val pref.length tail s := by
  induction tail generalizing pref s with
  | nil => rfl
  | cons i is ih =>
      have hget : (code tag)[pref.length]?=some i := by rw [hcode]; simp
      have hpref : pref.length<stride := by
        rw [hcode,List.length_append,List.length_cons] at hstride
        omega
      have hp := at_counter q stride code tag pref.length s.ram (by omega) hpref hpc
      rw [hget] at hp
      have hnext : pc q
          (ControlledNormalization.logicalStep (instrument q stride tag.val pref.length i) s).ram=
          tag.val*stride+(pref++[i]).length := by
        rw [List.length_append,List.length_singleton]
        apply instrument_counter
        rw [hcode,List.length_append,List.length_cons] at hsize
        omega
      have hsplit : code tag=(pref++[i])++is := by
        simpa only [List.append_assoc,List.singleton_append] using hcode
      rw [List.length_cons,ControlledNormalization.runLogical,hp]
      dsimp only [Option.map]
      rw [ih (pref++[i]) hsplit _ hnext]
      simp only [execute,List.length_append,List.length_singleton,instrument]

/-- A run-time selected subroutine has exactly its previously proved disk
effect and transfer count.  The descriptor remains encoded until a later
RAM-only dispatch changes it. -/
theorem complete (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (tag : Fin K)
    (hstride : (code tag).length<stride)
    (hsize : tag.val*stride+(code tag).length≤q.N^q.exponent)
    (hsafe : ∀ i∈code tag,RespectsPC q i)
    (s : Machine q) (hpc : pc q s.ram=tag.val*stride) :
    let out := ControlledNormalization.runLogical (policy q stride code) (code tag).length s
    out.1.disk=(executeRaw q (code tag) s).1.disk ∧
      policy q stride code out.1.ram=none ∧ out.2=cost q (code tag) ∧
      pc q out.1.ram=tag.val*stride+(code tag).length ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  have hr := run_from q stride code tag [] (code tag) (by simp) hstride hsize s
    (by simpa using hpc)
  simp only [List.length_nil] at hr
  have hp := execute_counter q stride tag.val 0 (code tag) s
    (by simpa using hpc) (by simpa using hsize)
  simp only [Nat.zero_add] at hp
  have he := congrArg (fun t : Machine q => t.disk)
    (execute_payload q stride tag.val 0 (code tag) hsafe s s rfl)
  dsimp only
  rw [hr]
  refine ⟨he,?_,execute_cost q stride tag.val 0 (code tag) s,hp,resident_memory q⟩
  rw [at_counter q stride code tag (code tag).length _ (by omega) hstride hp]
  simp only [List.getElem?_length,Option.map]

/-- Initial selection may depend on counts and addresses fetched into RAM.
This instruction has zero transfers and never reads or captures the disk. -/
def enter (q : Configuration) {K : ℕ} (stride : ℕ)
    (choose : RAM q → Fin K) : Instruction q :=
  ⟨.localOp (fun ram => setPC q ((choose ram).val*stride) ram),id⟩

theorem enter_complete (q : Configuration) {K : ℕ} (stride : ℕ)
    (choose : RAM q → Fin K) (s : Machine q)
    (hsize : K*stride≤q.N^q.exponent) :
    let out := ControlledNormalization.logicalStep (enter q stride choose) s
    out.disk=s.disk ∧ pc q out.ram=(choose s.ram).val*stride ∧
      erasePC q out=erasePC q s ∧
      Normalization.transferCost (enter q stride choose).operation=0 := by
  have ht : (choose s.ram).val*stride≤q.N^q.exponent :=
    (Nat.mul_le_mul_right stride (Nat.le_of_lt (choose s.ram).isLt)).trans hsize
  refine ⟨rfl,pc_setPC q _ _ ht,?_,rfl⟩
  change {s with ram:=setPC q 0 (setPC q ((choose s.ram).val*stride) s.ram)}=erasePC q s
  simp only [setPC_setPC,erasePC]

end
end CodedSorting.CommonTaggedSchedule
end TaggedSchedule

section TaggedController
/-! A fixed controller joins RAM-selected static calls.  At the end of a
nonterminal call it executes one RAM-only continuation.  Thus the next tag
can be computed from the counts actually produced by the preceding scan;
no host recursion, hidden payload, or uncharged disk access selects a call.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonTaggedController
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (RAM Machine)
noncomputable section

def policy (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (terminal : Fin K → Bool)
    (next : Fin K → RAM q → RAM q) : SourcePolicy q := fun ram =>
  if h : pc q ram / stride < K then
    let tag : Fin K := ⟨pc q ram / stride,h⟩
    match (code tag)[pc q ram % stride]? with
    | some i => some (CommonTaggedSchedule.instrument q stride tag.val (pc q ram % stride) i)
    | none => if terminal tag then none else some ⟨.localOp (next tag),id⟩
  else none

theorem at_counter (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (terminal : Fin K → Bool)
    (next : Fin K → RAM q → RAM q) (tag : Fin K) (offset : ℕ)
    (ram : RAM q) (hs : 0<stride) (ho : offset<stride)
    (hp : pc q ram=tag.val*stride+offset) :
    policy q stride code terminal next ram =
      match (code tag)[offset]? with
      | some i => some (CommonTaggedSchedule.instrument q stride tag.val offset i)
      | none => if terminal tag then none else some ⟨.localOp (next tag),id⟩ := by
  have hd := CommonTaggedSchedule.decode stride tag.val offset hs ho
  simp only [policy,hp,hd.1,hd.2,tag.isLt,↓reduceDIte]

theorem run_from (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (terminal : Fin K → Bool)
    (next : Fin K → RAM q → RAM q) (tag : Fin K)
    (pref tail : List (Instruction q)) (hcode : code tag=pref++tail)
    (hstride : (code tag).length<stride)
    (hsize : tag.val*stride+(code tag).length≤q.N^q.exponent)
    (s : Machine q) (hpc : pc q s.ram=tag.val*stride+pref.length) :
    ControlledNormalization.runLogical (policy q stride code terminal next) tail.length s=
      CommonTaggedSchedule.execute q stride tag.val pref.length tail s := by
  induction tail generalizing pref s with
  | nil => rfl
  | cons i is ih =>
      have hget : (code tag)[pref.length]?=some i := by rw [hcode]; simp
      have hpref : pref.length<stride := by
        rw [hcode,List.length_append,List.length_cons] at hstride
        omega
      have hp := at_counter q stride code terminal next tag pref.length s.ram
        (by omega) hpref hpc
      rw [hget] at hp
      have hnext : pc q
          (ControlledNormalization.logicalStep
            (CommonTaggedSchedule.instrument q stride tag.val pref.length i) s).ram=
          tag.val*stride+(pref++[i]).length := by
        rw [List.length_append,List.length_singleton]
        apply CommonTaggedSchedule.instrument_counter
        rw [hcode,List.length_append,List.length_cons] at hsize
        omega
      have hsplit : code tag=(pref++[i])++is := by
        simpa only [List.append_assoc,List.singleton_append] using hcode
      rw [List.length_cons,ControlledNormalization.runLogical,hp]
      dsimp only
      rw [ih (pref++[i]) hsplit _ hnext]
      simp only [CommonTaggedSchedule.execute,List.length_append,List.length_singleton,
        CommonTaggedSchedule.instrument]

/-- One complete body executes within the fixed multi-call controller.
Its final resident data, including measured bucket counts, remain available
to the next transition. -/
theorem segment (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (terminal : Fin K → Bool)
    (next : Fin K → RAM q → RAM q) (tag : Fin K)
    (hstride : (code tag).length<stride)
    (hsize : tag.val*stride+(code tag).length≤q.N^q.exponent)
    (s : Machine q) (hpc : pc q s.ram=tag.val*stride) :
    ControlledNormalization.runLogical (policy q stride code terminal next) (code tag).length s=
      CommonTaggedSchedule.execute q stride tag.val 0 (code tag) s := by
  simpa only [List.length_nil] using run_from q stride code terminal next tag [] (code tag)
    (by simp) hstride hsize s (by simpa using hpc)

theorem boundary (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (terminal : Fin K → Bool)
    (next : Fin K → RAM q → RAM q) (tag : Fin K)
    (hstride : (code tag).length<stride) (ht : terminal tag=false)
    (s : Machine q) (hpc : pc q s.ram=tag.val*stride+(code tag).length) :
    ControlledNormalization.runLogical (policy q stride code terminal next) 1 s=
      ({s with ram:=next tag s.ram},0) := by
  have hp := at_counter q stride code terminal next tag (code tag).length s.ram
    (by omega) hstride hpc
  simp only [List.getElem?_length,ht,Bool.false_eq_true,↓reduceIte] at hp
  simp only [ControlledNormalization.runLogical,hp,ControlledNormalization.logicalStep,
    Normalization.logicalStep,Normalization.transferCost,Nat.zero_add]
  rfl

theorem halted (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (terminal : Fin K → Bool)
    (next : Fin K → RAM q → RAM q) (tag : Fin K)
    (hstride : (code tag).length<stride) (ht : terminal tag=true)
    (s : Machine q) (hpc : pc q s.ram=tag.val*stride+(code tag).length) :
    policy q stride code terminal next s.ram=none := by
  rw [at_counter q stride code terminal next tag (code tag).length s.ram
    (by omega) hstride hpc]
  simp only [List.getElem?_length,ht,↓reduceIte]

/-- The body and its return are one chronological policy run.  The return
contributes no I/O and receives exactly the RAM produced by the body. -/
theorem call (q : Configuration) {K : ℕ} (stride : ℕ)
    (code : Fin K → List (Instruction q)) (terminal : Fin K → Bool)
    (next : Fin K → RAM q → RAM q) (tag : Fin K)
    (hstride : (code tag).length<stride)
    (hsize : tag.val*stride+(code tag).length≤q.N^q.exponent)
    (ht : terminal tag=false) (s : Machine q) (hpc : pc q s.ram=tag.val*stride) :
    let body := CommonTaggedSchedule.execute q stride tag.val 0 (code tag) s
    ControlledNormalization.runLogical (policy q stride code terminal next)
      ((code tag).length+1) s=
      ({body.1 with ram:=next tag body.1.ram},cost q (code tag)) := by
  have hp := CommonTaggedSchedule.execute_counter q stride tag.val 0 (code tag) s
    (by simpa using hpc) (by simpa using hsize)
  simp only [Nat.zero_add] at hp
  rw [CommonPolicyComposition.run_add,
    segment q stride code terminal next tag hstride hsize s hpc,
    boundary q stride code terminal next tag hstride ht _ hp]
  simp only [Nat.add_zero,CommonTaggedSchedule.execute_cost]

end
end CodedSorting.CommonTaggedController
end TaggedController
