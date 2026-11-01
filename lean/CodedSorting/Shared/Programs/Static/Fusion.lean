import CodedSorting.Shared.Memory.Leaf.Program

section Schedule
/-! A data-oblivious instruction schedule on the existing common machine.

The schedule is program text, not resident data. Its sole mutable program
counter uses the existing `top` words. The instruction at a given index may
read or transform payload RAM, but its address and operation are supplied by
the public schedule. Every instruction's continuation advances the encoded
counter, including instructions whose payload happens not to change.

`run_code` concerns the actual fixed RAM-controlled policy and the exact
same chronological instruction execution, finite disk and I/O charge. It
is a compiler theorem, not a proof that a sorting or exchange schedule has
already been generated. Such an instance must be generated independently
of input values and must establish its polynomial length and workspace.
-/
set_option autoImplicit false
namespace CodedSorting.CommonStaticSchedule
open WordControl CommonSortingNormalization
open CommonLeafProgram (Store RAM Disk Machine machine)
noncomputable section

abbrev Instruction (q : Configuration) :=
  ControlledNormalization.Instruction q.ramWords q.block (q.N^q.exponent) (Word q.w)

def pc (q : Configuration) (ram : RAM q) : ℕ := decodeWords (unpack ram).top

def setPC (q : Configuration) (k : ℕ) (ram : RAM q) : RAM q :=
  pack {unpack ram with top:=PhysicalStreamCursor.encodeNat q.digits q.w k}

theorem pc_capacity (q : Configuration) :
    q.N^q.exponent < (2^q.w)^q.digits := by
  have h := WordConvention.polynomial_capacity q.N q.w q.c q.exponent
    q.input_large q.word_convention
  change q.N^q.exponent+1 ≤ (2^q.w)^q.digits at h
  omega

@[simp] theorem pc_setPC (q : Configuration) (k : ℕ) (ram : RAM q)
    (hk : k≤q.N^q.exponent) : pc q (setPC q k ram)=k := by
  simp only [pc,setPC,unpack_pack]
  exact PhysicalStreamCursor.decodeNat_encode _ _ _ (hk.trans_lt (pc_capacity q))

/-- Only the existing counter words change. In particular all payload,
stream buffers and the three local frame banks remain resident in place. -/
theorem setPC_frame (q : Configuration) (k : ℕ) (ram : RAM q) :
    (unpack (setPC q k ram)).leaf=(unpack ram).leaf ∧
    (unpack (setPC q k ram)).readers=(unpack ram).readers ∧
    (unpack (setPC q k ram)).writers=(unpack ram).writers ∧
    (unpack (setPC q k ram)).transfer=(unpack ram).transfer ∧
    (unpack (setPC q k ram)).scalars=(unpack ram).scalars ∧
    (unpack (setPC q k ram)).directories=(unpack ram).directories ∧
    (unpack (setPC q k ram)).shapes=(unpack ram).shapes ∧
    (unpack (setPC q k ram)).pcs=(unpack ram).pcs := by
  simp only [setPC,unpack_pack]
  trivial

/-- The fixed schedule index is control information, never saved payload. -/
def instrument (q : Configuration) (k : ℕ) (i : Instruction q) : Instruction q :=
  ⟨i.operation,fun ram => setPC q (k+1) (i.resume ram)⟩

@[simp] theorem instrument_cost (q : Configuration) (k : ℕ) (i : Instruction q) :
    Normalization.transferCost (instrument q k i).operation=
      Normalization.transferCost i.operation := rfl

theorem instrument_pc (q : Configuration) (k : ℕ) (i : Instruction q)
    (s : Machine q) (hk : k+1≤q.N^q.exponent) :
    pc q (ControlledNormalization.logicalStep (instrument q k i) s).ram=k+1 := by
  exact pc_setPC q (k+1) _ hk

def policy (q : Configuration) (code : List (Instruction q)) : SourcePolicy q :=
  fun ram => (code[pc q ram]?).map (instrument q (pc q ram))

/-- Direct chronological semantics of the indexed program text. Both this
semantics and `policy` execute the same actual disk instructions. -/
def execute (q : Configuration) : ℕ → List (Instruction q) → Machine q → Machine q × ℕ
  | _,[],s => (s,0)
  | k,i::is,s =>
      let out := execute q (k+1) is
        (ControlledNormalization.logicalStep (instrument q k i) s)
      (out.1,Normalization.transferCost i.operation+out.2)

def cost (q : Configuration) : List (Instruction q) → ℕ
  | [] => 0
  | i::is => Normalization.transferCost i.operation+cost q is

@[simp] theorem execute_cost (q : Configuration) (code : List (Instruction q))
    (k : ℕ) (s : Machine q) : (execute q k code s).2=cost q code := by
  induction code generalizing k s with
  | nil => rfl
  | cons i is ih => simp only [execute,cost,ih]

/-- The suffix theorem is useful for concatenating generated fragments.
Its counter is read from RAM, not supplied as hidden run-time state. -/
theorem run_from (q : Configuration) (code pref tail : List (Instruction q))
    (hcode : code=pref++tail) (hsize : code.length≤q.N^q.exponent)
    (s : Machine q) (hpc : pc q s.ram=pref.length) :
    ControlledNormalization.runLogical (policy q code) tail.length s=
      execute q pref.length tail s := by
  induction tail generalizing pref s with
  | nil => rfl
  | cons i is ih =>
      have hget : code[pref.length]?=some i := by rw [hcode]; simp
      have hpol : policy q code s.ram=some (instrument q pref.length i) := by
        simp only [policy,hpc,hget,Option.map]
      have hlen : pref.length+1≤q.N^q.exponent := by
        rw [hcode,List.length_append,List.length_cons] at hsize
        omega
      have hnext : pc q
          (ControlledNormalization.logicalStep (instrument q pref.length i) s).ram=
          (pref++[i]).length := by
        rw [instrument_pc q _ _ _ hlen,List.length_append,List.length_singleton]
      have hsplit : code=(pref++[i])++is := by
        simpa only [List.append_assoc,List.singleton_append] using hcode
      rw [List.length_cons,ControlledNormalization.runLogical,hpol]
      dsimp only
      rw [ih (pref++[i]) hsplit _ hnext]
      simp only [execute,List.length_append,List.length_singleton,instrument_cost]

theorem execute_pc (q : Configuration) (code : List (Instruction q))
    (k : ℕ) (s : Machine q) (hpc : pc q s.ram=k)
    (hsize : k+code.length≤q.N^q.exponent) :
    pc q (execute q k code s).1.ram=k+code.length := by
  induction code generalizing k s with
  | nil => simpa only [execute,List.length_nil,Nat.add_zero] using hpc
  | cons i is ih =>
      have hk : k+1≤q.N^q.exponent := by
        simp only [List.length_cons] at hsize
        omega
      have hs : k+1+is.length≤q.N^q.exponent := by
        simp only [List.length_cons] at hsize
        omega
      have h := ih (k+1) (ControlledNormalization.logicalStep (instrument q k i) s)
        (instrument_pc q k i s hk) hs
      simpa only [execute,List.length_cons,Nat.add_assoc,Nat.add_comm 1 is.length] using h

/-- Complete fixed-policy execution, actual halt and same-run I/O. All
instructions share one finite disk and the already budgeted source RAM. -/
theorem run_code (q : Configuration) (code : List (Instruction q))
    (hsize : code.length≤q.N^q.exponent) (s : Machine q) (hpc : pc q s.ram=0) :
    ControlledNormalization.runLogical (policy q code) code.length s=
      execute q 0 code s ∧
    policy q code (execute q 0 code s).1.ram=none ∧
    (ControlledNormalization.runLogical (policy q code) code.length s).2=cost q code ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have hr := run_from q code [] code (by simp) hsize s hpc
  have hp := execute_pc q code 0 s hpc (by simpa using hsize)
  simp only [List.length_nil] at hr
  simp only [Nat.zero_add] at hp
  refine ⟨hr,?_,?_,resident_memory q⟩
  · simp only [policy,hp,List.getElem?_length,Option.map]
  · rw [hr,execute_cost]

/-- The direct payload semantics does not include compiler bookkeeping. -/
def executeRaw (q : Configuration) : List (Instruction q) → Machine q → Machine q × ℕ
  | [],s => (s,0)
  | i::is,s =>
      let out := executeRaw q is (ControlledNormalization.logicalStep i s)
      (out.1,Normalization.transferCost i.operation+out.2)

@[simp] theorem setPC_setPC (q : Configuration) (a b : ℕ) (ram : RAM q) :
    setPC q a (setPC q b ram)=setPC q a ram := by
  simp only [setPC,unpack_pack]

/-- Proof-side observation which forgets only the reserved counter. -/
def erasePC (q : Configuration) (s : Machine q) : Machine q :=
  {s with ram:=setPC q 0 s.ram}

/-- Payload templates must not branch on, or export, the compiler's
reserved counter. This is a local instruction property, not a successful
execution, sorting or resource-bound assumption. -/
def RespectsPC (q : Configuration) (i : Instruction q) : Prop :=
  ∀ s t : Machine q,erasePC q s=erasePC q t →
    erasePC q (ControlledNormalization.logicalStep i s)=
      erasePC q (ControlledNormalization.logicalStep i t)

theorem instrument_step (q : Configuration) (k : ℕ) (i : Instruction q)
    (s : Machine q) :
    ControlledNormalization.logicalStep (instrument q k i) s=
      {ControlledNormalization.logicalStep i s with
        ram:=setPC q (k+1) (ControlledNormalization.logicalStep i s).ram} := rfl

@[simp] theorem erasePC_instrument (q : Configuration) (k : ℕ)
    (i : Instruction q) (s : Machine q) :
    erasePC q (ControlledNormalization.logicalStep (instrument q k i) s)=
      erasePC q (ControlledNormalization.logicalStep i s) := by
  rw [instrument_step]
  simp only [erasePC,setPC_setPC]

theorem execute_payload (q : Configuration) (code : List (Instruction q))
    (hsafe : ∀ i∈code,RespectsPC q i) (k : ℕ) (s t : Machine q)
    (hst : erasePC q s=erasePC q t) :
    erasePC q (execute q k code s).1=erasePC q (executeRaw q code t).1 := by
  induction code generalizing k s t with
  | nil => exact hst
  | cons i is ih =>
      have hs : RespectsPC q i := hsafe i (List.mem_cons_self ..)
      have ht : ∀ j∈is,RespectsPC q j := fun j hj => hsafe j (List.mem_cons_of_mem _ hj)
      have he : erasePC q (ControlledNormalization.logicalStep (instrument q k i) s)=
          erasePC q (ControlledNormalization.logicalStep i t) :=
        (erasePC_instrument q k i s).trans (hs s t hst)
      exact ih ht (k+1) _ _ he

/-- The compiled policy produces the same actual disk as the raw payload
program. Bookkeeping contributes no extra transfers and no extra RAM. -/
theorem run_code_disk (q : Configuration) (code : List (Instruction q))
    (hsize : code.length≤q.N^q.exponent)
    (hsafe : ∀ i∈code,RespectsPC q i) (s : Machine q) (hpc : pc q s.ram=0) :
    (ControlledNormalization.runLogical (policy q code) code.length s).1.disk=
      (executeRaw q code s).1.disk ∧
    policy q code (ControlledNormalization.runLogical (policy q code) code.length s).1.ram=none ∧
    (ControlledNormalization.runLogical (policy q code) code.length s).2=cost q code ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hr,hh,hc,hm⟩ := run_code q code hsize s hpc
  refine ⟨?_,by rw [hr]; exact hh,hc,hm⟩
  rw [hr]
  have hd := congrArg (fun t : Machine q => t.disk) (execute_payload q code hsafe 0 s s rfl)
  exact hd

end
end CodedSorting.CommonStaticSchedule
end Schedule

section Fusion
/-! Compile away runs of free local computation before installing the
program counter. Every noninitial local instruction is absorbed into the
continuation of the preceding instruction. The transformation preserves
the entire raw machine state and its I/O count; the resulting static
program has at most one instruction more than its number of transfers. -/

set_option autoImplicit false
namespace CodedSorting.CommonStaticFusion
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (RAM Machine)
noncomputable section

/-- Append a RAM-only instruction to an instruction's RAM continuation. -/
def mergeLocal (q : Configuration) (i : Instruction q)
    (f r : RAM q → RAM q) : Instruction q :=
  ⟨i.operation, fun ram => r (f (i.resume ram))⟩

theorem mergeLocal_step (q : Configuration) (i : Instruction q)
    (f r : RAM q → RAM q) (s : Machine q) :
    ControlledNormalization.logicalStep (mergeLocal q i f r) s =
      ControlledNormalization.logicalStep (⟨.localOp f,r⟩ : Instruction q)
        (ControlledNormalization.logicalStep i s) := by
  rfl

theorem mergeLocal_safe (q : Configuration) (i : Instruction q)
    (f r : RAM q → RAM q) (hi : RespectsPC q i)
    (hj : RespectsPC q (⟨.localOp f,r⟩ : Instruction q)) :
    RespectsPC q (mergeLocal q i f r) := by
  intro s t h
  rw [mergeLocal_step,mergeLocal_step]
  exact hj _ _ (hi s t h)

/-- Prepend one instruction, absorbing an initial local instruction. -/
def attach (q : Configuration) (i : Instruction q) :
    List (Instruction q) → List (Instruction q)
  | [] => [i]
  | j::js => match j.operation with
    | .localOp f => mergeLocal q i f j.resume :: js
    | .read _ _ => i::j::js
    | .write _ _ => i::j::js

def fuse (q : Configuration) : List (Instruction q) → List (Instruction q)
  | [] => []
  | i::is => attach q i (fuse q is)

theorem attach_executeRaw (q : Configuration) (i : Instruction q)
    (code : List (Instruction q)) (s : Machine q) :
    executeRaw q (attach q i code) s = executeRaw q (i::code) s := by
  cases code with
  | nil => rfl
  | cons j js =>
    cases j with
    | mk op r =>
      cases op with
      | localOp f =>
        simp only [attach,executeRaw,mergeLocal_step,mergeLocal,
          Normalization.transferCost,Nat.zero_add]
        rfl
      | read a w => rfl
      | write a w => rfl

theorem executeRaw_fuse (q : Configuration) (code : List (Instruction q))
    (s : Machine q) : executeRaw q (fuse q code) s=executeRaw q code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i is ih =>
    rw [fuse,attach_executeRaw]
    simp only [executeRaw,ih]

theorem attach_cost (q : Configuration) (i : Instruction q)
    (code : List (Instruction q)) :
    cost q (attach q i code)=Normalization.transferCost i.operation+cost q code := by
  cases code with
  | nil => rfl
  | cons j js =>
    cases j with
    | mk op r =>
      cases op <;> simp [attach,cost,mergeLocal,Normalization.transferCost]

@[simp] theorem cost_fuse (q : Configuration) (code : List (Instruction q)) :
    cost q (fuse q code)=cost q code := by
  induction code with
  | nil => rfl
  | cons i is ih => simp only [fuse,attach_cost,cost,ih]

theorem attach_safe (q : Configuration) (i : Instruction q)
    (code : List (Instruction q)) (hi : RespectsPC q i)
    (hc : ∀ j∈code,RespectsPC q j) :
    ∀ j∈attach q i code,RespectsPC q j := by
  cases code with
  | nil => simpa only [attach,List.mem_singleton] using
      (fun j (h : j=i) => h ▸ hi)
  | cons j js =>
    have hj := hc j (by simp)
    have hjs : ∀ k∈js,RespectsPC q k := fun k hk => hc k (by simp [hk])
    cases j with
    | mk op r =>
      cases op with
      | localOp f =>
        intro k hk
        simp only [attach,List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact mergeLocal_safe q i f r hi hj
        · exact hjs k hk
      | read a w =>
        intro k hk
        simp only [attach,List.mem_cons] at hk
        rcases hk with rfl | rfl | hk
        · exact hi
        · exact hj
        · exact hjs k hk
      | write a w =>
        intro k hk
        simp only [attach,List.mem_cons] at hk
        rcases hk with rfl | rfl | hk
        · exact hi
        · exact hj
        · exact hjs k hk

theorem fuse_safe (q : Configuration) (code : List (Instruction q))
    (hc : ∀ i∈code,RespectsPC q i) :
    ∀ i∈fuse q code,RespectsPC q i := by
  induction code with
  | nil => simp only [fuse,List.not_mem_nil,false_implies,implies_true]
  | cons i is ih =>
    exact attach_safe q i (fuse q is) (hc i (by simp))
      (ih (fun j hj => hc j (by simp [hj])))

/-- Every instruction after the first is an actual read or write. -/
theorem fuse_tail_transfer (q : Configuration) (code : List (Instruction q)) :
    ∀ i ∈ (fuse q code).tail, Normalization.transferCost i.operation=1 := by
  induction code with
  | nil => simp only [fuse,List.tail_nil,List.not_mem_nil,false_implies,implies_true]
  | cons i is ih =>
    cases hf : fuse q is with
    | nil => simp only [fuse,hf,attach,List.tail_cons,List.not_mem_nil,
        false_implies,implies_true]
    | cons j js =>
      rw [hf,List.tail_cons] at ih
      cases j with
      | mk op r =>
        cases op with
        | localOp f => simpa only [fuse,hf,attach,List.tail_cons] using ih
        | read a w =>
          intro k hk
          simp only [fuse,hf,attach,List.tail_cons,List.mem_cons] at hk
          rcases hk with rfl | hk
          · rfl
          · exact ih k hk
        | write a w =>
          intro k hk
          simp only [fuse,hf,attach,List.tail_cons,List.mem_cons] at hk
          rcases hk with rfl | hk
          · rfl
          · exact ih k hk

theorem length_eq_cost_of_transfers (q : Configuration)
    (code : List (Instruction q))
    (h : ∀ i∈code,Normalization.transferCost i.operation=1) :
    code.length=cost q code := by
  induction code with
  | nil => rfl
  | cons i is ih =>
    have hi := h i (by simp)
    have ht := ih (fun j hj => h j (by simp [hj]))
    simp only [List.length_cons,cost,hi,←ht,Nat.add_comm 1]

theorem length_fuse (q : Configuration) (code : List (Instruction q)) :
    (fuse q code).length≤cost q code+1 := by
  have h := fuse_tail_transfer q code
  rw [←cost_fuse q code]
  cases hf : fuse q code with
  | nil => simp [cost]
  | cons i is =>
    rw [hf,List.tail_cons] at h
    have ht := length_eq_cost_of_transfers q is h
    simp only [List.length_cons,cost]
    omega

/-- Counter capacity is required only for transfers and at most one
initial RAM operation, independently of the original number of free
local instructions. Output, halt, I/O and RAM refer to the same run. -/
theorem run_fused (q : Configuration) (code : List (Instruction q))
    (hsize : cost q code+1≤q.N^q.exponent)
    (hsafe : ∀ i∈code,RespectsPC q i) (s : Machine q)
    (hpc : pc q s.ram=0) :
    (ControlledNormalization.runLogical (policy q (fuse q code))
      (fuse q code).length s).1.disk=(executeRaw q code s).1.disk ∧
    policy q (fuse q code)
      (ControlledNormalization.runLogical (policy q (fuse q code))
        (fuse q code).length s).1.ram=none ∧
    (ControlledNormalization.runLogical (policy q (fuse q code))
      (fuse q code).length s).2=cost q code ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have h := run_code_disk q (fuse q code) ((length_fuse q code).trans hsize)
    (fuse_safe q code hsafe) s hpc
  simpa only [executeRaw_fuse,cost_fuse] using h

end
end CodedSorting.CommonStaticFusion
end Fusion
