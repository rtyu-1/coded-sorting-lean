import CodedSorting.Shared.Memory.PhysicalFileHandles
import CodedSorting.Shared.Programs.FullShapeContinuation

section PhysicalLevelContinuation
/-! A fixed, closure-free single-level instruction sequence.  Its only
nonlocal instruction is the explicit child call inherited from edge code.
It preserves the complete executeLevel file chain and exact charges.
The external directory interpretation still has to be refined to allocated
disk regions; this result does not count whole files as resident values.
-/
set_option maxRecDepth 1000
set_option maxHeartbeats 200000
namespace CodedSorting.PhysicalLevelContinuation
open PhysicalRecursiveExchange RecursiveExchange RecursiveExchangeCost
open PhysicalWholeLevel PhysicalRolePartition Circuit CircuitProgram
noncomputable section

abbrev State := PhysicalNetworkContinuation.State

inductive Instruction where
  | before
  | scatter
  | network (op : PhysicalNetworkContinuation.Instruction)
  | gather
  | after

@[irreducible] def codeAt (n : ℕ) : List Instruction := [.before,.scatter] ++
  (PhysicalNetworkContinuation.networkCode n).map .network ++ [.gather,.after]

@[irreducible] def code : List Instruction := codeAt ((globalProgram Parameters.d).length+1)

/-- Abstracting the stage count prevents elaboration from evaluating the
fixed, very large circuit table while checking the compiler proof. -/
def executeLevelAt {σ : Type} (n f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (source : File) (state : σ) : Option (Output σ) := do
  let before ← executeProgram B hB (OuterExchangeProgram.beforeProgram f (R*Parameters.W) G S) source
  let scattered ← scatterRoles R Parameters.W (segmentVolume f G S) B before.1
  let network ← PhysicalNetwork.execute (f := f) (P := R) (G := G) (S := S) (hG := hG) (hS := hS)
    B hB child (inputFiles scattered.1) n state
  let gathered ← gatherRoles R Parameters.W (segmentVolume f G S) B (sinkFiles network.files)
  let after ← executeProgram B hB (OuterExchangeProgram.afterProgram f (R*Parameters.W) G S hS) gathered.1
  return ⟨after.1,network.state,before.2+scattered.2+network.localCost+gathered.2+after.2,network.recursiveCost⟩

def step {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) : Instruction → State σ → Option (State σ)
  | .before,s => (executeProgram B hB
      (OuterExchangeProgram.beforeProgram f (R*Parameters.W) G S) s.active.file).map fun out =>
        {s with active := {s.active with file := out.1,localCost := s.active.localCost+out.2}}
  | .scatter,s => (scatterRoles R Parameters.W (segmentVolume f G S) B s.active.file).map fun out =>
      {s with inputs := inputFiles out.1,wires := (fun _ => []),active := {s.active with localCost := s.active.localCost+out.2}}
  | .network op,s => PhysicalNetworkContinuation.step f R G S B hG hS hB child op s
  | .gather,s => (gatherRoles R Parameters.W (segmentVolume f G S) B (sinkFiles s.wires)).map fun out =>
      {s with active := {s.active with file := out.1,localCost := s.active.localCost+out.2}}
  | .after,s => (executeProgram B hB
      (OuterExchangeProgram.afterProgram f (R*Parameters.W) G S hS) s.active.file).map fun out =>
        {s with active := {s.active with file := out.1,localCost := s.active.localCost+out.2}}

def run {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) : List Instruction → State σ → Option (State σ)
  | [],s => some s
  | op::ops,s => (step f R G S B hG hS hB child op s).bind
      (run f R G S B hG hS hB child ops)

theorem run_append {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (a b : List Instruction) (s : State σ) :
    run f R G S B hG hS hB child (a++b) s =
      (run f R G S B hG hS hB child a s).bind
        (run f R G S B hG hS hB child b) := by
  induction a generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [List.cons_append,run,ih,Option.bind_assoc]

theorem run_network {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (ops : List PhysicalNetworkContinuation.Instruction) (s : State σ) :
    run f R G S B hG hS hB child (ops.map .network) s =
      PhysicalNetworkContinuation.run f R G S B hG hS hB child ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [List.map_cons,run,step,PhysicalNetworkContinuation.run,ih]

theorem level_components {σ : Type} (n f R G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (s : State σ) (before : File × ℕ) (scattered : List File × ℕ)
    (network : LayerOutput σ) (gathered after : File × ℕ)
    (hb : executeProgram B hB (OuterExchangeProgram.beforeProgram f (R*Parameters.W) G S) s.active.file=some before)
    (hs : scatterRoles R Parameters.W (segmentVolume f G S) B before.1=some scattered)
    (hn : PhysicalNetwork.execute (f := f) (P := R) (G := G) (S := S) (hG := hG) (hS := hS)
      B hB child (inputFiles scattered.1) n s.active.user=some network)
    (hg : gatherRoles R Parameters.W (segmentVolume f G S) B (sinkFiles network.files)=some gathered)
    (ha : executeProgram B hB (OuterExchangeProgram.afterProgram f (R*Parameters.W) G S hS) gathered.1=some after) :
    ∃ result,run f R G S B hG hS hB child (codeAt n) s=some result ∧
      result.active.file=after.1 ∧ result.active.user=network.state ∧
      result.active.localCost=s.active.localCost+(before.2+scattered.2+network.localCost+gathered.2+after.2) ∧
      result.active.recursiveCost=s.active.recursiveCost+network.recursiveCost := by
  let start : State σ := {s with inputs := inputFiles scattered.1,wires := (fun _ => []),active := {s.active with file := before.1,localCost := s.active.localCost+before.2+scattered.2}}
  obtain ⟨rows,file,ret,hr⟩ := PhysicalNetworkContinuation.network_execution f R G S B hG hS hB
    child n start network rfl hn
  let finish : State σ :=
    {PhysicalNetworkContinuation.layerResult start network rows file ret with
      active := ⟨after.1,ret,network.state,
        s.active.localCost+before.2+scattered.2+network.localCost+gathered.2+after.2,
        s.active.recursiveCost+network.recursiveCost⟩}
  have hstart : run f R G S B hG hS hB child [.before,.scatter] s=some start := by
    simp [run,step,hb,hs,start]
  let gatheredState : State σ :=
    {PhysicalNetworkContinuation.layerResult start network rows file ret with
      active := ⟨gathered.1,ret,network.state,
        s.active.localCost+before.2+scattered.2+network.localCost+gathered.2,
        s.active.recursiveCost+network.recursiveCost⟩}
  have hgstep : step f R G S B hG hS hB child .gather
      (PhysicalNetworkContinuation.layerResult start network rows file ret)=some gatheredState := by
    simp only [step,PhysicalNetworkContinuation.layerResult]
    rw [hg]
    rfl
  have hastep : step f R G S B hG hS hB child .after gatheredState=some finish := by
    simp only [step,gatheredState]
    rw [ha]
    rfl
  refine ⟨finish,?_,rfl,rfl,?_,rfl⟩
  · rw [codeAt]
    rw [run_append,run_append]
    rw [hstart,Option.some_bind,run_network]
    change (PhysicalNetworkContinuation.run f R G S B hG hS hB child
      (PhysicalNetworkContinuation.networkCode n) start).bind _ = _
    rw [hr]
    rw [Option.some_bind,run,hgstep,Option.some_bind,run,hastep,Option.some_bind,run]
  · change s.active.localCost+before.2+scattered.2+network.localCost+gathered.2+after.2 =
      s.active.localCost+(before.2+scattered.2+network.localCost+gathered.2+after.2)
    simp only [Nat.add_assoc]



theorem level_executionAt {σ : Type} (n f R G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (s : State σ) (out : Output σ)
    (h : executeLevelAt n f R G S B hG hS hB child s.active.file s.active.user=some out) :
    ∃ result,run f R G S B hG hS hB child (codeAt n) s=some result ∧
      result.active.file=out.output ∧ result.active.user=out.state ∧
      result.active.localCost=s.active.localCost+out.localCost ∧
      result.active.recursiveCost=s.active.recursiveCost+out.recursiveCost := by
  simp only [executeLevelAt,Option.bind_eq_bind,Option.bind_eq_some,Option.some.injEq] at h
  rcases h with ⟨before,hb,scattered,hs,network,hn,gathered,hg,after,ha,hresult⟩
  cases hresult
  exact level_components n f R G S B hG hS hB child s before scattered network gathered after hb hs hn hg ha

/-- The actual fixed full-level code has exactly the executeLevel output
and charges. The large static circuit table is never evaluated to prove it. -/
theorem level_execution {σ : Type} (f R G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (s : State σ) (out : Output σ)
    (h : executeLevel f R G S B hG hS hB child s.active.file s.active.user=some out) :
    ∃ result,run f R G S B hG hS hB child code s=some result ∧
      result.active.file=out.output ∧ result.active.user=out.state ∧
      result.active.localCost=s.active.localCost+out.localCost ∧
      result.active.recursiveCost=s.active.recursiveCost+out.recursiveCost := by
  unfold code
  exact level_executionAt ((globalProgram Parameters.d).length+1) f R G S B hG hS hB child s out h

end
end CodedSorting.PhysicalLevelContinuation
end PhysicalLevelContinuation

section PhysicalLevelProgramCounter
/-! The complete one-level exchange driven by one bounded program counter.
Recursive calls are observable suspension points; all other instructions
run without access to a recursive callback.  This is the concrete control
schedule to be coupled with an allocated-file/physical-stack refinement.
-/
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace CodedSorting.PhysicalLevelProgramCounter
open PhysicalRecursiveExchange RecursiveExchange PhysicalLevelContinuation
noncomputable section

def callOf : Instruction → Option Child
  | .network (.edge (.call c)) => some c
  | _ => none

def resume {σ : Type} (s : State σ) (result : ChildOutput σ) : State σ :=
  {s with active := PhysicalEdgeContinuation.returned s.active result}

inductive Event (σ : Type) where
  | halt
  | local (next : State σ)
  | call (child : Child)

/-- The local instruction dispatcher is given the constantly failing
callback; it cannot execute a child, retain a child closure, or fabricate
a child result. A call is instead returned to the outer driver. -/
def dispatch {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (program : List Instruction) (pc : ℕ) (s : State σ) : Option (Event σ) :=
  match program[pc]? with
  | none => some .halt
  | some op => match callOf op with
      | some c => some (.call c)
      | none => (step f R G S B hG hS hB (fun _ _ _ => none) op s).map Event.local

def advance {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (program : List Instruction) (pc : ℕ) (s : State σ) :
    Option (ℕ × State σ) := do
  let event ← dispatch f R G S B hG hS hB program pc s
  match event with
  | .halt => some (pc,s)
  | .local next => some (pc+1,next)
  | .call c => (child c s.active.file s.active.user).map fun result => (pc+1,resume s result)

def execute {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (program : List Instruction) : ℕ → ℕ → State σ → Option (ℕ × State σ)
  | 0,pc,s => some (pc,s)
  | n+1,pc,s => (advance f R G S B hG hS hB child program pc s).bind fun next =>
      execute f R G S B hG hS hB child program n next.1 next.2

theorem step_local {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child other : FileChild σ) (op : Instruction) (s : State σ) (h : callOf op=none) :
    step f R G S B hG hS hB child op s=step f R G S B hG hS hB other op s := by
  cases op with
  | before => rfl
  | scatter => rfl
  | gather => rfl
  | after => rfl
  | network op =>
    cases op with
    | gate e => rfl
    | store r => rfl
    | beginLayer => rfl
    | commit t => rfl
    | edge op => cases op <;> first | rfl | simp [callOf] at h

theorem step_call {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (op : Instruction) (s : State σ) (c : Child) (h : callOf op=some c) :
    step f R G S B hG hS hB child op s=
      (child c s.active.file s.active.user).map (resume s) := by
  cases op with
  | before => simp [callOf] at h
  | scatter => simp [callOf] at h
  | gather => simp [callOf] at h
  | after => simp [callOf] at h
  | network op =>
    cases op with
    | gate e => simp [callOf] at h
    | store r => simp [callOf] at h
    | beginLayer => simp [callOf] at h
    | commit t => simp [callOf] at h
    | edge op =>
      cases op <;> try {simp [callOf] at h}
      next called =>
        simp only [callOf,Option.some.injEq] at h
        subst c
        simp only [step,PhysicalNetworkContinuation.step,PhysicalEdgeContinuation.step,
          Option.map_map,resume,Function.comp_def]
        rfl

theorem advance_at {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (program : List Instruction) (pc : ℕ) (s : State σ)
    (op : Instruction) (h : program[pc]?=some op) :
    advance f R G S B hG hS hB child program pc s =
      (step f R G S B hG hS hB child op s).map fun next => (pc+1,next) := by
  cases hc : callOf op with
  | none =>
      rw [step_local f R G S B hG hS hB child (fun _ _ _ => none) op s hc]
      simp [advance,dispatch,h,hc,Option.bind_map,Function.comp_def]
      exact Option.map_eq_bind.symm
  | some c =>
      rw [step_call f R G S B hG hS hB child op s c hc]
      simp [advance,dispatch,h,hc,Option.bind_map,Function.comp_def]

theorem execute_suffix {σ : Type} (f R G S B : ℕ) (hG : 0 < G) (hS : 0 < S) (hB : 0 < B)
    (child : FileChild σ) (pref suffix : List Instruction) (s : State σ) :
    execute f R G S B hG hS hB child (pref++suffix) suffix.length pref.length s =
      (run f R G S B hG hS hB child suffix s).map fun out => ((pref++suffix).length,out) := by
  induction suffix generalizing pref s with
  | nil => simp [execute,run]
  | cons op ops ih =>
      have lookup : (pref++op::ops)[pref.length]?=some op := by simp
      rw [List.length_cons,execute,advance_at f R G S B hG hS hB child _ _ _ _ lookup]
      cases hs : step f R G S B hG hS hB child op s with
      | none => simp [run,hs]
      | some next =>
        simp only [Option.map_some,Option.some_bind,run,hs]
        have htail := ih (pref++[op]) next
        simpa only [List.append_assoc,List.singleton_append,List.length_append,
          List.length_singleton,List.length_cons,Option.map_some,Option.some_bind,Nat.add_assoc]
          using htail

/-- The complete local circuit/scans have a successful, fixed-code counter
execution. It returns the same file and charges as executeLevel. -/
theorem execute_level {σ : Type} (f R G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (s : State σ) (out : Output σ)
    (h : PhysicalWholeLevel.executeLevel f R G S B hG hS hB child s.active.file s.active.user=some out) :
    ∃ result,execute f R G S B hG hS hB child code code.length 0 s=some (code.length,result) ∧
      result.active.file=out.output ∧ result.active.user=out.state ∧
      result.active.localCost=s.active.localCost+out.localCost ∧
      result.active.recursiveCost=s.active.recursiveCost+out.recursiveCost := by
  obtain ⟨result,hr,hf,hu,hl,hc⟩ := level_execution f R G S B hG hS hB child s out h
  refine ⟨result,?_,hf,hu,hl,hc⟩
  have he := execute_suffix f R G S B hG hS hB child [] code s
  simpa only [List.nil_append,List.length_nil,hr,Option.map_some] using he

theorem advance_pc_bound {σ : Type} (f R G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (program : List Instruction) (pc : ℕ) (s : State σ) (next : ℕ × State σ)
    (hpc : pc ≤ program.length)
    (h : advance f R G S B hG hS hB child program pc s=some next) :
    next.1 ≤ program.length := by
  cases hget : program[pc]? with
  | none =>
      simp only [advance,dispatch,hget,Option.some_bind,Option.some.injEq] at h
      cases h
      exact hpc
  | some op =>
      have hp : pc < program.length := by
        by_contra hn
        have : program[pc]?=none := List.getElem?_eq_none (by omega)
        rw [this] at hget
        contradiction
      rw [advance_at f R G S B hG hS hB child program pc s op hget] at h
      cases hs : step f R G S B hG hS hB child op s with
      | none => simp [hs] at h
      | some result =>
          simp only [hs,Option.map_some,Option.some.injEq] at h
          cases h
          exact hp

/-- A counter is bounded for every pref of every successful run, not only
at termination. It can therefore be encoded in a fixed finite pc type. -/
theorem execute_pc_bound {σ : Type} (f R G S B : ℕ)
    (hG : 0 < G) (hS : 0 < S) (hB : 0 < B) (child : FileChild σ)
    (program : List Instruction) (fuel pc : ℕ) (s : State σ) (next : ℕ × State σ)
    (hpc : pc ≤ program.length)
    (h : execute f R G S B hG hS hB child program fuel pc s=some next) :
    next.1 ≤ program.length := by
  induction fuel generalizing pc s with
  | zero => simp only [execute,Option.some.injEq] at h; cases h; exact hpc
  | succ fuel ih =>
      cases ha : advance f R G S B hG hS hB child program pc s with
      | none => simp [execute,ha] at h
      | some mid =>
          simp only [execute,ha,Option.some_bind] at h
          exact ih mid.1 mid.2 (advance_pc_bound f R G S B hG hS hB child program pc s mid hpc ha) h

end
end CodedSorting.PhysicalLevelProgramCounter
end PhysicalLevelProgramCounter

section PhysicalLevelFrame
/-! Fixed-size saved parents for the actual chronological level program.
The directory fields contain bounded handles, never external-file values.
The two control coordinates are the next instruction and the returned pivot.
All stack operations below read/write the same block disk used by payloads.
-/
set_option autoImplicit false
namespace CodedSorting.PhysicalLevelFrame
open RecursiveExchange WordControl
noncomputable section
variable {fields N exponent length B w : ℕ}

/-- `fields` counts the numeric fields of the complete handle directory.
Costs are proof instrumentation and are deliberately absent from the frame. -/
structure Saved (fields N exponent length : ℕ) where
  shape : Fin 13 → Fin (N^exponent+1)
  directory : Fin fields → Fin (N^exponent+1)
  pc : Fin (length+1)
  returned : Child

def states (length : ℕ) : ℕ := (length+1)*Parameters.S

theorem states_pos (length : ℕ) : 0 < states length :=
  Nat.mul_pos (Nat.zero_lt_succ _) RecursiveControl.child_states_pos

abbrev Descriptor (fields N exponent length : ℕ) :=
  RecursiveControl.Descriptor (13+fields) N exponent (states length)

def descriptor (s : Saved fields N exponent length) : Descriptor fields N exponent length :=
  ⟨Fin.append s.shape s.directory,
    finProdFinEquiv (s.pc,RecursiveControl.childEnumeration s.returned)⟩

def fromDescriptor (d : Descriptor fields N exponent length) : Saved fields N exponent length :=
  ⟨fun i => d.counters (i.castAdd fields),fun i => d.counters (i.natAdd 13),
    (finProdFinEquiv.symm d.pc).1,
    RecursiveControl.childEnumeration.symm (finProdFinEquiv.symm d.pc).2⟩

@[simp] theorem fromDescriptor_descriptor (s : Saved fields N exponent length) :
    fromDescriptor (descriptor s) = s := by
  cases s
  simp only [fromDescriptor,descriptor,Fin.append_left,Fin.append_right,
    Equiv.symm_apply_apply]

/-- The finite frame stores the true whole-level pc, not an enumeration
index of the recursive children. -/
abbrev LevelSaved (fields N exponent : ℕ) :=
  Saved fields N exponent PhysicalLevelContinuation.code.length

def words (fields exponent length : ℕ) : ℕ :=
  RecursiveControl.frameWords (13+fields) exponent (states length)

def encode (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (s : Saved fields N exponent length) : Frame (words fields exponent length) w :=
  RecursiveControl.encode hN hw (descriptor s)

def decode (frame : Frame (words fields exponent length) w) : Saved fields N exponent length :=
  fromDescriptor (RecursiveControl.decode (states_pos length) frame)

@[simp] theorem decode_encode (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (s : Saved fields N exponent length) : decode (encode hN hw s) = s := by
  simp only [decode,encode,RecursiveControl.decode_encode,fromDescriptor_descriptor]

def shapeOf (s : Saved fields N exponent length) : FullShapeControl.Shape :=
  ⟨(s.shape 0).val,(s.shape 1).val,(s.shape 2).val,(s.shape 3).val,
    (s.shape 4).val,(s.shape 5).val,(s.shape 6).val,(s.shape 7).val,
    (s.shape 8).val,(s.shape 9).val,(s.shape 10).val,(s.shape 11).val,(s.shape 12).val⟩

def boundedShape (s : FullShapeControl.Shape)
    (h : ∀ i, s.values i ≤ N^exponent) : Fin 13 → Fin (N^exponent+1) :=
  fun i => ⟨s.values i,Nat.lt_succ_of_le (h i)⟩

/-- Only the disk is external. The active top pointer has a concrete
polynomial bound; the used stack interval lies in the same address bound. -/
structure Stack (fields N exponent length B w : ℕ) where
  disk : BlockDisk B w
  top : Fin (N^exponent+1)
  space : top.val * blocksPerFrame (words fields exponent length) B ≤ N^exponent

def asStack (stack : Stack fields N exponent length B w) : WordControl.Stack B w :=
  ⟨stack.disk,stack.top.val⟩

structure StackOutput (fields N exponent length B w : ℕ) where
  stack : Stack fields N exponent length B w
  trace : List Transfer

def canPush (stack : Stack fields N exponent length B w) : Prop :=
  stack.top.val < N^exponent ∧
    (stack.top.val+1)*blocksPerFrame (words fields exponent length) B ≤ N^exponent

instance (stack : Stack fields N exponent length B w) : Decidable (canPush stack) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Rejected overflow does not perform disk accesses or reduce addresses
modulo a word capacity. A successful call saves the unadvanced parent pc. -/
def push (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (s : Saved fields N exponent length) (stack : Stack fields N exponent length B w) :
    Option (StackOutput fields N exponent length B w) :=
  if h : canPush stack then
    let result := WordControl.push (encode hN hw s) (asStack stack)
    some ⟨⟨result.state.disk,⟨stack.top.val+1,by have := h.1; omega⟩,h.2⟩,result.trace⟩
  else none

/-- The disk-read words, not a retained parent value, determine the returned
shape, directory, instruction counter and child identifier. -/
def pop (hB : 0 < B) (stack : Stack fields N exponent length B w) :
    Option (Saved fields N exponent length × StackOutput fields N exponent length B w) :=
  if hz : stack.top.val=0 then none else
    let result := popBlocks hB stack.disk
      ((stack.top.val-1)*blocksPerFrame (words fields exponent length) B)
      (blocksPerFrame (words fields exponent length) B)
      (fun _ : Fin (words fields exponent length) => (0 : Word w)) []
    some (decode result.1,
      ⟨⟨stack.disk,⟨stack.top.val-1,by have := stack.top.isLt; omega⟩,
        (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans stack.space⟩,result.2⟩)

def Valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (parents : List (Saved fields N exponent length))
    (stack : Stack fields N exponent length B w) : Prop :=
  RecursiveControl.Valid hN hw (parents.map descriptor) (asStack stack)

theorem push_valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (s : Saved fields N exponent length) (parents : List (Saved fields N exponent length))
    (stack : Stack fields N exponent length B w) (h : canPush stack)
    (hv : Valid hN hw parents stack) :
    ∃ result, push hN hw s stack=some result ∧
      Valid hN hw (s::parents) result.stack ∧
      result.stack.top.val=stack.top.val+1 ∧
      result.trace.length=blocksPerFrame (words fields exponent length) B := by
  unfold push
  rw [dif_pos h]
  refine ⟨_,rfl,?_,rfl,?_⟩
  · exact RecursiveControl.enter_valid hN hw (descriptor s) (parents.map descriptor)
      (asStack stack) hv
  · exact (pushBlocks_transfers (encode hN hw s) _ _ stack.disk []).trans (Nat.zero_add _)

theorem pop_valid (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w) (hB : 0 < B)
    (s : Saved fields N exponent length) (parents : List (Saved fields N exponent length))
    (stack : Stack fields N exponent length B w) (hv : Valid hN hw (s::parents) stack) :
    ∃ result,pop hB stack=some (s,result) ∧ Valid hN hw parents result.stack ∧
      result.trace.length=blocksPerFrame (words fields exponent length) B := by
  obtain ⟨result,hr,hv',hc⟩ := RecursiveControl.leave_valid hN hw (states_pos length) hB
    (descriptor s) (parents.map descriptor) (asStack stack) hv
  have hn : stack.top.val ≠ 0 := by
    have ht := hv.1
    simp only [List.map_cons,List.length_cons,List.length_map,asStack] at ht
    omega
  simp only [RecursiveControl.leave,WordControl.pop,asStack,if_neg hn,
    Option.map,Option.some.injEq] at hr
  obtain ⟨he,hr⟩ := Prod.mk.inj hr
  subst result
  have hd := congrArg fromDescriptor he
  simp only [fromDescriptor_descriptor] at hd
  unfold pop
  rw [dif_neg hn]
  dsimp only [decode,words]
  rw [hd]
  exact ⟨_,rfl,hv',hc⟩

/-- Saving a parent on the common disk leaves every payload address above
the reserved stack interval unchanged. -/
theorem push_preserves_high (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (s : Saved fields N exponent length) (stack : Stack fields N exponent length B w)
    (result : StackOutput fields N exponent length B w)
    (hr : push hN hw s stack=some result) (address : ℕ)
    (ha : (stack.top.val+1)*blocksPerFrame (words fields exponent length) B ≤ address) :
    result.stack.disk address=stack.disk address := by
  unfold push at hr
  split at hr
  next h =>
    cases hr
    exact pushBlocks_outside (encode hN hw s) _ _ _ _ _ (Or.inr (by
      simpa only [Nat.add_mul,Nat.one_mul] using ha))
  next h => simp at hr

theorem pop_disk_unchanged (hB : 0 < B)
    (stack : Stack fields N exponent length B w)
    (s : Saved fields N exponent length) (result : StackOutput fields N exponent length B w)
    (hr : pop hB stack=some (s,result)) : result.stack.disk=stack.disk := by
  unfold pop at hr
  split at hr
  next h => simp at hr
  next h => cases hr; rfl

/-- The current top pointer uses exponent+1 global words, independently
of recursion depth. Every accessed stack address has the same bound. -/
def topWords (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (stack : Stack fields N exponent length B w) : Words (exponent+1) w :=
  encodeCounter N w exponent hN hw stack.top

@[simp] theorem decode_topWords (hN : 2 ≤ N) (hw : Nat.clog 2 N ≤ w)
    (stack : Stack fields N exponent length B w) :
    decodeWords (topWords hN hw stack)=stack.top.val := decode_encodeCounter _ _ _ _ _ _

end
end CodedSorting.PhysicalLevelFrame
end PhysicalLevelFrame

section PhysicalLevelFrameGeneral
/-! General-word-size codec and actual stack for the complete parent frame.
Unlike the older codec, this permits every fixed lower constant in w=Θ(log N).
Only one common word disk occurs in the runtime state. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalLevelFrameGeneral
open WordControl PhysicalLevelFrame
noncomputable section
variable {fields N exponent length B w c : ℕ}

def words (fields exponent length c : ℕ) : ℕ :=
  (13+fields)*(c*(exponent+1))+Nat.clog 2 (states length+1)

def encode (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (s : Saved fields N exponent length) : Frame (words fields exponent length c) w :=
  Fin.append
    (WordConvention.encodeTuple N w c exponent (13+fields) hN hw (descriptor s).counters)
    (encodeConstant w (states length) (WordConvention.positive_words N w c hN hw).1
      (descriptor s).pc.castSucc)

def decode (frame : Frame (words fields exponent length c) w) : Saved fields N exponent length :=
  fromDescriptor ⟨fun i =>
    ⟨decodeWords (fun j : Fin (c*(exponent+1)) =>
      frame ((finProdFinEquiv (i,j)).castAdd (Nat.clog 2 (states length+1)))) % (N^exponent+1),
      Nat.mod_lt _ (by omega)⟩,
    ⟨decodeWords (fun j : Fin (Nat.clog 2 (states length+1)) =>
      frame (j.natAdd ((13+fields)*(c*(exponent+1))))) % states length,
      Nat.mod_lt _ (states_pos length)⟩⟩

@[simp] theorem decode_encode (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (s : Saved fields N exponent length) : decode (encode hN hw s)=s := by
  have hc : (fun i : Fin (13+fields) =>
      (⟨decodeWords (fun j : Fin (c*(exponent+1)) =>
        encode hN hw s ((finProdFinEquiv (i,j)).castAdd (Nat.clog 2 (states length+1)))) % (N^exponent+1),
        Nat.mod_lt _ (by omega)⟩ : Fin (N^exponent+1))) = (descriptor s).counters := by
    funext i
    apply Fin.ext
    simp only [encode,Fin.append_left,WordConvention.encodeTuple,Equiv.symm_apply_apply,
      WordConvention.decode_encode,Nat.mod_eq_of_lt ((descriptor s).counters i).isLt]
  have hp : (⟨decodeWords (fun j : Fin (Nat.clog 2 (states length+1)) =>
      encode hN hw s (j.natAdd ((13+fields)*(c*(exponent+1))))) % states length,
      Nat.mod_lt _ (states_pos length)⟩ : Fin (states length)) = (descriptor s).pc := by
    apply Fin.ext
    simp only [encode,Fin.append_right,decode_encodeConstant,Fin.coe_castSucc,
      Nat.mod_eq_of_lt (descriptor s).pc.isLt]
  unfold decode
  rw [hc,hp]
  exact fromDescriptor_descriptor s

structure Stack (fields N exponent length B w c : ℕ) where
  disk : BlockDisk B w
  top : Fin (N^exponent+1)
  space : top.val * blocksPerFrame (words fields exponent length c) B ≤ N^exponent

structure StackOutput (fields N exponent length B w c : ℕ) where
  stack : Stack fields N exponent length B w c
  trace : List Transfer

def canPush (stack : Stack fields N exponent length B w c) : Prop :=
  stack.top.val < N^exponent ∧
    (stack.top.val+1)*blocksPerFrame (words fields exponent length c) B ≤ N^exponent

instance (stack : Stack fields N exponent length B w c) : Decidable (canPush stack) :=
  inferInstanceAs (Decidable (_ ∧ _))

def push (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (s : Saved fields N exponent length) (stack : Stack fields N exponent length B w c) :
    Option (StackOutput fields N exponent length B w c) :=
  if h : canPush stack then
    let result := WordControl.push (encode hN hw s) ⟨stack.disk,stack.top.val⟩
    some ⟨⟨result.state.disk,⟨stack.top.val+1,by have := h.1; omega⟩,h.2⟩,result.trace⟩
  else none

def pop (hB : 0<B) (stack : Stack fields N exponent length B w c) :
    Option (Saved fields N exponent length × StackOutput fields N exponent length B w c) :=
  if hz : stack.top.val=0 then none else
    let result := popBlocks hB stack.disk
      ((stack.top.val-1)*blocksPerFrame (words fields exponent length c) B)
      (blocksPerFrame (words fields exponent length c) B)
      (fun _ : Fin (words fields exponent length c) => (0 : Word w)) []
    some (decode result.1,
      ⟨⟨stack.disk,⟨stack.top.val-1,by have := stack.top.isLt; omega⟩,
        (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans stack.space⟩,result.2⟩)

/-- A proof-only list names the words currently on disk. It is not a field
of the machine and is never used by its dispatcher or return operation. -/
def logicalDisk (hN : 2≤N) (hw : WordConvention.Covers N w c) :
    List (Saved fields N exponent length) → BlockDisk B w
  | [] => fun _ _ => 0
  | s::parents => fun address =>
      if parents.length*blocksPerFrame (words fields exponent length c) B ≤ address then
        frameBlock B (address-parents.length*blocksPerFrame (words fields exponent length c) B)
          (encode hN hw s)
      else logicalDisk hN hw parents address

def Valid (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (parents : List (Saved fields N exponent length))
    (stack : Stack fields N exponent length B w c) : Prop :=
  stack.top.val=parents.length ∧
    ∀ address < stack.top.val*blocksPerFrame (words fields exponent length c) B,
      stack.disk address = logicalDisk hN hw parents address

theorem push_valid (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (s : Saved fields N exponent length) (parents : List (Saved fields N exponent length))
    (stack : Stack fields N exponent length B w c) (h : canPush stack)
    (hv : Valid hN hw parents stack) :
    ∃ result,push hN hw s stack=some result ∧ Valid hN hw (s::parents) result.stack ∧
      result.stack.top.val=stack.top.val+1 ∧
      result.trace.length=blocksPerFrame (words fields exponent length c) B := by
  unfold push
  rw [dif_pos h]
  refine ⟨_,rfl,⟨by simp only [List.length_cons,hv.1],?_⟩,rfl,?_⟩
  · intro address ha
    let t := blocksPerFrame (words fields exponent length c) B
    by_cases hlow : address < stack.top.val*t
    · change (WordControl.push (encode hN hw s) ⟨stack.disk,stack.top.val⟩).state.disk address = _
      rw [push_preserves_parents _ _ address hlow]
      change stack.disk address = _
      rw [hv.2 address hlow]
      simp only [logicalDisk]
      rw [if_neg (by change ¬parents.length*t≤address; rw [←hv.1]; omega)]
    · have hi : address-stack.top.val*t<t := by
        change address<(stack.top.val+1)*t at ha
        rw [Nat.add_mul,Nat.one_mul] at ha
        omega
      have he : stack.top.val*t+(address-stack.top.val*t)=address := by omega
      change (pushBlocks (encode hN hw s) (stack.top.val*t) t stack.disk []).1 address = _
      rw [←he,pushBlocks_at _ _ _ _ _ _ hi,he]
      simp only [logicalDisk]
      rw [if_pos (by change parents.length*t≤address; rw [←hv.1]; omega),←hv.1]
  · exact (pushBlocks_transfers (encode hN hw s) _ _ stack.disk []).trans (Nat.zero_add _)

theorem pop_valid (hN : 2≤N) (hw : WordConvention.Covers N w c) (hB : 0<B)
    (s : Saved fields N exponent length) (parents : List (Saved fields N exponent length))
    (stack : Stack fields N exponent length B w c) (hv : Valid hN hw (s::parents) stack) :
    ∃ result,pop hB stack=some (s,result) ∧ Valid hN hw parents result.stack ∧
      result.trace.length=blocksPerFrame (words fields exponent length c) B := by
  let F := words fields exponent length c
  let t := blocksPerFrame F B
  have ht : stack.top.val=parents.length+1 := by simpa only [List.length_cons] using hv.1
  let restored := popBlocks hB stack.disk (parents.length*t) t (fun _ : Fin F => (0 : Word w)) []
  have hframe : restored.1=encode hN hw s := by
    funext i
    have hi : i.val/B<t := (Nat.div_lt_iff_lt_mul hB).2 (i.isLt.trans_le (frame_fits F B hB))
    rw [show restored.1 i = stack.disk (parents.length*t+i.val/B)
      ⟨i.val%B,Nat.mod_lt _ hB⟩ from popBlocks_at hB stack.disk _ _ _ _ i hi]
    have ha : parents.length*t+i.val/B<stack.top.val*t := by rw [ht]; nlinarith
    rw [hv.2 _ ha]
    simp only [logicalDisk]
    rw [if_pos (by change parents.length*t≤parents.length*t+i.val/B; exact Nat.le_add_right _ _)]
    change frameBlock B (parents.length*t+i.val/B-parents.length*t) (encode hN hw s)
      ⟨i.val%B,Nat.mod_lt _ hB⟩ = _
    rw [Nat.add_sub_cancel_left]
    have he : i.val/B*B+i.val%B=i.val := by simpa only [Nat.mul_comm] using Nat.div_add_mod i.val B
    have hib : i.val<words fields exponent length c := i.isLt
    simp only [frameBlock,he,hib,↓reduceDIte,Fin.eta]
  unfold pop
  rw [dif_neg (by omega)]
  have heq : stack.top.val-1=parents.length := by omega
  simp only [heq]
  change ∃ result,some (decode restored.1,_) = some (s,result) ∧ _
  rw [hframe,decode_encode]
  refine ⟨_,rfl,⟨rfl,?_⟩,?_⟩
  · intro address ha
    change stack.disk address = _
    have ha' : address<stack.top.val*t := by
      change address<parents.length*t at ha
      rw [ht]
      nlinarith
    rw [hv.2 address ha']
    simp only [logicalDisk]
    rw [if_neg (by change ¬parents.length*t≤address; exact Nat.not_le.mpr ha)]
  · exact (popBlocks_transfers hB stack.disk (parents.length*t) t (fun _ : Fin F => (0 : Word w)) []).trans (Nat.zero_add _)

theorem push_preserves_high (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (s : Saved fields N exponent length) (stack : Stack fields N exponent length B w c)
    (result : StackOutput fields N exponent length B w c)
    (hr : push hN hw s stack=some result) (address : ℕ)
    (ha : (stack.top.val+1)*blocksPerFrame (words fields exponent length c) B≤address) :
    result.stack.disk address=stack.disk address := by
  unfold push at hr
  split at hr
  next h =>
    cases hr
    exact pushBlocks_outside (encode hN hw s) _ _ _ _ _ (Or.inr (by
      simpa only [Nat.add_mul,Nat.one_mul] using ha))
  next h => simp at hr

theorem pop_disk_unchanged (hB : 0<B)
    (stack : Stack fields N exponent length B w c)
    (s : Saved fields N exponent length) (result : StackOutput fields N exponent length B w c)
    (hr : pop hB stack=some (s,result)) : result.stack.disk=stack.disk := by
  unfold pop at hr
  split at hr
  next h => simp at hr
  next h => cases hr; rfl

def topWords (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (stack : Stack fields N exponent length B w c) : Words (c*(exponent+1)) w :=
  WordConvention.encode N w c exponent hN hw stack.top

@[simp] theorem decode_topWords (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (stack : Stack fields N exponent length B w c) :
    decodeWords (topWords hN hw stack)=stack.top.val := WordConvention.decode_encode _ _ _ _ _ _ _

end
end CodedSorting.PhysicalLevelFrameGeneral
end PhysicalLevelFrameGeneral
