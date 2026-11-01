import CodedSorting.Sorting.Radix.Framework.Routine
import CodedSorting.Sorting.Radix.Framework.StackFrames

section LocalSorter
/-! The shared controller consumes an actual verified interval program.
Each construction supplies its existing program, space and charge definitions;
the interface does not assume that the global controller sorts correctly. -/
set_option autoImplicit false
namespace CodedSorting.RadixController
open CommonSortingNormalization CommonRecordProgram

class LocalSorter (Normal : Configuration → Prop) where
  space : (q : Configuration) → Normal q → ℕ → ℕ
  charge : Configuration → ℕ → ℕ
  program : (q : Configuration) → (reader : Fin q.inventory.readers) →
    (normal : Normal q) → (n : ℕ) → n≤q.height^2 → 2≤q.exponent →
    (source offset buffer limit : ℕ) →
    source+PhysicalStreamCursor.blockCount q.block (3*offset+3*n)+2≤buffer →
    buffer+space q normal n≤limit → limit≤q.N^q.exponent →
    CommonRecordInterval.Program q n source offset buffer limit Columnsort.sortColumn
  program_charge : ∀ (q : Configuration) (reader : Fin q.inventory.readers)
    (normal : Normal q) (n : ℕ) (hn : n≤q.height^2) (he : 2≤q.exponent)
    (source offset buffer limit : ℕ)
    (hs : source+PhysicalStreamCursor.blockCount q.block (3*offset+3*n)+2≤buffer)
    (hw : buffer+space q normal n≤limit) (hc : limit≤q.N^q.exponent),
    (program q reader normal n hn he source offset buffer limit hs hw hc).charge=charge q n

end CodedSorting.RadixController
end LocalSorter

section Control
/-! The global DFS controller. Active jobs and finite phase data occupy
the existing counter. A suspended parent is an actual disk-stack frame;
child sizes come from actual reads of the parent's persisted directories.
The node family consists of public instruction bodies, never a recursive
sorting callback or an input-dependent code list. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace CodedSorting.RadixController
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonLeafProgram (RAM Machine)
noncomputable section
variable {Normal : Configuration → Prop} [LocalSorter Normal]

/-- Remaining digit groups, record offset, record count, stack depth. -/
abbrev Job (N L : ℕ) := Fin (L+1) × Fin (N+1) × Fin (N+1) × Fin (L+1)
def level {N L : ℕ} (j : Job N L) : ℕ := j.1.val
def offset {N L : ℕ} (j : Job N L) : ℕ := j.2.1.val
def records {N L : ℕ} (j : Job N L) : ℕ := j.2.2.1.val
def depth {N L : ℕ} (j : Job N L) : ℕ := j.2.2.2.val
def bounded (N n : ℕ) : Fin (N+1) := ⟨n%(N+1),Nat.mod_lt _ (by omega)⟩

structure Components (Normal : Configuration → Prop) (q : Configuration) (L A : ℕ) where
  reader : Fin q.inventory.readers
  normal : Normal q
  exponent : 2≤q.exponent
  source : ℕ
  stack : ℕ
  buffer : Job q.N L → ℕ
  limit : Job q.N L → ℕ
  directories : Job q.N L → List ℕ
  node : Job q.N L → Routine q A

variable {q : Configuration} {L A K : ℕ}

/-- Job, phase, node state, next bucket, child cursor, child count.
Phases are visit=0, node=1, count=2, push=3, leaf=4, return=5, halt=6. -/
abbrev Tag (N L A K : ℕ) :=
  Job N L × Fin 7 × Fin A × Fin (K+1) × Fin (N+1) × Fin (N+1)
abbrev tagCount (N L A K : ℕ) := Fintype.card (Tag N L A K)
def tagEquiv (N L A K : ℕ) : Tag N L A K ≃ Fin (tagCount N L A K) := Fintype.equivFin _

def state (j : Job q.N L) (phase : Fin 7) (inner : Fin A)
    (key : Fin (K+1)) (cursor count : Fin (q.N+1)) : Tag q.N L A K :=
  (j,phase,inner,key,cursor,count)
def visit (c : Components Normal q L A) (j : Job q.N L) : Tag q.N L A K :=
  state j 0 (c.node j).entry 0 0 0
def nodeState (c : Components Normal q L A) (j : Job q.N L) (inner : Fin A) : Tag q.N L A K :=
  state j 1 inner 0 0 0
def counting (c : Components Normal q L A) (j : Job q.N L)
    (key : Fin (K+1)) (cursor : Fin (q.N+1)) : Tag q.N L A K :=
  state j 2 (c.node j).entry key cursor 0
def pushing (c : Components Normal q L A) (j : Job q.N L)
    (key : Fin (K+1)) (cursor count : Fin (q.N+1)) : Tag q.N L A K :=
  state j 3 (c.node j).entry key cursor count
def leaf (c : Components Normal q L A) (j : Job q.N L) : Tag q.N L A K :=
  state j 4 (c.node j).entry 0 0 0
def returning (c : Components Normal q L A) (j : Job q.N L) : Tag q.N L A K :=
  state j 5 (c.node j).entry 0 0 0
def halted (c : Components Normal q L A) (j : Job q.N L) : Tag q.N L A K :=
  state j 6 (c.node j).entry 0 0 0

def child (j : Job q.N L) (cursor count : Fin (q.N+1)) : Job q.N L :=
  (bounded L (level j-1),bounded q.N (offset j+cursor.val),count,bounded L (depth j+1))

def resume (c : Components Normal q L A) (j : Job q.N L)
    (key : Fin (K+1)) (cursor count : Fin (q.N+1)) : Tag q.N L A K :=
  counting c j (bounded K (key.val+1)) (bounded q.N (cursor.val+count.val))

def LeafFits (c : Components Normal q L A) (j : Job q.N L) : Prop :=
  records j≤q.height^2 ∧
  c.source+PhysicalStreamCursor.blockCount q.block (3*offset j+3*records j)+2≤c.buffer j ∧
  c.buffer j+LocalSorter.space q c.normal (records j)≤c.limit j ∧
  c.limit j≤q.N^q.exponent

instance (c : Components Normal q L A) (j : Job q.N L) : Decidable (LeafFits c j) := by
  unfold LeafFits
  infer_instance

def leafCode (c : Components Normal q L A) (j : Job q.N L) : List (Instruction q) :=
  if h : LeafFits c j then
    (LocalSorter.program q c.reader c.normal (records j) h.1 c.exponent
      c.source (offset j) (c.buffer j) (c.limit j) h.2.1 h.2.2.1 h.2.2.2).instructions
  else []

def body (c : Components Normal q L A) (t : Tag q.N L A K) : List (Instruction q) :=
  let j := t.1
  let phase := t.2.1.val
  if phase=1 then (c.node j).body t.2.2.1
  else if phase=2 then
    if t.2.2.2.1.val<K then CommonMSDChildCount.code q (c.directories j) t.2.2.2.1.val else []
  else if phase=3 then CommonMSDStack.pushCode q c.stack (depth j)
    (tagEquiv q.N L A K (resume c j t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2)).val
  else if phase=4 then leafCode c j
  else if phase=5 then if depth j=0 then [] else CommonMSDStack.popCode q c.stack (depth j-1)
  else []

def next (c : Components Normal q L A) (t : Tag q.N L A K) (ram : RAM q) : Tag q.N L A K :=
  let j := t.1
  let phase := t.2.1.val
  if phase=0 then
    if level j=0 then returning c j
    else if records j≤q.height^2 then leaf c j else nodeState c j (c.node j).entry
  else if phase=1 then
    if (c.node j).terminal t.2.2.1 then counting c j 0 0
    else nodeState c j ((c.node j).successor t.2.2.1 ram)
  else if phase=2 then
    if t.2.2.2.1.val<K then
      let count := bounded q.N (CommonMSDChildCount.acc q (unpack ram))
      if count.val=0 then resume c j t.2.2.2.1 t.2.2.2.2.1 count
      else pushing c j t.2.2.2.1 t.2.2.2.2.1 count
    else returning c j
  else if phase=3 then visit c (child j t.2.2.2.2.1 t.2.2.2.2.2)
  else if phase=4 then returning c j
  else if phase=5 then
    if depth j=0 then halted c j
    else (tagEquiv q.N L A K).symm
      ⟨CommonMSDStack.loaded q (unpack ram)%tagCount q.N L A K,
        Nat.mod_lt _ (Fintype.card_pos_iff.mpr ⟨t⟩)⟩
  else t

theorem leafCode_safe (c : Components Normal q L A) (j : Job q.N L) :
    ∀ i∈leafCode c j,RespectsPC q i := by
  unfold leafCode
  split
  · exact (LocalSorter.program q c.reader c.normal (records j) _ c.exponent
      c.source (offset j) (c.buffer j) (c.limit j) _ _ _).safe
  · simp

theorem body_safe (c : Components Normal q L A) (t : Tag q.N L A K) :
    ∀ i∈body c t,RespectsPC q i := by
  unfold body
  dsimp only
  split
  · exact (c.node t.1).safe _
  · split
    · split
      · exact CommonMSDChildCount.code_safe q _ _
      · simp
    · split
      · exact CommonMSDStack.push_safe q _ _ _
      · split
        · exact leafCode_safe c _
        · split
          · split
            · simp
            · exact CommonMSDStack.pop_safe q _ _
          · simp

def terminal (t : Tag q.N L A K) : Bool := decide (t.2.1.val=6)

theorem terminal_empty (c : Components Normal q L A) (t : Tag q.N L A K)
    (h : terminal t=true) : body c t=[] := by
  have hp : t.2.1.val=6 := of_decide_eq_true h
  simp only [body,hp,show ¬(6:ℕ)=1 by omega,show ¬(6:ℕ)=2 by omega,
    show ¬(6:ℕ)=3 by omega,show ¬(6:ℕ)=4 by omega,show ¬(6:ℕ)=5 by omega,↓reduceIte]

def routine (c : Components Normal q L A) (root : Job q.N L) : Routine q (tagCount q.N L A K) where
  entry := tagEquiv q.N L A K (visit c root)
  body tag := body c ((tagEquiv q.N L A K).symm tag)
  next tag ram := tagEquiv q.N L A K (next c ((tagEquiv q.N L A K).symm tag) ram)
  terminal tag := terminal ((tagEquiv q.N L A K).symm tag)
  safe tag := body_safe c _
  terminal_empty tag := terminal_empty c _

end
end CodedSorting.RadixController
end Control

section Base
/-! Actual base paths of the global MSD controller. Zero remaining digits
return without changing data. Small positive-level jobs invoke the concrete
unaligned-interval sorter, with its neighboring-record frame and charge. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
namespace CodedSorting.RadixController.Base
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open RadixController CommonRecordProgram
open CommonLeafProgram (Machine)
open CommonRecordInterval (EncodedAt)
open CommonMarginTransform (wordAt)
noncomputable section
variable {Normal : Configuration → Prop} [LocalSorter Normal]
variable {q : Configuration} {L A K : ℕ}

/-- A single active body, stopped at its actual continuation. -/
theorem one (r : Routine q A) (tag : Fin A) (s : Machine q)
    (ht : r.terminal tag=false) :
    r.Path tag s (r.nextTag tag s) (r.rawBody tag s)
      ((r.body tag).length+1) (cost q (r.body tag)) := by
  have hd := Routine.Path.done (r:=r) (r.nextTag tag s) (r.rawBody tag s)
  have hi : erasePC q (r.rawBody tag s)=r.rawBody tag s := by
    simp only [Routine.rawBody,erasePC,setPC_setPC]
  rw [hi] at hd
  simpa only [Nat.add_zero] using Routine.Path.step tag (r.nextTag tag s) s
    (r.rawBody tag s) 0 0 ht hd

/-- Digit exhaustion is a genuine zero-I/O controller transition. -/
theorem level_zero (c : Components Normal q L A) (root j : Job q.N L)
    (hj : level j=0) (s : Machine q) :
    (routine (K:=K) c root).Path (tagEquiv q.N L A K (visit c j)) s
      (tagEquiv q.N L A K (returning c j)) (erasePC q s) 1 0 := by
  simpa [routine,Routine.nextTag,Routine.successor,Routine.rawBody,
    terminal,body,next,visit,state,hj,executeRaw,cost] using
    one (routine (K:=K) c root) (tagEquiv q.N L A K (visit c j)) s
      (by simp [routine,terminal,visit,state])

/-- The leaf phase executes the actual public local-sort instruction list. -/
theorem leaf_path (c : Components Normal q L A) (root j : Job q.N L) (s : Machine q) :
    (routine (K:=K) c root).Path (tagEquiv q.N L A K (leaf c j)) s
      (tagEquiv q.N L A K (returning c j))
      (erasePC q (executeRaw q (leafCode c j) s).1)
      ((leafCode c j).length+1) (cost q (leafCode c j)) := by
  simpa [routine,Routine.nextTag,Routine.successor,Routine.rawBody,
    terminal,body,next,leaf,state] using
    one (routine (K:=K) c root) (tagEquiv q.N L A K (leaf c j)) s
      (by simp [routine,terminal,leaf,state]; decide)

/-- Visit and the leaf call belong to the same global controller path. -/
theorem small_path (c : Components Normal q L A) (root j : Job q.N L)
    (hj : level j≠0) (hn : records j≤q.height^2) (s : Machine q) :
    (routine (K:=K) c root).Path (tagEquiv q.N L A K (visit c j)) s
      (tagEquiv q.N L A K (returning c j))
      (erasePC q (executeRaw q (leafCode c j) s).1)
      ((leafCode c j).length+2) (cost q (leafCode c j)) := by
  have hv : (routine (K:=K) c root).Path (tagEquiv q.N L A K (visit c j)) s
      (tagEquiv q.N L A K (leaf c j)) (erasePC q s) 1 0 := by
    simpa [routine,Routine.nextTag,Routine.successor,Routine.rawBody,
      terminal,body,next,visit,state,hj,hn,executeRaw,cost] using
      one (routine (K:=K) c root) (tagEquiv q.N L A K (visit c j)) s
        (by simp [routine,terminal,visit,state])
  have hl := (routine (K:=K) c root).path_congr (leaf_path (K:=K) c root j s)
    (erasePC q s) (by simp only [erasePC,setPC_setPC])
  simpa only [Nat.zero_add,show 1+((leafCode c j).length+1)=(leafCode c j).length+2 by omega]
    using (routine (K:=K) c root).path_append hv hl

/-- The selected leaf code is the already verified physical interval program. -/
def leafProgram (c : Components Normal q L A) (j : Job q.N L) (h : LeafFits c j) :
    CommonRecordInterval.Program q (records j) c.source (offset j) (c.buffer j) (c.limit j)
      Columnsort.sortColumn :=
  LocalSorter.program q c.reader c.normal (records j) h.1 c.exponent
    c.source (offset j) (c.buffer j) (c.limit j) h.2.1 h.2.2.1 h.2.2.2

@[simp] theorem leafProgram_code (c : Components Normal q L A) (j : Job q.N L) (h : LeafFits c j) :
    (leafProgram c j h).instructions=leafCode c j := by
  simp only [leafProgram,leafCode,dif_pos h]

@[simp] theorem leafProgram_charge (c : Components Normal q L A) (j : Job q.N L) (h : LeafFits c j) :
    (leafProgram c j h).charge=LocalSorter.charge (Normal:=Normal) q (records j) :=
  LocalSorter.program_charge ..

/-- Concrete sorted-permutation semantics and the frame of the same leaf execution. -/
theorem leaf_correct (c : Components Normal q L A) (j : Job q.N L) (h : LeafFits c j)
    (s : Machine q) (f : Records q (records j))
    (hf : EncodedAt q s.disk c.source (offset j) f) :
    let out := erasePC q (executeRaw q (leafCode c j) s).1
    EncodedAt q out.disk c.source (offset j) (Columnsort.sortColumn f) ∧
    Monotone (Columnsort.sortColumn f) ∧
    (List.ofFn (Columnsort.sortColumn f)).Perm (List.ofFn f) ∧
    (∀ w,c.source+w/q.block<q.N^q.exponent →
      (w<3*offset j ∨ 3*offset j+3*records j≤w) →
      (c.source+w/q.block<c.buffer j ∨ c.limit j≤c.source+w/q.block) →
      wordAt q out.disk c.source w=wordAt q s.disk c.source w) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<c.source+3*offset j/q.block ∨
        c.source+PhysicalStreamCursor.blockCount q.block (3*offset j+3*records j)≤a.val) →
      (a.val<c.buffer j ∨ c.limit j≤a.val) → out.disk a=s.disk a) ∧
    cost q (leafCode c j)≤LocalSorter.charge (Normal:=Normal) q (records j) ∧
    (leafCode c j).length≤LocalSorter.charge (Normal:=Normal) q (records j) := by
  let p := leafProgram c j h
  have hp : p.instructions=leafCode c j := leafProgram_code c j h
  have hc : p.charge=LocalSorter.charge (Normal:=Normal) q (records j) :=
    leafProgram_charge c j h
  dsimp only [erasePC]
  rw [←hp,←hc]
  exact ⟨p.correct s f hf,Columnsort.sortColumn_monotone f,Columnsort.sortColumn_perm f,
    p.word_frame s,p.frame s,p.cost_le,p.length_le⟩

/-- The same leaf path updates the literal encoding of the whole main file. -/
theorem leaf_global (c : Components Normal q L A) (j : Job q.N L) (h : LeafFits c j)
    (hspan : offset j+records j≤q.N)
    (hfile : c.source+recordBlocks q q.N≤c.buffer j)
    (s : Machine q) (f : Records q q.N) (hf : Encoded q s.disk c.source f) :
    Encoded q (erasePC q (executeRaw q (leafCode c j) s).1).disk c.source
      (CommonRecordIntervalSplice.replace hspan f
        (Columnsort.sortColumn (CommonRecordIntervalSplice.slice hspan f))) := by
  have hbuffer : c.buffer j≤q.N^q.exponent := by
    have hw := h.2.2.1
    have hc := h.2.2.2
    omega
  simpa only [leafProgram_code,erasePC] using
    CommonRecordIntervalSplice.program_global q hspan (leafProgram c j h) hfile hbuffer s f hf

end
end CodedSorting.RadixController.Base
end Base

section Steps
/-! Structural embeddings for the single global DFS policy. Inner node
routines retain their actual instruction bodies; their terminal state
becomes the parent continuation instead of halting the global run. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace CodedSorting.RadixController
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonLeafProgram (RAM Machine)
noncomputable section
variable {Normal : Configuration → Prop} [LocalSorter Normal]
variable {q : Configuration} {L A K : ℕ}

def index (t : Tag q.N L A K) : Fin (tagCount q.N L A K) := tagEquiv q.N L A K t

@[simp] theorem routine_body (c : Components Normal q L A) (root : Job q.N L)
    (t : Tag q.N L A K) : (routine c root).body (index t)=body c t := by
  simp only [routine,index,Equiv.symm_apply_apply]

@[simp] theorem routine_terminal (c : Components Normal q L A) (root : Job q.N L)
    (t : Tag q.N L A K) : (routine c root).terminal (index t)=terminal t := by
  simp only [routine,index,Equiv.symm_apply_apply]

@[simp] theorem routine_next (c : Components Normal q L A) (root : Job q.N L)
    (t : Tag q.N L A K) (ram : RAM q) :
    (routine c root).next (index t) ram=index (next c t ram) := by
  simp only [routine,index,Equiv.symm_apply_apply]

@[simp] theorem node_body (c : Components Normal q L A) (j : Job q.N L) (a : Fin A) :
    body c (nodeState (K:=K) c j a)=(c.node j).body a := by
  simp [body,nodeState,state]

@[simp] theorem node_terminal (c : Components Normal q L A) (j : Job q.N L) (a : Fin A) :
    terminal (nodeState (K:=K) c j a)=false := by
  simp [terminal,nodeState,state]

@[simp] theorem node_raw (c : Components Normal q L A) (root j : Job q.N L)
    (a : Fin A) (s : Machine q) :
    (routine c root).rawBody (index (nodeState (K:=K) c j a)) s=(c.node j).rawBody a s := by
  simp only [Routine.rawBody,routine_body,node_body]

theorem node_next (c : Components Normal q L A) (root j : Job q.N L)
    (a : Fin A) (s : Machine q) (ha : (c.node j).terminal a=false) :
    (routine c root).nextTag (index (nodeState (K:=K) c j a)) s=
      index (nodeState c j ((c.node j).nextTag a s)) := by
  simp only [Routine.nextTag,node_raw,Routine.successor,routine_next]
  simp only [next,nodeState,state,Fin.val_one,show ¬(1:ℕ)=0 by omega,↓reduceIte,ha,
    Bool.false_eq_true]
  simp only [Routine.successor,setPC_setPC]

theorem node_path (c : Components Normal q L A) (root j : Job q.N L)
    {a b : Fin A} {s t : Machine q} {steps charge : ℕ}
    (h : (c.node j).Path a s b t steps charge) :
    (routine c root).Path (index (nodeState (K:=K) c j a)) s
      (index (nodeState c j b)) t steps charge := by
  apply (c.node j).path_map (routine c root) (fun a => index (nodeState c j a))
    (fun a _ => by simp) (fun a s ha => node_next c root j a s ha)
    (fun a _ => by simp) h

theorem node_trace_path (c : Components Normal q L A) (root j : Job q.N L)
    {a b : Fin A} {s t : Machine q} {steps charge : ℕ}
    (h : (c.node j).Trace a s b t steps charge) :
    (routine c root).Path (index (nodeState (K:=K) c j a)) s
      (index (nodeState c j b)) t steps charge :=
  node_path c root j ((c.node j).trace_toPath h)

@[simp] theorem node_done_body (c : Components Normal q L A) (j : Job q.N L)
    (a : Fin A) (ha : (c.node j).terminal a=true) :
    body c (nodeState (K:=K) c j a)=[] := by
  rw [node_body,(c.node j).terminal_empty a ha]

theorem node_done_next (c : Components Normal q L A) (root j : Job q.N L)
    (a : Fin A) (s : Machine q) (ha : (c.node j).terminal a=true) :
    (routine c root).nextTag (index (nodeState (K:=K) c j a)) s=
      index (counting c j 0 0) := by
  simp only [Routine.nextTag,Routine.successor,routine_next]
  simp [next,nodeState,state,ha]

theorem node_return (c : Components Normal q L A) (root j : Job q.N L)
    (a : Fin A) (s : Machine q) (ha : (c.node j).terminal a=true) :
    (routine c root).Path (index (nodeState (K:=K) c j a)) s
      (index (counting c j 0 0)) (erasePC q s) 1 0 := by
  have hr : (routine c root).rawBody (index (nodeState (K:=K) c j a)) s=erasePC q s := by
    simp only [Routine.rawBody,routine_body,node_done_body c j a ha,executeRaw]
  have hp := Routine.Path.step (r:=routine (K:=K) c root)
    (index (nodeState c j a)) (index (counting c j 0 0)) s (erasePC q s) 0 0
    (by simp) (by
      rw [node_done_next c root j a s ha,hr]
      simpa only [erasePC,setPC_setPC] using
        Routine.Path.done (r:=routine (K:=K) c root) (index (counting c j 0 0)) (erasePC q s))
  simpa only [routine_body,node_done_body c j a ha,List.length_nil,cost,zero_add,add_zero] using hp

end
end CodedSorting.RadixController
end Steps

section CountSteps
/-! The global controller obtains child lengths through actual directory
reads. Zero buckets advance without a recursive call; nonempty buckets
proceed to the charged stack push. -/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option maxRecDepth 4096
namespace CodedSorting.RadixController
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonLeafProgram (RAM Machine)
noncomputable section
variable {Normal : Configuration → Prop} [LocalSorter Normal]
attribute [local irreducible] CommonMSDChildCount.code CommonMSDChildCount.acc
  CommonMSDChildCount.totalCount CommonMSDDirectoryRead.code executeRaw
variable {q : Configuration} {L A K : ℕ}

/-- Equality transport performed with an abstract routine and abstract result. -/
theorem path_of_one {B : ℕ} (r : Routine q B) (tag nextTag : Fin B)
    (s out : Machine q) (steps charge : ℕ) (ht : r.terminal tag=false)
    (hn : r.nextTag tag s=nextTag) (ho : r.rawBody tag s=out)
    (hl : (r.body tag).length+1=steps) (hc : cost q (r.body tag)=charge) :
    r.Path tag s nextTag out steps charge := by
  subst nextTag
  subst out
  subst steps
  subst charge
  exact RadixController.Base.one r tag s ht

theorem one_step (c : Components Normal q L A) (root : Job q.N L)
    (t : Tag q.N L A K) (s : Machine q) (ht : terminal t=false) :
    (routine (K:=K) c root).Path (index t) s ((routine (K:=K) c root).nextTag (index t) s)
      ((routine (K:=K) c root).rawBody (index t) s) ((body c t).length+1) (cost q (body c t)) := by
  simpa only [routine_body] using RadixController.Base.one (routine (K:=K) c root) (index t) s
    (by simpa only [routine_terminal] using ht)

@[simp] theorem count_body (c : Components Normal q L A) (j : Job q.N L)
    (k : Fin (K+1)) (cursor : Fin (q.N+1)) (hk : k.val<K) :
    body c (counting c j k cursor)=CommonMSDChildCount.code q (c.directories j) k.val := by
  change (if k.val<K then CommonMSDChildCount.code q (c.directories j) k.val else [])=_
  rw [if_pos hk]

@[simp] theorem count_terminal (c : Components Normal q L A) (j : Job q.N L)
    (k : Fin (K+1)) (cursor : Fin (q.N+1)) :
    terminal (counting c j k cursor)=false := by rfl

@[simp] theorem counting_next (c : Components Normal q L A) (j : Job q.N L)
    (k : Fin (K+1)) (cursor : Fin (q.N+1)) (ram : RAM q) :
    next c (counting c j k cursor) ram=
      (if k.val<K then
        (if (bounded q.N (CommonMSDChildCount.acc q (unpack ram))).val=0
          then resume c j k cursor (bounded q.N (CommonMSDChildCount.acc q (unpack ram)))
          else pushing c j k cursor (bounded q.N (CommonMSDChildCount.acc q (unpack ram))))
       else returning c j) := rfl

theorem count_next_loaded (c : Components Normal q L A) (j : Job q.N L)
    (k : Fin (K+1)) (cursor : Fin (q.N+1)) (ram : RAM q) (n : ℕ)
    (hk : k.val<K) (ha : CommonMSDChildCount.acc q (unpack ram)=n) :
    index (next c (counting c j k cursor) ram)=
      index (if (bounded q.N n).val=0 then resume c j k cursor (bounded q.N n)
        else pushing c j k cursor (bounded q.N n)) := by
  rw [counting_next,if_pos hk,ha]

theorem count_path (c : Components Normal q L A) (root j : Job q.N L)
    (k : Fin (K+1)) (cursor : Fin (q.N+1)) (hk : k.val<K) (s : Machine q)
    (hs : ∀ target∈c.directories j,CommonMSDDirectoryRead.base q target k.val+
      CommonMSDDirectoryRead.blocks q k.val≤q.N^q.exponent)
    (hc : CommonMSDChildCount.totalCount q s.disk (c.directories j) k.val<(2^q.w)^q.digits) :
    let n := bounded q.N (CommonMSDChildCount.totalCount q s.disk (c.directories j) k.val)
    ∃ out : Machine q,
      (routine (K:=K) c root).Path (index (counting c j k cursor)) s
        (index (if n.val=0 then resume c j k cursor n else pushing c j k cursor n)) out
        ((CommonMSDChildCount.code q (c.directories j) k.val).length+1)
        ((c.directories j).length*CommonMSDDirectoryRead.blocks q k.val) ∧
      out.disk=s.disk := by
  dsimp only
  obtain ⟨out,hr,hdisk,hacc⟩ := CommonMSDChildCountPayload.complete q (c.directories j) k.val s hs hc
  have hraw : (routine (K:=K) c root).rawBody (index (counting c j k cursor)) s=out := by
    simpa only [Routine.rawBody,routine_body,count_body c j k cursor hk] using hr
  have hnext : (routine (K:=K) c root).nextTag (index (counting c j k cursor)) s=
      index (if (bounded q.N (CommonMSDChildCount.totalCount q s.disk (c.directories j) k.val)).val=0
        then resume c j k cursor (bounded q.N (CommonMSDChildCount.totalCount q s.disk (c.directories j) k.val))
        else pushing c j k cursor (bounded q.N (CommonMSDChildCount.totalCount q s.disk (c.directories j) k.val))) := by
    rw [Routine.nextTag,hraw]
    simp only [Routine.successor,routine_next]
    have hzero : CommonMSDChildCount.acc q (unpack (setPC q 0 out.ram))=
        CommonMSDChildCount.acc q (unpack out.ram) := by
      exact CommonMSDChildCount.acc_eq_of_erasePC q (erasePC q out) out
        (by simp only [erasePC,setPC_setPC])
    exact count_next_loaded c j k cursor (setPC q 0 out.ram) _ hk (hzero.trans hacc)

  refine ⟨out,?_,hdisk⟩
  apply path_of_one (routine (K:=K) c root) (index (counting c j k cursor)) _ s out
    _ _ (by rw [routine_terminal];exact count_terminal c j k cursor) hnext hraw
  · rw [routine_body,count_body c j k cursor hk]
  · rw [routine_body,count_body c j k cursor hk]
    exact CommonMSDChildCount.code_cost q _ _ hs

theorem count_done (c : Components Normal q L A) (root j : Job q.N L)
    (k : Fin (K+1)) (cursor : Fin (q.N+1)) (hk : k.val=K) (s : Machine q) :
    (routine (K:=K) c root).Path (index (counting c j k cursor)) s
      (index (returning c j)) (erasePC q s) 1 0 := by
  have hb : body c (counting c j k cursor)=[] := by
    change (if k.val<K then CommonMSDChildCount.code q (c.directories j) k.val else [])=[]
    rw [if_neg (by omega)]
  have hr : (routine (K:=K) c root).rawBody (index (counting c j k cursor)) s=erasePC q s := by
    simp only [Routine.rawBody,routine_body,hb,executeRaw]
  have hn : (routine (K:=K) c root).nextTag (index (counting c j k cursor)) s=index (returning c j) := by
    simp only [Routine.nextTag,Routine.successor,routine_next]
    rw [counting_next,if_neg (by omega)]
  simpa only [hb,hr,hn,List.length_nil,cost,Nat.zero_add] using
    one_step c root (counting c j k cursor) s (count_terminal c j k cursor)

end
end CodedSorting.RadixController
end CountSteps

section PopStep
/-! A global return reads its continuation from the actual disk stack.
The resulting controller tag is the decoded saved value. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.RadixController
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonLeafProgram (Machine RAM machine)
noncomputable section
variable {Normal : Configuration → Prop} [LocalSorter Normal]
variable {q : Configuration} {L A K : ℕ}

theorem pop_body (c : Components Normal q L A) (j : Job q.N L) (hj : depth j≠0) :
    body c (returning (K:=K) c j)=CommonMSDStack.popCode q c.stack (depth j-1) := by
  simp only [body,returning,state,show ((5:Fin 7):ℕ)=5 by rfl,
    show ¬(5:ℕ)=1 by omega,show ¬(5:ℕ)=2 by omega,
    show ¬(5:ℕ)=3 by omega,show ¬(5:ℕ)=4 by omega,↓reduceIte,hj]

theorem pop_terminal (c : Components Normal q L A) (j : Job q.N L) :
    terminal (returning (K:=K) c j)=false := by rfl

theorem pop_next_loaded (c : Components Normal q L A) (j : Job q.N L)
    (target : Tag q.N L A K) (ram : RAM q) (hj : depth j≠0)
    (hl : CommonMSDStack.loaded q (unpack ram)=(index target).val) :
    index (next c (returning (K:=K) c j) ram)=index target := by
  simp only [next,returning,state,show ((5:Fin 7):ℕ)=5 by rfl,
    show ¬(5:ℕ)=0 by omega,show ¬(5:ℕ)=1 by omega,
    show ¬(5:ℕ)=2 by omega,show ¬(5:ℕ)=3 by omega,
    show ¬(5:ℕ)=4 by omega,↓reduceIte,hj,hl]
  change tagEquiv q.N L A K ((tagEquiv q.N L A K).symm _)=index target
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  exact Nat.mod_eq_of_lt (index target).isLt

/-- The target is proved equal to a word loaded by pop, not supplied to
the instruction list as a decoded input or an oracle. -/
theorem pop_path (c : Components Normal q L A) (root j : Job q.N L)
    (target : Tag q.N L A K) (s : Machine q) (hj : depth j≠0)
    (hfit : CommonMSDStack.frameBase q c.stack (depth j-1)+CommonMSDStack.frameBlocks q≤q.N^q.exponent)
    (hframe : CommonMSDStack.Frame q s.disk c.stack (depth j-1) (index target).val)
    (hcapacity : (index target).val<(2^q.w)^q.digits) :
    ∃ out : Machine q,
      (routine c root).Path (index (returning c j)) s (index target) out
        (CommonMSDStack.frameBlocks q+1) (CommonMSDStack.frameBlocks q) ∧ out.disk=s.disk := by
  obtain ⟨final,hraw,_,hload⟩ := CommonMSDStack.pop_raw q c.stack (depth j-1)
    (unpack s.ram) s.disk hfit
  rw [CommonBlockPair.machine_eta] at hraw
  have hloaded : CommonMSDStack.loaded q final=(index target).val :=
    hload.trans (CommonMSDStack.frame_decodes q s.disk c.stack (depth j-1) _ hframe hcapacity)
  let out := erasePC q (machine q final s.disk)
  have hr : (routine c root).rawBody (index (returning (K:=K) c j)) s=out := by
    simp only [Routine.rawBody,routine_body,pop_body c j hj,hraw]
    rfl
  have hl : CommonMSDStack.loaded q (unpack (setPC q 0 out.ram))=(index target).val := by
    simpa only [out,erasePC,machine,setPC_setPC,setPC,unpack_pack,
      CommonMSDStack.loaded,CommonMSDStack.loadedWords] using hloaded
  have hn : (routine c root).nextTag (index (returning (K:=K) c j)) s=index target := by
    simp only [Routine.nextTag,hr,Routine.successor,routine_next]
    exact pop_next_loaded c j target (setPC q 0 out.ram) hj hl
  have hterminal : (routine (K:=K) c root).terminal (index (returning c j))=false := by
    rw [routine_terminal,pop_terminal]
  have hp:=RadixController.Base.one (routine (K:=K) c root) (index (returning c j)) s hterminal
  rw [hn,hr] at hp
  have hsteps : ((routine (K:=K) c root).body (index (returning c j))).length+1=
      CommonMSDStack.frameBlocks q+1 := by
    rw [routine_body,pop_body c j hj,CommonMSDStack.pop_length]
  have hcost : cost q ((routine (K:=K) c root).body (index (returning c j)))=
      CommonMSDStack.frameBlocks q := by
    rw [routine_body,pop_body c j hj]
    exact CommonMSDStack.pop_cost q c.stack (depth j-1) hfit
  refine ⟨out,?_,rfl⟩
  exact hsteps ▸ hcost ▸ hp

end
end CodedSorting.RadixController
end PopStep

section StackSteps
/-! One-step execution paths for the actual disk stack. A push stores the
bounded parent continuation; a return reads that value and resumes it.
Neither operation receives a proof-side continuation value as RAM input. -/
set_option autoImplicit false
set_option maxHeartbeats 120000
namespace CodedSorting.RadixController
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonLeafProgram (Machine RAM machine)
noncomputable section
variable {Normal : Configuration → Prop} [LocalSorter Normal]
variable {q : Configuration} {L A K : ℕ}

@[simp] theorem pushing_body (c : Components Normal q L A) (j : Job q.N L)
    (key : Fin (K+1)) (cursor count : Fin (q.N+1)) :
    body c (pushing c j key cursor count)=CommonMSDStack.pushCode q c.stack (depth j)
      (index (resume c j key cursor count)).val := by
  rfl

@[simp] theorem pushing_terminal (c : Components Normal q L A) (j : Job q.N L)
    (key : Fin (K+1)) (cursor count : Fin (q.N+1)) :
    terminal (pushing c j key cursor count)=false := by
  rfl

theorem pushing_next (c : Components Normal q L A) (root j : Job q.N L)
    (key : Fin (K+1)) (cursor count : Fin (q.N+1)) (s : Machine q) :
    (routine c root).nextTag (index (pushing c j key cursor count)) s=
      index (visit c (child j cursor count)) := by
  simp only [Routine.nextTag,Routine.successor,routine_next]
  rfl

/-- The child is entered only after the parent's continuation has been
written to its actual stack slot. -/
theorem push_path (c : Components Normal q L A) (root j : Job q.N L)
    (key : Fin (K+1)) (cursor count : Fin (q.N+1)) (s : Machine q)
    (hfit : CommonMSDStack.frameBase q c.stack (depth j)+CommonMSDStack.frameBlocks q≤q.N^q.exponent) :
    ∃ out : Machine q,
      (routine c root).Path (index (pushing c j key cursor count)) s
        (index (visit c (child j cursor count))) out
        (2*CommonMSDStack.frameBlocks q+2) (CommonMSDStack.frameBlocks q) ∧
      CommonMSDStack.Frame q out.disk c.stack (depth j) (index (resume c j key cursor count)).val ∧
      (∀ a : Fin (q.N^q.exponent),a.val<CommonMSDStack.frameBase q c.stack (depth j) ∨
        CommonMSDStack.frameBase q c.stack (depth j)+CommonMSDStack.frameBlocks q≤a.val →
        out.disk a=s.disk a) := by
  obtain ⟨final,disk,hraw,hframe,houtside⟩ := CommonMSDStack.push_raw q c.stack (depth j)
    (index (resume c j key cursor count)).val (unpack s.ram) s.disk hfit
  rw [CommonBlockPair.machine_eta] at hraw
  let out := erasePC q (machine q final disk)
  have hr : (routine c root).rawBody (index (pushing c j key cursor count)) s=out := by
    simp only [Routine.rawBody,routine_body,pushing_body,hraw]
    rfl
  refine ⟨out,?_,hframe,houtside⟩
  have hp := RadixController.Base.one (routine (K:=K) c root)
    (index (pushing c j key cursor count)) s
    (by simp only [routine_terminal,pushing_terminal])
  rw [pushing_next,hr] at hp
  have hb : (routine c root).body (index (pushing c j key cursor count))=
      CommonMSDStack.pushCode q c.stack (depth j) (index (resume c j key cursor count)).val :=
    (routine_body c root _).trans (pushing_body c j key cursor count)
  have hl := CommonMSDStack.push_length q c.stack (depth j) (index (resume c j key cursor count)).val
  have hc := CommonMSDStack.push_cost q c.stack (depth j) (index (resume c j key cursor count)).val hfit
  rw [hb,hl,hc] at hp
  simpa only [Nat.add_assoc] using hp

end
end CodedSorting.RadixController
end StackSteps

section CallSteps
/-! Public descriptor arithmetic and entry/exit paths used by the
well-founded proof of the actual recursive controller. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.RadixController
open CommonSortingNormalization CommonStaticSchedule CommonMSDRoutine
open CommonLeafProgram
noncomputable section
variable {Normal : Configuration → Prop} [LocalSorter Normal]
variable {q : Configuration} {L A K : ℕ}

@[simp] theorem bounded_val {N n : ℕ} (h : n≤N) : (bounded N n).val=n :=
  Nat.mod_eq_of_lt (by omega)

theorem child_properties (j : Job q.N L) (cursor count : Fin (q.N+1))
    (hj : offset j+records j≤q.N) (hl : 0<level j)
    (hd : depth j+level j≤L) (hc : cursor.val+count.val≤records j) :
    level (child j cursor count)=level j-1 ∧
    offset (child j cursor count)=offset j+cursor.val ∧
    records (child j cursor count)=count.val ∧
    depth (child j cursor count)=depth j+1 ∧
    offset (child j cursor count)+records (child j cursor count)≤q.N ∧
    depth (child j cursor count)+level (child j cursor count)≤L := by
  have hlev : level j≤L := by have:=j.1.isLt;unfold level;omega
  have hoff : offset j+cursor.val≤q.N := by omega
  have hdep : depth j+1≤L := by omega
  have hlv : level (child j cursor count)=level j-1 :=
    bounded_val (show level j-1≤L by omega)
  have hof : offset (child j cursor count)=offset j+cursor.val := bounded_val hoff
  have hdp : depth (child j cursor count)=depth j+1 := bounded_val hdep
  refine ⟨hlv,hof,rfl,hdp,?_,?_⟩
  · rw [hof]
    change offset j+cursor.val+count.val≤q.N
    omega
  · rw [hlv,hdp]
    omega

theorem visit_node (c : Components Normal q L A) (root j : Job q.N L)
    (hl : level j≠0) (hn : q.height^2<records j) (s : Machine q) :
    (routine (K:=K) c root).Path (index (visit (K:=K) c j)) s
      (index (nodeState c j (c.node j).entry)) (erasePC q s) 1 0 := by
  have hb : body c (visit (K:=K) c j)=[] := by simp [body,visit,state]
  have hr : (routine (K:=K) c root).rawBody (index (visit (K:=K) c j)) s=erasePC q s := by
    simp only [Routine.rawBody,routine_body,hb,executeRaw]
  have hnext : (routine (K:=K) c root).nextTag (index (visit (K:=K) c j)) s=
      index (nodeState c j (c.node j).entry) := by
    simp [Routine.nextTag,Routine.successor,routine_next,next,visit,state,hl,not_le.mpr hn]
  have ht : terminal (visit (K:=K) c j)=false := by simp [terminal,visit,state]
  simpa only [hb,hr,hnext,List.length_nil,cost,Nat.zero_add] using
    one_step c root (visit (K:=K) c j) s ht

theorem trace_terminal (r : Routine q A) {start finish : Fin A}
    {s final : Machine q} {steps charge : ℕ}
    (h : r.Trace start s finish final steps charge) : r.terminal finish=true := by
  induction h with
  | done _ _ ht => exact ht
  | step _ _ _ _ _ _ _ _ ih => exact ih

theorem node_call (c : Components Normal q L A) (root j : Job q.N L)
    (hl : level j≠0) (hn : q.height^2<records j) (s final : Machine q)
    (tag : Fin A) (steps charge : ℕ)
    (htrace : (c.node j).Trace (c.node j).entry s tag final steps charge) :
    (routine (K:=K) c root).Path (index (visit (K:=K) c j)) s
      (index (counting c j 0 0)) final (steps+2) charge := by
  have htag : (c.node j).terminal tag=true := trace_terminal (c.node j) htrace
  have herase := (c.node j).path_final_erased ((c.node j).trace_toPath htrace)
  have h1 := visit_node (K:=K) c root j hl hn s
  have h2 := node_trace_path (K:=K) c root j htrace
  have h2' := (routine (K:=K) c root).path_congr h2 (erasePC q s)
    (by simp only [erasePC,setPC_setPC])
  have h3 := node_return (K:=K) c root j tag final htag
  rw [herase] at h3
  have hp := (routine (K:=K) c root).path_append
    ((routine (K:=K) c root).path_append h1 h2') h3
  simpa only [Nat.zero_add,Nat.add_zero,show 1+steps+1=steps+2 by omega] using hp

theorem root_halt (c : Components Normal q L A) (root j : Job q.N L)
    (hd : depth j=0) (s : Machine q) :
    (routine (K:=K) c root).Trace (index (returning (K:=K) c j)) s
      (index (halted c j)) (erasePC q s) 1 0 := by
  have hb : body c (returning (K:=K) c j)=[] := by
    change (if depth j=0 then [] else CommonMSDStack.popCode q c.stack (depth j-1))=[]
    rw [if_pos hd]
  have hr : (routine (K:=K) c root).rawBody (index (returning (K:=K) c j)) s=erasePC q s := by
    simp only [Routine.rawBody,routine_body,hb,executeRaw]
  have hn : (routine (K:=K) c root).nextTag (index (returning (K:=K) c j)) s=index (halted c j) := by
    simp only [Routine.nextTag,Routine.successor,routine_next]
    change index (if depth j=0 then halted c j else _)=_
    rw [if_pos hd]
  have hp := one_step c root (returning (K:=K) c j) s (by rfl)
  have hp' : (routine (K:=K) c root).Path (index (returning (K:=K) c j)) s
      (index (halted c j)) (erasePC q s) 1 0 := by
    simpa only [hb,hr,hn,List.length_nil,cost,Nat.zero_add] using hp
  exact (routine (K:=K) c root).path_toTrace hp' (by rw [routine_terminal];rfl)

end
end CodedSorting.RadixController
end CallSteps
