import CodedSorting.Sorting.Radix.Framework.ChunkRows
import CodedSorting.Sorting.Radix.Framework.Routine

/-! Shared MSD node proofs. The two exchange constructions supply only their
existing chunk-sort program and its proved charge bound. The interface keeps
the exact sorted-chunk operation, safety and disk frame in the `Program` type;
node execution and correctness are constructed below, not assumed. -/
set_option autoImplicit false
namespace CodedSorting.RadixNode
open CommonSortingNormalization CommonRecordProgram

class ChunkSorter (Normal : Configuration → Prop) where
  space : (q : Configuration) → Normal q → ℕ → ℕ
  charge : Configuration → ℕ → ℕ
  program : (q : Configuration) → (reader : Fin q.inventory.readers) →
    (normal : Normal q) → (n : ℕ) → 2≤q.exponent →
    (source buffer limit : ℕ) → source+max 1 (recordBlocks q n)≤buffer →
    buffer+space q normal n≤limit → limit≤q.N^q.exponent →
    3*CommonMSDChunks.paddedSize q n<(2^q.w)^q.digits →
    Program q n source buffer limit (CommonMSDChunks.operation q n)
  program_charge_le : ∀ (q : Configuration) (reader : Fin q.inventory.readers)
    (normal : Normal q) (n : ℕ) (he : 2≤q.exponent) (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q normal n≤limit) (hl : limit≤q.N^q.exponent)
    (hd : 3*CommonMSDChunks.paddedSize q n<(2^q.w)^q.digits),
    (program q reader normal n he source buffer limit hs hw hl hd).charge≤charge q n

end CodedSorting.RadixNode

section Pass
/-! The actual static prefix of one MSD node: sort its H² chunks, then
construct every row directory from those resulting records. The public
code depends on lengths and allocation, never on input records. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace CodedSorting.RadixNode.Pass
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open RadixNode CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
noncomputable section
variable {Normal : Configuration → Prop} [ChunkSorter Normal]
attribute [local irreducible] ControlledNormalization.runLogical

def directory (q : Configuration) (buffer : ℕ) : ℕ :=
  buffer+recordBlocks q (CommonMSDChunks.chunkSize q)

structure Resources (q : Configuration) (hnormal : Normal q) (n K : ℕ) where
  source : ℕ
  buffer : ℕ
  limit : ℕ
  exponent : 2≤q.exponent
  source_before : source+recordBlocks q n+2≤buffer
  prepare_space : buffer+ChunkSorter.space q hnormal n≤limit
  directory_space : directory q buffer+CommonMSDChunks.chunkCount q n*CommonMSDDirectory.blocks q K≤limit
  capacity : limit≤q.N^q.exponent
  descriptors : 3*CommonMSDChunks.paddedSize q n<(2^q.w)^q.digits
  counters : recordBlocks q (CommonMSDChunks.chunkSize q)*q.block<(2^q.w)^q.digits

def chunks (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K) :
    Program q n r.source r.buffer r.limit (CommonMSDChunks.operation q n) :=
  ChunkSorter.program q reader hnormal n r.exponent r.source r.buffer r.limit
    (by have:=r.source_before;omega) r.prepare_space r.capacity r.descriptors

def withChunks (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (p : Program q n r.source r.buffer r.limit (CommonMSDChunks.operation q n))
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K) :
    List (Instruction q) :=
  p.instructions++
    CommonMSDRowDirectoryBatch.code q reader hfit key (CommonMSDChunkRows.row q n)
      r.source r.buffer (directory q r.buffer) (List.finRange (CommonMSDChunks.chunkCount q n))

def code (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K) :
    List (Instruction q) := withChunks q reader r (chunks q reader r) hfit key

def directoryCharge (q : Configuration) (n K : ℕ) : ℕ :=
  7*CommonMSDRowDirectoryBatch.rowBlocks q (CommonMSDChunkRows.row q n)
    (List.finRange (CommonMSDChunks.chunkCount q n))+
    CommonMSDDirectory.blocks q K*CommonMSDChunks.chunkCount q n

def charge (q : Configuration) (n K : ℕ) : ℕ := ChunkSorter.charge (Normal:=Normal) q n+directoryCharge q n K

def lengthBound (q : Configuration) (n K : ℕ) : ℕ :=
  ChunkSorter.charge (Normal:=Normal) q n+
    7*CommonMSDRowDirectoryBatch.rowBlocks q (CommonMSDChunkRows.row q n)
      (List.finRange (CommonMSDChunks.chunkCount q n))+
    (2*CommonMSDDirectory.blocks q K+2)*CommonMSDChunks.chunkCount q n

structure Ready (q : Configuration) {n K : ℕ} (key : Word q.w→Fin K)
    (source dir : ℕ) (disk : Disk q) (f : Records q n) : Prop where
  input : Encoded q disk source f
  starts : ∀ c : Fin (CommonMSDChunks.chunkCount q n),∀ k : Fin K,
    CommonMSDDirectory.entry q disk (CommonMSDRowDirectoryBatch.target q K dir c.val) k 0=
      CommonMSDDirectory.start (CommonMSDDirectorySemantics.lengths q key
        (CommonMSDRowDirectory.slice (CommonMSDChunkRows.row q n c).offset
          (CommonMSDChunkRows.row q n c).length (CommonMSDChunkRows.row q n c).fits f)) k
  lengths : ∀ c : Fin (CommonMSDChunks.chunkCount q n),∀ k : Fin K,
    CommonMSDDirectory.entry q disk (CommonMSDRowDirectoryBatch.target q K dir c.val) k 1=
      CommonMSDDirectorySemantics.lengths q key
        (CommonMSDRowDirectory.slice (CommonMSDChunkRows.row q n c).offset
          (CommonMSDChunkRows.row q n c).length (CommonMSDChunkRows.row q n c).fits f) k

theorem directories_raw (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk r.source f) :
    let out := (executeRaw q (CommonMSDRowDirectoryBatch.code q reader hfit key (CommonMSDChunkRows.row q n)
      r.source r.buffer (directory q r.buffer) (List.finRange (CommonMSDChunks.chunkCount q n))) s).1.disk
    Ready q key r.source (directory q r.buffer) out f ∧
    (∀ a : Fin (q.N^q.exponent),(a.val<r.buffer ∨ r.limit≤a.val) → out a=s.disk a) := by
  obtain ⟨hout,hstarts,hcounts,hframes⟩ := CommonMSDRowDirectoryBatch.raw_complete q reader hfit key
    (CommonMSDChunkRows.row q n) r.source r.buffer (directory q r.buffer) (CommonMSDChunks.chunkSize q)
    (CommonMSDChunkRows.length_le q n) r.source_before le_rfl
    (r.directory_space.trans r.capacity) r.counters (List.finRange (CommonMSDChunks.chunkCount q n))
    (List.nodup_finRange _) s f hf
  refine ⟨⟨hout,fun c k=>hstarts c (by simp) k,fun c k=>hcounts c (by simp) k⟩,?_⟩
  intro a hb
  have hdir : directory q r.buffer≤r.limit := by have:=r.directory_space;omega
  apply hframes a (by
    rcases hb with hb|hb
    · exact Or.inl hb
    · exact Or.inr (by change directory q r.buffer≤a.val;omega))
  intro c _
  have hend := CommonMSDRowDirectoryBatch.target_end q (K:=K) (base:=directory q r.buffer) c
  have hlo : r.buffer≤CommonMSDRowDirectoryBatch.target q K (directory q r.buffer) c.val := by
    unfold CommonMSDRowDirectoryBatch.target directory
    omega
  have hfit := r.directory_space
  rcases hb with hb|hb
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem raw_with_chunks (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (p : Program q n r.source r.buffer r.limit (CommonMSDChunks.operation q n))
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk r.source f) :
    let out := (executeRaw q (withChunks q reader r p hfit key) s).1.disk
    Ready q key r.source (directory q r.buffer) out (CommonMSDChunks.operation q n f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<r.source ∨ r.source+recordBlocks q n≤a.val) →
      (a.val<r.buffer ∨ r.limit≤a.val) → out a=s.disk a) := by
  have h := directories_raw q reader r hfit key (executeRaw q p.instructions s).1
    (CommonMSDChunks.operation q n f) (p.correct s f hf)
  rw [withChunks,raw_append]
  exact ⟨h.1,fun a ha hb => (h.2 a hb).trans (p.frame s a ha hb)⟩

theorem raw_complete (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk r.source f) :
    let out := (executeRaw q (code q reader r hfit key) s).1.disk
    Ready q key r.source (directory q r.buffer) out (CommonMSDChunks.operation q n f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<r.source ∨ r.source+recordBlocks q n≤a.val) →
      (a.val<r.buffer ∨ r.limit≤a.val) → out a=s.disk a) :=
  raw_with_chunks q reader r (chunks q reader r) hfit key s f hf

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K) :
    ∀ i∈code q reader r hfit key,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact (chunks q reader r).safe i hi
  · exact CommonMSDRowDirectoryBatch.code_safe q reader hfit key _ _ _ _ _ i hi

theorem code_cost_le (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K) :
    cost q (code q reader r hfit key)≤charge (Normal:=Normal) q n K := by
  have hp : (chunks q reader r).charge≤ChunkSorter.charge (Normal:=Normal) q n :=
    ChunkSorter.program_charge_le q reader hnormal n r.exponent _ _ _ _ _ _ _
  rw [code,withChunks,cost_append,CommonMSDRowDirectoryBatch.code_cost q reader hfit key
    (CommonMSDChunkRows.row q n) r.source r.buffer (directory q r.buffer) (CommonMSDChunks.chunkSize q)
    (CommonMSDChunkRows.length_le q n) le_rfl (r.directory_space.trans r.capacity),List.length_finRange]
  exact Nat.add_le_add_right ((chunks q reader r).cost_le.trans hp) _

theorem code_length_le (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K) :
    (code q reader r hfit key).length≤lengthBound (Normal:=Normal) q n K := by
  have hp : (chunks q reader r).charge≤ChunkSorter.charge (Normal:=Normal) q n :=
    ChunkSorter.program_charge_le q reader hnormal n r.exponent _ _ _ _ _ _ _
  rw [code,withChunks,List.length_append,CommonMSDRowDirectoryBatch.code_length,List.length_finRange]
  have h := (chunks q reader r).length_le.trans hp
  unfold lengthBound
  omega

theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K : ℕ} (r : Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk r.source f)
    (hsize : lengthBound (Normal:=Normal) q n K≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := code q reader r hfit key
    let result := ControlledNormalization.runLogical (policy q p) p.length s
    Ready q key r.source (directory q r.buffer) result.1.disk (CommonMSDChunks.operation q n f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<r.source ∨ r.source+recordBlocks q n≤a.val) →
      (a.val<r.buffer ∨ r.limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p result.1.ram=none ∧ result.2≤charge (Normal:=Normal) q n K ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hDisk,hhalt,hcost,hm⟩ := run_code_disk q (code q reader r hfit key)
    ((code_length_le q reader r hfit key).trans hsize) (code_safe q reader r hfit key) s hpc
  obtain ⟨hout,hframe⟩ := raw_complete q reader r hfit key s f hf
  refine ⟨?_,?_,hhalt,?_,hm⟩
  · simpa only [hDisk] using hout
  · simpa only [hDisk] using hframe
  · exact hcost.trans_le (code_cost_le q reader r hfit key)

end
end CodedSorting.RadixNode.Pass
end Pass

section Controller
/-! Public finite control states for one MSD node. The first body creates
the sorted rows and their actual disk directory. Subsequent bodies read
that directory and copy its intervals through the existing gather loop. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.RadixNode.Controller
open WordControl CommonSortingNormalization CommonStaticSchedule RadixNode
open CommonLeafProgram (RAM)
noncomputable section
variable {Normal : Configuration → Prop} [ChunkSorter Normal]

abbrev Tag (F C : ℕ) := Option (CommonMSDGatherController.Tag F C)
abbrev tagCount (F C : ℕ) := Fintype.card (Tag F C)
def tagEquiv (F C : ℕ) : Tag F C≃Fin (tagCount F C) := Fintype.equivFin _

def body (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K F C : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (layout : CommonMSDGatherController.Layout F) : Tag F C→List (Instruction q)
  | none => RadixNode.Pass.code q reader r hfit key
  | some t => CommonMSDGatherController.body q reader layout t

def terminal {F C : ℕ} : Tag F C→Bool
  | none => false
  | some t => decide (F≤t.1.val)

def advance (q : Configuration) {F C : ℕ} (layout : CommonMSDGatherController.Layout F) :
    Tag F C→RAM q→Tag F C
  | none,_ => some (CommonMSDGatherController.ready 0 0)
  | some t,ram => some (CommonMSDGatherController.nextTag q layout t ram)

def code (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K F C : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (layout : CommonMSDGatherController.Layout F) (tag : Fin (tagCount F C)) :
    List (Instruction q) := body q reader r hfit key layout ((tagEquiv F C).symm tag)

def done {F C : ℕ} (tag : Fin (tagCount F C)) : Bool := terminal ((tagEquiv F C).symm tag)

def next (q : Configuration) {F C : ℕ} (layout : CommonMSDGatherController.Layout F)
    (tag : Fin (tagCount F C)) (ram : RAM q) : Fin (tagCount F C) :=
  tagEquiv F C (advance q layout ((tagEquiv F C).symm tag) ram)

theorem body_safe (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K F C : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (layout : CommonMSDGatherController.Layout F) (tag : Tag F C) :
    ∀ i∈body q reader r hfit key layout tag,RespectsPC q i := by
  cases tag with
  | none => exact RadixNode.Pass.code_safe q reader r hfit key
  | some t => exact CommonMSDGatherController.body_safe q reader layout t

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K F C : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (layout : CommonMSDGatherController.Layout F) (tag : Fin (tagCount F C)) :
    ∀ i∈code q reader r hfit key layout tag,RespectsPC q i :=
  body_safe q reader r hfit key layout _

@[simp] theorem code_at (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K F C : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (layout : CommonMSDGatherController.Layout F) (tag : Tag F C) :
    code q reader r hfit key layout (tagEquiv F C tag)=body q reader r hfit key layout tag := by
  simp only [code,Equiv.symm_apply_apply]

@[simp] theorem done_at {F C : ℕ} (tag : Tag F C) : done (tagEquiv F C tag)=terminal tag := by
  simp only [done,Equiv.symm_apply_apply]

@[simp] theorem next_at (q : Configuration) {F C : ℕ} (layout : CommonMSDGatherController.Layout F)
    (tag : Tag F C) (ram : RAM q) :
    next q layout (tagEquiv F C tag) ram=tagEquiv F C (advance q layout tag ram) := by
  simp only [next,Equiv.symm_apply_apply]

def chosenStride (q : Configuration) (n K C : ℕ) :=
  max (RadixNode.Pass.lengthBound (Normal:=Normal) q n K+1) (CommonMSDGatherCapacity.chosenStride q C)

theorem code_length_lt (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K F C : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (layout : CommonMSDGatherController.Layout F) (tag : Fin (tagCount F C)) :
    (code q reader r hfit key layout tag).length<chosenStride (Normal:=Normal) q n K C := by
  unfold code
  cases (tagEquiv F C).symm tag with
  | none =>
      have h := RadixNode.Pass.code_length_le q reader r hfit key
      change (RadixNode.Pass.code q reader r hfit key).length<_
      exact (Nat.lt_succ_of_le h).trans_le (Nat.le_max_left _ _)
  | some t =>
      exact (CommonMSDGatherCapacity.body_length_lt q reader layout t).trans_le (Nat.le_max_right _ _)

end
end CodedSorting.RadixNode.Controller
end Controller

section Routine
/-! The complete node control family in the compositional routine format.
It can be embedded in a larger finite controller without capturing input
records or consulting a proof-side successful execution. -/
set_option autoImplicit false
namespace CodedSorting.RadixNode.Controller
open WordControl CommonSortingNormalization CommonStaticSchedule RadixNode
open CommonMSDRoutine
noncomputable section
variable {Normal : Configuration → Prop} [ChunkSorter Normal]

def routine (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K F C : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (layout : CommonMSDGatherController.Layout F) : Routine q (tagCount F C) where
  entry:=tagEquiv F C none
  body:=code q reader r hfit key layout
  next:=next q layout
  terminal:=done
  safe:=code_safe q reader r hfit key layout
  terminal_empty:=by
    intro tag ht
    unfold done at ht
    unfold code
    cases he : (tagEquiv F C).symm tag with
    | none => simp only [he,terminal,Bool.false_eq_true] at ht
    | some t =>
        simp only [he,terminal,decide_eq_true_eq] at ht
        simp only [body,CommonMSDGatherController.body,show ¬t.1.val<F by omega,↓reduceDIte]

theorem routine_fits (q : Configuration) (reader : Fin q.inventory.readers)
    {hnormal : Normal q} {n K F C : ℕ} (r : RadixNode.Pass.Resources q hnormal n K)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
    (layout : CommonMSDGatherController.Layout F)
    (hc : tagCount F C*chosenStride (Normal:=Normal) q n K C≤q.N^q.exponent) :
    (routine q reader r hfit key layout (C:=C)).Fits (chosenStride (Normal:=Normal) q n K C) :=
  ⟨code_length_lt q reader r hfit key layout,hc⟩

end
end CodedSorting.RadixNode.Controller
end Routine

section Trace
/-! The node's embedded gather executes the same read/copy bodies as the
verified gather loop. This trace is constructed from those actual bodies;
it is not a successful-execution assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace CodedSorting.RadixNode.Trace
open WordControl CommonSortingNormalization CommonStaticSchedule RadixNode
open CommonMSDRoutine RadixNode.Controller
open CommonLeafProgram (RAM Machine)
namespace G
abbrev Tag := CommonMSDGatherController.Tag
abbrev ready := @CommonMSDGatherController.ready
abbrev copying := @CommonMSDGatherController.copying
end G
noncomputable section
variable {Normal : Configuration → Prop} [ChunkSorter Normal]

theorem nextTag_setPC (q : Configuration) {F C : ℕ} (layout : CommonMSDGatherController.Layout F)
    (t : G.Tag F C) (ram : RAM q) (k : ℕ) :
    CommonMSDGatherController.nextTag q layout t (setPC q k ram)=
      CommonMSDGatherController.nextTag q layout t ram := by
  unfold CommonMSDGatherController.nextTag
  split
  · split
    · rfl
    · have hfield (e : ℕ) (f : Fin 2) :
          CommonMSDDirectoryRead.field q e f (unpack (setPC q k ram))=
            CommonMSDDirectoryRead.field q e f (unpack ram) := by
        unfold CommonMSDDirectoryRead.field CommonMSDDirectoryRead.fieldWords
        rw [(setPC_frame q k ram).1]
      simp only [hfield]
  · rfl

variable (q : Configuration) (reader : Fin q.inventory.readers)
variable {hnormal : Normal q} {n K F C : ℕ}
variable (r : RadixNode.Pass.Resources q hnormal n K)
variable (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q) (key : Word q.w→Fin K)
variable (layout : CommonMSDGatherController.Layout F)

theorem raw_some (t : G.Tag F C) (s : Machine q) :
    (routine q reader r hfit key layout (C:=C)).rawBody (tagEquiv F C (some t)) s=
      erasePC q (executeRaw q (CommonMSDGatherController.body q reader layout t) s).1 := by
  simp only [Routine.rawBody,routine,code_at,body]

theorem next_some (t : G.Tag F C) (s : Machine q) :
    (routine q reader r hfit key layout (C:=C)).nextTag (tagEquiv F C (some t)) s=
      tagEquiv F C (some (CommonMSDGatherController.nextTag q layout t
        (executeRaw q (CommonMSDGatherController.body q reader layout t) s).1.ram)) := by
  unfold Routine.nextTag
  rw [raw_some]
  simp only [Routine.successor,routine,next_at,advance,erasePC,
    setPC_setPC,nextTag_setPC]

theorem read_payload (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) :
    (routine q reader r hfit key layout (C:=C)).rawBody
      (tagEquiv F C (some (G.ready j.castSucc D))) s=
      erasePC q (CommonMSDGatherRun.afterRead q reader layout stride j D s) := by
  rw [raw_some,CommonMSDGatherController.body_ready]
  have he := CommonTaggedSchedule.execute_payload q stride
    (CommonMSDGatherController.tagEquiv F C (G.ready j.castSucc D)).val 0
    (CommonMSDDirectoryRead.code q (layout.directory j) (layout.entry j))
    (CommonMSDDirectoryRead.code_safe q _ _) s s rfl
  unfold CommonMSDGatherRun.afterRead CommonMSDGatherRun.readBody
  dsimp only
  rw [CommonMSDGatherController.next_ready]
  simp only [erasePC,setPC_setPC]
  exact he.symm

theorem copy_payload (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) :
    let p := CommonMSDGatherRun.observed q reader layout stride j D s
    (routine q reader r hfit key layout (C:=C)).rawBody
      (tagEquiv F C (some (G.copying j D p.1 p.2)))
      (CommonMSDGatherRun.afterRead q reader layout stride j D s)=
      erasePC q (CommonMSDGatherRun.afterCopy q reader layout stride j D s) := by
  dsimp only
  rw [raw_some,CommonMSDGatherController.body_copying]
  let p := CommonMSDGatherRun.observed q reader layout stride j D s
  have he := CommonTaggedSchedule.execute_payload q stride
    (CommonMSDGatherController.tagEquiv F C (G.copying j D p.1 p.2)).val 0
    (CommonIntervalCopy.code q reader p.1.val D.val p.2.val (layout.source j) layout.target)
    (CommonIntervalCopy.code_safe q reader _ _ _ _ _)
    (CommonMSDGatherRun.afterRead q reader layout stride j D s)
    (CommonMSDGatherRun.afterRead q reader layout stride j D s) rfl
  unfold CommonMSDGatherRun.afterCopy CommonMSDGatherRun.copyBody
  dsimp only
  rw [CommonMSDGatherController.next_copying]
  simp only [erasePC,setPC_setPC]
  exact he.symm

theorem read_next (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) :
    (routine q reader r hfit key layout (C:=C)).nextTag
      (tagEquiv F C (some (G.ready j.castSucc D))) s=
      tagEquiv F C (some (G.copying j D
        (CommonMSDGatherRun.observed q reader layout stride j D s).1
        (CommonMSDGatherRun.observed q reader layout stride j D s).2)) := by
  unfold Routine.nextTag
  rw [read_payload q reader r hfit key layout stride]
  simp only [Routine.successor,routine,next_at,advance,erasePC,setPC_setPC,nextTag_setPC]
  unfold CommonMSDGatherRun.afterRead
  dsimp only
  rw [CommonMSDGatherController.next_ready,nextTag_setPC]
  simp only [CommonMSDGatherController.nextTag,G.ready,CommonMSDGatherController.ready,
    Fin.coe_castSucc,j.isLt,↓reduceDIte,Bool.false_eq_true,↓reduceIte,
    CommonMSDGatherRun.observed,G.copying]

theorem copy_next (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) :
    let p := CommonMSDGatherRun.observed q reader layout stride j D s
    (routine q reader r hfit key layout (C:=C)).nextTag
      (tagEquiv F C (some (G.copying j D p.1 p.2)))
      (CommonMSDGatherRun.afterRead q reader layout stride j D s)=
      tagEquiv F C (some (G.ready (CommonMSDGatherRun.nextIndex j)
        (CommonMSDGatherRun.nextDest q reader layout stride j D s))) := by
  dsimp only
  rw [next_some]
  simp only [CommonMSDGatherController.nextTag,G.copying,CommonMSDGatherController.copying,
    Fin.coe_castSucc,j.isLt,↓reduceDIte,↓reduceIte,CommonMSDGatherRun.nextDest,
    G.ready,CommonMSDGatherRun.nextIndex]

/-- Every gather trace is generated here from actual read/copy bodies.
It therefore embeds in the node routine without an execution premise. -/
theorem gather_trace_from (stride fuel : ℕ) (j : Fin (F+1)) (D : Fin (C+1))
    (s : Machine q) (hcount : j.val+fuel=F) :
    let out := CommonMSDGatherRun.observe q reader layout stride fuel j D s
    (routine q reader r hfit key layout (C:=C)).Trace
      (tagEquiv F C (some (G.ready j D))) s
      (tagEquiv F C (some (G.ready ⟨F,by omega⟩ out.destination)))
      (erasePC q out.machine) out.steps out.charge := by
  induction fuel generalizing j D s with
  | zero =>
      have hj : j=(⟨F,Nat.lt_succ_self F⟩ : Fin (F+1)) :=
        Fin.ext (by change j.val=F;simpa only [Nat.add_zero] using hcount)
      subst j
      exact Routine.Trace.done _ s (by simp [routine,done_at,terminal,G.ready,CommonMSDGatherController.ready])
  | succ fuel ih =>
      have hj : j.val<F := by omega
      let i : Fin F := ⟨j.val,hj⟩
      have hij : i.castSucc=j := Fin.ext rfl
      let p := CommonMSDGatherRun.observed q reader layout stride i D s
      let afterRead := CommonMSDGatherRun.afterRead q reader layout stride i D s
      let afterCopy := CommonMSDGatherRun.afterCopy q reader layout stride i D s
      let out := CommonMSDGatherRun.observe q reader layout stride fuel
        (CommonMSDGatherRun.nextIndex i) (CommonMSDGatherRun.nextDest q reader layout stride i D s) afterCopy
      let nr := routine q reader r hfit key layout (C:=C)
      let finalTag := tagEquiv F C (some (G.ready ⟨F,Nat.lt_succ_self F⟩ out.destination))
      have tail : nr.Trace (tagEquiv F C (some (G.ready (CommonMSDGatherRun.nextIndex i)
          (CommonMSDGatherRun.nextDest q reader layout stride i D s)))) afterCopy
          finalTag (erasePC q out.machine) out.steps out.charge :=
        ih (CommonMSDGatherRun.nextIndex i) _ afterCopy (by
          dsimp only [CommonMSDGatherRun.nextIndex,i];omega)
      have copyTail : nr.Trace (nr.nextTag (tagEquiv F C (some (G.copying i D p.1 p.2))) afterRead)
          (nr.rawBody (tagEquiv F C (some (G.copying i D p.1 p.2))) afterRead)
          finalTag (erasePC q out.machine) out.steps out.charge := by
        rw [copy_next q reader r hfit key layout stride]
        apply nr.trace_congr tail
        rw [copy_payload q reader r hfit key layout stride]
        simp only [erasePC,setPC_setPC,afterCopy]
      have copyTrace := Routine.Trace.step (r:=nr)
        (tagEquiv F C (some (G.copying i D p.1 p.2))) finalTag afterRead
        (erasePC q out.machine) out.steps out.charge
        (by simp [nr,routine,done_at,terminal,G.copying,CommonMSDGatherController.copying,i.isLt]) copyTail
      have readTail : nr.Trace (nr.nextTag (tagEquiv F C (some (G.ready i.castSucc D))) s)
          (nr.rawBody (tagEquiv F C (some (G.ready i.castSucc D))) s) finalTag
          (erasePC q out.machine)
          ((nr.body (tagEquiv F C (some (G.copying i D p.1 p.2)))).length+1+out.steps)
          (cost q (nr.body (tagEquiv F C (some (G.copying i D p.1 p.2))))+out.charge) := by
        rw [read_next q reader r hfit key layout stride]
        apply nr.trace_congr copyTrace
        rw [read_payload q reader r hfit key layout stride]
        simp only [erasePC,setPC_setPC,afterRead]
      have readTrace := Routine.Trace.step (r:=nr)
        (tagEquiv F C (some (G.ready i.castSucc D))) finalTag s (erasePC q out.machine)
        _ _ (by simp [nr,routine,done_at,terminal,G.ready,CommonMSDGatherController.ready,i.isLt]) readTail
      simp only [nr,routine,code_at,body,G.ready,G.copying,CommonMSDGatherController.body_ready,
        CommonMSDGatherController.body_copying] at readTrace
      rw [hij] at readTrace
      simpa only [CommonMSDGatherRun.observe,dif_pos hj,CommonMSDGatherRun.cycleSteps,
        CommonMSDGatherRun.cycleCost,Nat.add_assoc,i,p,afterCopy,afterRead,out,finalTag] using readTrace

end
end CodedSorting.RadixNode.Trace
end Trace

section Head
/-! An opaque proof boundary for the actual preparation body followed by
the directory-reading gather trace. The fragment count stays abstract. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace CodedSorting.RadixNode.Head
open WordControl CommonSortingNormalization CommonStaticSchedule RadixNode
open CommonMSDRoutine RadixNode.Controller
open CommonLeafProgram (Machine)
noncomputable section
variable {Normal : Configuration → Prop} [ChunkSorter Normal]
attribute [local irreducible] RadixNode.Pass.code RadixNode.Pass.chunks
  CommonMSDGatherRun.observe executeRaw

variable (q : Configuration) (reader : Fin q.inventory.readers)
variable {hnormal : Normal q} {n K F C : ℕ}
variable (r : RadixNode.Pass.Resources q hnormal n K)
variable (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
variable (key : Word q.w→Fin K) (layout : CommonMSDGatherController.Layout F)

theorem prepend (s : Machine q) (finalTag : Fin (tagCount F C))
    (final : Machine q) (steps charge : ℕ)
    (tail : (routine q reader r hfit key layout (C:=C)).Trace
      (tagEquiv F C (some (CommonMSDGatherController.ready 0 0)))
      (erasePC q (executeRaw q (RadixNode.Pass.code q reader r hfit key) s).1)
      finalTag final steps charge) :
    (routine q reader r hfit key layout (C:=C)).Trace
      (routine q reader r hfit key layout (C:=C)).entry s finalTag final
      ((RadixNode.Pass.code q reader r hfit key).length+1+steps)
      (cost q (RadixNode.Pass.code q reader r hfit key)+charge) := by
  let nr := routine q reader r hfit key layout (C:=C)
  have hbody : nr.rawBody nr.entry s=
      erasePC q (executeRaw q (RadixNode.Pass.code q reader r hfit key) s).1 := by
    simp only [nr,routine,Routine.rawBody,code_at,body]
  have hnext : nr.nextTag nr.entry s=tagEquiv F C
      (some (CommonMSDGatherController.ready 0 0)) := by
    simp only [Routine.nextTag,Routine.successor,nr,routine,next_at,advance]
  have hdone : nr.terminal nr.entry=false := by
    simp only [nr,routine,done_at,terminal]
  have hcode : nr.body nr.entry=RadixNode.Pass.code q reader r hfit key := by
    simp only [nr,routine,code_at,body]
  have ht : nr.Trace (nr.nextTag nr.entry s) (nr.rawBody nr.entry s)
      finalTag final steps charge := by
    rw [hbody,hnext]
    exact tail
  simpa only [hcode] using Routine.Trace.step nr.entry finalTag s final steps charge hdone ht

theorem trace (stride : ℕ) (s : Machine q) :
    let mid := erasePC q (executeRaw q (RadixNode.Pass.code q reader r hfit key) s).1
    let out := CommonMSDGatherRun.observe q reader layout stride F 0 (0 : Fin (C+1)) mid
    (routine q reader r hfit key layout (C:=C)).Trace
      (routine q reader r hfit key layout (C:=C)).entry s
      (tagEquiv F C (some (CommonMSDGatherController.ready ⟨F,by omega⟩ out.destination)))
      (erasePC q out.machine)
      ((RadixNode.Pass.code q reader r hfit key).length+1+out.steps)
      (cost q (RadixNode.Pass.code q reader r hfit key)+out.charge) := by
  apply prepend q reader r hfit key layout s
  exact RadixNode.Trace.gather_trace_from q reader r hfit key layout stride F 0
    (0 : Fin (C+1)) _ (by simp)

end
end CodedSorting.RadixNode.Head
end Head

namespace CodedSorting.CommonMSDNodePass
noncomputable instance : CodedSorting.RadixNode.ChunkSorter
    CodedSorting.CommonPrunedParameters.Normalized where
  space := CodedSorting.CommonMSDChunks.space
  charge := CodedSorting.CommonMSDChunks.charge
  program := CodedSorting.CommonMSDChunks.program
  program_charge_le := CodedSorting.CommonMSDChunks.program_charge_le
end CodedSorting.CommonMSDNodePass

namespace CodedSorting.CommonMSDNodePass
open CodedSorting.CommonSortingNormalization
export CodedSorting.RadixNode.Pass (
  directory Resources chunks withChunks code directoryCharge
  Ready directories_raw raw_with_chunks raw_complete code_safe code_cost_le
  code_length_le complete)
noncomputable def charge (q : Configuration) (n K : ℕ) : ℕ := CommonMSDChunks.charge q n+directoryCharge q n K
noncomputable def lengthBound (q : Configuration) (n K : ℕ) : ℕ :=
  CommonMSDChunks.charge q n+
    7*CommonMSDRowDirectoryBatch.rowBlocks q (CommonMSDChunkRows.row q n)
      (List.finRange (CommonMSDChunks.chunkCount q n))+
    (2*CommonMSDDirectory.blocks q K+2)*CommonMSDChunks.chunkCount q n
end CodedSorting.CommonMSDNodePass

namespace CodedSorting.CommonMSDNodeController
open CodedSorting.CommonSortingNormalization
export CodedSorting.RadixNode.Controller (
  Tag tagCount tagEquiv body terminal advance
  code done next body_safe code_safe code_at
  done_at next_at code_length_lt)
noncomputable def chosenStride (q : Configuration) (n K C : ℕ) :=
  max (CommonMSDNodePass.lengthBound q n K+1) (CommonMSDGatherCapacity.chosenStride q C)
end CodedSorting.CommonMSDNodeController

namespace CodedSorting.CommonMSDNodeController
export CodedSorting.RadixNode.Controller (
  routine routine_fits)
end CodedSorting.CommonMSDNodeController

namespace CodedSorting.CommonMSDNodeTrace
export CodedSorting.RadixNode.Trace (
  nextTag_setPC raw_some next_some read_payload copy_payload read_next
  copy_next gather_trace_from)
namespace G
export CodedSorting.RadixNode.Trace.G (Tag ready copying)
end G
end CodedSorting.CommonMSDNodeTrace

namespace CodedSorting.CommonMSDNodeHead
export CodedSorting.RadixNode.Head (
  prepend trace)
end CodedSorting.CommonMSDNodeHead

section TagBound
/-! A single public finite tag space contains every node routine of an
input of at most N records, including extraction and restoration phases. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDNodeTagBound
open CommonSortingNormalization CommonMSDNodeController
noncomputable section

def bound (q : Configuration) (K : ℕ) : ℕ :=
  tagCount (K*q.N) (3*q.N)+3

theorem card_formula (F C : ℕ) : tagCount F C=1+2*(F+1)*(C+1)^3 := by
  simp only [tagCount,Tag,CommonMSDGatherController.Tag,Fintype.card_option,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

theorem card_mono {F G C D : ℕ} (hf : F≤G) (hc : C≤D) :
    tagCount F C≤tagCount G D := by
  rw [card_formula,card_formula]
  exact Nat.add_le_add_left (Nat.mul_le_mul
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hf 1))
    (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 3)) 1

theorem node_fits (q : Configuration) (K n : ℕ) (hn : n≤q.N) :
    tagCount (K*CommonMSDChunks.chunkCount q n) (3*n)+3≤bound q K := by
  apply Nat.add_le_add_right
  apply card_mono
  · exact Nat.mul_le_mul_left K ((CommonMSDChunkRows.count_le q n).trans hn)
  · exact Nat.mul_le_mul_left 3 hn

theorem bound_positive (q : Configuration) (K : ℕ) : 0<bound q K := by
  unfold bound
  omega

end
end CodedSorting.CommonMSDNodeTagBound
end TagBound
