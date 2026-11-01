import CodedSorting.Shared.Memory.PhysicalFileHandles

section AllocatedDirectory
/-! Allocated file handles on the common word disk. The statements below
connect actual invocation spans with finite descriptors, preserve every
directory alias across writes to fresh slots, and reserve a separate stack
prefix without changing the word size. They do not replace scanner execution
or recursive scheduling with a whole-file copying instruction. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace CodedSorting.AllocatedDirectory
open PhysicalFileHandles WorkspaceAllocation WordControl

def fromSpan (N e : ℕ) (span : Span) (records : ℕ)
    (hb : span.start≤N^e) (hr : records≤N^e) : Handle N e :=
  ⟨⟨span.start,by omega⟩,⟨records,by omega⟩⟩

theorem fromSpan_fits (N e B : ℕ) (span : Span) (records : ℕ)
    (hb : span.start≤N^e) (hr : records≤N^e)
    (hcap : PhysicalStreamCursor.blockCount B records≤span.blocks) :
    Fits B (fromSpan N e span records hb hr) span := ⟨rfl,hcap⟩

theorem fromSpan_base (N e : ℕ) (span : Span) (records : ℕ)
    (hb : span.start≤N^e) (hr : records≤N^e) :
    (fromSpan N e span records hb hr).base.val=span.start := rfl

theorem fromSpan_records (N e : ℕ) (span : Span) (records : ℕ)
    (hb : span.start≤N^e) (hr : records≤N^e) :
    (fromSpan N e span records hb hr).records.val=records := rfl

def shiftSpan (offset : ℕ) (s : Span) : Span := ⟨offset+s.start,s.blocks⟩

theorem shiftSpan_stop (offset : ℕ) (s : Span) :
    (shiftSpan offset s).stop=offset+s.stop := by simp [shiftSpan,Span.stop,Nat.add_assoc]

/-- A polynomial stack prefix and polynomial data area fit another fixed
polynomial. The additional exponent is explicit and independent of input. -/
theorem shifted_polynomial_bound (N a b offset : ℕ) (hN : 2≤N) (s : Span)
    (ho : offset≤N^a) (hs : s.stop≤N^b) :
    (shiftSpan offset s).stop≤N^(max a b+1) := by
  have ha := Nat.pow_le_pow_right (by omega : 0<N) (Nat.le_max_left a b)
  have hb := Nat.pow_le_pow_right (by omega : 0<N) (Nat.le_max_right a b)
  have hc : offset+s.stop≤2*N^(max a b) := by omega
  rw [shiftSpan_stop,pow_succ]
  exact hc.trans (by nlinarith [Nat.mul_le_mul_right (N^(max a b)) hN])

theorem shiftSpan_after_stack (offset : ℕ) (s : Span) : offset≤(shiftSpan offset s).start :=
  Nat.le_add_right _ _

theorem shiftSpan_disjoint (offset : ℕ) {s t : Span} (h : Before s t) :
    Before (shiftSpan offset s) (shiftSpan offset t) := by
  simpa only [Before,shiftSpan,Span.stop,Nat.add_assoc] using Nat.add_le_add_left h offset

section ActualInvocation
open RecursiveExchange
open InvocationWorkspaceBound
noncomputable section

theorem actual_span_handle (C base cutoff k rows B records : ℕ) (hb : 0<base)
    (leaf : ℕ→ℕ) (charge : ℕ→ℕ→ℕ)
    {P G Z : Type} [Fintype P] [Fintype G] [Fintype Z]
    (layout : P≃Fin (rows*Parameters.W^k))
    (hV : 0<Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z))
    (file : Span)
    (hf : file∈files C (cutoffExchange base cutoff leaf charge k rows (Gap := G) (Suffix := Z) layout).calls)
    (hr : records≤Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z))
    (hcap : PhysicalStreamCursor.blockCount B records≤file.blocks) :
    ∃ h : Handle (Fintype.card (Address.FullAddress P (Scalar (base*Parameters.m^k)) G Z)) (exponent C),
      h.base.val=file.start ∧ h.records.val=records ∧ Fits B h file := by
  have hs := actual_span_bound C base cutoff k rows hb leaf charge layout hV file hf
  have he : 1≤exponent C := by unfold exponent; omega
  have hp := Nat.pow_le_pow_right hV he
  rw [pow_one] at hp
  let result := fromSpan _ (exponent C) file records hs.1 (hr.trans hp)
  exact ⟨result,rfl,rfl,fromSpan_fits _ _ _ _ _ hs.1 (hr.trans hp) hcap⟩

end
end ActualInvocation

section Directories
variable {N e B w : ℕ} {Key : Type*}

/-- Several entries may point at the same span. All remain valid when a
different allocated target receives its actual sequence of block writes. -/
theorem writePrefix_preserves_directory (hB : 0<B*w)
    (dir : Directory N e Key) (locations : Key→Span)
    (hf : ∀ k,Fits (B*w) (dir k) (locations k))
    (target : Span) (hd : ∀ k,Before target (locations k) ∨ Before (locations k) target)
    (produce : Fin target.blocks→Fin B→Word w) (n : ℕ) (hn : n≤target.blocks)
    (disk : BlockDisk B w) :
    ∀ k,bitView hB (writePrefix target produce n hn disk) (dir k)=bitView hB disk (dir k) :=
  fun k => writePrefix_preserves_bitView hB target (locations k) (hd k) produce n hn disk (dir k) (hf k)

theorem directory_preserved_above (hB : 0<B*w) (disk disk' : BlockDisk B w)
    (dir : Directory N e Key) (limit : ℕ)
    (hb : ∀ k,limit≤(dir k).base.val) (hd : ∀ a,limit≤a→disk' a=disk a) :
    ∀ k,bitView hB disk' (dir k)=bitView hB disk (dir k) :=
  fun k => bitView_preserved_above hB disk disk' (dir k) limit (hb k) hd

variable [DecidableEq Key]

/-- Installation updates only the selected directory entry. Its new view
is the stream actually present in the written target; every old alias to a
different span continues to denote the old stream. -/
theorem install_written_file (hB : 0<B*w)
    (dir : Directory N e Key) (locations : Key→Span)
    (hf : ∀ k,Fits (B*w) (dir k) (locations k))
    (target : Span) (hd : ∀ k,Before target (locations k) ∨ Before (locations k) target)
    (produce : Fin target.blocks→Fin B→Word w) (n : ℕ) (hn : n≤target.blocks)
    (disk : BlockDisk B w) (files : Key→PhysicalRecursiveExchange.File)
    (hr : Represents hB disk dir files) (key : Key) (handle : Handle N e) :
    let disk' := writePrefix target produce n hn disk
    Represents hB disk' (Function.update dir key handle)
      (Function.update files key (bitView hB disk' handle)) := by
  dsimp only
  intro k
  by_cases hk : k=key
  · subst k
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hk]
    exact (writePrefix_preserves_directory hB dir locations hf target hd produce n hn disk k).trans (hr k)

end Directories

section Contents
variable {N e B w : ℕ}

/-- Concrete cells of the common word disk determine the exact canonical
bit file consumed by the existing file interpreter. This is a specification
lemma; no payload packing is added to the runtime. -/
theorem bitView_of_cells (hB : 0<B*w) (disk : BlockDisk B w) (h : Handle N e)
    (F : Fin h.records.val→Circuit.Bit)
    (hc : ∀ i,BitWordPacking.blockBits B w (disk (h.base.val+i.val/(B*w)))
      ⟨i.val%(B*w),Nat.mod_lt _ hB⟩=F i) :
    bitView hB disk h=PhysicalRecursiveExchange.canonical (B*w) hB F := by
  unfold bitView fileView PhysicalRecursiveExchange.canonical
  congr 1
  apply congrArg List.ofFn
  funext i
  exact hc i

/-- Filling a target prefix with the actual produced word blocks gives the
canonical output view. Only the n writes in writePrefix are performed. -/
theorem written_cells (hB : 0<B*w) (target : Span) (produce : Fin target.blocks→Fin B→Word w)
    (n : ℕ) (hn : n≤target.blocks) (disk : BlockDisk B w) (h : Handle N e)
    (hb : h.base.val=target.start)
    (hcap : PhysicalStreamCursor.blockCount (B*w) h.records.val≤n)
    (F : Fin h.records.val→Circuit.Bit)
    (hc : ∀ (i : Fin h.records.val) (j : Fin target.blocks),j.val=i.val/(B*w) →
      BitWordPacking.blockBits B w (produce j) ⟨i.val%(B*w),Nat.mod_lt _ hB⟩=F i) :
    bitView hB (writePrefix target produce n hn disk) h=
      PhysicalRecursiveExchange.canonical (B*w) hB F := by
  apply bitView_of_cells
  intro i
  have hl : (i.val/(B*w))*(B*w)<h.records.val := (Nat.div_mul_le_self _ _).trans_lt i.isLt
  have hi := ((PhysicalStreamCursor.cursor_live_iff (B*w) h.records.val (i.val/(B*w)) hB).2 hl).trans_le hcap
  let j : Fin target.blocks := ⟨i.val/(B*w),hi.trans_le hn⟩
  rw [hb]
  change BitWordPacking.blockBits B w (writePrefix target produce n hn disk (target.start+j.val)) _=F i
  rw [writePrefix_at target produce n hn disk j hi]
  exact hc i j rfl

end Contents

end CodedSorting.AllocatedDirectory
end AllocatedDirectory

section PhysicalBlockCopy
/-! A fixed two-phase block-copy scanner on one shared physical disk.
The phase, source/destination bases, file length, and current block cursor
are all resident words. No list of source blocks is available to execution.
The public execution horizon is used only to state termination and cost. -/
set_option autoImplicit false
namespace CodedSorting.PhysicalBlockCopy
open WordControl PhysicalStreamCursor

structure State (B d w : ℕ) where
  source : Words d w
  target : Words d w
  records : Words d w
  cursor : Words d w
  phase : Word w
  buffer : Words B w
  disk : BlockDisk B w

def initial (B d w source target records cursor : ℕ)
    (buffer : Words B w) (disk : BlockDisk B w) : State B d w :=
  ⟨encodeNat d w source,encodeNat d w target,encodeNat d w records,
    encodeNat d w cursor,0,buffer,disk⟩

def phaseOne (w : ℕ) (hw : 0<w) : Word w :=
  ⟨1,Nat.one_lt_pow (by omega : w≠0) (by decide)⟩

/-- Phase 0 reads or halts at EOF. Phase 1 writes the transfer bank and
advances the encoded cursor. Each transition issues at most one disk I/O. -/
def step {B d w : ℕ} (hw : 0<w) (s : State B d w) : State B d w × ℕ :=
  let cursor := decodeWords s.cursor
  if s.phase.val=0 then
    if cursor*B<decodeWords s.records then
      ({s with phase := phaseOne w hw, buffer := s.disk (decodeWords s.source+cursor)},1)
    else (s,0)
  else
    ({s with phase := 0, cursor := encodeNat d w (cursor+1), disk := writeBlock s.disk (decodeWords s.target+cursor) s.buffer},1)

def run {B d w : ℕ} (hw : 0<w) : ℕ → State B d w → State B d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
    let next := step hw s
    let result := run hw fuel next.1
    (result.1,next.2+result.2)

theorem step_cost {B d w : ℕ} (hw : 0<w) (s : State B d w) : (step hw s).2≤1 := by
  unfold step
  split
  · dsimp only
    split <;> simp
  · simp

theorem step_records {B d w : ℕ} (hw : 0<w) (s : State B d w) :
    (step hw s).1.records=s.records := by
  unfold step
  dsimp only
  split <;> try rfl
  split <;> rfl

theorem run_records {B d w : ℕ} (hw : 0<w) (fuel : ℕ) (s : State B d w) :
    (run hw fuel s).1.records=s.records := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [run]
    exact (ih _).trans (step_records hw s)

/-- Reference to the actual successive disk writes, not a parallel copy
that would grant free simultaneous access to all source blocks. -/
def copyDisk {B w : ℕ} (source target : ℕ) :
    ℕ → ℕ → BlockDisk B w → BlockDisk B w
  | _,0,disk => disk
  | cursor,left+1,disk => copyDisk source target (cursor+1) left
      (writeBlock disk (target+cursor) (disk (source+cursor)))

theorem two_steps (B d w source target records cursor : ℕ) (hw : 0<w)
    (buffer : Words B w) (disk : BlockDisk B w)
    (hs : source<(2^w)^d) (ht : target<(2^w)^d)
    (hn : records<(2^w)^d) (hc : cursor<(2^w)^d)
    (hlive : cursor*B<records) :
    run hw 2 (initial B d w source target records cursor buffer disk) =
      (initial B d w source target records (cursor+1) (disk (source+cursor))
        (writeBlock disk (target+cursor) (disk (source+cursor))),2) := by
  simp only [run,step,initial,decodeNat_encode d w source hs,
    decodeNat_encode d w target ht,decodeNat_encode d w records hn,
    decodeNat_encode d w cursor hc]
  simp only [Fin.val_zero,phaseOne,hlive,↓reduceIte,one_ne_zero,Nat.add_zero]
  simp only [decodeNat_encode d w cursor hc,decodeNat_encode d w target ht]

/-- Disk and cursor refinement for the whole loop. The post-cursor range
is explicit, preventing modular wrap at the last iteration. -/
theorem run_pairs (B d w source target records cursor left : ℕ)
    (hw : 0<w) (hB : 0<B) (buffer : Words B w) (disk : BlockDisk B w)
    (hs : source<(2^w)^d) (ht : target<(2^w)^d) (hn : records<(2^w)^d)
    (hlimit : cursor+left≤blockCount B records) (hc : cursor+left<(2^w)^d) :
    let result := run hw (2*left) (initial B d w source target records cursor buffer disk)
    result.1.disk=copyDisk source target cursor left disk ∧
    decodeWords result.1.cursor=cursor+left ∧ result.1.phase=0 ∧ result.2=2*left := by
  induction left generalizing cursor buffer disk with
  | zero =>
    simp only [Nat.mul_zero,run,initial,copyDisk,Nat.add_zero] at *
    exact ⟨True.intro,decodeNat_encode d w cursor hc,True.intro,True.intro⟩
  | succ left ih =>
    have hlive := (cursor_live_iff B records cursor hB).1 (by omega)
    have hcur : cursor<(2^w)^d := by omega
    have hp := two_steps B d w source target records cursor hw buffer disk hs ht hn hcur hlive
    have hnext := ih (cursor+1) (disk (source+cursor))
      (writeBlock disk (target+cursor) (disk (source+cursor))) (by omega) (by omega)
    have hrun : run hw (2*(left+1)) (initial B d w source target records cursor buffer disk) =
        let result := run hw (2*left)
          (initial B d w source target records (cursor+1) (disk (source+cursor))
            (writeBlock disk (target+cursor) (disk (source+cursor))))
        (result.1,2+result.2) := by
      have hnstep : 2*(left+1)=2*left+2 := by omega
      rw [hnstep]
      simp only [run] at hp ⊢
      have hstate := congrArg Prod.fst hp
      have hcost := congrArg Prod.snd hp
      dsimp only at hstate hcost ⊢
      rw [hstate]
      congr 1
      omega
    dsimp only
    rw [hrun]
    dsimp only at hnext ⊢
    exact ⟨hnext.1,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hnext.2.1,
      hnext.2.2.1,by omega⟩

theorem copyDisk_outside {B w : ℕ} (source target cursor left : ℕ)
    (disk : BlockDisk B w) (address : ℕ)
    (ha : address<target+cursor ∨ target+cursor+left≤address) :
    copyDisk source target cursor left disk address=disk address := by
  induction left generalizing cursor disk with
  | zero => rfl
  | succ left ih =>
    rw [copyDisk,ih (cursor+1) _ (by omega)]
    simp only [writeBlock,if_neg (show address≠target+cursor by omega)]

/-- Ordinary disjoint source and target intervals prevent read-after-write
corruption throughout the concrete sequential loop. -/
theorem copyDisk_at {B w : ℕ} (source target count cursor left : ℕ)
    (disk : BlockDisk B w) (hbound : cursor+left≤count)
    (hdisjoint : ∀ i j,i<count → j<count → source+i≠target+j)
    (i : ℕ) (hi : cursor ≤ i ∧ i < cursor+left) :
    copyDisk source target cursor left disk (target+i)=disk (source+i) := by
  induction left generalizing cursor disk with
  | zero => omega
  | succ left ih =>
    rw [copyDisk]
    by_cases he : i=cursor
    · subst i
      rw [copyDisk_outside source target (cursor+1) left _ (target+cursor) (Or.inl (by omega))]
      simp [writeBlock]
    · rw [ih (cursor+1) _ (by omega) ⟨by omega,by omega⟩]
      simp only [writeBlock,if_neg (hdisjoint i cursor (by omega) (by omega))]

/-- Complete aligned file-copy correctness, with exactly two transfers per
physical source block. The final partial block is copied with its padding;
the public record count retains its original logical length. -/
theorem complete_copy (B d w source target records : ℕ)
    (hw : 0<w) (hB : 0<B) (buffer : Words B w) (disk : BlockDisk B w)
    (hs : source<(2^w)^d) (ht : target<(2^w)^d) (hn : records<(2^w)^d)
    (hc : blockCount B records<(2^w)^d)
    (hdisjoint : ∀ i j,i<blockCount B records → j<blockCount B records → source+i≠target+j) :
    let result := run hw (2*blockCount B records)
      (initial B d w source target records 0 buffer disk)
    result.2=2*blockCount B records ∧
    (∀ i,i<blockCount B records → result.1.disk (target+i)=disk (source+i)) ∧
    (∀ address,address<target ∨ target+blockCount B records≤address →
      result.1.disk address=disk address) := by
  have hr := run_pairs B d w source target records 0 (blockCount B records)
    hw hB buffer disk hs ht hn (by omega) (by omega)
  dsimp only at hr ⊢
  refine ⟨hr.2.2.2,?_,?_⟩
  · intro i hi
    rw [hr.1]
    exact copyDisk_at source target (blockCount B records) 0 (blockCount B records)
      disk (by omega) hdisjoint i ⟨Nat.zero_le _,by omega⟩
  · intro address ha
    rw [hr.1]
    exact copyDisk_outside source target 0 (blockCount B records) disk address (by simpa using ha)

/-- The bounded execution really reaches the EOF branch of the same fixed
machine; further steps perform no I/O and leave its state unchanged. -/
theorem complete_halts (B d w source target records : ℕ)
    (hw : 0<w) (hB : 0<B) (buffer : Words B w) (disk : BlockDisk B w)
    (hs : source<(2^w)^d) (ht : target<(2^w)^d) (hn : records<(2^w)^d)
    (hc : blockCount B records<(2^w)^d) :
    let result := run hw (2*blockCount B records)
      (initial B d w source target records 0 buffer disk)
    step hw result.1=(result.1,0) := by
  have hr := run_pairs B d w source target records 0 (blockCount B records)
    hw hB buffer disk hs ht hn (by omega) (by omega)
  have hend : ¬blockCount B records*B<records := by
    rw [←cursor_live_iff B records (blockCount B records) hB]
    omega
  dsimp only at hr ⊢
  have hrn : decodeWords (run hw (2*blockCount B records)
      (initial B d w source target records 0 buffer disk)).1.records=records := by
    rw [run_records]
    exact decodeNat_encode d w records hn
  unfold step
  rw [hr.2.2.1]
  simp only [Fin.val_zero,↓reduceIte]
  rw [hr.2.1,hrn]
  simp only [Nat.zero_add,hend,↓reduceIte]

/-- Exactly the resident descriptor/phase/buffer fields of State, excluding
its external disk. Uniform code is the single step function above. -/
abbrev ResidentWords (B d w : ℕ) :=
  Words d w × Words d w × Words d w × Words d w × Word w × Words B w

def resident {B d w : ℕ} (s : State B d w) : ResidentWords B d w :=
  (s.source,s.target,s.records,s.cursor,s.phase,s.buffer)

theorem resident_count (B d w : ℕ) :
    Fintype.card (ResidentWords B d w)=(2^w)^(4*d+1+B) := by
  simp only [ResidentWords,Words,Word,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  ring

/-- There is no additional persistent phase, earlier buffer snapshot, or
input-dependent program hidden outside the declared resident fields. -/
theorem state_recover {B d w : ℕ} (s t : State B d w)
    (hr : resident s=resident t) (hd : s.disk=t.disk) : s=t := by
  cases s
  cases t
  simp only [resident,Prod.mk.injEq] at hr
  rcases hr with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  cases hd
  rfl

end CodedSorting.PhysicalBlockCopy
end PhysicalBlockCopy

section PhysicalFileHandlesXor
/-! A uniform XOR scanner on the same B-word disk as allocated files.
Only five encoded counters, two phase words and three B-word buffers are
resident. Each live block takes two physical reads and one physical write.
The external execution horizon appears only in the termination theorem.
-/
set_option autoImplicit false
namespace CodedSorting.PhysicalFileHandlesXor
open WordControl PhysicalStreamCursor Circuit

def xorBlock {B w : ℕ} (a b : Words B w) : Words B w :=
  (BitWordPacking.blockBits B w).symm
    (fun i => BitWordPacking.blockBits B w a i+BitWordPacking.blockBits B w b i)

@[simp] theorem xorBlock_bits {B w : ℕ} (a b : Words B w) (i : Fin (B*w)) :
    BitWordPacking.blockBits B w (xorBlock a b) i=
      BitWordPacking.blockBits B w a i+BitWordPacking.blockBits B w b i := by
  simp only [xorBlock,Equiv.apply_symm_apply]

structure State (B d w : ℕ) where
  sourceLeft : Words d w
  sourceRight : Words d w
  target : Words d w
  records : Words d w
  cursor : Words d w
  phase : Words 2 w
  leftBuffer : Words B w
  rightBuffer : Words B w
  outputBuffer : Words B w
  disk : BlockDisk B w

def initial (B d w sourceLeft sourceRight target records cursor : ℕ)
    (left right output : Words B w) (disk : BlockDisk B w) : State B d w :=
  ⟨encodeNat d w sourceLeft,encodeNat d w sourceRight,encodeNat d w target,
    encodeNat d w records,encodeNat d w cursor,encodeNat 2 w 0,left,right,output,disk⟩

private theorem phase_capacity (w : ℕ) (hw : 0<w) : 2<(2^w)^2 := by
  have hpow : 2≤2^w := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0<2) hw
  nlinarith

/-- The second read also performs a local computation on its buffer and
the first buffer. This local operation has no further disk access. -/
def step {B d w : ℕ} (s : State B d w) : State B d w × ℕ :=
  let cursor := decodeWords s.cursor
  if decodeWords s.phase=0 then
    if cursor*(B*w)<decodeWords s.records then
      ({s with phase := encodeNat 2 w 1, leftBuffer := s.disk (decodeWords s.sourceLeft+cursor)},1)
    else (s,0)
  else if decodeWords s.phase=1 then
    let next := s.disk (decodeWords s.sourceRight+cursor)
    ({s with phase := encodeNat 2 w 2,rightBuffer := next,outputBuffer := xorBlock s.leftBuffer next},1)
  else
    ({s with phase := encodeNat 2 w 0,cursor := encodeNat d w (cursor+1),disk := writeBlock s.disk (decodeWords s.target+cursor) s.outputBuffer},1)

def run {B d w : ℕ} : ℕ→State B d w→State B d w×ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let next := step s
      let rest := run fuel next.1
      (rest.1,next.2+rest.2)

theorem step_cost {B d w : ℕ} (s : State B d w) : (step s).2≤1 := by
  unfold step
  split
  · dsimp only
    split <;> simp
  · split <;> simp

theorem step_records {B d w : ℕ} (s : State B d w) : (step s).1.records=s.records := by
  unfold step
  dsimp only
  split
  · split <;> rfl
  · split <;> rfl

theorem run_records {B d w : ℕ} (fuel : ℕ) (s : State B d w) :
    (run fuel s).1.records=s.records := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => exact (ih _).trans (step_records s)

/-- Sequential reference disk: each write uses the two source blocks that
were actually read at that time, not free access to the original files. -/
def xorDisk {B w : ℕ} (sourceLeft sourceRight target : ℕ) :
    ℕ→ℕ→BlockDisk B w→BlockDisk B w
  | _,0,disk => disk
  | cursor,left+1,disk => xorDisk sourceLeft sourceRight target (cursor+1) left
      (writeBlock disk (target+cursor)
        (xorBlock (disk (sourceLeft+cursor)) (disk (sourceRight+cursor))))

theorem three_steps (B d w sourceLeft sourceRight target records cursor : ℕ) (hw : 0<w)
    (left right output : Words B w) (disk : BlockDisk B w)
    (ha : sourceLeft<(2^w)^d) (hb : sourceRight<(2^w)^d) (ht : target<(2^w)^d)
    (hn : records<(2^w)^d) (hc : cursor<(2^w)^d)
    (hlive : cursor*(B*w)<records) :
    run 3 (initial B d w sourceLeft sourceRight target records cursor left right output disk) =
      (initial B d w sourceLeft sourceRight target records (cursor+1)
        (disk (sourceLeft+cursor)) (disk (sourceRight+cursor))
        (xorBlock (disk (sourceLeft+cursor)) (disk (sourceRight+cursor)))
        (writeBlock disk (target+cursor)
          (xorBlock (disk (sourceLeft+cursor)) (disk (sourceRight+cursor)))),3) := by
  have hp := phase_capacity w hw
  simp only [run,step,initial,decodeNat_encode d w sourceLeft ha,
    decodeNat_encode d w sourceRight hb,decodeNat_encode d w target ht,
    decodeNat_encode d w records hn,decodeNat_encode d w cursor hc,
    decodeNat_encode 2 w 0 (by omega),decodeNat_encode 2 w 1 (by omega),
    decodeNat_encode 2 w 2 hp,hlive,↓reduceIte,one_ne_zero,Nat.add_zero]
  rfl

/-- All counters, including the cursor after its last increment, retain
their encoded values. The exact transfer count is three per live block. -/
theorem run_triples (B d w sourceLeft sourceRight target records cursor left : ℕ)
    (hw : 0<w) (hB : 0<B*w) (lb rb ob : Words B w) (disk : BlockDisk B w)
    (ha : sourceLeft<(2^w)^d) (hb : sourceRight<(2^w)^d) (ht : target<(2^w)^d)
    (hn : records<(2^w)^d) (hlimit : cursor+left≤blockCount (B*w) records)
    (hc : cursor+left<(2^w)^d) :
    let result := run (3*left) (initial B d w sourceLeft sourceRight target records cursor lb rb ob disk)
    result.1.disk=xorDisk sourceLeft sourceRight target cursor left disk ∧
    decodeWords result.1.cursor=cursor+left ∧
    result.1.phase=encodeNat 2 w 0 ∧ result.2=3*left := by
  induction left generalizing cursor lb rb ob disk with
  | zero =>
      simp only [Nat.mul_zero,run,initial,xorDisk,Nat.add_zero] at *
      exact ⟨True.intro,decodeNat_encode d w cursor hc,True.intro,True.intro⟩
  | succ left ih =>
      have hlive := (cursor_live_iff (B*w) records cursor hB).1 (by omega)
      have hcur : cursor<(2^w)^d := by omega
      have hp := three_steps B d w sourceLeft sourceRight target records cursor hw
        lb rb ob disk ha hb ht hn hcur hlive
      have hnext := ih (cursor+1) (disk (sourceLeft+cursor)) (disk (sourceRight+cursor))
        (xorBlock (disk (sourceLeft+cursor)) (disk (sourceRight+cursor)))
        (writeBlock disk (target+cursor)
          (xorBlock (disk (sourceLeft+cursor)) (disk (sourceRight+cursor)))) (by omega) (by omega)
      have hrun : run (3*(left+1))
          (initial B d w sourceLeft sourceRight target records cursor lb rb ob disk) =
          let result := run (3*left)
            (initial B d w sourceLeft sourceRight target records (cursor+1)
              (disk (sourceLeft+cursor)) (disk (sourceRight+cursor))
              (xorBlock (disk (sourceLeft+cursor)) (disk (sourceRight+cursor)))
              (writeBlock disk (target+cursor)
                (xorBlock (disk (sourceLeft+cursor)) (disk (sourceRight+cursor)))))
          (result.1,3+result.2) := by
        have hnstep : 3*(left+1)=3*left+3 := by omega
        rw [hnstep]
        simp only [run] at hp ⊢
        have hstate := congrArg Prod.fst hp
        have hcost := congrArg Prod.snd hp
        dsimp only at hstate hcost ⊢
        rw [hstate]
        congr 1
        omega
      dsimp only
      rw [hrun]
      dsimp only at hnext ⊢
      exact ⟨hnext.1,by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hnext.2.1,
        hnext.2.2.1,by omega⟩

theorem xorDisk_outside {B w : ℕ} (sourceLeft sourceRight target cursor left : ℕ)
    (disk : BlockDisk B w) (address : ℕ)
    (ha : address<target+cursor ∨ target+cursor+left≤address) :
    xorDisk sourceLeft sourceRight target cursor left disk address=disk address := by
  induction left generalizing cursor disk with
  | zero => rfl
  | succ left ih =>
      rw [xorDisk,ih (cursor+1) _ (by omega)]
      simp only [writeBlock,if_neg (show address≠target+cursor by omega)]

theorem xorDisk_at {B w : ℕ} (sourceLeft sourceRight target count cursor left : ℕ)
    (disk : BlockDisk B w) (hbound : cursor+left≤count)
    (hleft : ∀ i j,i<count→j<count→sourceLeft+i≠target+j)
    (hright : ∀ i j,i<count→j<count→sourceRight+i≠target+j)
    (i : ℕ) (hi : cursor ≤ i ∧ i < cursor+left) :
    xorDisk sourceLeft sourceRight target cursor left disk (target+i)=
      xorBlock (disk (sourceLeft+i)) (disk (sourceRight+i)) := by
  induction left generalizing cursor disk with
  | zero => omega
  | succ left ih =>
      rw [xorDisk]
      by_cases he : i=cursor
      · subst i
        rw [xorDisk_outside sourceLeft sourceRight target (cursor+1) left _
          (target+cursor) (Or.inl (by omega))]
        simp [writeBlock]
      · rw [ih (cursor+1) _ (by omega) ⟨by omega,by omega⟩]
        simp only [writeBlock,if_neg (hleft i cursor (by omega) (by omega)),
          if_neg (hright i cursor (by omega) (by omega))]

theorem complete_xor (B d w sourceLeft sourceRight target records : ℕ)
    (hw : 0<w) (hB : 0<B*w) (lb rb ob : Words B w) (disk : BlockDisk B w)
    (ha : sourceLeft<(2^w)^d) (hb : sourceRight<(2^w)^d) (ht : target<(2^w)^d)
    (hn : records<(2^w)^d) (hc : blockCount (B*w) records<(2^w)^d)
    (hleft : ∀ i j,i<blockCount (B*w) records→j<blockCount (B*w) records→sourceLeft+i≠target+j)
    (hright : ∀ i j,i<blockCount (B*w) records→j<blockCount (B*w) records→sourceRight+i≠target+j) :
    let result := run (3*blockCount (B*w) records)
      (initial B d w sourceLeft sourceRight target records 0 lb rb ob disk)
    result.2=3*blockCount (B*w) records ∧
    (∀ i,i<blockCount (B*w) records → result.1.disk (target+i)=
      xorBlock (disk (sourceLeft+i)) (disk (sourceRight+i))) ∧
    (∀ address,address<target ∨ target+blockCount (B*w) records≤address →
      result.1.disk address=disk address) := by
  have hr := run_triples B d w sourceLeft sourceRight target records 0 (blockCount (B*w) records)
    hw hB lb rb ob disk ha hb ht hn (by omega) (by omega)
  dsimp only at hr ⊢
  refine ⟨hr.2.2.2,?_,?_⟩
  · intro i hi
    rw [hr.1]
    exact xorDisk_at sourceLeft sourceRight target (blockCount (B*w) records) 0
      (blockCount (B*w) records) disk (by omega) hleft hright i ⟨Nat.zero_le _,by omega⟩
  · intro address haddress
    rw [hr.1]
    exact xorDisk_outside sourceLeft sourceRight target 0 (blockCount (B*w) records)
      disk address (by simpa only [Nat.add_zero] using haddress)

theorem complete_halts (B d w sourceLeft sourceRight target records : ℕ)
    (hw : 0<w) (hB : 0<B*w) (lb rb ob : Words B w) (disk : BlockDisk B w)
    (ha : sourceLeft<(2^w)^d) (hb : sourceRight<(2^w)^d) (ht : target<(2^w)^d)
    (hn : records<(2^w)^d) (hc : blockCount (B*w) records<(2^w)^d) :
    let result := run (3*blockCount (B*w) records)
      (initial B d w sourceLeft sourceRight target records 0 lb rb ob disk)
    step result.1=(result.1,0) := by
  have hr := run_triples B d w sourceLeft sourceRight target records 0 (blockCount (B*w) records)
    hw hB lb rb ob disk ha hb ht hn (by omega) (by omega)
  have hend : ¬blockCount (B*w) records*(B*w)<records := by
    rw [←cursor_live_iff (B*w) records (blockCount (B*w) records) hB]
    omega
  dsimp only at hr ⊢
  have hrn : decodeWords (run (3*blockCount (B*w) records)
      (initial B d w sourceLeft sourceRight target records 0 lb rb ob disk)).1.records=records := by
    rw [run_records]
    exact decodeNat_encode d w records hn
  unfold step
  rw [hr.2.2.1]
  simp only [decodeNat_encode 2 w 0 (by have hp := phase_capacity w hw; omega),↓reduceIte]
  rw [hr.2.1,hrn]
  simp only [Nat.zero_add,hend,↓reduceIte]

abbrev ResidentWords (B d w : ℕ) :=
  Words d w × Words d w × Words d w × Words d w × Words d w ×
    Words 2 w × Words B w × Words B w × Words B w

def resident {B d w : ℕ} (s : State B d w) : ResidentWords B d w :=
  (s.sourceLeft,s.sourceRight,s.target,s.records,s.cursor,s.phase,
    s.leftBuffer,s.rightBuffer,s.outputBuffer)

theorem resident_count (B d w : ℕ) :
    Fintype.card (ResidentWords B d w)=(2^w)^(5*d+2+3*B) := by
  simp only [ResidentWords,Words,Word,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  ring

theorem state_recover {B d w : ℕ} (s t : State B d w)
    (hr : resident s=resident t) (hd : s.disk=t.disk) : s=t := by
  cases s
  cases t
  simp only [resident,Prod.mk.injEq] at hr
  rcases hr with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  cases hd
  rfl

end CodedSorting.PhysicalFileHandlesXor
end PhysicalFileHandlesXor

section AllocatedDirectoryXor
/-! Refinement of the actual XOR gate's two-file scan by the uniform
three-buffer word machine. Inputs and output are bounded file handles.
Fresh allocated intervals make both source files and all other aliases
survive the actual writes. Logical File values appear only in the theorem.
-/
set_option autoImplicit false
namespace CodedSorting.AllocatedDirectoryXor
open WordControl PhysicalStreamCursor PhysicalFileHandles PhysicalFileHandlesXor
open WorkspaceAllocation Circuit

variable {N e B w c : ℕ}

theorem blockCount_le_records (B records : ℕ) (hB : 0<B) : blockCount B records≤records := by
  by_contra h
  have hh := (cursor_live_iff B records records hB).1 (by omega)
  have hm := Nat.le_mul_of_pos_right records hB
  omega

def execute (B w c : ℕ) (a b output : Handle N e)
    (lb rb ob : Words B w) (disk : BlockDisk B w) : State B (c*(e+1)) w×ℕ :=
  run (3*blockCount (B*w) a.records.val)
    (initial B (c*(e+1)) w a.base.val b.base.val output.base.val a.records.val 0 lb rb ob disk)

private theorem counter_bound (hN : 2≤N) (hw : WordConvention.Covers N w c)
    (x : Fin (N^e+1)) : x.val<(2^w)^(c*(e+1)) :=
  x.isLt.trans_le (WordConvention.polynomial_capacity N w c e hN hw)

theorem execute_blocks (hN : 2≤N) (hw : WordConvention.Covers N w c) (hB : 0<B*w)
    (a b output : Handle N e) (lb rb ob : Words B w) (disk : BlockDisk B w)
    (hleft : ∀ i j,i<blockCount (B*w) a.records.val→j<blockCount (B*w) a.records.val→
      a.base.val+i≠output.base.val+j)
    (hright : ∀ i j,i<blockCount (B*w) a.records.val→j<blockCount (B*w) a.records.val→
      b.base.val+i≠output.base.val+j) :
    let result := execute B w c a b output lb rb ob disk
    result.2=3*blockCount (B*w) a.records.val ∧
    (∀ i,i<blockCount (B*w) a.records.val → result.1.disk (output.base.val+i)=
      xorBlock (disk (a.base.val+i)) (disk (b.base.val+i))) ∧
    (∀ address,address<output.base.val ∨ output.base.val+blockCount (B*w) a.records.val≤address →
      result.1.disk address=disk address) := by
  apply complete_xor B (c*(e+1)) w a.base.val b.base.val output.base.val a.records.val
    (WordConvention.positive_words N w c hN hw).1 hB lb rb ob disk
      (counter_bound hN hw a.base) (counter_bound hN hw b.base)
      (counter_bound hN hw output.base) (counter_bound hN hw a.records)
  · exact (blockCount_le_records (B*w) a.records.val hB).trans_lt (counter_bound hN hw a.records)
  · exact hleft
  · exact hright

theorem execute_halts (hN : 2≤N) (hw : WordConvention.Covers N w c) (hB : 0<B*w)
    (a b output : Handle N e) (lb rb ob : Words B w) (disk : BlockDisk B w) :
    step (execute B w c a b output lb rb ob disk).1=
      ((execute B w c a b output lb rb ob disk).1,0) := by
  apply complete_halts B (c*(e+1)) w a.base.val b.base.val output.base.val a.records.val
    (WordConvention.positive_words N w c hN hw).1 hB lb rb ob disk
      (counter_bound hN hw a.base) (counter_bound hN hw b.base)
      (counter_bound hN hw output.base) (counter_bound hN hw a.records)
  exact (blockCount_le_records (B*w) a.records.val hB).trans_lt (counter_bound hN hw a.records)

def cells (hB : 0<B*w) (disk : BlockDisk B w) (base V : ℕ) : Fin V→Bit :=
  fun i => BitWordPacking.blockBits B w (disk (base+i.val/(B*w)))
    ⟨i.val%(B*w),Nat.mod_lt _ hB⟩

theorem bitView_canonical (hB : 0<B*w) (disk : BlockDisk B w) (a : Handle N e)
    (V : ℕ) (hr : a.records.val=V) :
    bitView hB disk a=PhysicalRecursiveExchange.canonical (B*w) hB (cells hB disk a.base.val V) := by
  subst V
  rfl

/-- Exact equality with the existing gate primitive, including its I/O
charge. The machine reads only its two input buffers, never a File list. -/
theorem xorScan_refinement (hN : 2≤N) (hw : WordConvention.Covers N w c) (hB : 0<B*w)
    (a b output : Handle N e) (hb : b.records.val=a.records.val)
    (ho : output.records.val=a.records.val)
    (lb rb ob : Words B w) (disk : BlockDisk B w)
    (hleft : ∀ i j,i<blockCount (B*w) a.records.val→j<blockCount (B*w) a.records.val→
      a.base.val+i≠output.base.val+j)
    (hright : ∀ i j,i<blockCount (B*w) a.records.val→j<blockCount (B*w) a.records.val→
      b.base.val+i≠output.base.val+j) :
    let result := execute B w c a b output lb rb ob disk
    GateStreamMachine.xorScan (B*w) a.records.val (bitView hB disk a) (bitView hB disk b)=
      some ⟨bitView hB result.1.disk output,result.2⟩ := by
  let result := execute B w c a b output lb rb ob disk
  have hr := execute_blocks hN hw hB a b output lb rb ob disk hleft hright
  change result.2=_ ∧ _ at hr
  have hout : bitView hB result.1.disk output=PhysicalRecursiveExchange.canonical (B*w) hB
      (fun i => cells hB disk a.base.val a.records.val i+cells hB disk b.base.val a.records.val i) := by
    rw [bitView_canonical hB result.1.disk output a.records.val ho]
    apply congrArg (PhysicalRecursiveExchange.canonical (B*w) hB)
    funext i
    have hj : i.val/(B*w)<blockCount (B*w) a.records.val :=
      (cursor_live_iff (B*w) a.records.val (i.val/(B*w)) hB).2
        ((Nat.div_mul_le_self _ _).trans_lt i.isLt)
    simp only [cells]
    rw [hr.2.1 _ hj,xorBlock_bits]
  dsimp only
  rw [bitView_canonical hB disk a a.records.val rfl,bitView_canonical hB disk b a.records.val hb]
  change GateStreamMachine.xorScan (B*w) a.records.val
    (BucketMachine.pack (B*w) hB (List.ofFn (cells hB disk a.base.val a.records.val)))
    (BucketMachine.pack (B*w) hB (List.ofFn (cells hB disk b.base.val a.records.val)))=_
  rw [GateStreamMachine.xorScan_correct]
  unfold PhysicalRecursiveExchange.canonical at hout
  rw [←hout]
  congr 2
  exact hr.1.symm

theorem disjoint_indices (source target : Span) (count : ℕ)
    (hs : count≤source.blocks) (ht : count≤target.blocks)
    (hd : Before source target ∨ Before target source) :
    ∀ i j,i<count→j<count→source.start+i≠target.start+j := by
  intro i j hi hj
  unfold Before Span.stop at hd
  rcases hd with hd|hd <;> omega

/-- Allocated, disjoint file intervals discharge all sequential scan alias
conditions. The source files may alias each other; only the output is fresh. -/
theorem allocated_refinement (hN : 2≤N) (hw : WordConvention.Covers N w c) (hB : 0<B*w)
    (a b output : Handle N e) (hb : b.records.val=a.records.val)
    (ho : output.records.val=a.records.val) (sa sb target : Span)
    (haFit : Fits (B*w) a sa) (hbFit : Fits (B*w) b sb) (hoFit : Fits (B*w) output target)
    (hleft : Before sa target ∨ Before target sa)
    (hright : Before sb target ∨ Before target sb)
    (lb rb ob : Words B w) (disk : BlockDisk B w) :
    let result := execute B w c a b output lb rb ob disk
    GateStreamMachine.xorScan (B*w) a.records.val (bitView hB disk a) (bitView hB disk b)=
      some ⟨bitView hB result.1.disk output,result.2⟩ := by
  apply xorScan_refinement hN hw hB a b output hb ho lb rb ob disk
  · rw [haFit.1,hoFit.1]
    exact disjoint_indices sa target _ haFit.2 (by simpa only [ho] using hoFit.2) hleft
  · rw [hbFit.1,hoFit.1]
    exact disjoint_indices sb target _ (by simpa only [hb] using hbFit.2)
      (by simpa only [ho] using hoFit.2) hright

/-- Every other valid handle keeps its full bit stream after the concrete
XOR scanner. In particular, all directory aliases remain meaningful. -/
theorem allocated_preserves_file (hN : 2≤N) (hw : WordConvention.Covers N w c) (hB : 0<B*w)
    (a b output : Handle N e) (hb : b.records.val=a.records.val)
    (ho : output.records.val=a.records.val) (sa sb target : Span)
    (haFit : Fits (B*w) a sa) (hbFit : Fits (B*w) b sb) (hoFit : Fits (B*w) output target)
    (hleft : Before sa target ∨ Before target sa)
    (hright : Before sb target ∨ Before target sb)
    (lb rb ob : Words B w) (disk : BlockDisk B w)
    (other : Handle N e) (sother : Span) (hf : Fits (B*w) other sother)
    (hd : Before sother target ∨ Before target sother) :
    bitView hB (execute B w c a b output lb rb ob disk).1.disk other=bitView hB disk other := by
  have hl : ∀ i j,i<blockCount (B*w) a.records.val→j<blockCount (B*w) a.records.val→
      a.base.val+i≠output.base.val+j := by
    rw [haFit.1,hoFit.1]
    exact disjoint_indices sa target _ haFit.2 (by simpa only [ho] using hoFit.2) hleft
  have hright' : ∀ i j,i<blockCount (B*w) a.records.val→j<blockCount (B*w) a.records.val→
      b.base.val+i≠output.base.val+j := by
    rw [hbFit.1,hoFit.1]
    exact disjoint_indices sb target _ (by simpa only [hb] using hbFit.2)
      (by simpa only [ho] using hoFit.2) hright
  have hr := execute_blocks hN hw hB a b output lb rb ob disk hl hright'
  apply bitView_congr hB disk _ other sother hf
  intro address haddress
  apply hr.2.2
  have hcap : blockCount (B*w) a.records.val≤target.blocks := by simpa only [ho] using hoFit.2
  rw [hoFit.1]
  simp only [Before,Span.Contains,Span.stop] at hd haddress
  rcases hd with hd|hd
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end CodedSorting.AllocatedDirectoryXor
end AllocatedDirectoryXor
