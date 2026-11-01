import CodedSorting.Sorting.Radix.Framework.Directory

section GatherController
/-! One fixed finite-RAM controller gathers an enumerated family of
fragments. It really reads a two-field disk-directory entry, copies that
interval, advances the destination position and proceeds to the next
entry. Tags hold only bounded control data, never records or disk contents.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace CodedSorting.CommonMSDGatherController
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (RAM Machine Store)
noncomputable section

/-- Index, copy/read phase, destination offset, source offset, word count. -/
abbrev Tag (F C : ℕ) := Fin (F+1) × Bool × Fin (C+1) × Fin (C+1) × Fin (C+1)
abbrev tagCount (F C : ℕ) := Fintype.card (Tag F C)
def tagEquiv (F C : ℕ) : Tag F C ≃ Fin (tagCount F C) := Fintype.equivFin _

def ready {F C : ℕ} (j : Fin (F+1)) (D : Fin (C+1)) : Tag F C :=
  (j,false,D,0,0)
def copying {F C : ℕ} (j : Fin F) (D O N : Fin (C+1)) : Tag F C :=
  (j.castSucc,true,D,O,N)
def bounded (C n : ℕ) : Fin (C+1) := ⟨n%(C+1),Nat.mod_lt _ (by omega)⟩

structure Layout (F : ℕ) where
  source : Fin F → ℕ
  offset : Fin F → ℕ
  directory : Fin F → ℕ
  entry : Fin F → ℕ
  target : ℕ

def body (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (t : Tag F C) : List (Instruction q) :=
  if h : t.1.val<F then
    if t.2.1 then CommonIntervalCopy.code q reader t.2.2.2.1.val t.2.2.1.val
      t.2.2.2.2.val (layout.source ⟨t.1.val,h⟩) layout.target
    else CommonMSDDirectoryRead.code q (layout.directory ⟨t.1.val,h⟩)
      (layout.entry ⟨t.1.val,h⟩)
  else []

def code (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (tag : Fin (tagCount F C)) : List (Instruction q) :=
  body q reader layout ((tagEquiv F C).symm tag)

def terminal {F C : ℕ} (tag : Fin (tagCount F C)) : Bool :=
  decide (F≤((tagEquiv F C).symm tag).1.val)

def nextTag (q : Configuration) {F C : ℕ} (layout : Layout F)
    (t : Tag F C) (ram : RAM q) : Tag F C :=
  if h : t.1.val<F then
    if t.2.1 then ready ⟨t.1.val+1,by omega⟩
      (bounded C (t.2.2.1.val+t.2.2.2.2.val))
    else copying ⟨t.1.val,h⟩ t.2.2.1
      (bounded C (layout.offset ⟨t.1.val,h⟩+3*CommonMSDDirectoryRead.field q (layout.entry ⟨t.1.val,h⟩)
        0 (unpack ram)))
      (bounded C (3*CommonMSDDirectoryRead.field q (layout.entry ⟨t.1.val,h⟩)
        1 (unpack ram)))
  else t

def next (q : Configuration) {F C : ℕ} (layout : Layout F) (stride : ℕ)
    (tag : Fin (tagCount F C)) (ram : RAM q) : RAM q :=
  setPC q ((tagEquiv F C (nextTag q layout ((tagEquiv F C).symm tag) ram)).val*stride) ram

def policy (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) : SourcePolicy q :=
  CommonTaggedController.policy q stride (code q reader (C:=C) layout)
    terminal (next q layout stride)

@[simp] theorem body_ready (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (j : Fin F) (D : Fin (C+1)) :
    body q reader layout (ready j.castSucc D)=
      CommonMSDDirectoryRead.code q (layout.directory j) (layout.entry j) := by
  simp only [body,ready,Fin.coe_castSucc,j.isLt,↓reduceDIte,Bool.false_eq_true,↓reduceIte]

@[simp] theorem body_copying (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (j : Fin F) (D O N : Fin (C+1)) :
    body q reader layout (copying j D O N)=
      CommonIntervalCopy.code q reader O.val D.val N.val (layout.source j) layout.target := by
  simp only [body,copying,Fin.coe_castSucc,j.isLt,↓reduceDIte,↓reduceIte]

@[simp] theorem body_done (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (D : Fin (C+1)) :
    body q reader layout (ready ⟨F,by omega⟩ D)=[] := by
  simp only [body,ready,lt_self_iff_false,↓reduceDIte]

theorem body_safe (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (t : Tag F C) :
    ∀ i∈body q reader layout t,RespectsPC q i := by
  unfold body
  split
  · split
    · exact CommonIntervalCopy.codeFrom_safe q reader _ _ _ _ _ _ _
    · exact CommonMSDDirectoryRead.code_safe q _ _
  · simp

@[simp] theorem code_tag (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (t : Tag F C) :
    code q reader layout (tagEquiv F C t)=body q reader layout t := by
  simp only [code,Equiv.symm_apply_apply]

@[simp] theorem terminal_ready {F C : ℕ} (j : Fin F) (D : Fin (C+1)) :
    terminal (tagEquiv F C (ready j.castSucc D))=false := by
  simp only [terminal,Equiv.symm_apply_apply,ready,Fin.coe_castSucc,
    show ¬F≤j.val by omega,decide_false]

@[simp] theorem terminal_copying {F C : ℕ} (j : Fin F) (D O N : Fin (C+1)) :
    terminal (tagEquiv F C (copying j D O N))=false := by
  simp only [terminal,Equiv.symm_apply_apply,copying,Fin.coe_castSucc,
    show ¬F≤j.val by omega,decide_false]

@[simp] theorem terminal_done {F C : ℕ} (D : Fin (C+1)) :
    terminal (tagEquiv F C (ready ⟨F,by omega⟩ D))=true := by
  simp only [terminal,Equiv.symm_apply_apply,ready,le_refl,decide_true]

theorem next_copying (q : Configuration) {F C : ℕ} (layout : Layout F)
    (stride : ℕ) (j : Fin F) (D O N : Fin (C+1)) (ram : RAM q) :
    next q layout stride (tagEquiv F C (copying j D O N)) ram=
      setPC q ((tagEquiv F C (ready ⟨j.val+1,by have:=j.isLt;omega⟩
        (bounded C (D.val+N.val)))).val*stride) ram := by
  simp only [next,Equiv.symm_apply_apply,nextTag,copying,Fin.coe_castSucc,j.isLt,
    ↓reduceDIte,↓reduceIte]

theorem next_ready (q : Configuration) {F C : ℕ} (layout : Layout F)
    (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (ram : RAM q) :
    next q layout stride (tagEquiv F C (ready j.castSucc D)) ram=
      setPC q ((tagEquiv F C (copying j D
        (bounded C (layout.offset j+3*CommonMSDDirectoryRead.field q (layout.entry j) 0 (unpack ram)))
        (bounded C (3*CommonMSDDirectoryRead.field q (layout.entry j) 1 (unpack ram))))).val*stride) ram := by
  simp only [next,Equiv.symm_apply_apply,nextTag,ready,Fin.coe_castSucc,j.isLt,
    ↓reduceDIte,Bool.false_eq_true,↓reduceIte]

/-- Public resource condition for the finite control table, independent
of which directory values are observed at run time. -/
structure Fits (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (stride : ℕ) : Prop where
  code_length : ∀ t : Tag F C,(body q reader layout t).length<stride
  capacity : tagCount F C*stride≤q.N^q.exponent

theorem tag_capacity (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (stride : ℕ)
    (h : Fits q reader (C:=C) layout stride) (tag : Fin (tagCount F C)) :
    tag.val*stride≤q.N^q.exponent :=
  (Nat.mul_le_mul_right stride (Nat.le_of_lt tag.isLt)).trans h.capacity

theorem body_capacity (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (stride : ℕ)
    (h : Fits q reader (C:=C) layout stride) (t : Tag F C) :
    (tagEquiv F C t).val*stride+(body q reader layout t).length≤q.N^q.exponent := by
  have ht := (tagEquiv F C t).isLt
  have hl := h.code_length t
  have hc := h.capacity
  nlinarith

theorem body_call (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (stride : ℕ)
    (h : Fits q reader (C:=C) layout stride) (t : Tag F C)
    (ht : terminal (tagEquiv F C t)=false)
    (s : Machine q) (hpc : pc q s.ram=(tagEquiv F C t).val*stride) :
    let out := CommonTaggedSchedule.execute q stride (tagEquiv F C t).val 0
      (body q reader layout t) s
    ControlledNormalization.runLogical (policy q reader (C:=C) layout stride)
      ((body q reader layout t).length+1) s=
      ({out.1 with ram:=next q layout stride (tagEquiv F C t) out.1.ram},
        cost q (body q reader layout t)) := by
  simpa only [code_tag] using CommonTaggedController.call q stride
    (code q reader layout) terminal (next q layout stride) (tagEquiv F C t)
    (by simpa only [code_tag] using h.code_length t)
    (by simpa only [code_tag] using body_capacity q reader layout stride h t) ht s hpc

end
end CodedSorting.CommonMSDGatherController
end GatherController

section GatherInvariant
/-! Disk invariants used when interval copies follow actual directory reads.
Reading a descriptor changes resident scratch; the copying result is independent
of that scratch. Each copied interval preserves the already assembled prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonMSDGatherInvariant
open WordControl CommonSortingNormalization CommonStaticSchedule CommonIntervalCopy
open CommonLeafProgram (Machine Disk)
open CommonMarginTransform (wordAt)
noncomputable section

theorem pair_disk_congr (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k p : ℕ) (s t : Machine q) (h : s.disk=t.disk) :
    (executeRaw q (pairCode q reader O D N source target k p) s).1.disk=
      (executeRaw q (pairCode q reader O D N source target k p) t).1.disk := by
  rw [pair_raw,pair_raw,h]

theorem codeFrom_disk_congr (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k n : ℕ) (s t : Machine q) (h : s.disk=t.disk) :
    (executeRaw q (codeFrom q reader O D N source target k n) s).1.disk=
      (executeRaw q (codeFrom q reader O D N source target k n) t).1.disk := by
  induction n generalizing k s t with
  | zero => exact h
  | succ n ih =>
    rw [codeFrom,CommonPermutationPairs.raw_append,CommonPermutationPairs.raw_append]
    apply ih (k+1)
    rw [fragment,CommonPermutationPairs.raw_append,CommonPermutationPairs.raw_append]
    apply pair_disk_congr
    exact pair_disk_congr q reader O D N source target k _ s t h

theorem code_disk_congr (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) (s t : Machine q) (h : s.disk=t.disk) :
    (executeRaw q (code q reader O D N source target) s).1.disk=
      (executeRaw q (code q reader O D N source target) t).1.disk :=
  codeFrom_disk_congr q reader O D N source target _ _ s t h

/-- Copying the next interval never changes the already assembled words,
including the portion of a boundary block occupied by the preceding interval. -/
theorem prefix_preserved (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) (s : Machine q)
    (hs : source+PhysicalStreamCursor.blockCount q.block (O+N)≤q.N^q.exponent)
    (ht : target+D/q.block+pages q D N≤q.N^q.exponent)
    (hsep : ReadsOutside q O D source target (D/q.block) (D/q.block+pages q D N))
    (hcover : ∀ j,D≤j → j<D+N → D/q.block≤j/q.block ∧ j/q.block<D/q.block+pages q D N)
    (j : ℕ) (hj : j<D) (hfit : target+j/q.block<q.N^q.exponent) :
    wordAt q (executeRaw q (code q reader O D N source target) s).1.disk target j=
      wordAt q s.disk target j := by
  have h := written_word q O D N source target s.disk _
    (raw q reader O D N source target s ht hsep) hs hcover j hfit
  simpa only [show ¬D≤j by omega,false_and,if_false] using h

/-- The newly appended words come from the source interval read by the
copy, at their original order within that interval. -/
theorem appended_word (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) (s : Machine q)
    (hs : source+PhysicalStreamCursor.blockCount q.block (O+N)≤q.N^q.exponent)
    (ht : target+D/q.block+pages q D N≤q.N^q.exponent)
    (hsep : ReadsOutside q O D source target (D/q.block) (D/q.block+pages q D N))
    (hcover : ∀ j,D≤j → j<D+N → D/q.block≤j/q.block ∧ j/q.block<D/q.block+pages q D N)
    (j : ℕ) (hj : j<N) :
    wordAt q (executeRaw q (code q reader O D N source target) s).1.disk target (D+j)=
      wordAt q s.disk source (O+j) := by
  have hp := (hcover (D+j) (by omega) (by omega)).2
  have h := written_word q O D N source target s.disk _
    (raw q reader O D N source target s ht hsep) hs hcover (D+j) (by omega)
  simpa only [show D≤D+j by omega,show D+j<D+N by omega,true_and,if_true,
    Nat.add_sub_cancel_left] using h

/-- An outside disk block remains the same after one copy. In particular,
source rows and the descriptor directory can share the untouched region. -/
theorem outside_word (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target base j : ℕ) (s : Machine q)
    (ht : target+D/q.block+pages q D N≤q.N^q.exponent)
    (hsep : ReadsOutside q O D source target (D/q.block) (D/q.block+pages q D N))
    (hfit : base+j/q.block<q.N^q.exponent)
    (hout : base+j/q.block<target+D/q.block ∨
      target+D/q.block+pages q D N≤base+j/q.block) :
    wordAt q (executeRaw q (code q reader O D N source target) s).1.disk base j=
      wordAt q s.disk base j := by
  have hw := raw q reader O D N source target s ht hsep
  rw [←disk_word q _ base j hfit,←disk_word q s.disk base j hfit]
  rw [hw.outside (address q base (j/q.block)) (by
    rw [CommonColumnSplit.address_val q base (j/q.block) hfit]
    omega)]


/-- Inductive concatenation step: a previously assembled prefix and the
newly read source interval become their exact ordered concatenation. -/
theorem append_prefix (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) (s : Machine q) (prior chunk : ℕ → Word q.w)
    (hs : source+PhysicalStreamCursor.blockCount q.block (O+N)≤q.N^q.exponent)
    (ht : target+D/q.block+pages q D N≤q.N^q.exponent)
    (hsep : ReadsOutside q O D source target (D/q.block) (D/q.block+pages q D N))
    (hcover : ∀ j,D≤j → j<D+N → D/q.block≤j/q.block ∧ j/q.block<D/q.block+pages q D N)
    (hprefix : ∀ j,j<D → wordAt q s.disk target j=prior j)
    (hchunk : ∀ j,j<N → wordAt q s.disk source (O+j)=chunk j)
    (j : ℕ) (hj : j<D+N) (hfit : target+j/q.block<q.N^q.exponent) :
    wordAt q (executeRaw q (code q reader O D N source target) s).1.disk target j=
      if j<D then prior j else chunk (j-D) := by
  rw [written_word q O D N source target s.disk _
    (raw q reader O D N source target s ht hsep) hs hcover j hfit]
  by_cases hl : j<D
  · rw [if_pos hl,if_neg (by omega)]
    exact hprefix j hl
  · rw [if_neg hl,if_pos (by omega)]
    exact hchunk (j-D) (by omega)

end
end CodedSorting.CommonMSDGatherInvariant
end GatherInvariant

section GatherCapacity
/-! A concrete polynomial bound for every control state of the actual
gather controller, including states not reached on valid input. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonMSDGatherCapacity
open CommonSortingNormalization CommonMSDGatherController SortingResourceBudget
noncomputable section

def chosenStride (q : Configuration) (C : ℕ) : ℕ :=
  6*(C+q.block+2*q.digits+2)

theorem copy_pages_le (q : Configuration) (D N : ℕ) :
    CommonIntervalCopy.pages q D N≤N+q.block+1 := by
  have h := CommonIntervalCopyBounds.pages_le q D N
  have hd := Nat.div_le_self (N+q.block-1) q.block
  unfold PhysicalStreamCursor.blockCount at h
  omega

theorem read_blocks_le (q : Configuration) (e : ℕ) :
    CommonMSDDirectoryRead.blocks q e≤2*q.block+2*q.digits := by
  have hb := CommonLeafProgram.block_positive q
  have hl := Nat.mod_lt (CommonMSDDirectoryRead.offset q e) hb
  have hd := Nat.div_le_self
    (CommonMSDDirectoryRead.lead q e+2*q.digits+q.block-1) q.block
  unfold CommonMSDDirectoryRead.blocks CommonMSDDirectoryRead.total
    PhysicalStreamCursor.blockCount
  unfold CommonMSDDirectoryRead.lead at *
  omega

theorem body_length_lt (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F) (t : Tag F C) :
    (body q reader layout t).length<chosenStride q C := by
  unfold body
  split
  · split
    · rw [CommonIntervalCopy.code_length]
      have hp := copy_pages_le q t.2.2.1.val t.2.2.2.2.val
      have hn := t.2.2.2.2.isLt
      unfold chosenStride
      omega
    · rw [CommonMSDDirectoryRead.code_length]
      have hr := read_blocks_le q (layout.entry ⟨t.1.val,by assumption⟩)
      have hb := CommonLeafProgram.block_positive q
      unfold chosenStride
      omega
  · simp only [List.length_nil]
    unfold chosenStride
    omega

theorem tag_count (F C : ℕ) : tagCount F C=2*(F+1)*(C+1)^3 := by
  simp only [tagCount,Tag,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

theorem tag_count_le (F C N : ℕ) (hN : 1≤N) (hF : F≤N) (hC : C≤3*N) :
    tagCount F C≤256*N^4 := by
  rw [tag_count]
  have hf : F+1≤2*N := by omega
  have hc : C+1≤4*N := by omega
  have hp := Nat.pow_le_pow_left hc 3
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hf) hp
  nlinarith only [hm]

theorem stride_le (q : Configuration) (C : ℕ) (hC : C≤3*q.N) :
    chosenStride q C≤48*q.N := by
  have hd := CommonMSDDirectoryBounds.digits_le_height q
  have hb : q.block≤q.height :=
    (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory; omega)).2.1
  have hh := CommonLocalDescriptorBounds.height_scaled_le_input q
  have hn := q.input_large
  unfold chosenStride
  omega

/-- The normalized configuration already forces an input of at least 96
records, enough to absorb the fixed control-table coefficient. -/
theorem capacity (q : Configuration) (F C : ℕ)
    (hF : F≤q.N) (hC : C≤3*q.N) (he : 8≤q.exponent) :
    tagCount F C*chosenStride q C≤q.N^q.exponent := by
  have hH : 0<q.height :=
    (normalized_shape q.inventory q.c q.digits q.M q.B q.memory_large
      (by have:=q.block_memory; omega)).1
  have h96 : 96≤q.N := by
    have hh := CommonLocalDescriptorBounds.height_scaled_le_input q
    nlinarith
  have htags := tag_count_le F C q.N (by omega) hF hC
  have hstride := stride_le q C hC
  have hprod := Nat.mul_le_mul htags hstride
  have hcube : 12288≤q.N^3 := by
    have hp := Nat.pow_le_pow_left h96 3
    norm_num at hp
    omega
  have hlarge := Nat.mul_le_mul_right (q.N^5) hcube
  have heighth : tagCount F C*chosenStride q C≤q.N^8 := by
    nlinarith only [hprod,hlarge]
  exact heighth.trans (Nat.pow_le_pow_right (by have:=q.input_large; omega) he)

/-- No execution-success predicate is assumed: these numeric input and
exponent bounds discharge the controller's entire finite-table condition. -/
theorem fits (q : Configuration) (reader : Fin q.inventory.readers)
    {F C : ℕ} (layout : Layout F)
    (hF : F≤q.N) (hC : C≤3*q.N) (he : 8≤q.exponent) :
    Fits q reader (C:=C) layout (chosenStride q C) :=
  ⟨body_length_lt q reader layout,capacity q F C hF hC he⟩

end
end CodedSorting.CommonMSDGatherCapacity
end GatherCapacity

section GatherRun
/-! Finite execution of the concrete read/copy gather controller. The
recursive objects below are proof-side observations of actual directory
reads and actual copies, not inputs available to the running policy. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace CodedSorting.CommonMSDGatherRun
open CommonSortingNormalization CommonStaticSchedule CommonMSDGatherController
open CommonLeafProgram (Machine RAM Store)
noncomputable section

def readBody (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) :=
  CommonTaggedSchedule.execute q stride (tagEquiv F C (ready j.castSucc D)).val 0
    (CommonMSDDirectoryRead.code q (layout.directory j) (layout.entry j)) s

def observed (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) :
    Fin (C+1) × Fin (C+1) :=
  let r := readBody q reader layout stride j D s
  (bounded C (layout.offset j+3*CommonMSDDirectoryRead.field q (layout.entry j) 0 (unpack r.1.ram)),
   bounded C (3*CommonMSDDirectoryRead.field q (layout.entry j) 1 (unpack r.1.ram)))

def afterRead (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) : Machine q :=
  let r := readBody q reader layout stride j D s
  {r.1 with ram:=next q layout stride (tagEquiv F C (ready j.castSucc D)) r.1.ram}

def copyBody (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) :=
  let p := observed q reader layout stride j D s
  CommonTaggedSchedule.execute q stride (tagEquiv F C (copying j D p.1 p.2)).val 0
    (CommonIntervalCopy.code q reader p.1.val D.val p.2.val (layout.source j) layout.target)
    (afterRead q reader layout stride j D s)

def nextDest (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) : Fin (C+1) :=
  bounded C (D.val+(observed q reader layout stride j D s).2.val)

def nextIndex {F : ℕ} (j : Fin F) : Fin (F+1) := ⟨j.val+1,by have:=j.isLt;omega⟩

def afterCopy (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) : Machine q :=
  let p := observed q reader layout stride j D s
  let r := copyBody q reader layout stride j D s
  {r.1 with ram:=next q layout stride (tagEquiv F C (copying j D p.1 p.2)) r.1.ram}

def cycleSteps (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) : ℕ :=
  let p := observed q reader layout stride j D s
  (CommonMSDDirectoryRead.code q (layout.directory j) (layout.entry j)).length+1+
    ((CommonIntervalCopy.code q reader p.1.val D.val p.2.val (layout.source j) layout.target).length+1)

def cycleCost (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q) : ℕ :=
  let p := observed q reader layout stride j D s
  cost q (CommonMSDDirectoryRead.code q (layout.directory j) (layout.entry j))+
    cost q (CommonIntervalCopy.code q reader p.1.val D.val p.2.val (layout.source j) layout.target)

theorem afterRead_pc (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (h : Fits q reader (C:=C) layout stride)
    (j : Fin F) (D : Fin (C+1)) (s : Machine q) :
    pc q (afterRead q reader layout stride j D s).ram=
      (tagEquiv F C (copying j D (observed q reader layout stride j D s).1
        (observed q reader layout stride j D s).2)).val*stride := by
  unfold afterRead
  dsimp only
  rw [next_ready]
  exact pc_setPC q _ _ (tag_capacity q reader layout stride h _)

theorem afterCopy_pc (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (h : Fits q reader (C:=C) layout stride)
    (j : Fin F) (D : Fin (C+1)) (s : Machine q) :
    pc q (afterCopy q reader layout stride j D s).ram=
      (tagEquiv F C (ready (nextIndex j) (nextDest q reader layout stride j D s))).val*stride := by
  unfold afterCopy
  dsimp only
  rw [next_copying]
  exact pc_setPC q _ _ (tag_capacity q reader layout stride h _)

/-- Two real bodies and two RAM-only transitions form one fixed-policy
cycle, with precisely the sum of the actual read and copy charges. -/
theorem cycle (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (h : Fits q reader (C:=C) layout stride)
    (j : Fin F) (D : Fin (C+1)) (s : Machine q)
    (hpc : pc q s.ram=(tagEquiv F C (ready j.castSucc D)).val*stride) :
    ControlledNormalization.runLogical (policy q reader (C:=C) layout stride)
      (cycleSteps q reader layout stride j D s) s=
      (afterCopy q reader layout stride j D s,cycleCost q reader layout stride j D s) := by
  have hr := body_call q reader layout stride h (ready j.castSucc D) (terminal_ready j D) s hpc
  simp only [body_ready] at hr
  have hc := body_call q reader layout stride h
    (copying j D (observed q reader layout stride j D s).1
      (observed q reader layout stride j D s).2)
    (terminal_copying j D _ _) (afterRead q reader layout stride j D s)
    (afterRead_pc q reader layout stride h j D s)
  simp only [body_copying] at hc
  change ControlledNormalization.runLogical _ (_+_) s=_
  rw [CommonPolicyComposition.run_add,hr]
  change ( (ControlledNormalization.runLogical _ _ (afterRead q reader layout stride j D s)).1,
    cost q (CommonMSDDirectoryRead.code q (layout.directory j) (layout.entry j))+
      (ControlledNormalization.runLogical _ _ (afterRead q reader layout stride j D s)).2)=_
  rw [hc]
  rfl

theorem readBody_fields (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q)
    (hs : CommonMSDDirectoryRead.base q (layout.directory j) (layout.entry j)+
      CommonMSDDirectoryRead.blocks q (layout.entry j)≤q.N^q.exponent)
    (hw : CommonMSDDirectoryRead.total q (layout.entry j)≤CommonExchangeLeaf.bankWords q) :
    (readBody q reader layout stride j D s).1.disk=s.disk ∧
      observed q reader layout stride j D s=
        (bounded C (layout.offset j+3*CommonMSDDirectoryRead.stored q s.disk (layout.directory j) (layout.entry j) 0),
         bounded C (3*CommonMSDDirectoryRead.stored q s.disk (layout.directory j) (layout.entry j) 1)) := by
  obtain ⟨hd,hc,hf⟩ := CommonMSDDirectoryTagged.execute_complete q stride
    (tagEquiv F C (ready j.castSucc D)).val 0 (layout.directory j) (layout.entry j) s hs hw
  refine ⟨hd,?_⟩
  unfold observed readBody
  dsimp only
  rw [hf 0,hf 1]

/-- Reading metadata may overwrite the leaf bank, but it does not alter
the disk copied by the following interval program. -/
theorem cycle_disk (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (j : Fin F) (D : Fin (C+1)) (s : Machine q)
    (hs : CommonMSDDirectoryRead.base q (layout.directory j) (layout.entry j)+
      CommonMSDDirectoryRead.blocks q (layout.entry j)≤q.N^q.exponent)
    (hw : CommonMSDDirectoryRead.total q (layout.entry j)≤CommonExchangeLeaf.bankWords q) :
    let p := observed q reader layout stride j D s
    (afterCopy q reader layout stride j D s).disk=
      (executeRaw q (CommonIntervalCopy.code q reader p.1.val D.val p.2.val
        (layout.source j) layout.target) s).1.disk := by
  let p := observed q reader layout stride j D s
  have he := CommonTaggedSchedule.execute_payload q stride
    (tagEquiv F C (copying j D p.1 p.2)).val 0
    (CommonIntervalCopy.code q reader p.1.val D.val p.2.val (layout.source j) layout.target)
    (CommonIntervalCopy.codeFrom_safe q reader _ _ _ _ _ _ _)
    (afterRead q reader layout stride j D s) (afterRead q reader layout stride j D s) rfl
  have hd := congrArg (fun t : Machine q => t.disk) he
  have hr := (readBody_fields q reader layout stride j D s hs hw).1
  exact hd.trans (CommonMSDGatherInvariant.code_disk_congr q reader _ _ _ _ _
    (afterRead q reader layout stride j D s) s hr)

structure Fragment where
  index : ℕ
  source : ℕ
  offset : ℕ
  destination : ℕ
  words : ℕ
  charge : ℕ

structure Result (q : Configuration) (C : ℕ) where
  machine : Machine q
  destination : Fin (C+1)
  steps : ℕ
  charge : ℕ
  fragments : List Fragment

/-- Proof-side observation of the finite loop; it is absent from `policy`.
Each observed length comes from the preceding real directory read. -/
def observe (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) :
    ℕ → Fin (F+1) → Fin (C+1) → Machine q → Result q C
  | 0,_,D,s => ⟨s,D,0,0,[]⟩
  | fuel+1,j,D,s =>
      if h : j.val<F then
        let i : Fin F := ⟨j.val,h⟩
        let p := observed q reader layout stride i D s
        let tail := observe q reader layout stride fuel (nextIndex i)
          (nextDest q reader layout stride i D s) (afterCopy q reader layout stride i D s)
        ⟨tail.machine,tail.destination,
          cycleSteps q reader layout stride i D s+tail.steps,
          cycleCost q reader layout stride i D s+tail.charge,
          ⟨i.val,layout.source i,p.1.val,D.val,p.2.val,
            cycleCost q reader layout stride i D s⟩::tail.fragments⟩
      else ⟨s,D,0,0,[]⟩

theorem observed_charge (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride fuel : ℕ) (j : Fin (F+1)) (D : Fin (C+1)) (s : Machine q) :
    (observe q reader layout stride fuel j D s).charge=
      ((observe q reader layout stride fuel j D s).fragments.map Fragment.charge).sum := by
  induction fuel generalizing j D s with
  | zero => rfl
  | succ fuel ih =>
      simp only [observe]
      split
      · dsimp only
        rw [List.map_cons,List.sum_cons,ih]
      · rfl

/-- Every fragment is executed by the same policy. The final state has
the terminal read tag, and the exact I/O charge is the observed sum. -/
theorem complete_from (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (h : Fits q reader (C:=C) layout stride)
    (fuel : ℕ) (j : Fin (F+1)) (D : Fin (C+1)) (s : Machine q)
    (hcount : j.val+fuel=F)
    (hpc : pc q s.ram=(tagEquiv F C (ready j D)).val*stride) :
    let out := observe q reader layout stride fuel j D s
    ControlledNormalization.runLogical (policy q reader (C:=C) layout stride) out.steps s=
      (out.machine,out.charge) ∧
    pc q out.machine.ram=(tagEquiv F C (ready ⟨F,by omega⟩ out.destination)).val*stride ∧
    out.fragments.length=fuel := by
  induction fuel generalizing j D s with
  | zero =>
      have hj : j=(⟨F,Nat.lt_succ_self F⟩ : Fin (F+1)) := Fin.ext (by simpa using hcount)
      rw [hj] at hpc ⊢
      exact ⟨rfl,hpc,rfl⟩
  | succ fuel ih =>
      have hj : j.val<F := by omega
      let i : Fin F := ⟨j.val,hj⟩
      have hi : i.castSucc=j := Fin.ext rfl
      have hc := cycle q reader layout stride h i D s (by simpa only [hi] using hpc)
      have ht := ih (nextIndex i) (nextDest q reader layout stride i D s)
        (afterCopy q reader layout stride i D s) (by dsimp only [nextIndex,i];omega)
        (afterCopy_pc q reader layout stride h i D s)
      simp only [observe,dif_pos hj]
      refine ⟨?_,ht.2.1,?_⟩
      · rw [CommonPolicyComposition.run_add,hc,ht.1]
      · simpa only [List.length_cons] using congrArg Nat.succ ht.2.2

theorem complete (q : Configuration) (reader : Fin q.inventory.readers) {F C : ℕ}
    (layout : Layout F) (stride : ℕ) (h : Fits q reader (C:=C) layout stride)
    (D : Fin (C+1)) (s : Machine q)
    (hpc : pc q s.ram=(tagEquiv F C (ready (0 : Fin (F+1)) D)).val*stride) :
    let out := observe q reader layout stride F 0 D s
    ControlledNormalization.runLogical (policy q reader (C:=C) layout stride) out.steps s=
      (out.machine,(out.fragments.map Fragment.charge).sum) ∧
    policy q reader (C:=C) layout stride out.machine.ram=none ∧
    out.fragments.length=F ∧ Fintype.card (ResidentIndex q)≤q.M := by
  dsimp only
  obtain ⟨hr,hpc',hlen⟩ := complete_from q reader layout stride h F 0 D s (by simp) hpc
  refine ⟨?_,?_,hlen,resident_memory q⟩
  · rw [hr,observed_charge]
  · let out := observe q reader layout stride F 0 D s
    have hs : 0<stride := by
      simpa only [body_done,List.length_nil] using
        (h.code_length (ready ⟨F,by omega⟩ out.destination))
    apply CommonTaggedController.halted q stride (code q reader layout) terminal (next q layout stride)
      (tagEquiv F C (ready ⟨F,by omega⟩ out.destination))
    · simpa only [code_tag,body_done,List.length_nil] using hs
    · exact terminal_done _
    · simpa only [code_tag,body_done,List.length_nil,Nat.add_zero] using hpc'

end
end CodedSorting.CommonMSDGatherRun
end GatherRun

section GatherSequence
/-! Proof-side interval sequence for the directory-driven gather controller.
Only the controller reads its descriptors. This module specifies the exact
concatenation and verifies the real copy instructions for those descriptors. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonMSDGatherSequence
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine Disk)
open CommonMarginTransform (wordAt)
noncomputable section
variable {F : ℕ}

def total (count : Fin F → ℕ) (is : List (Fin F)) : ℕ := (is.map count).sum
@[simp] theorem total_nil (count : Fin F → ℕ) : total count []=0 := rfl
@[simp] theorem total_cons (count : Fin F → ℕ) (i : Fin F) (is : List (Fin F)) :
    total count (i::is)=count i+total count is := by simp [total]

def ghostFrom (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin F → ℕ) (target : ℕ) (start count : Fin F → ℕ) :
    ℕ → List (Fin F) → List (Instruction q)
  | _,[] => []
  | D,i::is => CommonIntervalCopy.code q reader (start i) D (count i) (source i) target ++
    ghostFrom q reader source target start count (D+count i) is

def ghostCode (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin F → ℕ) (target : ℕ) (start count : Fin F → ℕ) (D : ℕ) :
    List (Instruction q) := ghostFrom q reader source target start count D (List.finRange F)

def contents (q : Configuration) (source start count : Fin F → ℕ) (original : Disk q) :
    List (Fin F) → ℕ → Word q.w
  | [],_ => 0
  | i::is,j => if j<count i then wordAt q original (source i) (start i+j)
    else contents q source start count original is (j-count i)

def SourcesBefore (q : Configuration) (source start count : Fin F → ℕ)
    (target : ℕ) (is : List (Fin F)) : Prop :=
  ∀ i∈is,source i+PhysicalStreamCursor.blockCount q.block (start i+count i)+2≤target

theorem blockCount_mono (B n m : ℕ) (h : n≤m) :
    PhysicalStreamCursor.blockCount B n≤PhysicalStreamCursor.blockCount B m := by
  unfold PhysicalStreamCursor.blockCount
  exact Nat.div_le_div_right (by omega)

theorem copy_target_fits (q : Configuration) (target D N V : ℕ) (hV : D+N≤V)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block V+2≤q.N^q.exponent) :
    target+D/q.block+CommonIntervalCopy.pages q D N≤q.N^q.exponent := by
  have hp := CommonIntervalCopyBounds.pages_le q D N
  have hn := blockCount_mono q.block N V (by omega)
  have hb := CommonLeafProgram.block_positive q
  have hd : D/q.block≤PhysicalStreamCursor.blockCount q.block V := by
    apply Nat.le_trans (Nat.div_le_div_right (show D≤V by omega))
    unfold PhysicalStreamCursor.blockCount
    exact Nat.div_le_div_right (by omega)
  omega

theorem source_word_eq (q : Configuration) (source start count : Fin F → ℕ)
    (target : ℕ) (i : Fin F) (a b : Disk q)
    (hi : source i+PhysicalStreamCursor.blockCount q.block (start i+count i)+2≤target)
    (ht : target≤q.N^q.exponent)
    (heq : ∀ x : Fin (q.N^q.exponent),x.val<target → a x=b x)
    (j : ℕ) (hj : j<count i) :
    wordAt q a (source i) (start i+j)=wordAt q b (source i) (start i+j) := by
  have hblock : (start i+j)/q.block<PhysicalStreamCursor.blockCount q.block (start i+count i) := by
    apply (PhysicalStreamCursor.cursor_live_iff q.block (start i+count i) _
      (CommonLeafProgram.block_positive q)).2
    exact (Nat.div_mul_le_self _ _).trans_lt (by omega)
  have hfit : source i+(start i+j)/q.block<q.N^q.exponent := by omega
  rw [←CommonIntervalCopy.disk_word q a _ _ hfit,←CommonIntervalCopy.disk_word q b _ _ hfit]
  rw [heq _ (by rw [CommonColumnSplit.address_val q _ _ hfit];omega)]

theorem contents_eq (q : Configuration) (source start count : Fin F → ℕ)
    (target : ℕ) (a b : Disk q) (is : List (Fin F))
    (hs : SourcesBefore q source start count target is)
    (ht : target≤q.N^q.exponent)
    (heq : ∀ x : Fin (q.N^q.exponent),x.val<target → a x=b x) (j : ℕ) :
    contents q source start count a is j=contents q source start count b is j := by
  induction is generalizing j with
  | nil => rfl
  | cons i is ih =>
    rw [contents,contents]
    by_cases hj : j<count i
    · rw [if_pos hj,if_pos hj]
      exact source_word_eq q source start count target i a b (hs i (by simp)) ht heq j hj
    · rw [if_neg hj,if_neg hj]
      exact ih (fun k hk => hs k (by simp [hk])) (j-count i)

/-- Every interval is copied in order; metadata and source blocks before
`target` remain unchanged. The formula also preserves both boundary words. -/
theorem raw (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin F → ℕ) (target : ℕ) (start count : Fin F → ℕ)
    (D : ℕ) (is : List (Fin F)) (s : Machine q)
    (hs : SourcesBefore q source start count target is)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (D+total count is)+2≤q.N^q.exponent) :
    (∀ a : Fin (q.N^q.exponent),a.val<target →
      (executeRaw q (ghostFrom q reader source target start count D is) s).1.disk a=s.disk a) ∧
    (∀ j,target+j/q.block<q.N^q.exponent →
      wordAt q (executeRaw q (ghostFrom q reader source target start count D is) s).1.disk target j=
        if D≤j ∧ j<D+total count is then contents q source start count s.disk is (j-D)
        else wordAt q s.disk target j) := by
  induction is generalizing D s with
  | nil =>
    constructor
    · intro a ha;rfl
    · intro j hj;simp [ghostFrom,executeRaw,total,show ¬(D≤j ∧ j<D) by omega]
  | cons i is ih =>
    have hsi := hs i (by simp)
    have hst : SourcesBefore q source start count target is := fun k hk => hs k (by simp [hk])
    have htarget : target≤q.N^q.exponent := by omega
    have hsrc : source i+PhysicalStreamCursor.blockCount q.block (start i+count i)+2≤q.N^q.exponent := by omega
    have hdst := copy_target_fits q target D (count i) (D+total count (i::is))
      (by simp) hcap
    have hsep : source i+PhysicalStreamCursor.blockCount q.block (start i+count i)+2≤target+D/q.block ∨
        target+D/q.block+CommonIntervalCopy.pages q D (count i)≤source i := Or.inl (hsi.trans (Nat.le_add_right target (D/q.block)))
    let t := (executeRaw q (CommonIntervalCopy.code q reader (start i) D (count i) (source i) target) s).1
    have hbefore : ∀ a : Fin (q.N^q.exponent),a.val<target → t.disk a=s.disk a := by
      intro a ha
      exact (CommonIntervalCopy.raw q reader (start i) D (count i) (source i) target s hdst
        (CommonIntervalCopyBounds.readsOutside q (start i) D (count i) (source i) target hsrc hsep)).outside a
        (Or.inl (ha.trans_le (Nat.le_add_right target (D/q.block))))
    have hnextcap : target+2*PhysicalStreamCursor.blockCount q.block (D+count i+total count is)+2≤q.N^q.exponent := by
      simpa only [total_cons,Nat.add_assoc] using hcap
    obtain ⟨hframe,hwords⟩ := ih (D+count i) t hst hnextcap
    rw [ghostFrom,CommonPermutationPairs.raw_append]
    change (∀ a : Fin (q.N^q.exponent),a.val<target →
      (executeRaw q (ghostFrom q reader source target start count (D+count i) is) t).1.disk a=s.disk a) ∧ _
    constructor
    · intro a ha;exact (hframe a ha).trans (hbefore a ha)
    · intro j hj
      rw [hwords j hj]
      have hcontent := contents_eq q source start count target t.disk s.disk is hst htarget hbefore
      have hcopy := CommonIntervalCopyBounds.raw_word q reader (start i) D (count i) (source i) target s
        hsrc hdst hsep j hj
      change wordAt q t.disk target j=_ at hcopy
      simp only [total_cons]
      by_cases h0 : j<D
      · rw [if_neg (by omega),hcopy,if_neg (by omega),if_neg (by omega)]
      · by_cases h1 : j<D+count i
        · rw [if_neg (by omega),hcopy,if_pos (by omega),if_pos (by omega),contents,if_pos (by omega)]
        · by_cases h2 : j<D+(count i+total count is)
          · rw [if_pos (by omega),hcontent,if_pos (by omega),contents,if_neg (by omega)]
            congr 1
            omega
          · rw [if_neg (by omega),hcopy,if_neg (by omega),if_neg (by omega)]


/-- Exact charge of the actual copy bodies, before metadata reads. -/
def charge (q : Configuration) (count : Fin F → ℕ) : ℕ → List (Fin F) → ℕ
  | _,[] => 0
  | D,i::is => 6*CommonIntervalCopy.pages q D (count i)+charge q count (D+count i) is

theorem ghostFrom_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin F → ℕ) (target : ℕ) (start count : Fin F → ℕ)
    (D : ℕ) (is : List (Fin F)) :
    cost q (ghostFrom q reader source target start count D is)=charge q count D is := by
  induction is generalizing D with
  | nil => rfl
  | cons i is ih => rw [ghostFrom,CommonPermutationPairs.cost_append,CommonIntervalCopy.code_cost,ih,charge]

theorem ghostFrom_length (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin F → ℕ) (target : ℕ) (start count : Fin F → ℕ)
    (D : ℕ) (is : List (Fin F)) :
    (ghostFrom q reader source target start count D is).length=charge q count D is := by
  induction is generalizing D with
  | nil => rfl
  | cons i is ih => rw [ghostFrom,List.length_append,CommonIntervalCopy.code_length,ih,charge]

theorem ghostFrom_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin F → ℕ) (target : ℕ) (start count : Fin F → ℕ)
    (D : ℕ) (is : List (Fin F)) :
    ∀ i∈ghostFrom q reader source target start count D is,RespectsPC q i := by
  induction is generalizing D with
  | nil => simp [ghostFrom]
  | cons j is ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact CommonIntervalCopy.code_safe q reader _ _ _ _ _ i hi
    · exact ih _ i hi

/-- The additive overhead is per fragment, not quadratic in their number. -/
theorem charge_le (q : Configuration) (count : Fin F → ℕ)
    (D : ℕ) (is : List (Fin F)) :
    charge q count D is≤6*((is.map (fun i => PhysicalStreamCursor.blockCount q.block (count i))).sum+is.length) := by
  induction is generalizing D with
  | nil => simp [charge]
  | cons i is ih =>
    rw [charge,List.map_cons,List.sum_cons,List.length_cons]
    have hp := CommonIntervalCopyBounds.pages_le q D (count i)
    have ht := ih (D+count i)
    omega

theorem ghostFrom_disk_congr (q : Configuration) (reader : Fin q.inventory.readers)
    (source : Fin F → ℕ) (target : ℕ) (start count : Fin F → ℕ)
    (D : ℕ) (is : List (Fin F)) (s t : Machine q) (h : s.disk=t.disk) :
    (executeRaw q (ghostFrom q reader source target start count D is) s).1.disk=
      (executeRaw q (ghostFrom q reader source target start count D is) t).1.disk := by
  induction is generalizing D s t with
  | nil => exact h
  | cons i is ih =>
    rw [ghostFrom,CommonPermutationPairs.raw_append,CommonPermutationPairs.raw_append]
    apply ih
    exact CommonMSDGatherInvariant.code_disk_congr q reader _ _ _ _ _ s t h

end
end CodedSorting.CommonMSDGatherSequence
end GatherSequence
