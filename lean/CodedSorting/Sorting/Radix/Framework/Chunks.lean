import CodedSorting.Sorting.Radix.Framework.Words.Definitions
import CodedSorting.Shared.Records.TopPrefix
import CodedSorting.Sorting.Radix.Framework.GatherComplete

section Semantics
/-! High-digit radix recursion whose local calls sort the original keys.
The higher-prefix invariant makes each current-digit class contiguous in
a sorted chunk, without rekeying or changing record payloads. This is a
semantic specification, not a claimed RAM/disk implementation. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDSemantics
open BucketMachine ExternalMSD
variable {α : Type*}

def LocalCorrect (key : α → ℕ) (localSort : List α → List α) : Prop :=
  ∀ xs, (localSort xs).Perm xs ∧ (localSort xs).Pairwise (fun x y => key x≤key y)

def Prefix (key : α → ℕ) (base fuel p : ℕ) (xs : List α) : Prop :=
  ∀ x∈xs,key x/base^fuel=p

def digit (key : α → ℕ) (base : ℕ) (hb : 0<base) (fuel : ℕ) : α → Fin base :=
  fun x => MSD.digit base hb fuel (key x)

def prepare (H : ℕ) (hH : 0<H) (localSort : List α → List α) (xs : List α) :
    List (List α) := sortedChunks (H^2) (Nat.pow_pos hH) localSort xs

def sort (key : α → ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α → List α) : ℕ → List α → List α
  | 0,xs => xs
  | fuel+1,xs =>
      if xs.length≤H^2 then localSort xs
      else (List.finRange base).flatMap fun k =>
        sort key base hb H hH localSort fuel
          (child (digit key base hb fuel) (prepare H hH localSort xs) k)

theorem prepare_perm (key : α → ℕ) (H : ℕ) (hH : 0<H)
    (localSort : List α → List α) (hc : LocalCorrect key localSort) (xs : List α) :
    (prepare H hH localSort xs).flatten.Perm xs :=
  sortedChunks_perm _ _ _ (fun row => (hc row).1) xs

theorem prepare_prefix (key : α → ℕ) (base fuel p H : ℕ) (hH : 0<H)
    (localSort : List α → List α) (hc : LocalCorrect key localSort) (xs : List α)
    (hp : Prefix key base fuel p xs) :
    Prefix key base fuel p (prepare H hH localSort xs).flatten := by
  intro x hx
  exact hp x ((prepare_perm key H hH localSort hc xs).mem_iff.mp hx)

theorem prepare_digit_sorted (key : α → ℕ) (base : ℕ) (hb : 0<base)
    (fuel p H : ℕ) (hH : 0<H) (localSort : List α → List α)
    (hc : LocalCorrect key localSort) (xs : List α)
    (hp : Prefix key base (fuel+1) p xs)
    (row : List α) (hr : row∈prepare H hH localSort xs) :
    row.Pairwise (fun x y => digit key base hb fuel x≤digit key base hb fuel y) := by
  have hrow : row.Pairwise (fun x y => key x≤key y) := by
    obtain ⟨source,_,rfl⟩ := List.mem_map.mp hr
    exact (hc source).2
  have hp' := prepare_prefix key base (fuel+1) p H hH localSort hc xs hp
  apply hrow.imp_of_mem
  intro x y hx hy hxy
  exact CommonWordMSD.digit_mono_fixed_prefix base fuel (key x) (key y) hb hxy
    ((hp' x (List.mem_flatten.mpr ⟨row,hr,hx⟩)).trans
      (hp' y (List.mem_flatten.mpr ⟨row,hr,hy⟩)).symm)

theorem child_prefix (key : α → ℕ) (base : ℕ) (hb : 0<base)
    (fuel p : ℕ) (rows : List (List α)) (hp : Prefix key base (fuel+1) p rows.flatten)
    (k : Fin base) :
    Prefix key base fuel (p*base+k.val) (child (digit key base hb fuel) rows k) := by
  intro x hx
  have hk := congrArg Fin.val (child_key (digit key base hb fuel) rows k x hx)
  obtain ⟨row,hr,hxr⟩ := List.mem_flatMap.mp hx
  have hxrow := (mem_bucket (digit key base hb fuel) row k x).mp hxr |>.1
  have hh := hp x (List.mem_flatten.mpr ⟨row,hr,hxrow⟩)
  have hdiv : (key x/base^fuel)/base=p := by
    simpa only [Nat.div_div_eq_div_mul,pow_succ] using hh
  have he := Nat.mod_add_div (key x/base^fuel) base
  change key x/base^fuel%base=k.val at hk
  rw [hk,hdiv] at he
  nlinarith

private theorem flatMap_perm {β : Type*} (keys : List β) (f g : β → List α)
    (h : ∀ k∈keys,(f k).Perm (g k)) : (keys.flatMap f).Perm (keys.flatMap g) := by
  induction keys with
  | nil => simp
  | cons k rest ih =>
    simp only [List.flatMap_cons]
    exact (h k (by simp)).append (ih (fun k hk => h k (by simp [hk])))

theorem sort_perm (key : α → ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α → List α) (hc : LocalCorrect key localSort)
    (fuel : ℕ) (xs : List α) : (sort key base hb H hH localSort fuel xs).Perm xs := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl xs
  | succ fuel ih =>
    rw [sort]
    split
    · exact (hc xs).1
    · exact (flatMap_perm _ _ _ (fun k _ => ih _)).trans
        ((gather_perm (digit key base hb fuel) _).trans
          (prepare_perm key H hH localSort hc xs))

theorem prefix_order (base fuel x y p q : ℕ) (hb : 0<base)
    (hx : x/base^fuel=p) (hy : y/base^fuel=q) (hpq : p<q) : x≤y := by
  have hpow : 0<base^fuel := Nat.pow_pos hb
  have hr := Nat.mod_lt x hpow
  have hex := Nat.mod_add_div x (base^fuel)
  have hey := Nat.mod_add_div y (base^fuel)
  rw [hx] at hex
  rw [hy] at hey
  have hm := Nat.mul_le_mul_left (base^fuel) (Nat.succ_le_of_lt hpq)
  simp only [Nat.succ_eq_add_one,Nat.mul_add,Nat.mul_one] at hm
  have hlow := Nat.div_mul_le_self y (base^fuel)
  rw [hy,Nat.mul_comm] at hlow
  omega

theorem sort_pairwise (key : α → ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α → List α) (hc : LocalCorrect key localSort)
    (fuel p : ℕ) (xs : List α) (hp : Prefix key base fuel p xs) :
    (sort key base hb H hH localSort fuel xs).Pairwise (fun x y => key x≤key y) := by
  induction fuel generalizing p xs with
  | zero =>
    change xs.Pairwise _
    have ht : xs.Pairwise (fun _ _ => True) := List.pairwise_of_forall (by intros; trivial)
    apply ht.imp_of_mem
    intro x y hx hy _
    have hx' := hp x hx
    have hy' := hp y hy
    simp only [pow_zero,Nat.div_one] at hx' hy'
    omega
  | succ fuel ih =>
    rw [sort]
    split
    · exact (hc xs).2
    · let rows := prepare H hH localSort xs
      let output := fun k => sort key base hb H hH localSort fuel
        (child (digit key base hb fuel) rows k)
      have hp' : Prefix key base (fuel+1) p rows.flatten :=
        prepare_prefix key base (fuel+1) p H hH localSort hc xs hp
      have hc' (k : Fin base) :
          Prefix key base fuel (p*base+k.val) (child (digit key base hb fuel) rows k) :=
        child_prefix key base hb fuel p rows hp' k
      have ho (k : Fin base) : Prefix key base fuel (p*base+k.val) (output k) := by
        intro x hx
        exact hc' k x ((sort_perm key base hb H hH localSort hc fuel _).mem_iff.mp hx)
      change ((List.finRange base).map output).flatten.Pairwise _
      apply BucketOrder.pairwise_flatten_of_buckets
      · intro ys hys
        obtain ⟨k,_,rfl⟩ := List.mem_map.mp hys
        exact ih _ _ (hc' k)
      · apply (List.pairwise_lt_finRange base).map output
        intro k l hkl x hx y hy
        exact prefix_order base fuel (key x) (key y) (p*base+k.val) (p*base+l.val)
          hb (ho k x hx) (ho l y hy) (Nat.add_lt_add_left hkl _)

theorem sort_correct (key : α → ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α → List α) (hc : LocalCorrect key localSort)
    (fuel : ℕ) (xs : List α) (hbound : ∀ x∈xs,key x<base^fuel) :
    (sort key base hb H hH localSort fuel xs).Perm xs ∧
      (sort key base hb H hH localSort fuel xs).Pairwise (fun x y => key x≤key y) :=
  ⟨sort_perm key base hb H hH localSort hc fuel xs,
    sort_pairwise key base hb H hH localSort hc fuel 0 xs
      (fun x hx => Nat.div_eq_of_lt (hbound x hx))⟩

theorem prepare_intervals (key : α → ℕ) (base : ℕ) (hb : 0<base)
    (fuel p H : ℕ) (hH : 0<H) (localSort : List α → List α)
    (hc : LocalCorrect key localSort) (xs : List α)
    (hp : Prefix key base (fuel+1) p xs)
    (row : List α) (hr : row∈prepare H hH localSort xs) (k : Fin base) :
    interval (digit key base hb fuel) row k=bucket (digit key base hb fuel) row k :=
  sorted_interval_is_bucket _ _
    (prepare_digit_sorted key base hb fuel p H hH localSort hc xs hp row hr) k

theorem record_local_correct (w : ℕ) :
    LocalCorrect (@CommonWordMSD.key w) CommonWordMSD.localSort :=
  CommonWordMSD.localSort_correct

noncomputable def recordSort (w base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H) :
    ℕ → List (KeyRecordWords.Record w) → List (KeyRecordWords.Record w) :=
  sort CommonWordMSD.key base hb H hH CommonWordMSD.localSort

theorem recordSort_correct (w base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (fuel : ℕ) (xs : List (KeyRecordWords.Record w))
    (hbound : ∀ x∈xs,CommonWordMSD.key x<base^fuel) :
    (recordSort w base hb H hH fuel xs).Perm xs ∧
      (recordSort w base hb H hH fuel xs).Pairwise
        (fun x y => CommonWordMSD.key x≤CommonWordMSD.key y) :=
  sort_correct _ base hb H hH _ (record_local_correct w) fuel xs hbound

end CodedSorting.CommonMSDSemantics
end Semantics

section Chunks
/-! Sort every public H²-sized chunk on the common finite machine.
The final partial chunk receives top padding; real margin scans add and
remove this padding. Every slab invokes the verified local program. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDChunks
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonSlabBatch CommonPrunedParameters
open CommonLeafProgram (Machine)
noncomputable section
attribute [local irreducible] CommonLocalRecursion.build
  ControlledNormalization.runLogical

def chunkSize (q : Configuration) : ℕ := q.height^2
def chunkCount (q : Configuration) (n : ℕ) : ℕ :=
  PhysicalStreamCursor.blockCount (chunkSize q) n
def paddedSize (q : Configuration) (n : ℕ) : ℕ := chunkCount q n*chunkSize q

theorem chunk_positive (q : Configuration) : 0<chunkSize q :=
  Nat.pow_pos (CommonLocalRecursion.height_pos q)

theorem padded_covers (q : Configuration) (n : ℕ) : n≤paddedSize q n :=
  LayoutConversion.blockCount_covers n (chunkSize q) (chunk_positive q)

def operation (q : Configuration) (n : ℕ) : Records q n→Records q n :=
  CommonRecordTopPrefix.operation (padded_covers q n)
    (batchOutput (C:=chunkCount q n) (r:=chunkSize q) Columnsort.sortColumn)

def space (q : Configuration) (hnormal : Normalized q) (n : ℕ) : ℕ :=
  max 1 (recordBlocks q (paddedSize q n))+
    chunkCount q n*recordBlocks q (chunkSize q)+
    CommonLocalRecursion.space q hnormal 3 (chunkSize q)

def charge (q : Configuration) (n : ℕ) : ℕ :=
  3*recordBlocks q (paddedSize q n)+
    chunkCount q n*(CommonLocalBudget.budget q 3 (chunkSize q)+12*recordBlocks q (chunkSize q))+
    3*recordBlocks q n

def batchProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (C : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+recordBlocks q (C*chunkSize q)≤buffer)
    (hw : buffer+C*recordBlocks q (chunkSize q)+
      CommonLocalRecursion.space q hnormal 3 (chunkSize q)≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (C*chunkSize q) source buffer limit (batchOutput Columnsort.sortColumn) := by
  let R := chunkSize q
  let work := buffer+C*recordBlocks q R
  have hwork : work+CommonLocalRecursion.space q hnormal 3 R≤limit := hw
  have hpos : 0<recordBlocks q R :=
    CommonLocalRecursion.blocks_positive q R (chunk_positive q)
  let kids : Children q C R buffer work limit Columnsort.sortColumn := fun c =>
    CommonLocalMachine.localProgram q reader hnormal R le_rfl he
      (recordBase q R buffer c.val) work limit
      (by
        rw [max_eq_right hpos]
        have h := base_end q (C:=C) (n:=R*3) (buffer:=buffer) c
        simpa only [←record_blocks,work] using h)
      hwork hl
  exact CommonSlabBatch.program reader kids hs
    (by dsimp only [work]; rw [record_blocks]) (by omega) hl

theorem batchProgram_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (C : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+recordBlocks q (C*chunkSize q)≤buffer)
    (hw : buffer+C*recordBlocks q (chunkSize q)+
      CommonLocalRecursion.space q hnormal 3 (chunkSize q)≤limit)
    (hl : limit≤q.N^q.exponent) :
    (batchProgram q reader hnormal C he source buffer limit hs hw hl).charge≤
      C*(CommonLocalBudget.budget q 3 (chunkSize q)+12*recordBlocks q (chunkSize q)) := by
  unfold batchProgram
  simp only [CommonSlabBatch.program]
  have hsum : ∀ (p : Children q C (chunkSize q) buffer
      (buffer+C*recordBlocks q (chunkSize q)) limit Columnsort.sortColumn),
      (∀ c,(p c).charge≤CommonLocalBudget.budget q 3 (chunkSize q)) →
      childrenCharge p (List.finRange C)≤C*CommonLocalBudget.budget q 3 (chunkSize q) := by
    intro p hp
    unfold childrenCharge
    calc
      _ ≤ ((List.finRange C).map (fun _=>CommonLocalBudget.budget q 3 (chunkSize q))).sum := by
        apply List.sum_le_sum
        intro i hi
        exact hp i
      _ = C*CommonLocalBudget.budget q 3 (chunkSize q) := by simp
  refine (Nat.add_le_add_right (hsum _ ?_) _).trans ?_
  · intro c
    exact CommonLocalMachine.local_charge_le q reader hnormal
      (chunkSize q) le_rfl he _ _ _ _ hw hl
  · rw [←record_blocks]
    exact le_of_eq (by ring)

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*paddedSize q n<(2^q.w)^q.digits) :
    Program q n source buffer limit (operation q n) := by
  let slabs := buffer+max 1 (recordBlocks q (paddedSize q n))
  have hslabs : slabs+chunkCount q n*recordBlocks q (chunkSize q)+
      CommonLocalRecursion.space q hnormal 3 (chunkSize q)≤limit := by
    simpa only [slabs,space,Nat.add_assoc] using hw
  let inner := batchProgram q reader hnormal (chunkCount q n) he buffer slabs limit
    (by
      change buffer+recordBlocks q (paddedSize q n)≤buffer+max 1 (recordBlocks q (paddedSize q n))
      omega) hslabs hl
  exact CommonRecordTopPrefix.program q reader (padded_covers q n) inner hs
    le_rfl (by omega) hl hshape

theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*paddedSize q n<(2^q.w)^q.digits) :
    (program q reader hnormal n he source buffer limit hs hw hl hshape).charge≤charge q n := by
  unfold program
  rw [CommonRecordTopPrefix.program_charge]
  have h := batchProgram_charge_le q reader hnormal (chunkCount q n) he buffer
    (buffer+max 1 (recordBlocks q (paddedSize q n))) limit (by
      change buffer+recordBlocks q (paddedSize q n)≤buffer+max 1 (recordBlocks q (paddedSize q n))
      omega)
    (by simpa only [space,Nat.add_assoc] using hw) hl
  unfold charge
  exact Nat.add_le_add_right (Nat.add_le_add_left h _) _

/-- Correct chunk output, preservation, termination and charged transfers
describe the same actual machine run. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hnormal : Normalized q) (n : ℕ) (he : 2≤q.exponent)
    (source buffer limit : ℕ)
    (hs : source+max 1 (recordBlocks q n)≤buffer)
    (hw : buffer+space q hnormal n≤limit) (hl : limit≤q.N^q.exponent)
    (hshape : 3*paddedSize q n<(2^q.w)^q.digits)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : charge q n≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader hnormal n he source buffer limit hs hw hl hshape
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    Encoded q result.1.disk source (operation q n f) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+recordBlocks q n≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧ result.2≤charge q n ∧
    Fintype.card (ResidentIndex q)≤q.M :=
  by
    let p := program q reader hnormal n he source buffer limit hs hw hl hshape
    have hc : p.charge≤charge q n :=
      program_charge_le q reader hnormal n he source buffer limit hs hw hl hshape
    obtain ⟨hout,hframe,hhalt,hcost,hram⟩ :=
      CommonRecordProgram.complete q p s f hf (hc.trans hsize) hpc
    exact ⟨hout,hframe,hhalt,hcost.trans hc,hram⟩

end
end CodedSorting.CommonMSDChunks
end Chunks

section Children
/-! Proof-side parent invariant for in-place depth-first MSD calls.
The first j children have returned; all remaining children still contain
exactly the partition output. These lists describe disk contents and are
never controller state. Completing every child yields the existing MSD
specification, so its sorting proof can be reused without a new algorithm. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDChildren
open BucketMachine ExternalMSD CommonMSDSemantics
variable {α : Type*} {K : ℕ}

/-- Values before the next child's fixed physical offset. -/
def front (children : Fin K→List α) (j : ℕ) : List α :=
  ((List.finRange K).take j).flatMap children

def back (children : Fin K→List α) (j : ℕ) : List α :=
  ((List.finRange K).drop j).flatMap children

/-- The parent after exactly its first j child calls have returned. -/
def stage (before after : Fin K→List α) (j : ℕ) : List α :=
  front after j++back before j

@[simp] theorem partial_zero (before after : Fin K→List α) :
    stage before after 0=(List.finRange K).flatMap before := by
  simp [stage,front,back]

@[simp] theorem partial_done (before after : Fin K→List α) :
    stage before after K=(List.finRange K).flatMap after := by
  have ht : (List.finRange K).take K=List.finRange K :=
    List.take_of_length_le (by simp)
  have hd : (List.finRange K).drop K=[] := List.drop_eq_nil_of_le (by simp)
  simp [stage,front,back,ht,hd]

theorem prefix_next (children : Fin K→List α) (j : Fin K) :
    front children (j.val+1)=front children j.val++children j := by
  unfold front
  rw [List.take_succ_eq_append_getElem (show j.val<(List.finRange K).length by simpa using j.isLt)]
  simp

theorem suffix_next (children : Fin K→List α) (j : Fin K) :
    back children j.val=children j++back children (j.val+1) := by
  unfold back
  rw [List.drop_eq_getElem_cons (show j.val<(List.finRange K).length by simpa using j.isLt)]
  simp

theorem prefix_length (before after : Fin K→List α)
    (hl : ∀ k,(after k).length=(before k).length) (j : ℕ) :
    (front after j).length=(front before j).length := by
  simp only [front,List.length_flatMap,Function.comp_def]
  simp_rw [hl]

/-- Processing earlier siblings does not change the next sibling's offset. -/
theorem current_context (before after : Fin K→List α)
    (hl : ∀ k,(after k).length=(before k).length) (j : Fin K) :
    stage before after j.val=
        front after j.val++before j++back before (j.val+1) ∧
    stage before after (j.val+1)=
        front after j.val++after j++back before (j.val+1) ∧
    (front after j.val).length=(front before j.val).length := by
  refine ⟨?_,?_,prefix_length before after hl j.val⟩
  · rw [stage,suffix_next,List.append_assoc]
  · rw [stage,prefix_next]

/-- All parent extents are unchanged, including a zero-length child. -/
theorem partial_length (before after : Fin K→List α)
    (hl : ∀ k,(after k).length=(before k).length) (j : ℕ) :
    (stage before after j).length=((List.finRange K).flatMap before).length := by
  rw [stage,List.length_append,prefix_length before after hl j]
  rw [←List.length_append]
  unfold front back
  rw [←List.flatMap_append,List.take_append_drop]

theorem next_offset (before after : Fin K→List α)
    (hl : ∀ k,(after k).length=(before k).length) (j : Fin K) :
    (front after (j.val+1)).length=(front before j.val).length+(before j).length := by
  rw [prefix_next,List.length_append,prefix_length before after hl j.val,hl]

theorem child_fits (before : Fin K→List α) (j : Fin K) :
    (front before j.val).length+(before j).length≤
      ((List.finRange K).flatMap before).length := by
  have hh := current_context before before (fun _ => rfl) j
  have hlen := congrArg List.length hh.1
  rw [partial_length before before (fun _ => rfl) j.val] at hlen
  simp only [List.length_append] at hlen
  omega

private theorem sum_filtered {β : Type*} (xs : List β) (p : β→Prop) [DecidablePred p]
    (f : β→ℕ) :
    ((xs.filter (fun x => decide (p x))).map f).sum=
      (xs.map (fun x => if p x then f x else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : p x <;> simp [hx,ih]

/-- The semantic prefix is the exact record offset written in the directory. -/
theorem front_length_start (children : Fin K→List α) (j : Fin K) :
    (front children j.val).length=
      CommonMSDDirectory.start (fun k => (children k).length) j := by
  have hmem (k : Fin K) : k∈(List.finRange K).take j.val ↔ k<j := by
    rw [List.mem_take_iff_getElem]
    constructor
    · rintro ⟨i,hi,he⟩
      have hv := congrArg Fin.val he
      simp at hv
      change k.val<j.val
      omega
    · intro hk
      refine ⟨k.val,by simpa using hk,?_⟩
      simp
  have ht : (List.finRange K).take j.val=
      (List.finRange K).filter (fun k => decide (k<j)) := by
    rw [List.Nodup.take_eq_filter_mem (List.nodup_finRange K)]
    apply List.filter_congr
    intro k _
    simp [hmem]
  simp only [front,List.length_flatMap,Function.comp_def]
  rw [ht,sum_filtered,←List.ofFn_eq_map,List.sum_ofFn]
  rfl

/-- The child family is the one already used by the proved MSD recursion. -/
def nodeChildren (key : α→ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α→List α) (fuel : ℕ) (xs : List α) : Fin base→List α :=
  ExternalMSD.child (CommonMSDSemantics.digit key base hb fuel)
    (CommonMSDSemantics.prepare H hH localSort xs)

def returnedChildren (key : α→ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α→List α) (fuel : ℕ) (xs : List α) : Fin base→List α :=
  fun k => CommonMSDSemantics.sort key base hb H hH localSort fuel
    (nodeChildren key base hb H hH localSort fuel xs k)

theorem returned_length (key : α→ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α→List α) (hc : LocalCorrect key localSort)
    (fuel : ℕ) (xs : List α) (k : Fin base) :
    (returnedChildren key base hb H hH localSort fuel xs k).length=
      (nodeChildren key base hb H hH localSort fuel xs k).length :=
  (CommonMSDSemantics.sort_perm key base hb H hH localSort hc fuel _).length_eq

theorem parent_size (key : α→ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α→List α) (hc : LocalCorrect key localSort)
    (fuel j : ℕ) (xs : List α) :
    (stage (nodeChildren key base hb H hH localSort fuel xs)
      (returnedChildren key base hb H hH localSort fuel xs) j).length=xs.length := by
  rw [partial_length _ _ (returned_length key base hb H hH localSort hc fuel xs)]
  exact ((ExternalMSD.gather_perm (CommonMSDSemantics.digit key base hb fuel) _).trans
    (CommonMSDSemantics.prepare_perm key H hH localSort hc xs)).length_eq

/-- Once all children have returned, the parent equals the original
recursive specification. No permutation of equal-key payloads is assumed. -/
theorem parent_done (key : α→ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α→List α) (fuel : ℕ) (xs : List α) (hlarge : H^2<xs.length) :
    stage (nodeChildren key base hb H hH localSort fuel xs)
      (returnedChildren key base hb H hH localSort fuel xs) base=
      CommonMSDSemantics.sort key base hb H hH localSort (fuel+1) xs := by
  rw [partial_done,CommonMSDSemantics.sort,if_neg (by omega)]
  rfl

/-- The actual full-key local-call endpoint matches the terminal branch. -/
theorem parent_terminal (key : α→ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α→List α) (fuel : ℕ) (xs : List α) (hsmall : xs.length≤H^2) :
    localSort xs=CommonMSDSemantics.sort key base hb H hH localSort (fuel+1) xs := by
  rw [CommonMSDSemantics.sort,if_pos hsmall]

end CodedSorting.CommonMSDChildren
end Children

section ChunksSemantic
/-! The actual padded chunk batch produces exactly the unpadded list of
locally sorted H² chunks used in the full-key MSD specification. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDChunksSemantic
open BucketMachine CommonWordMSD
noncomputable section

private theorem localSort_length {w : ℕ} (xs : List (KeyRecordWords.Record w)) :
    (localSort xs).length=xs.length := (localSort_perm xs).length_eq

private theorem localSort_top {w : ℕ} (xs : List (KeyRecordWords.Record w)) (p : ℕ) :
    localSort (xs++List.replicate p ⊤)=localSort xs++List.replicate p ⊤ := by
  have hp := (localSort_perm (xs++List.replicate p ⊤)).trans
    ((localSort_perm xs).append_right _).symm
  have hleft : (localSort (xs++List.replicate p ⊤)).Pairwise (·≤·) := by
    simpa only [localSort] using
      (Columnsort.sortColumn_monotone (xs++List.replicate p (⊤ : KeyRecordWords.Record w)).get).ofFn_sorted
  have hright : (localSort xs++List.replicate p ⊤).Pairwise (·≤·) := by
    apply List.pairwise_append.mpr
    refine ⟨(Columnsort.sortColumn_monotone xs.get).ofFn_sorted,?_,?_⟩
    · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
    · intro a ha b hb
      have hb' : b=(⊤ : KeyRecordWords.Record w) := (List.mem_replicate.mp hb).2
      rw [hb']
      exact le_top
  exact List.eq_of_perm_of_sorted hp hleft hright

private theorem pack_full_prefix {α : Type*} (r : ℕ) (hr : 0<r)
    (front back : List α) (hf : front.length=r) :
    pack r hr (front++back)=front::pack r hr back := by
  cases front with
  | nil => simp only [List.length_nil] at hf; omega
  | cons a rest =>
    rw [List.cons_append,pack]
    change (a::rest++back).take r::pack r hr ((a::rest++back).drop r)=_
    rw [List.take_left' hf,List.drop_left' hf]

private theorem pack_full_rows {α : Type*} (r : ℕ) (hr : 0<r) (rows : List (List α))
    (h : ∀ row∈rows,row.length=r) : pack r hr rows.flatten=rows := by
  induction rows with
  | nil => simp [pack]
  | cons row rest ih =>
    rw [List.flatten_cons,pack_full_prefix r hr row _ (h row (by simp)),
      ih (fun row hh => h row (by simp [hh]))]

private theorem trim_list {α : Type*} [LinearOrder α] [OrderTop α]
    {n N : ℕ} (hn : n≤N) (f : Fin N→α) :
    List.ofFn (RecursiveColumnsort.trim hn f)=(List.ofFn f).take n := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    simp [RecursiveColumnsort.trim]

private theorem batch_list (q : CommonSortingNormalization.Configuration) (C r : ℕ)
    (hr : 0<r) (f : CommonRecordProgram.Records q (C*r)) :
    List.ofFn (CommonSlabBatch.batchOutput Columnsort.sortColumn f)=
      ((pack r hr (List.ofFn f)).map localSort).flatten := by
  let rows := List.ofFn (fun c : Fin C => List.ofFn (CommonLocalSemantic.columns C r f c))
  have hf : (List.ofFn f)=rows.flatten := by
    rw [List.ofFn_mul]
    congr 2
    funext c
    congr 1
    funext i
    unfold CommonLocalSemantic.columns
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have hrows : ∀ row∈rows,row.length=r := by
    intro row hrow
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hrow
    simp
  rw [hf,pack_full_rows r hr rows hrows]
  simp only [rows,List.map_ofFn,Function.comp_def,localSort_ofFn]
  rw [List.ofFn_mul]
  congr 2
  funext c
  congr 1
  funext i
  unfold CommonSlabBatch.batchOutput PhysicalLocalSortPadding.flattenColumns
  have hid : (⟨c.val*r+i.val,by have:=c.isLt; have:=i.isLt; nlinarith⟩ : Fin (C*r))=
      finProdFinEquiv (c,i) := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  rw [hid,Equiv.symm_apply_apply]

private theorem sorted_pack_top {w : ℕ} (r : ℕ) (hr : 0<r)
    (xs : List (KeyRecordWords.Record w)) (p : ℕ) :
    (((pack r hr (xs++List.replicate p ⊤)).map localSort).flatten).take xs.length=
      ((pack r hr xs).map localSort).flatten := by
  induction xs using pack.induct r hr generalizing p with
  | case1 => simp [pack]
  | case2 a rest ih =>
    let xs := a::rest
    by_cases hshort : xs.length≤r
    · have htake : (xs++List.replicate p ⊤).take r=
          xs++List.replicate (min (r-xs.length) p) ⊤ := by
        rw [List.take_append_eq_append_take,List.take_of_length_le hshort,List.take_replicate]
      have hlen : xs.length≤(localSort ((xs++List.replicate p ⊤).take r)).length := by
        rw [localSort_length,htake,List.length_append,List.length_replicate]
        omega
      change (((pack r hr (xs++List.replicate p ⊤)).map localSort).flatten).take xs.length=_
      have hexpand : pack r hr (xs++List.replicate p ⊤)=
          (xs++List.replicate p ⊤).take r::pack r hr ((xs++List.replicate p ⊤).drop r) := by
        exact pack.eq_2 r hr a (rest++List.replicate p ⊤)
      rw [hexpand,List.map_cons,List.flatten_cons,List.take_append_of_le_length hlen,
        htake,localSort_top,←localSort_length xs,List.take_left]
      have he : pack r hr xs=[xs] := by
        change pack r hr (a::rest)=[a::rest]
        rw [pack,List.take_of_length_le hshort,List.drop_eq_nil_of_le hshort,pack]
      rw [he]
      simp
    · have hlarge : r≤xs.length := by omega
      have hfront : (xs.take r).length=r := by simp [hlarge]
      have he : xs++List.replicate p ⊤=xs.take r++(xs.drop r++List.replicate p ⊤) := by
        rw [←List.append_assoc,List.take_append_drop]
      rw [show a::rest=xs from rfl,he,pack_full_prefix r hr _ _ hfront,
        List.map_cons,List.flatten_cons,List.take_append_eq_append_take]
      have hkeep : (localSort (xs.take r)).take xs.length=localSort (xs.take r) := by
        apply List.take_of_length_le
        rw [localSort_length,hfront]
        exact hlarge
      rw [hkeep,localSort_length,hfront]
      have htail := ih p
      change (((pack r hr (xs.drop r++List.replicate p ⊤)).map localSort).flatten).take
        (xs.drop r).length=_ at htail
      rw [List.length_drop] at htail
      rw [htail]
      change _=((pack r hr (a::rest)).map localSort).flatten
      rw [pack]
      rfl

/-- The actual fixed-size padded batch agrees byte-for-byte with the pure
MSD preparation; only the newly introduced top padding is removed. -/
theorem operation_list (q : CommonSortingNormalization.Configuration) (n : ℕ)
    (f : CommonRecordProgram.Records q n) :
    List.ofFn (CommonMSDChunks.operation q n f)=
      (CommonMSDSemantics.prepare q.height (CommonLocalRecursion.height_pos q)
        CommonWordMSD.localSort (List.ofFn f)).flatten := by
  unfold CommonMSDChunks.operation CommonRecordTopPrefix.operation
  rw [trim_list,batch_list q _ _ (CommonMSDChunks.chunk_positive q),
    RecursiveColumnsort.pad_ofFn (CommonMSDChunks.padded_covers q n)]
  have h := sorted_pack_top (CommonMSDChunks.chunkSize q) (CommonMSDChunks.chunk_positive q)
    (List.ofFn f) (CommonMSDChunks.paddedSize q n-n)
  simpa only [List.length_ofFn,CommonMSDSemantics.prepare,ExternalMSD.sortedChunks,
    CommonMSDChunks.chunkSize] using h

theorem operation_perm (q : CommonSortingNormalization.Configuration) (n : ℕ)
    (f : CommonRecordProgram.Records q n) :
    (List.ofFn (CommonMSDChunks.operation q n f)).Perm (List.ofFn f) := by
  rw [operation_list]
  exact CommonMSDSemantics.prepare_perm CommonWordMSD.key q.height
    (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
    (CommonMSDSemantics.record_local_correct q.w) _

theorem operation_prefix (q : CommonSortingNormalization.Configuration) (n base fuel p : ℕ)
    (f : CommonRecordProgram.Records q n)
    (hp : CommonMSDSemantics.Prefix CommonWordMSD.key base fuel p (List.ofFn f)) :
    CommonMSDSemantics.Prefix CommonWordMSD.key base fuel p
      (List.ofFn (CommonMSDChunks.operation q n f)) := by
  intro x hx
  exact hp x ((operation_perm q n f).mem_iff.mp hx)

theorem operation_bucket_length (q : CommonSortingNormalization.Configuration) (n K : ℕ)
    (key : KeyRecordWords.Record q.w→Fin K) (f : CommonRecordProgram.Records q n)
    (k : Fin K) :
    (bucket key (List.ofFn (CommonMSDChunks.operation q n f)) k).length=
      (bucket key (List.ofFn f) k).length := by
  exact ((operation_perm q n f).filter (fun a => key a==k)).length_eq

end
end CodedSorting.CommonMSDChunksSemantic
end ChunksSemantic
