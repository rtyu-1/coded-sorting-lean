import CodedSorting.Shared.Records.WordRoles.Transpose

section SlabJoin
/-! Static, concrete column concatenation. Every slab block uses two
read/modify/write fragments; the selection maps touch only its useful
words. Program text contains only public dimensions and addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonStaticSlabJoin
open WordControl BitWordPacking PhysicalStreamCursor
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store Disk Machine machine)
open CommonLeafBatchProgram (extendDisk)
open CommonColumnJoin (start useful first last joinStep joinDisk Separated)
noncomputable section
abbrev address := CommonColumnSplit.address

def select (q : Configuration) (n k targetBlock : ℕ) : CommonBlockPair.Selection q := fun j =>
  let pair : Fin q.block × Fin q.w := finProdFinEquiv.symm j
  if h : start q.block n k≤targetBlock*q.block+pair.1.val ∧
      targetBlock*q.block+pair.1.val<start q.block n k+useful q.block n k then
    some (finProdFinEquiv (⟨targetBlock*q.block+pair.1.val-start q.block n k,by
      have : useful q.block n k≤q.block := Nat.min_le_left _ _
      omega⟩,pair.2))
  else none

theorem blend_merge (q : Configuration) (n k j : ℕ) (a b : Words q.block q.w) :
    CommonBlockPair.blend q (select q n k j) a b=CommonColumnJoin.merge n k j a b := by
  apply (blockBits q.block q.w).injective
  funext x
  obtain ⟨⟨word,bit⟩,rfl⟩ := finProdFinEquiv.surjective x
  rw [CommonBlockPair.blend_bits]
  simp only [select,Equiv.symm_apply_apply,blockBits_at]
  split_ifs with h
  · simp only [blockBits_at,CommonColumnJoin.merge,dif_pos h]
  · simp only [CommonColumnJoin.merge,dif_neg h]

def fragment (q : Configuration) (reader : Fin q.inventory.readers)
    (n source target k : ℕ) : List (Instruction q) :=
  CommonBlockPair.code q reader (address q source k) (address q target (first q.block n k))
    (select q n k (first q.block n k)) ++
  CommonBlockPair.code q reader (address q source k) (address q target (last q.block n k))
    (select q n k (last q.block n k))

def codeFrom (q : Configuration) (reader : Fin q.inventory.readers)
    (n source target k : ℕ) : ℕ → List (Instruction q)
  | 0 => []
  | left+1 => fragment q reader n source target k ++ codeFrom q reader n source target (k+1) left

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (n C source target : ℕ) := codeFrom q reader n source target 0 (C*blockCount q.block n)

@[simp] theorem fragment_length (q : Configuration) (reader : Fin q.inventory.readers)
    (n source target k : ℕ) : (fragment q reader n source target k).length=6 := by
  simp [fragment]
@[simp] theorem fragment_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (n source target k : ℕ) : cost q (fragment q reader n source target k)=6 := by
  rw [fragment,CommonPermutationPairs.cost_append]
  simp only [CommonBlockPair.cost_code]

theorem codeFrom_length (q : Configuration) (reader : Fin q.inventory.readers)
    (n source target k left : ℕ) : (codeFrom q reader n source target k left).length=6*left := by
  induction left generalizing k with
  | zero => rfl
  | succ left ih => rw [codeFrom,List.length_append,fragment_length,ih]; omega

theorem codeFrom_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (n source target k left : ℕ) : cost q (codeFrom q reader n source target k left)=6*left := by
  induction left generalizing k with
  | zero => rfl
  | succ left ih => rw [codeFrom,CommonPermutationPairs.cost_append,fragment_cost,ih]; omega

theorem fragment_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (n source target k : ℕ) : ∀ i∈fragment q reader n source target k,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with h|h
  · exact CommonBlockPair.safe q reader _ _ _ i h
  · exact CommonBlockPair.safe q reader _ _ _ i h

theorem codeFrom_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (n source target k left : ℕ) : ∀ i∈codeFrom q reader n source target k left,RespectsPC q i := by
  induction left generalizing k with
  | zero => simp [codeFrom]
  | succ left ih =>
      intro i hi
      rcases List.mem_append.mp hi with h|h
      · exact fragment_safe q reader n source target k i h
      · exact ih (k+1) i h

theorem fragment_disk (q : Configuration) (reader : Fin q.inventory.readers)
    (n C source target k : ℕ) (s : Machine q)
    (hk : k<C*blockCount q.block n)
    (hs : source+C*blockCount q.block n≤q.N^q.exponent)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (hsep : Separated source (C*blockCount q.block n) target (blockCount q.block (C*n))) :
    extendDisk q (executeRaw q (fragment q reader n source target k) s).1.disk=
      joinStep n source target k (extendDisk q s.disk) := by
  obtain ⟨hfirst,hlast⟩ := CommonColumnJoin.endpoint_bounds (CommonLeafProgram.block_positive q) hk
  have ha : source+k<q.N^q.exponent := by omega
  have hb : target+first q.block n k<q.N^q.exponent := by omega
  have hc : target+last q.block n k<q.N^q.exponent := by omega
  have hne : address q source k ≠ address q target (first q.block n k) := by
    intro h
    have hv := congrArg Fin.val h
    rw [CommonColumnSplit.address_val q source k ha,
      CommonColumnSplit.address_val q target _ hb] at hv
    rcases hsep with h|h <;> omega
  rw [fragment,CommonPermutationPairs.raw_append,CommonBlockPair.raw_disk,
    CommonBlockPair.raw_disk,Function.update_of_ne hne]
  simp only [blend_merge]
  rw [CommonExchangePolicy.extend_update,CommonExchangePolicy.extend_update]
  have hmiddle := congrFun (CommonExchangePolicy.extend_update q s.disk
    (address q target (first q.block n k))
    (CommonColumnJoin.merge n k (first q.block n k) (s.disk (address q source k))
      (s.disk (address q target (first q.block n k))))) (target+last q.block n k)
  have haddrA : address q source k=⟨source+k,ha⟩ := by simp [CommonColumnSplit.address,ha]
  have haddrB : address q target (first q.block n k)=⟨target+first q.block n k,hb⟩ := by
    simp [CommonColumnSplit.address,hb]
  have haddrC : address q target (last q.block n k)=⟨target+last q.block n k,hc⟩ := by
    simp [CommonColumnSplit.address,hc]
  simp only [extendDisk,hc,dif_pos] at hmiddle
  rw [haddrC,hmiddle]
  simp only [joinStep,haddrA,haddrB,haddrC,Fin.val_mk,extendDisk,ha,hb,dif_pos]

/-- The whole public instruction list implements the already verified
counted disk join, including every actual read/modify/write. -/
theorem raw_disk (q : Configuration) (reader : Fin q.inventory.readers)
    (n C source target k left : ℕ) (s : Machine q)
    (hk : k+left≤C*blockCount q.block n)
    (hs : source+C*blockCount q.block n≤q.N^q.exponent)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (hsep : Separated source (C*blockCount q.block n) target (blockCount q.block (C*n))) :
    extendDisk q (executeRaw q (codeFrom q reader n source target k left) s).1.disk=
      joinDisk n source target k left (extendDisk q s.disk) := by
  induction left generalizing k s with
  | zero => rfl
  | succ left ih =>
      rw [codeFrom,CommonPermutationPairs.raw_append,ih (k+1) _ (by omega)]
      rw [fragment_disk q reader n C source target k s (by omega) hs ht hsep]
      rfl

end
end CodedSorting.CommonStaticSlabJoin
end SlabJoin

section SlabJoinMapped
/-! Static concatenation from separately allocated column slabs. Only the
public source-address map is embedded in program text; original payloads
occur solely in the reference semantics and its proof. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonStaticSlabJoinMapped
open WordControl BitWordPacking PhysicalStreamCursor
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store Disk Machine machine)
open CommonLeafBatchProgram (extendDisk)
open CommonColumnJoin (start useful first last merge)
noncomputable section
abbrev address := CommonColumnSplit.address
abbrev select := CommonStaticSlabJoin.select

/-- Proof-only update by one useful source slab block. -/
def writeChunk {B w : ℕ} (n target k : ℕ) (input : Words B w)
    (disk : ℕ → Words B w) : ℕ → Words B w :=
  let middle := writeBlock disk (target+first B n k)
    (merge n k (first B n k) input (disk (target+first B n k)))
  writeBlock middle (target+last B n k)
    (merge n k (last B n k) input (middle (target+last B n k)))

/-- The fixed input function belongs only to the mathematical specification. -/
def writeChunks {B w : ℕ} (n target : ℕ) (input : ℕ → Words B w) (k : ℕ) :
    ℕ → (ℕ → Words B w) → (ℕ → Words B w)
  | 0,disk => disk
  | left+1,disk => writeChunks n target input (k+1) left
      (writeChunk n target k (input k) disk)

def fragment (q : Configuration) (reader : Fin q.inventory.readers)
    (n target k : ℕ) (source : ℕ → Fin (q.N^q.exponent)) : List (Instruction q) :=
  CommonBlockPair.code q reader (source k) (address q target (first q.block n k))
    (select q n k (first q.block n k)) ++
  CommonBlockPair.code q reader (source k) (address q target (last q.block n k))
    (select q n k (last q.block n k))

def codeFrom (q : Configuration) (reader : Fin q.inventory.readers)
    (n target k : ℕ) (source : ℕ → Fin (q.N^q.exponent)) : ℕ → List (Instruction q)
  | 0 => []
  | left+1 => fragment q reader n target k source ++ codeFrom q reader n target (k+1) source left

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target : ℕ) (source : ℕ → Fin (q.N^q.exponent)) := codeFrom q reader n target 0 source (C*blockCount q.block n)

@[simp] theorem fragment_length (q : Configuration) (reader : Fin q.inventory.readers)
    (n target k : ℕ) (source : ℕ → Fin (q.N^q.exponent)) : (fragment q reader n target k source).length=6 := by
  simp [fragment]
@[simp] theorem fragment_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (n target k : ℕ) (source : ℕ → Fin (q.N^q.exponent)) : cost q (fragment q reader n target k source)=6 := by
  rw [fragment,CommonPermutationPairs.cost_append]
  simp only [CommonBlockPair.cost_code]

theorem codeFrom_length (q : Configuration) (reader : Fin q.inventory.readers)
    (n target k left : ℕ) (source : ℕ → Fin (q.N^q.exponent)) : (codeFrom q reader n target k source left).length=6*left := by
  induction left generalizing k with
  | zero => rfl
  | succ left ih => rw [codeFrom,List.length_append,fragment_length,ih]; omega

theorem codeFrom_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (n target k left : ℕ) (source : ℕ → Fin (q.N^q.exponent)) : cost q (codeFrom q reader n target k source left)=6*left := by
  induction left generalizing k with
  | zero => rfl
  | succ left ih => rw [codeFrom,CommonPermutationPairs.cost_append,fragment_cost,ih]; omega

theorem fragment_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (n target k : ℕ) (source : ℕ → Fin (q.N^q.exponent)) : ∀ i∈fragment q reader n target k source,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with h|h
  · exact CommonBlockPair.safe q reader _ _ _ i h
  · exact CommonBlockPair.safe q reader _ _ _ i h

theorem codeFrom_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (n target k left : ℕ) (source : ℕ → Fin (q.N^q.exponent)) : ∀ i∈codeFrom q reader n target k source left,RespectsPC q i := by
  induction left generalizing k with
  | zero => simp [codeFrom]
  | succ left ih =>
      intro i hi
      rcases List.mem_append.mp hi with h|h
      · exact fragment_safe q reader n target k source i h
      · exact ih (k+1) i h

/-- The two real fragments merge exactly the useful words; both source
reads are valid even if the two destination blocks coincide. -/
theorem fragment_disk (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target k : ℕ) (source : ℕ → Fin (q.N^q.exponent)) (s : Machine q)
    (hk : k<C*blockCount q.block n)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (hsep : (source k).val<target ∨ target+blockCount q.block (C*n)≤(source k).val) :
    extendDisk q (executeRaw q (fragment q reader n target k source) s).1.disk=
      writeChunk n target k (s.disk (source k)) (extendDisk q s.disk) := by
  obtain ⟨hfirst,hlast⟩ := CommonColumnJoin.endpoint_bounds (CommonLeafProgram.block_positive q) hk
  have hb : target+first q.block n k<q.N^q.exponent := by omega
  have hc : target+last q.block n k<q.N^q.exponent := by omega
  have hne : source k ≠ address q target (first q.block n k) := by
    intro h
    have hv := congrArg Fin.val h
    rw [CommonColumnSplit.address_val q target _ hb] at hv
    rcases hsep with h|h <;> omega
  rw [fragment,CommonPermutationPairs.raw_append,CommonBlockPair.raw_disk,
    CommonBlockPair.raw_disk,Function.update_of_ne hne]
  simp only [CommonStaticSlabJoin.blend_merge]
  rw [CommonExchangePolicy.extend_update,CommonExchangePolicy.extend_update]
  have hmiddle := congrFun (CommonExchangePolicy.extend_update q s.disk
    (address q target (first q.block n k))
    (merge n k (first q.block n k) (s.disk (source k))
      (s.disk (address q target (first q.block n k))))) (target+last q.block n k)
  have haddrB : address q target (first q.block n k)=⟨target+first q.block n k,hb⟩ := by
    simp [CommonColumnSplit.address,hb]
  have haddrC : address q target (last q.block n k)=⟨target+last q.block n k,hc⟩ := by
    simp [CommonColumnSplit.address,hc]
  simp only [extendDisk,hc,dif_pos] at hmiddle
  rw [haddrC,hmiddle]
  simp only [writeChunk,haddrB,haddrC,Fin.val_mk,extendDisk,hb,dif_pos]

theorem writeChunk_outside {B w : ℕ} (n target k : ℕ) (input : Words B w)
    (disk : ℕ → Words B w) (a : ℕ)
    (hf : a≠target+first B n k) (hl : a≠target+last B n k) :
    writeChunk n target k input disk a=disk a := by
  simp [writeChunk,writeBlock,hf,hl]

theorem fragment_source (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target k : ℕ) (source : ℕ → Fin (q.N^q.exponent)) (s : Machine q)
    (hk : k<C*blockCount q.block n)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (hsep : ∀ j<C*blockCount q.block n,
      (source j).val<target ∨ target+blockCount q.block (C*n)≤(source j).val)
    (j : ℕ) (hj : j<C*blockCount q.block n) :
    (executeRaw q (fragment q reader n target k source) s).1.disk (source j)=s.disk (source j) := by
  have h := congrFun (fragment_disk q reader n C target k source s hk ht (hsep k hk)) (source j).val
  obtain ⟨hf,hl⟩ := CommonColumnJoin.endpoint_bounds (CommonLeafProgram.block_positive q) hk
  have hf' : (source j).val≠target+first q.block n k := by
    rcases hsep j hj with h|h <;> omega
  have hl' : (source j).val≠target+last q.block n k := by
    rcases hsep j hj with h|h <;> omega
  rw [writeChunk_outside _ _ _ _ _ _ hf' hl'] at h
  simpa only [extendDisk,(source j).isLt,dif_pos] using h

/-- A single raw execution, with its original source payloads used only in
this proof statement. Source blocks may lie in arbitrary allocated slots. -/
theorem raw_disk_fixed (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target k left : ℕ) (source : ℕ → Fin (q.N^q.exponent)) (s : Machine q)
    (input : ℕ → Words q.block q.w)
    (hinput : ∀ j<C*blockCount q.block n,s.disk (source j)=input j)
    (hk : k+left≤C*blockCount q.block n)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (hsep : ∀ j<C*blockCount q.block n,
      (source j).val<target ∨ target+blockCount q.block (C*n)≤(source j).val) :
    extendDisk q (executeRaw q (codeFrom q reader n target k source left) s).1.disk=
      writeChunks n target input k left (extendDisk q s.disk) := by
  induction left generalizing k s with
  | zero => rfl
  | succ left ih =>
      rw [codeFrom,CommonPermutationPairs.raw_append]
      have hin : ∀ j<C*blockCount q.block n,
          (executeRaw q (fragment q reader n target k source) s).1.disk (source j)=input j := by
        intro j hj
        rw [fragment_source q reader n C target k source s (by omega) ht hsep j hj,hinput j hj]
      rw [ih (k+1) _ hin (by omega)]
      rw [fragment_disk q reader n C target k source s (by omega) ht (hsep k (by omega)),
        hinput k (by omega)]
      rfl

theorem raw_disk (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target : ℕ) (source : ℕ → Fin (q.N^q.exponent)) (s : Machine q)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (hsep : ∀ j<C*blockCount q.block n,
      (source j).val<target ∨ target+blockCount q.block (C*n)≤(source j).val) :
    extendDisk q (executeRaw q (code q reader n C target source) s).1.disk=
      writeChunks n target (fun j=>s.disk (source j)) 0 (C*blockCount q.block n)
        (extendDisk q s.disk) := by
  exact raw_disk_fixed q reader n C target 0 _ source s _ (by intros; rfl) (by omega) ht hsep

@[simp] theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target : ℕ) (source : ℕ → Fin (q.N^q.exponent)) :
    (code q reader n C target source).length=6*(C*blockCount q.block n) :=
  codeFrom_length q reader n target 0 _ source

@[simp] theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target : ℕ) (source : ℕ → Fin (q.N^q.exponent)) :
    cost q (code q reader n C target source)=6*(C*blockCount q.block n) :=
  codeFrom_cost q reader n target 0 _ source

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target : ℕ) (source : ℕ → Fin (q.N^q.exponent)) :
    ∀ i∈code q reader n C target source,RespectsPC q i :=
  codeFrom_safe q reader n target 0 _ source

end
end CodedSorting.CommonStaticSlabJoinMapped
end SlabJoinMapped

section SlabJoinMappedMath
/-! Exact packing semantics for separately allocated input slabs.
The source function is proof-only and is supplied by actual disk reads in
CommonStaticSlabJoinMapped; it is not a resident payload array. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonStaticSlabJoinMapped
open WordControl PhysicalStreamCursor CommonColumnJoin

theorem writeChunk_word {B w n target k r : ℕ} (hB : 0<B)
    (input : Words B w) (disk : ℕ→Words B w) :
    outputWord hB (writeChunk n target k input disk) target r =
      if h : start B n k≤r ∧ r<start B n k+useful B n k then
        input ⟨r-start B n k,by have:=Nat.min_le_left B (n-k%blockCount B n*B); unfold useful at h; omega⟩
      else outputWord hB disk target r := by
  have hrmod := Nat.mod_lt r hB
  have hrdecomp : r/B*B+r%B=r := by simpa [Nat.mul_comm] using Nat.div_add_mod r B
  have hmerge (j : ℕ) (hj : r/B=j) (input old : Words B w) :
      merge n k j input old ⟨r%B,hrmod⟩ =
        if h : start B n k≤r ∧ r<start B n k+useful B n k then
          input ⟨r-start B n k,by have:=Nat.min_le_left B (n-k%blockCount B n*B); unfold useful at h; omega⟩
        else old ⟨r%B,hrmod⟩ := by
    have hd : j*B+r%B=r := by rw [←hj]; exact hrdecomp
    simp only [merge,hd]
  unfold outputWord writeChunk writeBlock
  dsimp only
  simp only [Nat.add_left_cancel_iff]
  by_cases hl : r/B=last B n k
  · simp only [hl,↓reduceIte]
    rw [hmerge _ hl]
    split_ifs with h hf
    · rfl
    · rw [hmerge _ (hl.trans hf)]
      simp only [dif_neg h]
      rw [hf]
    · rfl
  · simp only [hl,↓reduceIte]
    by_cases hf : r/B=first B n k
    · simp only [hf,↓reduceIte]
      exact hmerge _ hf _ _
    · simp only [hf,↓reduceIte]
      have h : ¬(start B n k≤r ∧ r<start B n k+useful B n k) := by
        intro h
        rcases chunk_block hB h.1 h.2 with h|h
        · exact hf h
        · exact hl h
      simp only [dif_neg h]

/-- Later chunks do not disturb any word preceding their first word. -/
theorem writeChunks_earlier {B w n target k r : ℕ} (hB : 0<B) (hn : 0<n)
    (hr : r<start B n k) (left : ℕ) (input : ℕ→Words B w) (disk : ℕ→Words B w) :
    outputWord hB (writeChunks n target input k left disk) target r=
      outputWord hB disk target r := by
  induction left generalizing k disk with
  | zero => rfl
  | succ left ih =>
    rw [writeChunks,ih]
    · rw [writeChunk_word]
      simp only [dif_neg (show ¬(start B n k≤r ∧ r<start B n k+useful B n k) by omega)]
    · have hm := start_mono hB hn (show k≤k+1 by omega)
      omega

/-- Each useful source word is written exactly once and survives the rest
of the join, even when consecutive chunks share an output block. -/
theorem writeChunks_chunk {B w n target : ℕ} (hB : 0<B) (hn : 0<n)
    (k left : ℕ)
    (input : ℕ→Words B w) (disk : ℕ→Words B w) (j : ℕ) (hjk : k≤j) (hjl : j<k+left)
    (i : Fin B) (hi : i.val<useful B n j) :
    outputWord hB (writeChunks n target input k left disk) target (start B n j+i.val)=
      input j i := by
  induction left generalizing k disk with
  | zero => omega
  | succ left ih =>
    rw [writeChunks]
    by_cases hj : j=k
    · subst j
      rw [writeChunks_earlier hB hn]
      · rw [writeChunk_word]
        have h : start B n k≤start B n k+i.val ∧
            start B n k+i.val<start B n k+useful B n k := by omega
        simp only [dif_pos h,Nat.add_sub_cancel_left]
      · rw [start_step hB hn]
        omega
    · rw [ih (k+1) _ (by omega) (by omega)]


theorem writeChunks_packed {B w n C target : ℕ} (hB : 0<B)
    (input : ℕ→Words B w) (disk : ℕ→Words B w)
    (c i : ℕ) (hc : c<C) (hi : i<n) :
    outputWord hB (writeChunks n target input 0 (C*blockCount B n) disk) target (c*n+i)=
      input (c*blockCount B n+i/B) ⟨i%B,Nat.mod_lt _ hB⟩ := by
  have hn : 0<n := by omega
  obtain ⟨he,hu,hix⟩ := packed_chunk_index (c:=c) hB hi
  have hj : c*blockCount B n+i/B<C*blockCount B n := by
    have hmul := Nat.mul_le_mul_right (blockCount B n) (show c+1≤C by omega)
    nlinarith
  have h := writeChunks_chunk (target:=target) hB hn 0 (C*blockCount B n) input disk
    (c*blockCount B n+i/B) (Nat.zero_le _) (by simpa only [Nat.zero_add] using hj)
    ⟨i%B,Nat.mod_lt _ hB⟩ hu
  simpa only [he] using h

theorem writeChunks_outside {B w n C target : ℕ} (hB : 0<B)
    (input : ℕ→Words B w) (k left : ℕ) (hbound : k+left≤C*blockCount B n)
    (disk : ℕ→Words B w) (j : ℕ)
    (hj : j<target ∨ target+blockCount B (C*n)≤j) :
    writeChunks n target input k left disk j=disk j := by
  induction left generalizing k disk with
  | zero => rfl
  | succ left ih =>
    rw [writeChunks,ih (k+1) (by omega)]
    obtain ⟨hf,hl⟩ := endpoint_bounds (n:=n) (C:=C) (k:=k) hB (by omega)
    apply writeChunk_outside n target k (input k) disk j
    · rcases hj with h|h <;> omega
    · rcases hj with h|h <;> omega


open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine Disk)
open CommonLeafBatchProgram (extendDisk)

/-- The actual join reads arbitrary separated source slabs and emits only
+their live words, without appending the rounded allocation padding. -/
theorem raw_packed_word (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target : ℕ) (source : ℕ→Fin (q.N^q.exponent)) (s : Machine q)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (hsep : ∀ j<C*blockCount q.block n,
      (source j).val<target ∨ target+blockCount q.block (C*n)≤(source j).val)
    (c i : ℕ) (hc : c<C) (hi : i<n) :
    outputWord (CommonLeafProgram.block_positive q)
      (extendDisk q (executeRaw q (code q reader n C target source) s).1.disk)
      target (c*n+i)=s.disk (source (c*blockCount q.block n+i/q.block))
        ⟨i%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ := by
  rw [raw_disk q reader n C target source s ht hsep]
  exact writeChunks_packed (CommonLeafProgram.block_positive q) _ _ c i hc hi

theorem raw_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (n C target : ℕ) (source : ℕ→Fin (q.N^q.exponent)) (s : Machine q)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (hsep : ∀ j<C*blockCount q.block n,
      (source j).val<target ∨ target+blockCount q.block (C*n)≤(source j).val)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<target ∨ target+blockCount q.block (C*n)≤a.val) :
    (executeRaw q (code q reader n C target source) s).1.disk a=s.disk a := by
  have h := congrFun (raw_disk q reader n C target source s ht hsep) a.val
  rw [writeChunks_outside (C:=C) (CommonLeafProgram.block_positive q) _ 0 _ (by omega) _ a.val ha] at h
  simpa only [extendDisk,a.isLt,↓reduceDIte,Fin.eta] using h

end CodedSorting.CommonStaticSlabJoinMapped
end SlabJoinMappedMath
