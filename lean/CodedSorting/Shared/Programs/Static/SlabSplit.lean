import CodedSorting.Interchange.Framework.Memory.Reflection
import CodedSorting.Interchange.Framework.Columns.ColumnOperations

/-! A public static packed-to-slab scan. Each target slab block receives
its useful prefix through two actual read/read/write fragments. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonStaticSlabSplit
open WordControl CommonSortingNormalization CommonStaticSchedule BitWordPacking Circuit
open CommonLeafProgram (Store Disk Machine machine)
open PhysicalStreamCursor
noncomputable section
abbrev address := CommonColumnSplit.address
abbrev start := CommonColumnJoin.start
abbrev useful := CommonColumnJoin.useful
abbrev first := CommonColumnJoin.first
abbrev last := CommonColumnJoin.last
abbrev width := CommonPermutationPairs.width
abbrev width_pos := CommonPermutationPairs.width_pos

def inputWord (q : Configuration) (n k : ℕ) (i : CommonBlockPair.BitIndex q) : ℕ :=
  start q.block n k+i.val/q.w

def select (q : Configuration) (n k sourceBlock : ℕ) : CommonBlockPair.Selection q := fun i =>
  if h : i.val/q.w<useful q.block n k ∧ inputWord q n k i/q.block=sourceBlock then
    some ⟨inputWord q n k i%q.block*q.w+i.val%q.w,by
      have hb := Nat.mod_lt (inputWord q n k i) (CommonLeafProgram.block_positive q)
      have hw : 0<q.w := by have:=q.word_width; omega
      have hi := Nat.mod_lt i.val hw
      nlinarith⟩
  else none

def part (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (k b : ℕ) : List (Instruction q) :=
  CommonBlockPair.code q reader (address q source b) (target k) (select q n k b)

def fragment (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (k : ℕ) : List (Instruction q) :=
  part q reader n source target k (first q.block n k) ++
  part q reader n source target k (last q.block n k)

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (C n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) : List (Instruction q) :=
  (List.range (C*blockCount q.block n)).flatMap (fragment q reader n source target)

def stepDisk (q : Configuration) (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (k : ℕ) (disk : Disk q) : Disk q :=
  let firstDisk := Function.update disk (target k)
    (CommonBlockPair.blend q (select q n k (first q.block n k))
      (disk (address q source (first q.block n k))) (disk (target k)))
  Function.update firstDisk (target k)
    (CommonBlockPair.blend q (select q n k (last q.block n k))
      (firstDisk (address q source (last q.block n k))) (firstDisk (target k)))

def applyChunks (q : Configuration) (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) : List ℕ → Disk q → Disk q
  | [],disk => disk
  | k::ks,disk => applyChunks q n source target ks (stepDisk q n source target k disk)

theorem fragment_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (k : ℕ) (s : Machine q) :
    (executeRaw q (fragment q reader n source target k) s).1.disk=
      stepDisk q n source target k s.disk := by
  rw [fragment,CommonPermutationPairs.raw_append]
  simp only [part,CommonBlockPair.raw_disk,stepDisk]

theorem fragment_length (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (k : ℕ) : (fragment q reader n source target k).length=6 := by
  simp [fragment,part]

theorem fragment_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (k : ℕ) : cost q (fragment q reader n source target k)=6 := by
  rw [fragment,CommonPermutationPairs.cost_append]
  simp only [part,CommonBlockPair.cost_code]

theorem fragment_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (k : ℕ) : ∀ i∈fragment q reader n source target k,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with h|h
  · exact CommonBlockPair.safe q reader _ _ _ i h
  · exact CommonBlockPair.safe q reader _ _ _ i h

theorem chunks_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (ks : List ℕ) (s : Machine q) :
    (executeRaw q (ks.flatMap (fragment q reader n source target)) s).1.disk=
      applyChunks q n source target ks s.disk := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    rw [List.flatMap_cons,CommonPermutationPairs.raw_append,ih,fragment_raw]
    rfl

theorem chunks_length (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (ks : List ℕ) :
    (ks.flatMap (fragment q reader n source target)).length=6*ks.length := by
  induction ks with
  | nil => simp
  | cons k ks ih => rw [List.flatMap_cons,List.length_append,fragment_length,ih,List.length_cons]; omega

theorem chunks_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (ks : List ℕ) :
    cost q (ks.flatMap (fragment q reader n source target))=6*ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [List.flatMap_cons,CommonPermutationPairs.cost_append,fragment_cost,ih,List.length_cons]; omega

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (C n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) : (code q reader C n source target).length=6*(C*blockCount q.block n) := by
  rw [code,chunks_length,List.length_range]
theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (C n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) : cost q (code q reader C n source target)=6*(C*blockCount q.block n) := by
  rw [code,chunks_cost,List.length_range]
theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (C n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) : ∀ i∈code q reader C n source target,RespectsPC q i := by
  intro i hi
  obtain ⟨k,_,hi⟩ := List.mem_flatMap.mp hi
  exact fragment_safe q reader n source target k i hi

def sourceBit (q : Configuration) (n source k : ℕ) (disk : Disk q)
    (i : CommonBlockPair.BitIndex q) : Bit :=
  blockBits q.block q.w (disk (address q source (inputWord q n k i/q.block)))
    ⟨inputWord q n k i%q.block*q.w+i.val%q.w,by
      have hb := Nat.mod_lt (inputWord q n k i) (CommonLeafProgram.block_positive q)
      have hw : 0<q.w := by have:=q.word_width; omega
      have hi := Nat.mod_lt i.val hw
      nlinarith⟩

theorem step_outside (q : Configuration) (n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (k : ℕ) (disk : Disk q)
    (a : Fin (q.N^q.exponent)) (ha : a≠target k) :
    stepDisk q n source target k disk a=disk a := by
  simp only [stepDisk,Function.update_of_ne ha]

theorem step_target (q : Configuration) {C n source k : ℕ}
    (target : ℕ → Fin (q.N^q.exponent)) (disk : Disk q)
    (hk : k<C*blockCount q.block n)
    (sep : ∀ b<blockCount q.block (C*n),address q source b≠target k)
    (i : CommonBlockPair.BitIndex q) (hi : i.val/q.w<useful q.block n k) :
    blockBits q.block q.w (stepDisk q n source target k disk (target k)) i=
      sourceBit q n source k disk i := by
  have hb:=CommonLeafProgram.block_positive q
  have ends := CommonColumnJoin.endpoint_bounds hb hk
  have hne := sep _ ends.2
  have hchunk : inputWord q n k i/q.block=first q.block n k ∨
      inputWord q n k i/q.block=last q.block n k := by
    apply CommonColumnJoin.chunk_block hb
    · exact Nat.le_add_right _ _
    · exact Nat.add_lt_add_left hi _
  simp only [stepDisk,Function.update_self,Function.update_of_ne hne,CommonBlockPair.blend_bits]
  rcases hchunk with hf|hl
  · by_cases hl : inputWord q n k i/q.block=last q.block n k
    · simp only [select,hi,hl,and_self,↓reduceDIte,sourceBit]
    · simp only [select,hi,hl,and_false,↓reduceDIte]
      simp only [hf,and_self,↓reduceDIte,sourceBit]
  · simp only [select,hi,hl,and_self,↓reduceDIte,sourceBit]

theorem input_block_lt (q : Configuration) {C n k : ℕ}
    (hk : k<C*blockCount q.block n) (i : CommonBlockPair.BitIndex q)
    (hi : i.val/q.w<useful q.block n k) :
    inputWord q n k i/q.block<blockCount q.block (C*n) := by
  have hb:=CommonLeafProgram.block_positive q
  have ends:=CommonColumnJoin.endpoint_bounds hb hk
  have he:=CommonColumnJoin.chunk_block hb (Nat.le_add_right (start q.block n k) (i.val/q.w))
    (Nat.add_lt_add_left hi (start q.block n k))
  rcases he with he|he
  · exact he.trans_lt ends.1
  · exact he.trans_lt ends.2

theorem chunks_outside (q : Configuration) (n source : ℕ)
    (target : ℕ → Fin (q.N^q.exponent)) (ks : List ℕ) (disk : Disk q)
    (a : Fin (q.N^q.exponent)) (ha : ∀ k∈ks,a≠target k) :
    applyChunks q n source target ks disk a=disk a := by
  induction ks generalizing disk with
  | nil => rfl
  | cons k ks ih =>
    rw [applyChunks,ih _ (fun j hj => ha j (by simp [hj]))]
    exact step_outside q n source target k disk a (ha k (by simp))

theorem chunks_bits (q : Configuration) {C n source k : ℕ}
    (target : ℕ → Fin (q.N^q.exponent)) (ks : List ℕ) (disk : Disk q)
    (hall : ∀ p∈ks,p<C*blockCount q.block n)
    (hinj : ∀ p<C*blockCount q.block n,∀ j<C*blockCount q.block n,target p=target j→p=j)
    (sep : ∀ b<blockCount q.block (C*n),∀ p<C*blockCount q.block n,address q source b≠target p)
    (hmem : k∈ks) (i : CommonBlockPair.BitIndex q) (hi : i.val/q.w<useful q.block n k) :
    blockBits q.block q.w (applyChunks q n source target ks disk (target k)) i=
      sourceBit q n source k disk i := by
  induction ks generalizing disk with
  | nil => simp at hmem
  | cons p ps ih =>
    have hp:=hall p (by simp)
    have hps : ∀ j∈ps,j<C*blockCount q.block n := fun j hj => hall j (by simp [hj])
    have hk:=hall k hmem
    by_cases hm : k∈ps
    · rw [applyChunks,ih _ hps hm]
      unfold sourceBit
      rw [step_outside q n source target p disk _ (sep _ (input_block_lt q hk i hi) p hp)]
    · have hpk : p=k := (by simpa [hm] using hmem : k=p).symm
      subst p
      rw [applyChunks,chunks_outside q n source target ps _ (target k)]
      · exact step_target q target disk hk (fun b hb => sep b hb k hk) i hi
      · intro j hj he
        have hkj:=hinj k hk j (hps j hj) he
        exact hm (hkj ▸ hj)

/-- Every useful output bit is read from its exact packed input position.
The destination block map permits independently allocated, gapped slabs. -/
theorem raw_bits (q : Configuration) (reader : Fin q.inventory.readers)
    {C n source : ℕ} (target : ℕ → Fin (q.N^q.exponent)) (s : Machine q)
    (hinj : ∀ p<C*blockCount q.block n,∀ j<C*blockCount q.block n,target p=target j→p=j)
    (sep : ∀ b<blockCount q.block (C*n),∀ p<C*blockCount q.block n,address q source b≠target p)
    (k : ℕ) (hk : k<C*blockCount q.block n)
    (i : CommonBlockPair.BitIndex q) (hi : i.val/q.w<useful q.block n k) :
    blockBits q.block q.w
      ((executeRaw q (code q reader C n source target) s).1.disk (target k)) i=
      sourceBit q n source k s.disk i := by
  rw [code,chunks_raw]
  exact chunks_bits q target _ s.disk (fun p hp => List.mem_range.mp hp) hinj sep
    (List.mem_range.mpr hk) i hi

theorem raw_outside (q : Configuration) (reader : Fin q.inventory.readers)
    (C n source : ℕ) (target : ℕ → Fin (q.N^q.exponent)) (s : Machine q)
    (a : Fin (q.N^q.exponent)) (ha : ∀ k<C*blockCount q.block n,a≠target k) :
    (executeRaw q (code q reader C n source target) s).1.disk a=s.disk a := by
  rw [code,chunks_raw]
  exact chunks_outside q n source target _ s.disk a (fun k hk => ha k (List.mem_range.mp hk))


theorem sourceBit_word (q : Configuration) (n source k : ℕ) (disk : Disk q)
    (i : Fin q.block) (t : Fin q.w) :
    sourceBit q n source k disk (finProdFinEquiv (i,t))=
      wordBits q.w (disk (address q source ((start q.block n k+i.val)/q.block))
        ⟨(start q.block n k+i.val)%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩) t := by
  have hw : 0<q.w := by have:=q.word_width; omega
  have hd : (finProdFinEquiv (i,t)).val/q.w=i.val := by
    change (t.val+q.w*i.val)/q.w=i.val
    rw [Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt t.isLt,Nat.zero_add]
  have hm : (finProdFinEquiv (i,t)).val%q.w=t.val := by
    simp [bit_address,Nat.add_mod,Nat.mod_eq_of_lt t.isLt]
  unfold sourceBit inputWord
  simp only [hd,hm]
  have he : (⟨(start q.block n k+i.val)%q.block*q.w+t.val,by
      have hb:=Nat.mod_lt (start q.block n k+i.val) (CommonLeafProgram.block_positive q)
      have ht:=t.isLt
      nlinarith⟩ : Fin (q.block*q.w)) =
    finProdFinEquiv (⟨(start q.block n k+i.val)%q.block,
      Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩,t) := by
    apply Fin.ext
    simp only [bit_address]
  rw [he,blockBits_at]

/-- Whole-word form of the same actual finite-disk execution. -/
theorem raw_word (q : Configuration) (reader : Fin q.inventory.readers)
    {C n source : ℕ} (target : ℕ → Fin (q.N^q.exponent)) (s : Machine q)
    (hinj : ∀ p<C*blockCount q.block n,∀ j<C*blockCount q.block n,target p=target j→p=j)
    (sep : ∀ b<blockCount q.block (C*n),∀ p<C*blockCount q.block n,address q source b≠target p)
    (k : ℕ) (hk : k<C*blockCount q.block n)
    (i : Fin q.block) (hi : i.val<useful q.block n k) :
    (executeRaw q (code q reader C n source target) s).1.disk (target k) i=
      s.disk (address q source ((start q.block n k+i.val)/q.block))
        ⟨(start q.block n k+i.val)%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ := by
  apply (wordBits q.w).injective
  funext t
  rw [←blockBits_at q.block q.w _ i t]
  have hw : 0<q.w := by have:=q.word_width; omega
  have hd : (finProdFinEquiv (i,t)).val/q.w=i.val := by
    change (t.val+q.w*i.val)/q.w=i.val
    rw [Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt t.isLt,Nat.zero_add]
  rw [raw_bits q reader target s hinj sep k hk _ (by simpa only [hd] using hi)]
  exact sourceBit_word q n source k s.disk i t


/-- Direct column/word interface used by recursive network calls. -/
theorem raw_column_word (q : Configuration) (reader : Fin q.inventory.readers)
    {C n source : ℕ} (target : ℕ → Fin (q.N^q.exponent)) (s : Machine q)
    (hinj : ∀ p<C*blockCount q.block n,∀ j<C*blockCount q.block n,target p=target j→p=j)
    (sep : ∀ b<blockCount q.block (C*n),∀ p<C*blockCount q.block n,address q source b≠target p)
    (c j : ℕ) (hc : c<C) (hj : j<n) :
    (executeRaw q (code q reader C n source target) s).1.disk
      (target (c*blockCount q.block n+j/q.block))
      ⟨j%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩=
      s.disk (address q source ((c*n+j)/q.block))
        ⟨(c*n+j)%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ := by
  have hp:=CommonColumnSplit.column_position q.block n C c j
    (CommonLeafProgram.block_positive q) hc hj
  have he:=raw_word q reader target s hinj sep _ hp.1
    ⟨j%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ hp.2.1
  simpa only [hp.2.2] using he

end
end CodedSorting.CommonStaticSlabSplit
