import CodedSorting.Interchange.Framework.Memory.Reflection

section Definitions
/-! Word-to-bit views for the actual column split/join programs. Logical
files are views of the same disk blocks; converting the view moves no data. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonWordRoles
open WordControl BitWordPacking PhysicalFileHandles PhysicalStreamCursor
open Circuit

def wordAt {B w : ℕ} (hB : 0<B) (disk : BlockDisk B w) (base i : ℕ) : Word w :=
  disk (base+i/B) ⟨i%B,Nat.mod_lt _ hB⟩

def bitAt {B w : ℕ} (hB : 0<B) (hw : 0<w) (disk : BlockDisk B w) (base i : ℕ) : Bit :=
  blockBits B w (disk (base+i/(B*w))) ⟨i%(B*w),Nat.mod_lt _ (Nat.mul_pos hB hw)⟩

theorem bitAt_word {B w : ℕ} (hB : 0<B) (hw : 0<w)
    (disk : BlockDisk B w) (base i : ℕ) :
    bitAt hB hw disk base i=
      wordBits w (wordAt hB disk base (i/w)) ⟨i%w,Nat.mod_lt _ hw⟩ := by
  have hdiv : i/(B*w)=i/w/B := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm]
  unfold bitAt blockBits wordAt
  dsimp only [Equiv.coe_fn_mk,Equiv.symm,finProdFinEquiv,Fin.divNat,Fin.modNat]
  simp only [Nat.mod_mul_left_div_self,Nat.mod_mul_left_mod,hdiv]

/-- Every bit of a declared word-aligned file follows from the actual
word contents at its disk address. Final block padding is irrelevant. -/
theorem bitView_words {N e B w n : ℕ} (hB : 0<B) (hw : 0<w)
    (disk : BlockDisk B w) (h : Handle N e) (F : Fin n → Word w)
    (hc : h.records.val=n*w)
    (hwords : ∀ i : Fin n,wordAt hB disk h.base.val i.val=F i) :
    bitView (Nat.mul_pos hB hw) disk h=
      BucketMachine.pack (B*w) (Nat.mul_pos hB hw) (List.ofFn (blockBits n w F)) := by
  unfold bitView fileView
  congr 1
  apply List.ext_getElem
  · simp [hc]
  · intro i hi hj
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn]
    change bitAt hB hw disk h.base.val i = blockBits n w F ⟨i,hj⟩
    rw [bitAt_word]
    have hn : i/w<n := (Nat.div_lt_iff_lt_mul hw).2 hj
    rw [hwords ⟨i/w,hn⟩]
    rfl

/-- Directly lifting a literal word-offset correspondence gives the same
bit-offset correspondence, including words crossing disk-block boundaries. -/
theorem bitAt_offset {B w : ℕ} (hB : 0<B) (hw : 0<w)
    (source target : BlockDisk B w) (a b offset n : ℕ)
    (hwords : ∀ i,i<n → wordAt hB target b i=wordAt hB source a (offset+i))
    (i : ℕ) (hi : i<n*w) :
    bitAt hB hw target b i=bitAt hB hw source a (offset*w+i) := by
  have hiw : i/w<n := (Nat.div_lt_iff_lt_mul hw).2 hi
  rw [bitAt_word,bitAt_word,hwords (i/w) hiw]
  have hd : (offset*w+i)/w=offset+i/w := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hw,Nat.add_comm]
  have hm : (offset*w+i)%w=i%w := by simp [Nat.add_mod]
  simp only [hd,hm]

/-- The concatenation after a real join, expressed in the bit-file type
used by the existing physical algorithm. -/
theorem joined_bitView {N e B w n C : ℕ} (hB : 0<B) (hw : 0<w)
    (source target : BlockDisk B w) (a : ℕ) (out : Handle N e)
    (hc : out.records.val=(C*n)*w)
    (hwords : ∀ c i,c<C → i<n →
      wordAt hB target out.base.val (c*n+i)=
        wordAt hB source (a+c*blockCount B n) i) :
    bitView (Nat.mul_pos hB hw) target out=
      BucketMachine.pack (B*w) (Nat.mul_pos hB hw)
        (List.ofFn (blockBits (C*n) w (fun p =>
          wordAt hB source (a+(p.val/n)*blockCount B n) (p.val%n)))) := by
  apply bitView_words hB hw target out _ hc
  intro p
  have hn : 0<n := by have:=p.isLt; nlinarith
  have hcol : p.val/n<C := (Nat.div_lt_iff_lt_mul hn).2 p.isLt
  have hpos : p.val%n<n := Nat.mod_lt _ hn
  have he : p.val/n*n+p.val%n=p.val := by simpa [Nat.mul_comm] using Nat.div_add_mod p.val n
  have h := hwords (p.val/n) (p.val%n) hcol hpos
  simpa only [he] using h

end CodedSorting.CommonWordRoles
end Definitions

section Read
/-! Recover the actual resident-disk words from the canonical bit-file
invariant used by the physical network interpreter. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonWordRoles
open WordControl BitWordPacking PhysicalFileHandles Circuit

theorem words_of_bitView {N e B w n : ℕ} (hB : 0<B) (hw : 0<w)
    (disk : BlockDisk B w) (h : Handle N e) (F : Fin n → Word w)
    (hc : h.records.val=n*w)
    (hbits : bitView (Nat.mul_pos hB hw) disk h=
      BucketMachine.pack (B*w) (Nat.mul_pos hB hw) (List.ofFn (blockBits n w F))) :
    ∀ i : Fin n,wordAt hB disk h.base.val i.val=F i := by
  have he := congrArg List.flatten hbits
  simp only [bitView,fileView,BucketMachine.flatten_pack] at he
  intro i
  apply (wordBits w).injective
  funext j
  let x := finProdFinEquiv (i,j)
  have hx : x.val<h.records.val := by rw [hc]; exact x.isLt
  have hat := List.getElem_of_eq he (i:=x.val) (by simpa only [List.length_ofFn] using hx)
  simp only [List.getElem_ofFn] at hat
  change bitAt hB hw disk h.base.val x.val = blockBits n w F x at hat
  rw [bitAt_word] at hat
  have hd : x.val/w=i.val := by
    change (j.val+w*i.val)/w=i.val
    rw [Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have hm : x.val%w=j.val := by
    change (j.val+w*i.val)%w=j.val
    simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  rw [hd] at hat
  have hj : (⟨x.val%w,Nat.mod_lt _ hw⟩ : Fin w)=j := Fin.ext hm
  rw [hj] at hat
  exact hat.trans (blockBits_at n w F i j)

theorem bitView_words_iff {N e B w n : ℕ} (hB : 0<B) (hw : 0<w)
    (disk : BlockDisk B w) (h : Handle N e) (F : Fin n → Word w)
    (hc : h.records.val=n*w) :
    bitView (Nat.mul_pos hB hw) disk h=
      BucketMachine.pack (B*w) (Nat.mul_pos hB hw) (List.ofFn (blockBits n w F)) ↔
    ∀ i : Fin n,wordAt hB disk h.base.val i.val=F i :=
  ⟨words_of_bitView hB hw disk h F hc,bitView_words hB hw disk h F hc⟩

/-- The canonical bit view occupies exactly the original word blocks. -/
theorem blockCount_words (B w n : ℕ) (hB : 0<B) (hw : 0<w) :
    PhysicalStreamCursor.blockCount (B*w) (n*w)=PhysicalStreamCursor.blockCount B n := by
  apply eq_of_forall_lt_iff
  intro k
  rw [PhysicalStreamCursor.cursor_live_iff (B*w) (n*w) k (Nat.mul_pos hB hw),
    PhysicalStreamCursor.cursor_live_iff B n k hB]
  rw [←Nat.mul_assoc,Nat.mul_lt_mul_right hw]

end CodedSorting.CommonWordRoles
end Read

section Split
/-! The actual resident split program returns the canonical bit files used
by the earlier physical file interpreter. These descriptors name written
slabs; directory installation remains an explicit caller operation. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonWordRoles
open WordControl BitWordPacking PhysicalFileHandles PhysicalStreamCursor
open CommonSortingNormalization
open CommonLeafProgram (Slots Store Disk machine)
open CommonLeafBatchProgram (extendDisk)

/-- A proof-side name for an actual written slab. -/
def columnHandle (q : Configuration) (n C : Fin (q.N^q.exponent+1))
    (target : Fin (q.N^q.exponent))
    (ht : target.val+C.val*blockCount q.block n.val≤q.N^q.exponent)
    (hbits : n.val*q.w≤q.N^q.exponent) (c : Fin C.val) : Handle q.N q.exponent :=
  ⟨⟨target.val+c.val*blockCount q.block n.val,by
      have h:=Nat.mul_le_mul_right (blockCount q.block n.val) c.isLt.le
      omega⟩,⟨n.val*q.w,by omega⟩⟩

/-- The same initialized finite-machine run proves exact canonical output
bit files, halt, outside-disk preservation and the resident memory bound. -/
theorem split_bitfiles (q : Configuration) (z : Slots q) (f : Fin 3)
    (n C : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hs : source.val+blockCount q.block (C.val*n.val)≤q.N^q.exponent)
    (ht : target.val+C.val*blockCount q.block n.val≤q.N^q.exponent)
    (hsep : source.val+blockCount q.block (C.val*n.val)≤target.val ∨
      target.val+C.val*blockCount q.block n.val≤source.val)
    (hbits : n.val*q.w≤q.N^q.exponent) :
    ∃ finalStore finalDisk,
      CommonMarginGather.run q z f (CommonColumnSplit.scheme q)
        (3*(C.val*blockCount q.block n.val))
        (machine q (CommonColumnSplit.initialStore q z f n.val C.val source target s) disk)=
        (machine q finalStore finalDisk,3*(C.val*blockCount q.block n.val)) ∧
      CommonMarginGather.policy q z f (CommonColumnSplit.scheme q) (pack finalStore)=none ∧
      (∀ c : Fin C.val,
        bitView (Nat.mul_pos (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega))
          (extendDisk q finalDisk) (columnHandle q n C target ht hbits c)=
        BucketMachine.pack (q.block*q.w)
          (Nat.mul_pos (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega))
          (List.ofFn (blockBits n.val q.w (fun i : Fin n.val =>
            wordAt (CommonLeafProgram.block_positive q) (extendDisk q disk) source.val
              (c.val*n.val+i.val))))) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target.val ∨
        target.val+C.val*blockCount q.block n.val≤a.val → finalDisk a=disk a) ∧
      CommonMovementPolicy.Preserved q
        (CommonColumnSplit.initialStore q z f n.val C.val source target s) finalStore ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨sf,df,hr,hh,hwords,ho,hframe,hm⟩ := CommonColumnSplit.initialized q z f n C source target s disk hs ht hsep
  refine ⟨sf,df,hr,hh,?_,ho,hframe,hm⟩
  intro c
  apply bitView_words (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega)
    (extendDisk q df) (columnHandle q n C target ht hbits c) _ rfl
  intro i
  exact hwords c.val c.isLt i.val i.isLt

/-- A proof-side name for the packed output of the real join. -/
def joinedHandle (q : Configuration) (n C : Fin (q.N^q.exponent+1))
    (target : Fin (q.N^q.exponent)) (hbits : (C.val*n.val)*q.w≤q.N^q.exponent) : Handle q.N q.exponent :=
  ⟨target.castSucc,⟨(C.val*n.val)*q.w,by omega⟩⟩

/-- Actual join output in the canonical bit-file representation, including
arbitrary final block padding hidden by the declared length. -/
theorem join_bitfile (q : Configuration) (z : Slots q)
    (n C : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hs : source.val+C.val*blockCount q.block n.val≤q.N^q.exponent)
    (ht : target.val+blockCount q.block (C.val*n.val)≤q.N^q.exponent)
    (hsep : CommonColumnJoin.Separated source.val (C.val*blockCount q.block n.val) target.val
      (blockCount q.block (C.val*n.val)))
    (hbits : (C.val*n.val)*q.w≤q.N^q.exponent) :
    ∃ finalStore finalDisk,
      CommonColumnJoin.run q z (5*(C.val*blockCount q.block n.val))
        (machine q (CommonColumnJoin.initialStore q z n C source target s) disk)=
          (machine q finalStore finalDisk,5*(C.val*blockCount q.block n.val)) ∧
      CommonColumnJoin.policy q z (pack finalStore)=none ∧
      bitView (Nat.mul_pos (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega))
        (extendDisk q finalDisk) (joinedHandle q n C target hbits)=
        BucketMachine.pack (q.block*q.w)
          (Nat.mul_pos (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega))
          (List.ofFn (blockBits (C.val*n.val) q.w (fun p =>
            wordAt (CommonLeafProgram.block_positive q) (extendDisk q disk)
              (source.val+(p.val/n.val)*blockCount q.block n.val) (p.val%n.val)))) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target.val ∨
        target.val+blockCount q.block (C.val*n.val)≤a.val → finalDisk a=disk a) ∧
      finalStore.leaf=s.leaf ∧ finalStore.directories=s.directories ∧
      finalStore.shapes=s.shapes ∧ finalStore.top=s.top ∧ finalStore.pcs=s.pcs ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨sf,df,hr,hh,hwords,ho,hframe⟩ :=
    CommonColumnJoin.join_columns_policy_refines q z n C source target s disk hs ht hsep
  refine ⟨sf,df,hr,hh,?_,ho,hframe⟩
  apply joined_bitView (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega)
    (extendDisk q disk) (extendDisk q df) source.val (joinedHandle q n C target hbits) rfl
  intro c i hc hi
  simpa only [wordAt,joinedHandle,Fin.coe_castSucc,CommonColumnJoin.outputWord,Nat.add_assoc]
    using hwords c i hc hi

end CodedSorting.CommonWordRoles
end Split

section Files
/-! Identification of the concrete aligned role files. The hypothesis is
the word contents produced by the cyclic transpose, not a successful-run
oracle. It is consumed by the already proved real split program. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonWordRoles
open WordControl BitWordPacking PhysicalFileHandles PhysicalStreamCursor
open CommonSortingNormalization PhysicalRolePartition CommonWordAlignment
open CommonLeafProgram (Slots Store Disk machine)
open CommonLeafBatchProgram (extendDisk)
noncomputable section

/-- The canonical bits of one word-level role are exactly the old bit-level
`roleValues`; reassociation changes no numeric address. -/
theorem role_file_from_words {N e B w R K L : ℕ} (hB : 0<B) (hw : 0<w)
    (disk : BlockDisk B w) (h : Handle N e) (F : Fin (K*(R*L)) → Word w)
    (r : Fin K) (hc : h.records.val=(R*L)*w)
    (hwords : ∀ i : Fin (R*L),wordAt hB disk h.base.val i.val=
      F (rolePermutation.symm (finProdFinEquiv (r,i)))) :
    bitView (Nat.mul_pos hB hw) disk h=
      BucketMachine.pack (B*w) (Nat.mul_pos hB hw) (roleValues (roleBits F) r) := by
  rw [roleValues_bits]
  exact bitView_words hB hw disk h _ hc hwords

/-- Starting from the actual cyclically transposed words, the real split
returns precisely the files expected by the old role-scatter semantics. -/
theorem split_role_files (q : Configuration) (z : Slots q) (f : Fin 3)
    (R K L : ℕ) (hn : R*L≤q.N^q.exponent) (hK : K≤q.N^q.exponent)
    (source target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q)
    (hs : source.val+blockCount q.block (K*(R*L))≤q.N^q.exponent)
    (ht : target.val+K*blockCount q.block (R*L)≤q.N^q.exponent)
    (hsep : source.val+blockCount q.block (K*(R*L))≤target.val ∨
      target.val+K*blockCount q.block (R*L)≤source.val)
    (hbits : (R*L)*q.w≤q.N^q.exponent)
    (F : Fin (K*(R*L)) → Word q.w)
    (htranspose : ∀ p : Fin (K*(R*L)),
      wordAt (CommonLeafProgram.block_positive q) (extendDisk q disk) source.val p.val=
        F (rolePermutation.symm p)) :
    let n : Fin (q.N^q.exponent+1) := ⟨R*L,by omega⟩
    let C : Fin (q.N^q.exponent+1) := ⟨K,by omega⟩
    ∃ finalStore finalDisk,
      CommonMarginGather.run q z f (CommonColumnSplit.scheme q)
        (3*(K*blockCount q.block (R*L)))
        (machine q (CommonColumnSplit.initialStore q z f (R*L) K source target s) disk)=
        (machine q finalStore finalDisk,3*(K*blockCount q.block (R*L))) ∧
      CommonMarginGather.policy q z f (CommonColumnSplit.scheme q) (pack finalStore)=none ∧
      (∀ r : Fin K,
        bitView (Nat.mul_pos (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega))
          (extendDisk q finalDisk) (columnHandle q n C target ht hbits r)=
        BucketMachine.pack (q.block*q.w)
          (Nat.mul_pos (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega))
          (roleValues (roleBits F) r)) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target.val ∨
        target.val+K*blockCount q.block (R*L)≤a.val → finalDisk a=disk a) ∧
      CommonMovementPolicy.Preserved q
        (CommonColumnSplit.initialStore q z f (R*L) K source target s) finalStore ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  dsimp only
  let n : Fin (q.N^q.exponent+1) := ⟨R*L,by omega⟩
  let C : Fin (q.N^q.exponent+1) := ⟨K,by omega⟩
  obtain ⟨sf,df,hr,hh,hviews,ho,hframe,hm⟩ := split_bitfiles q z f n C source target s disk hs ht hsep hbits
  refine ⟨sf,df,hr,hh,?_,ho,hframe,hm⟩
  intro r
  rw [hviews r,roleValues_bits]
  congr 2
  apply congrArg (blockBits (R*L) q.w)
  funext i
  have h := htranspose (finProdFinEquiv (r,i))
  simpa only [finProdFinEquiv_apply_val,n,Nat.add_comm,Nat.mul_comm] using h

end
end CodedSorting.CommonWordRoles
end Files

section Transpose
/-! The actual cyclic role transpose: the physical bit program is executed
on the finite word disk, and word alignment identifies its output with the
word-level cyclic transpose required by the subsequent slab splitter. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonWordRoles
open WordControl BitWordPacking PhysicalFileHandles PhysicalStreamCursor
open CommonSortingNormalization PhysicalRolePartition CommonWordAlignment
open CommonLeafProgram (Store Disk Machine machine)
open CommonLeafBatchProgram (extendDisk)
noncomputable section

theorem role_blockCount (q : Configuration) (R K L : ℕ) :
    CommonPermutationPairs.count q (K*(R*(L*q.w)))=
      blockCount q.block (K*(R*L)) := by
  change blockCount (q.block*q.w) (K*(R*(L*q.w)))=_
  rw [show K*(R*(L*q.w))=(K*(R*L))*q.w by ring]
  exact blockCount_words q.block q.w _ (CommonLeafProgram.block_positive q)
    (by have:=q.word_width; omega)

theorem readBit_eq_bitAt (q : Configuration) (disk : Disk q) (base i : ℕ)
    (ha : base+i/(q.block*q.w)<q.N^q.exponent) :
    CommonPermutationPairs.readBit q disk base i=
      bitAt (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega) (extendDisk q disk) base i := by
  simp only [CommonPermutationPairs.readBit,CommonPermutationPairs.width,
    CommonColumnSplit.address,bitAt,extendDisk,dif_pos ha]

/-- Data result of the forward bit transpose, stated as literal words. -/
theorem role_transpose_words (q : Configuration) (R K L source target : ℕ)
    (before after : Disk q)
    (hs : source+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (ht : target+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (hbits : ∀ y : Fin (K*(R*(L*q.w))),
      CommonPermutationPairs.readBit q after target y.val=
        CommonPermutationPairs.readBit q before source (rolePermutation.symm y).val) :
    ∀ y : Fin (K*(R*L)),
      wordAt (CommonLeafProgram.block_positive q) (extendDisk q after) target y.val=
        wordAt (CommonLeafProgram.block_positive q) (extendDisk q before) source (rolePermutation.symm y).val := by
  intro y
  apply (wordBits q.w).injective
  funext j
  let x := roleBitIndex y j
  have hyb := CommonPermutationPairs.bit_block_lt q x
  have hxb := CommonPermutationPairs.bit_block_lt q (rolePermutation.symm x)
  have hv := hbits x
  rw [readBit_eq_bitAt q after target x.val (by exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hyb target) ht),
    readBit_eq_bitAt q before source (rolePermutation.symm x).val
      (by exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hxb source) hs)] at hv
  rw [show x=roleBitIndex y j from rfl,rolePermutation_inverse_word] at hv
  rw [bitAt_word,bitAt_word] at hv
  have hwy : (roleBitIndex y j).val/q.w=y.val := by
    rw [roleBitIndex_val]
    have hw : 0<q.w := by have:=q.word_width; omega
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hw,Nat.div_eq_of_lt j.isLt]
    omega
  have hwx : (roleBitIndex (rolePermutation.symm y) j).val/q.w=(rolePermutation.symm y).val := by
    rw [roleBitIndex_val]
    have hw : 0<q.w := by have:=q.word_width; omega
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hw,Nat.div_eq_of_lt j.isLt]
    omega
  have hby : (⟨(roleBitIndex y j).val%q.w,Nat.mod_lt _ (show 0<q.w by have:=q.word_width; omega)⟩ : Fin q.w)=j := by
    apply Fin.ext
    simp [roleBitIndex_val,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  have hbx : (⟨(roleBitIndex (rolePermutation.symm y) j).val%q.w,Nat.mod_lt _ (show 0<q.w by have:=q.word_width; omega)⟩ : Fin q.w)=j := by
    apply Fin.ext
    simp [roleBitIndex_val,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  simpa only [hwy,hwx,hby,hbx] using hv

/-- Inverse cyclic collection also moves whole words in their original
bit order; it accepts arbitrary contents in the grouped input. -/
theorem role_inverse_transpose_words (q : Configuration) (R K L source target : ℕ)
    (before after : Disk q)
    (hs : source+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (ht : target+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (hbits : ∀ y : Fin (K*(R*(L*q.w))),
      CommonPermutationPairs.readBit q after target y.val=
        CommonPermutationPairs.readBit q before source (rolePermutation y).val) :
    ∀ y : Fin (K*(R*L)),
      wordAt (CommonLeafProgram.block_positive q) (extendDisk q after) target y.val=
        wordAt (CommonLeafProgram.block_positive q) (extendDisk q before) source (rolePermutation y).val := by
  have hv := role_transpose_words q R K L target source after before ht hs (by
    intro y
    have h := hbits (rolePermutation.symm y)
    simpa only [Equiv.apply_symm_apply] using h.symm)
  intro y
  have h := hv (rolePermutation y)
  simpa only [Equiv.symm_apply_apply] using h.symm

def roleProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (R K L source target : ℕ) : List (CommonStaticSchedule.Instruction q) :=
  CommonPermutationScan.program q reader (rolePermutation (R:=R) (K:=K) (C:=L*q.w)) sourceKey source target

/-- Complete forward cyclic distribution on the actual machine. The
conclusion is the exact input invariant of `split_role_files`. -/
theorem role_transpose_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (R K L source target : ℕ) (s : Machine q)
    (hs : source+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (ht : target+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (hsep : source+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤target ∨
      target+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤source)
    (hsize : 6*K*CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (hpc : CommonStaticSchedule.pc q s.ram=0) :
    let program := roleProgram q reader R K L source target
    let result := ControlledNormalization.runLogical (CommonStaticSchedule.policy q program) program.length s
    (∀ y : Fin (K*(R*L)),
      wordAt (CommonLeafProgram.block_positive q) (extendDisk q result.1.disk) target y.val=
        wordAt (CommonLeafProgram.block_positive q) (extendDisk q s.disk) source (rolePermutation.symm y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨
      target+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤a.val → result.1.disk a=s.disk a) ∧
    CommonStaticSchedule.policy q program result.1.ram=none ∧
    result.2≤6*K*CommonPermutationPairs.count q (K*(R*(L*q.w))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hw,ho,hh,hcost,hm⟩ := CommonPermutationScan.complete q reader
    (rolePermutation (R:=R) (K:=K) (C:=L*q.w)) sourceKey role_increasing
    source target hs ht hsep hsize s hpc
  exact ⟨role_transpose_words q R K L source target _ _ hs ht hw,ho,hh,hcost,hm⟩

def roleInverseProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (R K L source target : ℕ) : List (CommonStaticSchedule.Instruction q) :=
  CommonPermutationScan.program q reader (rolePermutation (R:=R) (K:=K) (C:=L*q.w)).symm targetKey source target

theorem role_inverse_transpose_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (R K L source target : ℕ) (s : Machine q)
    (hs : source+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (ht : target+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (hsep : source+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤target ∨
      target+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤source)
    (hsize : 6*K*CommonPermutationPairs.count q (K*(R*(L*q.w)))≤q.N^q.exponent)
    (hpc : CommonStaticSchedule.pc q s.ram=0) :
    let program := roleInverseProgram q reader R K L source target
    let result := ControlledNormalization.runLogical (CommonStaticSchedule.policy q program) program.length s
    (∀ y : Fin (K*(R*L)),
      wordAt (CommonLeafProgram.block_positive q) (extendDisk q result.1.disk) target y.val=
        wordAt (CommonLeafProgram.block_positive q) (extendDisk q s.disk) source (rolePermutation y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨
      target+CommonPermutationPairs.count q (K*(R*(L*q.w)))≤a.val → result.1.disk a=s.disk a) ∧
    CommonStaticSchedule.policy q program result.1.ram=none ∧
    result.2≤6*K*CommonPermutationPairs.count q (K*(R*(L*q.w))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hw,ho,hh,hcost,hm⟩ := CommonPermutationScan.complete q reader
    (rolePermutation (R:=R) (K:=K) (C:=L*q.w)).symm targetKey inverse_increasing
    source target hs ht hsep hsize s hpc
  exact ⟨role_inverse_transpose_words q R K L source target _ _ hs ht hw,ho,hh,hcost,hm⟩

end
end CodedSorting.CommonWordRoles
end Transpose
