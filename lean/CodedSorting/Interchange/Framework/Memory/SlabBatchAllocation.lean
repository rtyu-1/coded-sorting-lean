import CodedSorting.Shared.Programs.Static.SlabSplit
import CodedSorting.Shared.Programs.Static.SlabJoinMappedMath

section SlabReadBits
/-! The actual packed-to-slab scan in the shared literal disk-bit view. -/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace CodedSorting.CommonSlabReadBits

open WordControl CommonSortingNormalization CommonStaticSchedule BitWordPacking Circuit
open CommonLeafProgram (Disk Machine)
open PhysicalStreamCursor
open CommonPermutationPairs (readBit)

noncomputable section

theorem readBit_word (q : Configuration) (disk : Disk q) (base j : ℕ) (t : Fin q.w) :
    readBit q disk base (j*q.w+t.val) =
      wordBits q.w (disk (CommonColumnSplit.address q base (j/q.block))
        ⟨j%q.block, Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩) t := by
  have hw : 0<q.w := by have := q.word_width; omega
  have hd : (j*q.w+t.val)/q.w=j := by
    rw [Nat.add_comm, Nat.mul_comm j q.w, Nat.add_mul_div_left _ _ hw,
      Nat.div_eq_of_lt t.isLt, Nat.zero_add]
  have hm : (j*q.w+t.val)%q.w=t.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt t.isLt]
  have hb : (j*q.w+t.val)/(q.block*q.w)=j/q.block := by
    rw [Nat.mul_comm q.block q.w, ← Nat.div_div_eq_div_mul, hd]
  change wordBits q.w
    (disk (CommonColumnSplit.address q base ((j*q.w+t.val)/(q.block*q.w)))
      ⟨(j*q.w+t.val)%(q.block*q.w)/q.w, _⟩)
    ⟨(j*q.w+t.val)%(q.block*q.w)%q.w, _⟩ = _
  simp only [hb, Nat.mod_mul_left_div_self, Nat.mod_mul_left_mod, hd, hm]

/-- The target address map can describe any disjoint public slab allocation.
Its values are literal finite-disk block addresses, not a logical file oracle. -/
theorem split_column_bits (q : Configuration) (reader : Fin q.inventory.readers)
    {C n source : ℕ} (target : ℕ → Fin (q.N^q.exponent)) (bases : Fin C → ℕ)
    (s : Machine q)
    (hinj : ∀ p<C*blockCount q.block n, ∀ j<C*blockCount q.block n,
      target p=target j → p=j)
    (sep : ∀ b<blockCount q.block (C*n), ∀ p<C*blockCount q.block n,
      CommonColumnSplit.address q source b≠target p)
    (hmap : ∀ c : Fin C, ∀ k<blockCount q.block n,
      target (c.val*blockCount q.block n+k)=CommonColumnSplit.address q (bases c) k)
    (c : Fin C) (i : Fin (n*q.w)) :
    readBit q (executeRaw q (CommonStaticSlabSplit.code q reader C n source target) s).1.disk
      (bases c) i.val =
      readBit q s.disk source (c.val*(n*q.w)+i.val) := by
  have hw : 0<q.w := by have := q.word_width; omega
  let j := i.val/q.w
  let t : Fin q.w := ⟨i.val%q.w, Nat.mod_lt _ hw⟩
  have hj : j<n := (Nat.div_lt_iff_lt_mul hw).2 i.isLt
  have he : j*q.w+t.val=i.val := by
    simpa only [j, t, Nat.mul_comm] using Nat.div_add_mod i.val q.w
  have hk : j/q.block<blockCount q.block n := by
    apply (PhysicalStreamCursor.cursor_live_iff q.block n _
      (CommonLeafProgram.block_positive q)).2
    exact (Nat.div_mul_le_self _ _).trans_lt hj
  have hword := CommonStaticSlabSplit.raw_column_word q reader target s hinj sep
    c.val j c.isLt hj
  rw [hmap c _ hk] at hword
  have hout := congrArg (fun x => wordBits q.w x t) hword
  have hpos : (c.val*n+j)*q.w+t.val=c.val*(n*q.w)+i.val := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, he]
  conv_lhs => rw [← he, readBit_word]
  rw [← hpos, readBit_word]
  exact hout

/-- Conversely, the actual join concatenates just the live column bits;
the rounded allocation gaps never become part of the packed output. -/
theorem join_column_bits (q : Configuration) (reader : Fin q.inventory.readers)
    {C n target : ℕ} (source : ℕ → Fin (q.N^q.exponent)) (bases : Fin C → ℕ)
    (s : Machine q)
    (ht : target+blockCount q.block (C*n)≤q.N^q.exponent)
    (sep : ∀ k<C*blockCount q.block n,
      (source k).val<target ∨ target+blockCount q.block (C*n)≤(source k).val)
    (hmap : ∀ c : Fin C, ∀ k<blockCount q.block n,
      source (c.val*blockCount q.block n+k)=CommonColumnSplit.address q (bases c) k)
    (c : Fin C) (i : Fin (n*q.w)) :
    readBit q (executeRaw q (CommonStaticSlabJoinMapped.code q reader n C target source) s).1.disk
      target (c.val*(n*q.w)+i.val) = readBit q s.disk (bases c) i.val := by
  have hw : 0<q.w := by have := q.word_width; omega
  let j := i.val/q.w
  let t : Fin q.w := ⟨i.val%q.w, Nat.mod_lt _ hw⟩
  have hj : j<n := (Nat.div_lt_iff_lt_mul hw).2 i.isLt
  have he : j*q.w+t.val=i.val := by
    simpa only [j, t, Nat.mul_comm] using Nat.div_add_mod i.val q.w
  have hk : j/q.block<blockCount q.block n := by
    apply (PhysicalStreamCursor.cursor_live_iff q.block n _
      (CommonLeafProgram.block_positive q)).2
    exact (Nat.div_mul_le_self _ _).trans_lt hj
  have hr : c.val*n+j<C*n := by have := c.isLt; nlinarith
  have hblock : (c.val*n+j)/q.block<blockCount q.block (C*n) := by
    apply (PhysicalStreamCursor.cursor_live_iff q.block (C*n) _
      (CommonLeafProgram.block_positive q)).2
    exact (Nat.div_mul_le_self _ _).trans_lt hr
  have ha : target+(c.val*n+j)/q.block<q.N^q.exponent := by omega
  have hword := CommonStaticSlabJoinMapped.raw_packed_word q reader n C target source s
    ht sep c.val j c.isLt hj
  rw [hmap c _ hk] at hword
  simp only [CommonColumnJoin.outputWord, CommonLeafBatchProgram.extendDisk,
    ha, dif_pos] at hword
  have hout := congrArg (fun x => wordBits q.w x t) hword
  have hpos : (c.val*n+j)*q.w+t.val=c.val*(n*q.w)+i.val := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, he]
  conv_rhs => rw [← he, readBit_word]
  rw [← hpos, readBit_word]
  simpa only [CommonColumnSplit.address, ha, dif_pos] using hout

end
end CodedSorting.CommonSlabReadBits
end SlabReadBits

section SlabBatchAllocation
/-! One contiguous bank of aligned column slabs, followed by one shared
child workspace. Slab padding is an allocation gap, never a payload. -/
set_option autoImplicit false
namespace CodedSorting.CommonSlabBatch
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Disk Machine)
open PhysicalStreamCursor
noncomputable section

abbrev stride (q : Configuration) (n : ℕ) := blockCount q.block n
def base (q : Configuration) (n buffer c : ℕ) := buffer+c*stride q n
def slabMap (q : Configuration) (buffer : ℕ) := CommonColumnSplit.address q buffer

theorem word_count (q : Configuration) (n : ℕ) : count q (n*q.w)=stride q n :=
  CommonWordRoles.blockCount_words q.block q.w n
    (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega)

theorem slabMap_eq (q : Configuration) (n buffer c k : ℕ) :
    slabMap q buffer (c*stride q n+k)=CommonColumnSplit.address q (base q n buffer c) k := by
  simp only [slabMap,CommonColumnSplit.address,base,Nat.add_assoc]

theorem slabMap_val (q : Configuration) {C n buffer limit : ℕ}
    (hw : buffer+C*stride q n≤limit) (hl : limit≤q.N^q.exponent)
    {k : ℕ} (hk : k<C*stride q n) :
    (slabMap q buffer k).val=buffer+k :=
  CommonColumnSplit.address_val q buffer k (by omega)

theorem slabMap_injective (q : Configuration) {C n buffer limit : ℕ}
    (hw : buffer+C*stride q n≤limit) (hl : limit≤q.N^q.exponent) :
    ∀ p<C*stride q n,∀ j<C*stride q n,slabMap q buffer p=slabMap q buffer j→p=j := by
  intro p hp j hj he
  have hv:=congrArg Fin.val he
  rw [slabMap_val q hw hl hp,slabMap_val q hw hl hj] at hv
  omega

theorem slabMap_separate (q : Configuration) {C n source buffer limit : ℕ}
    (hs : source+stride q (C*n)≤buffer)
    (hw : buffer+C*stride q n≤limit) (hl : limit≤q.N^q.exponent) :
    ∀ b<stride q (C*n),∀ p<C*stride q n,
      CommonColumnSplit.address q source b≠slabMap q buffer p := by
  intro b hb p hp he
  have hv:=congrArg Fin.val he
  rw [CommonColumnSplit.address_val q source b (by omega),slabMap_val q hw hl hp] at hv
  omega

theorem slabMap_after_source (q : Configuration) {C n source buffer limit : ℕ}
    (hs : source+stride q (C*n)≤buffer)
    (hw : buffer+C*stride q n≤limit) (hl : limit≤q.N^q.exponent) :
    ∀ k<C*stride q n,(slabMap q buffer k).val<source ∨
      source+stride q (C*n)≤(slabMap q buffer k).val := by
  intro k hk
  rw [slabMap_val q hw hl hk]
  omega

theorem base_end (q : Configuration) {C n buffer : ℕ} (c : Fin C) :
    base q n buffer c.val+stride q n≤buffer+C*stride q n := by
  have hc:=Nat.mul_le_mul_right (stride q n) (Nat.succ_le_of_lt c.isLt)
  unfold base
  nlinarith

theorem bit_address (q : Configuration) {C n buffer work limit : ℕ}
    (hw : buffer+C*stride q n≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (c : Fin C) (i : Fin (n*q.w)) :
    (CommonColumnSplit.address q (base q n buffer c.val) (i.val/width q)).val=
      base q n buffer c.val+i.val/width q := by
  have hi:=bit_block_lt q i
  rw [word_count] at hi
  have hc:=base_end q (n:=n) (buffer:=buffer) c
  exact CommonColumnSplit.address_val q _ _ (by omega)

theorem bit_before_work (q : Configuration) {C n buffer work limit : ℕ}
    (hw : buffer+C*stride q n≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (c : Fin C) (i : Fin (n*q.w)) :
    (CommonColumnSplit.address q (base q n buffer c.val) (i.val/width q)).val<work := by
  rw [bit_address q hw hwl hl]
  have hi:=bit_block_lt q i
  rw [word_count] at hi
  have hc:=base_end q (n:=n) (buffer:=buffer) c
  omega

theorem bit_outside_other (q : Configuration) {C n buffer work limit : ℕ}
    (hw : buffer+C*stride q n≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (c d : Fin C) (hne : c≠d) (i : Fin (n*q.w)) :
    (CommonColumnSplit.address q (base q n buffer c.val) (i.val/width q)).val<base q n buffer d.val ∨
    base q n buffer d.val+stride q n≤
      (CommonColumnSplit.address q (base q n buffer c.val) (i.val/width q)).val := by
  rw [bit_address q hw hwl hl]
  have hi:=bit_block_lt q i
  rw [word_count] at hi
  have hd : c.val≠d.val := fun h=>hne (Fin.ext h)
  unfold base
  rcases lt_or_gt_of_ne hd with h|h
  · have hh:=Nat.mul_le_mul_right (stride q n) (Nat.succ_le_of_lt h)
    left
    nlinarith
  · have hh:=Nat.mul_le_mul_right (stride q n) (Nat.succ_le_of_lt h)
    right
    simp only [Nat.succ_mul] at hh
    have hh' := (Nat.add_le_add_left hh buffer).trans (Nat.le_add_right _ (i.val/width q))
    simpa only [Nat.add_assoc] using hh'

end
end CodedSorting.CommonSlabBatch
end SlabBatchAllocation
