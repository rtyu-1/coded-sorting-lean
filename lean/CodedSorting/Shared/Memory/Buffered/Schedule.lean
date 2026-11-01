import CodedSorting.Interchange.Framework.Memory.Reflection
import Mathlib.Data.Fintype.BigOperators

section BaseLayout
/-! Exact, payload-only bucket addresses for a scalar field exchange.

The bucket identifier contains the two exchanged fields. Its offset contains
only the unchanged prefix, gap and suffix, in their original order. These
coordinates are compile-time address calculations, not stored payload tags.
This module proves the address bijection, within-bucket order, and rounded
disk allocation bound; it does not assert execution of the buffered program.
-/
set_option autoImplicit false
namespace CodedSorting.CommonBufferedBaseLayout
open Address CoordinateScans TriangularStreams

abbrev Volume := BaseExchangeProgram.Volume
abbrev bucketSize (P G S : ℕ) := P*(G*S)

def addressEquiv (P Q G S : ℕ) :
    FullAddress (Fin P) (Fin Q) (Fin G) (Fin S) ≃
      Fin (Q*Q) × Fin (bucketSize P G S) where
  toFun a := (finProdFinEquiv (a.high,a.low),
    tripleEncode (a.prefixCoord,a.gap,a.suffix))
  invFun x :=
    let hd := finProdFinEquiv.symm x.1
    let pgs := tripleEncode.symm x.2
    ⟨pgs.1,hd.1,pgs.2.1,hd.2,pgs.2.2⟩
  left_inv a := by cases a; simp
  right_inv x := by
    simp only [Prod.mk.eta,Equiv.apply_symm_apply]

/-- The existing linear input address is split into bucket and bucket offset. -/
def indexEquiv (P Q G S : ℕ) :
    Fin (Volume P Q G S) ≃ Fin (Q*Q) × Fin (bucketSize P G S) :=
  lowLayout.symm.trans (addressEquiv P Q G S)

def key (P Q G S : ℕ) (i : Fin (Volume P Q G S)) : Fin (Q*Q) :=
  (indexEquiv P Q G S i).1

def rank (P Q G S : ℕ) (i : Fin (Volume P Q G S)) : Fin (bucketSize P G S) :=
  (indexEquiv P Q G S i).2

theorem key_eq (P Q G S : ℕ) (i : Fin (Volume P Q G S)) :
    key P Q G S i = BaseExchangeProgram.key i := rfl

@[simp] theorem indexEquiv_encoded (P Q G S : ℕ)
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    indexEquiv P Q G S (lowLayout a) =
      (finProdFinEquiv (a.high,a.low),tripleEncode (a.prefixCoord,a.gap,a.suffix)) := by
  simp [indexEquiv,addressEquiv]

@[simp] theorem rank_encoded (P Q G S : ℕ)
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    rank P Q G S (lowLayout a) = tripleEncode (a.prefixCoord,a.gap,a.suffix) := by
  simp [rank]

theorem rank_encoded_val (P Q G S : ℕ)
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    (rank P Q G S (lowLayout a)).val =
      a.suffix.val+S*a.gap.val+(G*S)*a.prefixCoord.val := by
  rw [rank_encoded,tripleEncode_val]

@[simp] theorem key_inverse (P Q G S : ℕ) (k : Fin (Q*Q))
    (r : Fin (bucketSize P G S)) :
    key P Q G S ((indexEquiv P Q G S).symm (k,r)) = k := by
  simp [key]

@[simp] theorem rank_inverse (P Q G S : ℕ) (k : Fin (Q*Q))
    (r : Fin (bucketSize P G S)) :
    rank P Q G S ((indexEquiv P Q G S).symm (k,r)) = r := by
  simp [rank]

theorem inverse_key_rank (P Q G S : ℕ) (i : Fin (Volume P Q G S)) :
    (indexEquiv P Q G S).symm (key P Q G S i,rank P Q G S i) = i := by
  exact (indexEquiv P Q G S).symm_apply_apply i

/-- Each bucket has exactly one input position for every spectator offset. -/
def fiberEquiv (P Q G S : ℕ) (k : Fin (Q*Q)) :
    {i : Fin (Volume P Q G S) // key P Q G S i=k} ≃ Fin (bucketSize P G S) where
  toFun i := rank P Q G S i.val
  invFun r := ⟨(indexEquiv P Q G S).symm (k,r),key_inverse P Q G S k r⟩
  left_inv i := by
    apply Subtype.ext
    change (indexEquiv P Q G S).symm (k,rank P Q G S i.val)=i.val
    apply (indexEquiv P Q G S).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext i.property.symm rfl
  right_inv r := rank_inverse P Q G S k r

theorem fiber_card (P Q G S : ℕ) (k : Fin (Q*Q)) :
    Fintype.card {i : Fin (Volume P Q G S) // key P Q G S i=k} = bucketSize P G S := by
  classical
  exact (Fintype.card_congr (fiberEquiv P Q G S k)).trans (Fintype.card_fin _)

theorem volume_eq (P Q G S : ℕ) :
    Volume P Q G S = (Q*Q)*bucketSize P G S := by
  unfold Volume BaseExchangeProgram.Volume bucketSize
  ring

private theorem encoded_lt_iff {P Q G S : ℕ}
    (a b : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S))
    (hh : a.high=b.high) (hl : a.low=b.low) :
    lowLayout a < lowLayout b ↔
      tripleEncode (a.prefixCoord,a.gap,a.suffix) <
        tripleEncode (b.prefixCoord,b.gap,b.suffix) := by
  change tripleEncode (tripleEncode (a.prefixCoord,a.high,a.gap),a.low,a.suffix) <
    tripleEncode (tripleEncode (b.prefixCoord,b.high,b.gap),b.low,b.suffix) ↔ _
  rw [tripleEncode_lt_iff,tripleEncode_lt_iff,tripleEncode_lt_iff]
  simp only [hh,hl,lt_self_iff_false,true_and,false_or,Equiv.apply_eq_iff_eq,
    Prod.mk.injEq,and_true]
  aesop

/-- Source order inside one bucket is exactly offset order. -/
theorem rank_lt_iff (P Q G S : ℕ) (i j : Fin (Volume P Q G S))
    (hk : key P Q G S i=key P Q G S j) :
    rank P Q G S i < rank P Q G S j ↔ i<j := by
  obtain ⟨a,rfl⟩ := lowLayout.surjective i
  obtain ⟨b,rfl⟩ := lowLayout.surjective j
  have hp : (a.high,a.low)=(b.high,b.low) := by
    apply finProdFinEquiv.injective
    simpa only [key,indexEquiv_encoded] using hk
  have hh := congrArg Prod.fst hp
  have hl := congrArg Prod.snd hp
  rw [rank_encoded,rank_encoded]
  exact (encoded_lt_iff a b hh hl).symm

theorem inverse_lt_iff (P Q G S : ℕ) (k : Fin (Q*Q))
    (r s : Fin (bucketSize P G S)) :
    (indexEquiv P Q G S).symm (k,r) < (indexEquiv P Q G S).symm (k,s) ↔ r<s := by
  have h := rank_lt_iff P Q G S ((indexEquiv P Q G S).symm (k,r))
    ((indexEquiv P Q G S).symm (k,s)) (by simp)
  simpa only [rank_inverse] using h.symm

/-- Exchanging the fields changes only the bucket, never the offset. -/
theorem rank_permutation (P Q G S : ℕ) (i : Fin (Volume P Q G S)) :
    rank P Q G S (BaseExchangeProgram.permutation i) = rank P Q G S i := by
  obtain ⟨a,rfl⟩ := lowLayout.surjective i
  rw [BaseExchangeProgram.permutation_encoded,rank_encoded,rank_encoded]
  rfl

/-- A destination position requests the original bucket and original offset
of the source bit that belongs there. -/
def outputIndexEquiv (P Q G S : ℕ) :
    Fin (Volume P Q G S) ≃ Fin (Q*Q) × Fin (bucketSize P G S) :=
  BaseExchangeProgram.permutation.symm.trans (indexEquiv P Q G S)

@[simp] theorem outputIndexEquiv_permutation (P Q G S : ℕ)
    (i : Fin (Volume P Q G S)) :
    outputIndexEquiv P Q G S (BaseExchangeProgram.permutation i)=
      indexEquiv P Q G S i := by
  simp [outputIndexEquiv]

/-- Reconstruction also visits every original bucket from left to right. -/
theorem output_inverse_lt_iff (P Q G S : ℕ) (k : Fin (Q*Q))
    (r s : Fin (bucketSize P G S)) :
    (outputIndexEquiv P Q G S).symm (k,r) <
      (outputIndexEquiv P Q G S).symm (k,s) ↔ r<s := by
  have hm : StrictMono (fun r : Fin (bucketSize P G S) =>
      BaseExchangeProgram.permutation ((indexEquiv P Q G S).symm (k,r))) := by
    intro x y hxy
    apply BaseExchangeProgram.increasing_streams
    · exact (inverse_lt_iff P Q G S k x y).2 hxy
    · rw [← key_eq,← key_eq,key_inverse,key_inverse]
  exact hm.lt_iff_lt

/-- One rounded file per bucket costs at most one extra block per bucket. -/
theorem bucket_blocks_le (B K L : ℕ) (hB : 0<B) :
    K*PhysicalStreamCursor.blockCount B L ≤
      PhysicalStreamCursor.blockCount B (K*L)+K := by
  have hsmall : PhysicalStreamCursor.blockCount B L*B ≤ L+B := by
    exact (Nat.div_mul_le_self (L+B-1) B).trans (by omega)
  have hscaled := Nat.mul_le_mul_left K hsmall
  have hcover : K*L ≤ PhysicalStreamCursor.blockCount B (K*L)*B :=
    LayoutConversion.blockCount_covers (K*L) B hB
  have hfinal : (K*PhysicalStreamCursor.blockCount B L)*B ≤
      (PhysicalStreamCursor.blockCount B (K*L)+K)*B := by nlinarith
  exact Nat.le_of_mul_le_mul_right hfinal hB

theorem exchange_bucket_blocks_le (P Q G S B : ℕ) (hB : 0<B) :
    (Q*Q)*PhysicalStreamCursor.blockCount B (bucketSize P G S) ≤
      PhysicalStreamCursor.blockCount B (Volume P Q G S)+(Q*Q) := by
  rw [volume_eq]
  exact bucket_blocks_le B (Q*Q) (bucketSize P G S) hB

end CodedSorting.CommonBufferedBaseLayout
end BaseLayout

section Schedule
/-! Public transfer events of an equal-sized buffered distribution.
All flags depend only on the dimensions, positions, and public bucket layout.
Payload bits are not inspected. -/
set_option autoImplicit false
namespace CodedSorting.CommonBufferedSchedule
open PhysicalStreamCursor
noncomputable section

/-- First position of a physical payload block. -/
def starts (W i : ℕ) : Prop := i % W = 0
/-- Last live position of a physical payload block, including a partial tail. -/
def ends (W n i : ℕ) : Prop := i % W = W-1 ∨ i+1=n

instance (W i : ℕ) : Decidable (starts W i) := inferInstanceAs (Decidable (i%W=0))
instance (W n i : ℕ) : Decidable (ends W n i) :=
  inferInstanceAs (Decidable (i%W=W-1 ∨ i+1=n))

def startEquiv (W n : ℕ) (hW : 0<W) :
    {i : Fin n // starts W i.val} ≃ Fin (blockCount W n) where
  toFun i := ⟨i.1.val/W,(cursor_live_iff W n _ hW).2
    ((Nat.div_mul_le_self _ _).trans_lt i.1.isLt)⟩
  invFun j := ⟨⟨j.val*W,(cursor_live_iff W n _ hW).1 j.isLt⟩,by simp [starts]⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have hh := Nat.div_add_mod i.1.val W
    have hz := i.2
    change i.1.val % W=0 at hz
    rw [hz,Nat.add_zero] at hh
    simpa only [Nat.mul_comm] using hh
  right_inv j := by
    apply Fin.ext
    exact Nat.mul_div_cancel _ hW

private theorem flag_count {α : Type*} [Fintype α] (p : α→Prop) [DecidablePred p] :
    (∑ i : α,if p i then 1 else 0)=Fintype.card {i // p i} := by
  rw [Fintype.card_subtype]
  simp

theorem start_count (W n : ℕ) (hW : 0<W) :
    (∑ i : Fin n,if starts W i.val then 1 else 0)=blockCount W n := by
  rw [flag_count,Fintype.card_congr (startEquiv W n hW),Fintype.card_fin]

/-- Final live offset of numbered block j. -/
def lastPos (W n j : ℕ) := min ((j+1)*W) n-1

private theorem lastPos_bounds (W n : ℕ) (hW : 0<W)
    (j : Fin (blockCount W n)) :
    j.val*W ≤ lastPos W n j.val ∧ lastPos W n j.val < (j.val+1)*W ∧
      lastPos W n j.val < n := by
  have hj := (cursor_live_iff W n _ hW).1 j.isLt
  have hh : j.val*W < (j.val+1)*W := by rw [Nat.add_mul]; omega
  unfold lastPos
  have hl : j.val*W < min ((j.val+1)*W) n := lt_min hh hj
  have hm1 := Nat.min_le_left ((j.val+1)*W) n
  have hm2 := Nat.min_le_right ((j.val+1)*W) n
  omega

private theorem lastPos_ends (W n : ℕ) (hW : 0<W)
    (j : Fin (blockCount W n)) : ends W n (lastPos W n j.val) := by
  unfold lastPos ends
  by_cases hn : (j.val+1)*W≤n
  · rw [Nat.min_eq_left hn]
    left
    rw [Nat.add_mul,Nat.one_mul,Nat.add_sub_assoc (by omega : 1≤W),
      Nat.add_mod,Nat.mul_mod_left,Nat.zero_add]
    simpa only [Nat.mod_mod] using Nat.mod_eq_of_lt (by omega : W-1<W)
  · rw [Nat.min_eq_right (by omega : n≤(j.val+1)*W)]
    right
    have hj := (cursor_live_iff W n _ hW).1 j.isLt
    omega

def finishEquiv (W n : ℕ) (hW : 0<W) :
    {i : Fin n // ends W n i.val} ≃ Fin (blockCount W n) where
  toFun i := ⟨i.1.val/W,(cursor_live_iff W n _ hW).2
    ((Nat.div_mul_le_self _ _).trans_lt i.1.isLt)⟩
  invFun j := ⟨⟨lastPos W n j.val,(lastPos_bounds W n hW j).2.2⟩,
    lastPos_ends W n hW j⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change lastPos W n (i.1.val/W)=i.1.val
    have hh := Nat.div_add_mod i.1.val W
    rw [Nat.mul_comm W] at hh
    have hm := Nat.mod_lt i.1.val hW
    have hi := i.1.isLt
    have hf := i.2
    unfold ends at hf
    unfold lastPos
    rw [Nat.add_mul,Nat.one_mul]
    rcases hf with hf|hf
    · rw [hf] at hh
      have hfull : (i.1.val/W)*W+W=i.1.val+1 := by omega
      rw [hfull,Nat.min_eq_left (by omega)]
      omega
    · have htail : n≤(i.1.val/W)*W+W := by omega
      rw [Nat.min_eq_right htail]
      omega
  right_inv j := by
    apply Fin.ext
    change lastPos W n j.val/W=j.val
    have hb := lastPos_bounds W n hW j
    apply Nat.le_antisymm
    · have hh := (Nat.div_lt_iff_lt_mul hW).2 hb.2.1
      omega
    · exact (Nat.le_div_iff_mul_le hW).2 hb.1

theorem finish_count (W n : ℕ) (hW : 0<W) :
    (∑ i : Fin n,if ends W n i.val then 1 else 0)=blockCount W n := by
  rw [flag_count,Fintype.card_congr (finishEquiv W n hW),Fintype.card_fin]

variable {V K L : ℕ}

def distributeRead (W : ℕ) (i : Fin V) : Prop := starts W i.val
def distributeWrite (E : Fin V ≃ Fin K × Fin L) (W : ℕ) (i : Fin V) : Prop :=
  ends W L (E i).2.val
def reconstructRead (E : Fin V ≃ Fin K × Fin L) (e : Equiv.Perm (Fin V))
    (W : ℕ) (y : Fin V) : Prop := starts W (E (e.symm y)).2.val
def reconstructWrite (W : ℕ) (y : Fin V) : Prop := ends W V y.val

theorem bucket_start_count (E : Fin V ≃ Fin K × Fin L) (W : ℕ) (hW : 0<W) :
    (∑ i : Fin V,if starts W (E i).2.val then 1 else 0)=K*blockCount W L := by
  rw [Equiv.sum_comp E (fun p => if starts W p.2.val then 1 else 0)]
  simp only [Fintype.sum_prod_type,start_count W L hW,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]

theorem bucket_finish_count (E : Fin V ≃ Fin K × Fin L) (W : ℕ) (hW : 0<W) :
    (∑ i : Fin V,if ends W L (E i).2.val then 1 else 0)=K*blockCount W L := by
  rw [Equiv.sum_comp E (fun p => if ends W L p.2.val then 1 else 0)]
  simp only [Fintype.sum_prod_type,finish_count W L hW,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]

/-- Number of real disk operations in the public distribution schedule. -/
def distributionCount (E : Fin V ≃ Fin K × Fin L) (W : ℕ) : ℕ :=
  ∑ i : Fin V, ((if starts W i.val then 1 else 0)+
    (if ends W L (E i).2.val then 1 else 0))

/-- Reconstruction follows the output permutation, with one resident input
buffer per bucket and one sequential output buffer. -/
def reconstructionCount (E : Fin V ≃ Fin K × Fin L)
    (e : Equiv.Perm (Fin V)) (W : ℕ) : ℕ :=
  ∑ y : Fin V, ((if starts W (E (e.symm y)).2.val then 1 else 0)+
    (if ends W V y.val then 1 else 0))

theorem distribution_count (E : Fin V ≃ Fin K × Fin L) (W : ℕ) (hW : 0<W) :
    distributionCount E W=blockCount W V+K*blockCount W L := by
  rw [distributionCount,Finset.sum_add_distrib,start_count W V hW,
    bucket_finish_count E W hW]

theorem reconstruction_count (E : Fin V ≃ Fin K × Fin L)
    (e : Equiv.Perm (Fin V)) (W : ℕ) (hW : 0<W) :
    reconstructionCount E e W=K*blockCount W L+blockCount W V := by
  unfold reconstructionCount
  rw [Finset.sum_add_distrib,finish_count W V hW]
  have hh := bucket_start_count (e.symm.trans E) W hW
  simpa only [Equiv.trans_apply] using congrArg (fun x => x+blockCount W V) hh

theorem total_count (E : Fin V ≃ Fin K × Fin L)
    (e : Equiv.Perm (Fin V)) (W : ℕ) (hW : 0<W) :
    distributionCount E W+reconstructionCount E e W=
      2*blockCount W V+2*K*blockCount W L := by
  rw [distribution_count E W hW,reconstruction_count E e W hW]
  ring

/-- Padding loses at most one block per bucket. The bucket count is an
additive startup cost; it never multiplies the volume scan. -/
theorem total_count_le (E : Fin V ≃ Fin K × Fin L)
    (e : Equiv.Perm (Fin V)) (W : ℕ) (hW : 0<W) :
    distributionCount E W+reconstructionCount E e W≤4*blockCount W V+2*K := by
  have hcard := Fintype.card_congr E
  simp only [Fintype.card_fin,Fintype.card_prod] at hcard
  have hb := CommonBufferedBaseLayout.bucket_blocks_le W K L hW
  rw [←hcard] at hb
  rw [total_count E e W hW]
  nlinarith

end
end CodedSorting.CommonBufferedSchedule
end Schedule
