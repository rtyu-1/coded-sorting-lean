import CodedSorting.Shared.Memory.MonotoneExtension
import CodedSorting.Interchange.Framework.Chunks.Exchange

section FinitePaddingCore
/-! Actual zero initialization followed by a live-prefix copy. In particular,
the unused suffix of a partially filled block remains zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonFinitePadding
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open CommonRecursiveExchange (copyCode)
open BitWordPacking Circuit
noncomputable section
attribute [local instance] Classical.propDecidable

theorem count_mono (q : Configuration) {V M : ℕ} (h : V≤M) : count q V≤count q M := by
  apply LayoutConversion.blockCount_minimal _ _ _ (width_pos q)
  exact h.trans (LayoutConversion.blockCount_covers M (width q) (width_pos q))

theorem pair_preserves_tail (q : Configuration) {V M K : ℕ}
    (e : Equiv.Perm (Fin V)) (key : Fin V → Fin K) (source target : ℕ)
    (p : Entry K) (disk : Disk q) (hVM : V≤M) (hf : Fits q V p)
    (ht : target+count q M≤q.N^q.exponent) (i : Fin M) (hi : V ≤ i.val) :
    readBit q (stepDisk q e key source target p disk) target i.val=
      readBit q disk target i.val := by
  have hc := count_mono q hVM
  have hip := bit_block_lt q i
  have hpp := hf.2
  by_cases hp : i.val/width q=p.2.2
  · have he : p.2.2*width q+i.val%width q=i.val := by
      rw [←hp]
      simpa only [Nat.mul_comm] using Nat.div_add_mod i.val (width q)
    have hz : select q e key p ⟨i.val%width q,Nat.mod_lt _ (width_pos q)⟩=none := by
      simp only [select,he,dif_neg (by omega : ¬i.val<V)]
    unfold readBit stepDisk
    rw [hp,Function.update_self,CommonBlockPair.blend_bits]
    have hmod : i.val%width q=(i.val)%width q := rfl
    exact congrArg (fun o => match o with
      | none => blockBits q.block q.w (disk (address q target p.2.2))
          ⟨i.val%width q,Nat.mod_lt _ (width_pos q)⟩
      | some j => blockBits q.block q.w (disk (address q source p.2.1)) j) hz
  · have hne : address q target (i.val/width q)≠address q target p.2.2 := by
      intro hh
      have hv := congrArg Fin.val hh
      rw [CommonColumnSplit.address_val q target _ (by omega),
        CommonColumnSplit.address_val q target _ (by omega)] at hv
      omega
    simp only [readBit,stepDisk,Function.update_of_ne hne]

theorem pairs_preserve_tail (q : Configuration) {V M K : ℕ}
    (e : Equiv.Perm (Fin V)) (key : Fin V → Fin K) (source target : ℕ)
    (ps : List (Entry K)) (disk : Disk q) (hVM : V≤M)
    (hf : ∀ p∈ps,Fits q V p) (ht : target+count q M≤q.N^q.exponent)
    (i : Fin M) (hi : V ≤ i.val) :
    readBit q (applyPairs q e key source target ps disk) target i.val=
      readBit q disk target i.val := by
  induction ps generalizing disk with
  | nil => rfl
  | cons p ps ih =>
    rw [applyPairs,ih _ (fun a ha => hf a (List.mem_cons_of_mem p ha))]
    exact pair_preserves_tail q e key source target p disk hVM
      (hf p (List.mem_cons_self ..)) ht i hi

theorem copy_preserves_tail (q : Configuration) (reader : Fin q.inventory.readers)
    (V M source target : ℕ) (s : Machine q) (hVM : V≤M)
    (ht : target+count q M≤q.N^q.exponent) (i : Fin M) (hi : V ≤ i.val) :
    readBit q (executeRaw q (copyCode q reader V source target) s).1.disk target i.val=
      readBit q s.disk target i.val := by
  unfold copyCode CommonPermutationScan.program
  rw [CommonPermutationPairs.raw_disk]
  exact pairs_preserve_tail q _ _ source target _ s.disk hVM
    (MonotoneBlockPairs.schedule_bounds _ _ (width q) (width_pos q)) ht i hi

def zeroCode (q : Configuration) (reader : Fin q.inventory.readers)
    (M target : ℕ) : List (Instruction q) :=
  CommonXorAccumulator.code q reader M target []

theorem zero_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (M target : ℕ) (s : Machine q) (ht : target+count q M≤q.N^q.exponent) :
    (∀ i : Fin M, readBit q (executeRaw q (zeroCode q reader M target) s).1.disk
      target i.val=0) ∧
    (∀ a : Fin (q.N^q.exponent), a.val<target ∨ target+count q M≤a.val →
      (executeRaw q (zeroCode q reader M target) s).1.disk a=s.disk a) := by
  obtain ⟨hb,hf,_⟩ := CommonXorAccumulator.raw_complete q reader M target [] s ht
    (by simp) (by simp)
  exact ⟨by simpa only [List.map_nil,List.sum_nil] using hb,hf⟩

theorem zero_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (M target : ℕ) : ∀ i∈zeroCode q reader M target,RespectsPC q i :=
  CommonXorAccumulator.code_safe q reader M target []

theorem zero_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (M target : ℕ) : cost q (zeroCode q reader M target)=3*count q M := by
  simpa only [List.length_nil,Nat.zero_add,Nat.mul_one] using
    CommonXorAccumulator.code_cost q reader M target []

theorem zero_length (q : Configuration) (reader : Fin q.inventory.readers)
    (M target : ℕ) : (zeroCode q reader M target).length=3*count q M := by
  simpa only [List.length_nil,Nat.zero_add,Nat.mul_one] using
    CommonXorAccumulator.code_length q reader M target []

def prefixCode (q : Configuration) (reader : Fin q.inventory.readers)
    (V M source target : ℕ) : List (Instruction q) :=
  zeroCode q reader M target ++ copyCode q reader V source target

theorem prefix_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (V M source target : ℕ) (s : Machine q) (hVM : V≤M)
    (hs : source+count q V≤q.N^q.exponent)
    (ht : target+count q M≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q M≤source) :
    (∀ i : Fin V,readBit q (executeRaw q (prefixCode q reader V M source target) s).1.disk
      target i.val=readBit q s.disk source i.val) ∧
    (∀ i : Fin M,V ≤ i.val →
      readBit q (executeRaw q (prefixCode q reader V M source target) s).1.disk target i.val=0) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q M≤a.val →
      (executeRaw q (prefixCode q reader V M source target) s).1.disk a=s.disk a) := by
  let mid := (executeRaw q (zeroCode q reader M target) s).1
  have hc := count_mono q hVM
  obtain ⟨hz,hzf⟩ := zero_raw q reader M target s ht
  obtain ⟨hb,hbf⟩ := CommonRecursiveExchange.copyCode_raw q reader V source target mid hs
    (by omega) (by omega)
  rw [prefixCode,CommonPermutationPairs.raw_append]
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hb]
    have hi := bit_block_lt q i
    unfold readBit
    rw [hzf]
    rw [CommonColumnSplit.address_val q source _ (by omega)]
    rcases hsep with hh|hh
    · left; omega
    · right; exact hh.trans (Nat.le_add_right _ _)
  · intro i hi
    exact (copy_preserves_tail q reader V M source target mid hVM ht i hi).trans (hz i)
  · intro a ha
    exact (hbf a (by omega)).trans (hzf a ha)

theorem prefix_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (V M source target : ℕ) : ∀ i∈prefixCode q reader V M source target,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hz|hc
  · exact zero_safe q reader M target i hz
  · exact CommonRecursiveExchange.copyCode_safe q reader V source target i hc

theorem prefix_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (V M source target : ℕ) :
    cost q (prefixCode q reader V M source target)≤6*count q V+3*count q M := by
  rw [prefixCode,CommonPermutationPairs.cost_append,zero_cost]
  have hc := CommonRecursiveExchange.copyCode_cost q reader V source target
  omega

theorem prefix_length (q : Configuration) (reader : Fin q.inventory.readers)
    (V M source target : ℕ) :
    (prefixCode q reader V M source target).length≤6*count q V+3*count q M := by
  rw [prefixCode,List.length_append,zero_length]
  have hc := CommonRecursiveExchange.copyCode_length q reader V source target
  omega

end
end CodedSorting.CommonFinitePadding
end FinitePaddingCore

section FinitePadding
/-! Real finite-machine padding and erasure along an increasing embedding.
The inserted complement is zeroed by actual disk instructions, and every
permutation and copy is charged. No initial-zero premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonFinitePadding
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonRecursiveExchange (copyCode)
open CommonMonotoneExtension (permutation colour inverseColour)
noncomputable section
variable {V M : ℕ}

def insertCode (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ) :
    List (Instruction q) :=
  prefixCode q reader V M source scratch ++
    CommonPermutationScan.program q reader (permutation h e he) (colour V) scratch target

def eraseCode (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ) :
    List (Instruction q) :=
  CommonPermutationScan.program q reader (permutation h e he).symm
    (inverseColour h e he) source scratch ++ copyCode q reader V scratch target

theorem inverse_outside (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e)
    (i : Fin M) (hi : ¬∃ x : Fin V,e x=i) :
    V ≤ ((permutation h e he).symm i).val := by
  by_contra hn
  have hv : ((permutation h e he).symm i).val<V := by omega
  let x : Fin V := ⟨((permutation h e he).symm i).val,hv⟩
  have hx : x.castLE h=(permutation h e he).symm i := Fin.ext rfl
  apply hi
  refine ⟨x,?_⟩
  rw [←CommonMonotoneExtension.perm_prefix h e he x,hx,Equiv.apply_symm_apply]

/-- The original bits occupy exactly the embedding image; every other
live padded position is zero, regardless of initial scratch/target data. -/
theorem insert_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ)
    (s : Machine q) (hs : source+count q V≤q.N^q.exponent)
    (hw : scratch+count q M≤q.N^q.exponent) (ht : target+count q M≤q.N^q.exponent)
    (hsw : source+count q V≤scratch ∨ scratch+count q M≤source)
    (hwt : scratch+count q M≤target ∨ target+count q M≤scratch) :
    (∀ x : Fin V,readBit q (executeRaw q (insertCode q reader h e he source scratch target) s).1.disk
      target (e x).val=readBit q s.disk source x.val) ∧
    (∀ i : Fin M,(¬∃ x : Fin V,e x=i) →
      readBit q (executeRaw q (insertCode q reader h e he source scratch target) s).1.disk
        target i.val=0) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<scratch ∨ scratch+count q M≤a.val) →
      (a.val<target ∨ target+count q M≤a.val) →
      (executeRaw q (insertCode q reader h e he source scratch target) s).1.disk a=s.disk a) := by
  let mid := (executeRaw q (prefixCode q reader V M source scratch) s).1
  obtain ⟨hp,hz,hpf⟩ := prefix_raw q reader V M source scratch s h hs hw hsw
  obtain ⟨hb,hbf⟩ := CommonPermutationScan.raw_correct q reader (permutation h e he)
    (colour V) scratch target hw ht hwt mid
  rw [insertCode,CommonPermutationPairs.raw_append]
  refine ⟨?_,?_,?_⟩
  · intro x
    rw [hb,CommonMonotoneExtension.inverse_embed]
    exact hp x
  · intro i hi
    rw [hb]
    exact hz _ (inverse_outside h e he i hi)
  · intro a haw hat
    exact (hbf a hat).trans (hpf a haw)

/-- Erasure reads the embedding image. Values in its complement may be
arbitrary, so this operation also applies after an intervening computation. -/
theorem erase_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ)
    (s : Machine q) (hs : source+count q M≤q.N^q.exponent)
    (hw : scratch+count q M≤q.N^q.exponent) (ht : target+count q V≤q.N^q.exponent)
    (hsw : source+count q M≤scratch ∨ scratch+count q M≤source)
    (hwt : scratch+count q M≤target ∨ target+count q V≤scratch) :
    (∀ x : Fin V,readBit q (executeRaw q (eraseCode q reader h e he source scratch target) s).1.disk
      target x.val=readBit q s.disk source (e x).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<scratch ∨ scratch+count q M≤a.val) →
      (a.val<target ∨ target+count q V≤a.val) →
      (executeRaw q (eraseCode q reader h e he source scratch target) s).1.disk a=s.disk a) := by
  let mid := (executeRaw q (CommonPermutationScan.program q reader (permutation h e he).symm
    (inverseColour h e he) source scratch) s).1
  have hc := count_mono q h
  obtain ⟨hp,hpf⟩ := CommonPermutationScan.raw_correct q reader (permutation h e he).symm
    (inverseColour h e he) source scratch hs hw hsw s
  obtain ⟨hb,hbf⟩ := CommonRecursiveExchange.copyCode_raw q reader V scratch target mid
    (by omega) ht (by omega)
  rw [eraseCode,CommonPermutationPairs.raw_append]
  constructor
  · intro x
    rw [hb]
    have hp' := hp (x.castLE h)
    simpa only [Equiv.symm_symm,CommonMonotoneExtension.perm_prefix,Fin.coe_castLE] using hp'
  · intro a haw hat
    exact (hbf a hat).trans (hpf a haw)

theorem insert_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ) :
    ∀ i∈insertCode q reader h e he source scratch target,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hp|hs
  · exact prefix_safe q reader V M source scratch i hp
  · exact CommonPermutationScan.program_safe q reader _ _ scratch target i hs

theorem erase_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ) :
    ∀ i∈eraseCode q reader h e he source scratch target,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hp|hc
  · exact CommonPermutationScan.program_safe q reader _ _ source scratch i hp
  · exact CommonRecursiveExchange.copyCode_safe q reader V scratch target i hc

theorem insert_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ) :
    cost q (insertCode q reader h e he source scratch target)≤6*count q V+15*count q M := by
  have hp := prefix_cost q reader V M source scratch
  have hs := CommonPermutationScan.program_cost q reader (permutation h e he) (colour V)
    scratch target (CommonMonotoneExtension.increasing h e he)
  rw [insertCode,CommonPermutationPairs.cost_append]
  omega

theorem insert_length (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ) :
    (insertCode q reader h e he source scratch target).length≤6*count q V+15*count q M := by
  have hp := prefix_length q reader V M source scratch
  have hs := CommonPermutationScan.program_length q reader (permutation h e he) (colour V)
    scratch target (CommonMonotoneExtension.increasing h e he)
  rw [insertCode,List.length_append]
  omega

theorem erase_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ) :
    cost q (eraseCode q reader h e he source scratch target)≤6*count q V+12*count q M := by
  have hp := CommonPermutationScan.program_cost q reader (permutation h e he).symm
    (inverseColour h e he) source scratch (CommonMonotoneExtension.inverse_increasing h e he)
  have hc := CommonRecursiveExchange.copyCode_cost q reader V scratch target
  rw [eraseCode,CommonPermutationPairs.cost_append]
  omega

theorem erase_length (q : Configuration) (reader : Fin q.inventory.readers)
    (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e) (source scratch target : ℕ) :
    (eraseCode q reader h e he source scratch target).length≤6*count q V+12*count q M := by
  have hp := CommonPermutationScan.program_length q reader (permutation h e he).symm
    (inverseColour h e he) source scratch (CommonMonotoneExtension.inverse_increasing h e he)
  have hc := CommonRecursiveExchange.copyCode_length q reader V scratch target
  rw [eraseCode,List.length_append]
  omega

end
end CodedSorting.CommonFinitePadding
end FinitePadding

section PaddedPermutation
/-! Actual padding, computation and erasure on one finite machine.  The
wrapper is valid for arbitrary initial disk and RAM contents. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonPaddedPermutation
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonFinitePermutation CommonFinitePadding
open CommonChunkLayout (Volume swap)
open Address CoordinateScans
noncomputable section

def wrap (q : Configuration) (reader : Fin q.inventory.readers)
    {V M : ℕ} (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e)
    (smallπ : Equiv.Perm (Fin V)) (largeπ : Equiv.Perm (Fin M))
    (hcomm : ∀ y : Fin V,largeπ (e y)=e (smallπ y))
    (source buffer limit : ℕ)
    (child : Program q M (buffer+count q M) (buffer+count q M+count q M) limit largeπ)
    (hs : source+count q V≤buffer)
    (hw : buffer+count q M+count q M≤limit)
    (hl : limit≤q.N^q.exponent) : Program q V source buffer limit smallπ where
  instructions := insertCode q reader h e he source buffer (buffer+count q M) ++
    child.instructions ++ eraseCode q reader h e he (buffer+count q M) buffer source
  charge := child.charge+12*count q V+27*count q M
  correct := by
    intro s y
    let inserted := (executeRaw q
      (insertCode q reader h e he source buffer (buffer+count q M)) s).1
    let computed := (executeRaw q child.instructions inserted).1
    have hins := (insert_raw q reader h e he source buffer (buffer+count q M) s
      (by omega) (by omega) (by omega) (Or.inl hs) (Or.inl (le_refl _))).1
    have hcalc := child.correct inserted (e y)
    rw [hcomm] at hcalc
    have herase := (erase_raw q reader h e he (buffer+count q M) buffer source computed
      (by omega) (by omega) (by omega) (Or.inr (le_refl _)) (Or.inr hs)).1 y
    rw [raw_append,raw_append]
    exact herase.trans (hcalc.trans (hins (smallπ y)))
  frame := by
    intro s a hsource hbuffer
    let inserted := (executeRaw q
      (insertCode q reader h e he source buffer (buffer+count q M)) s).1
    let computed := (executeRaw q child.instructions inserted).1
    have hscratch : a.val<buffer ∨ buffer+count q M≤a.val := by omega
    have hpadded : a.val<buffer+count q M ∨ buffer+count q M+count q M≤a.val := by omega
    have hchild : a.val<buffer+count q M+count q M ∨ limit≤a.val := by omega
    have hins := (insert_raw q reader h e he source buffer (buffer+count q M) s
      (by omega) (by omega) (by omega) (Or.inl hs) (Or.inl (le_refl _))).2.2
      a hscratch hpadded
    have hcalc := child.frame inserted a hpadded hchild
    have herase := (erase_raw q reader h e he (buffer+count q M) buffer source computed
      (by omega) (by omega) (by omega) (Or.inr (le_refl _)) (Or.inr hs)).2
      a hscratch hsource
    rw [raw_append,raw_append]
    exact herase.trans (hcalc.trans hins)
  safe := by
    intro i hi
    rcases List.mem_append.mp hi with hic|hec
    · rcases List.mem_append.mp hic with hi|hc
      · exact insert_safe q reader h e he source buffer (buffer+count q M) i hi
      · exact child.safe i hc
    · exact erase_safe q reader h e he (buffer+count q M) buffer source i hec
  cost_le := by
    have hi := insert_cost q reader h e he source buffer (buffer+count q M)
    have he' := erase_cost q reader h e he (buffer+count q M) buffer source
    have hc := child.cost_le
    rw [cost_append,cost_append]
    omega
  length_le := by
    have hi := insert_length q reader h e he source buffer (buffer+count q M)
    have he' := erase_length q reader h e he (buffer+count q M) buffer source
    have hc := child.length_le
    rw [List.length_append,List.length_append]
    omega

theorem wrap_charge (q : Configuration) (reader : Fin q.inventory.readers)
    {V M : ℕ} (h : V≤M) (e : Fin V→Fin M) (he : StrictMono e)
    (smallπ : Equiv.Perm (Fin V)) (largeπ : Equiv.Perm (Fin M))
    (hcomm : ∀ y : Fin V,largeπ (e y)=e (smallπ y))
    (source buffer limit : ℕ)
    (child : Program q M (buffer+count q M) (buffer+count q M+count q M) limit largeπ)
    (hs : source+count q V≤buffer) (hw : buffer+count q M+count q M≤limit)
    (hl : limit≤q.N^q.exponent) :
    (wrap q reader h e he smallπ largeπ hcomm source buffer limit child hs hw hl).charge=
      child.charge+12*count q V+27*count q M := rfl

theorem prefix_swap_commutes (P P' Q G S : ℕ) (h : P≤P')
    (y : Fin (Volume P Q G S)) :
    swap P' Q G S (y.castLE (PhysicalPrefixPadding.volume_mono h))=
      (swap P Q G S y).castLE (PhysicalPrefixPadding.volume_mono h) := by
  obtain ⟨a,rfl⟩ := (lowLayout (P:=P) (Q:=Q) (G:=G) (S:=S)).surjective y
  rw [← PhysicalPrefixPadding.embed_address h a,CommonChunkLayout.swap_encoded,
    CommonChunkLayout.swap_encoded,← PhysicalPrefixPadding.embed_exchange h a,
    PhysicalPrefixPadding.embed_address h (exchange a)]

def prefixProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (P P' Q G S : ℕ) (h : P≤P') (source buffer limit : ℕ)
    (child : Program q (Volume P' Q G S)
      (buffer+count q (Volume P' Q G S))
      (buffer+count q (Volume P' Q G S)+count q (Volume P' Q G S)) limit (swap P' Q G S))
    (hs : source+count q (Volume P Q G S)≤buffer)
    (hw : buffer+count q (Volume P' Q G S)+count q (Volume P' Q G S)≤limit)
    (hl : limit≤q.N^q.exponent) : Program q (Volume P Q G S) source buffer limit (swap P Q G S) :=
  wrap q reader (PhysicalPrefixPadding.volume_mono h)
    (Fin.castLE (PhysicalPrefixPadding.volume_mono h)) (fun _ _ hab => hab)
    (swap P Q G S) (swap P' Q G S) (prefix_swap_commutes P P' Q G S h)
    source buffer limit child hs hw hl

theorem binary_volume_mono (P Q Q' G S : ℕ) (h : Q≤Q') :
    Volume P Q G S≤Volume P Q' G S :=
  Nat.mul_le_mul (Nat.mul_le_mul_left P (Nat.mul_le_mul_right G h))
    (Nat.mul_le_mul_right S h)

theorem binary_swap_commutes (P Q Q' G S : ℕ) (h : Q≤Q')
    (y : Fin (Volume P Q G S)) :
    swap P Q' G S (BinaryPadding.physicalEmbed h y)=
      BinaryPadding.physicalEmbed h (swap P Q G S y) := by
  obtain ⟨a,rfl⟩ := (lowLayout (P:=P) (Q:=Q) (G:=G) (S:=S)).surjective y
  simp only [BinaryPadding.physicalEmbed,Equiv.symm_apply_apply,
    CommonChunkLayout.swap_encoded,BinaryPadding.embed_exchange]

def binaryProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (P Q Q' G S : ℕ) (h : Q≤Q') (source buffer limit : ℕ)
    (child : Program q (Volume P Q' G S)
      (buffer+count q (Volume P Q' G S))
      (buffer+count q (Volume P Q' G S)+count q (Volume P Q' G S)) limit (swap P Q' G S))
    (hs : source+count q (Volume P Q G S)≤buffer)
    (hw : buffer+count q (Volume P Q' G S)+count q (Volume P Q' G S)≤limit)
    (hl : limit≤q.N^q.exponent) : Program q (Volume P Q G S) source buffer limit (swap P Q G S) :=
  wrap q reader (binary_volume_mono P Q Q' G S h)
    (BinaryPadding.physicalEmbed h) (BinaryPadding.physicalEmbed_strictMono h)
    (swap P Q G S) (swap P Q' G S) (binary_swap_commutes P Q Q' G S h)
    source buffer limit child hs hw hl

end
end CodedSorting.CommonPaddedPermutation
end PaddedPermutation

section PaddedChunks
/-! Prefix padding surrounds the actual common-machine chunk program.  Both
padding scans and their scratch files are included in the program and charge;
no successful child execution or zero initial scratch contents are assumed. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonPaddedChunks
open CommonSortingNormalization CommonPermutationPairs CommonFinitePermutation
open CommonChunkLayout PhysicalChunkExchange CommonChunkExchange RecursiveExchange Circuit
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m

/-- Two padded files, followed by the shared chunk workspace. -/
def space (q : Configuration) (cutoff : ℕ) (cs : List CommonChunkExchange.Call) (P' G S : ℕ)
    (hG : 0<G) (hS : 0<S) (hc : Conditions q cutoff cs P') : ℕ :=
  count q (Volume P' (fieldCount cs) G (S*q.w))+
  count q (Volume P' (fieldCount cs) G (S*q.w))+
  CommonChunkExchange.space q cutoff cs P' G S hG hS hc

/-- Every actual padding instruction is charged in addition to the chunk calls. -/
def bound (q : Configuration) (cutoff : ℕ) (cs : List CommonChunkExchange.Call) (P P' G S : ℕ) : ℕ :=
  CommonChunkCost.totalBound cutoff (width q) cs
    (Volume P' (fieldCount cs) G (S*q.w))+
  12*count q (Volume P (fieldCount cs) G (S*q.w))+
  27*count q (Volume P' (fieldCount cs) G (S*q.w))

theorem bound_le_scan (q : Configuration) (cutoff : ℕ) (cs : List CommonChunkExchange.Call)
    (P P' G S : ℕ) :
    bound q cutoff cs P P' G S≤
      CommonChunkCost.totalBound cutoff (width q) cs
        (Volume P' (fieldCount cs) G (S*q.w))+
      12*(Volume P (fieldCount cs) G (S*q.w)/width q+1)+
      27*(Volume P' (fieldCount cs) G (S*q.w)/width q+1) := by
  have hs := CommonResidentBase.count_le_floor q (Volume P (fieldCount cs) G (S*q.w))
  have hl := CommonResidentBase.count_le_floor q (Volume P' (fieldCount cs) G (S*q.w))
  unfold bound
  change _≤_+12*(_/(q.block*q.w)+1)+27*(_/(q.block*q.w)+1)
  omega

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List CommonChunkExchange.Call) (P P' G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S) (hp : P≤P') (hc : Conditions q cutoff cs P')
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P' G S hG hS hc≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (fieldCount cs) G (S*q.w)) source buffer limit
      (swap P (fieldCount cs) G (S*q.w)) := by
  let C := count q (Volume P' (fieldCount cs) G (S*q.w))
  have hchild : buffer+C+C+
      CommonChunkExchange.space q cutoff cs P' G S hG hS hc≤limit := by
    simpa only [space,C,Nat.add_assoc] using hw
  let child := CommonChunkExchange.program q reader cutoff cs P' G S
    (buffer+C) (buffer+C+C) limit hG hS hc (le_refl _) hchild hl
  exact CommonPaddedPermutation.prefixProgram q reader P P' (fieldCount cs)
    G (S*q.w) hp source buffer limit child hs (by omega) hl

@[simp] theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List CommonChunkExchange.Call) (P P' G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S) (hp : P≤P') (hc : Conditions q cutoff cs P')
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P' G S hG hS hc≤limit)
    (hl : limit≤q.N^q.exponent) :
    (program q reader cutoff cs P P' G S source buffer limit hG hS hp hc hs hw hl).charge=
      bound q cutoff cs P P' G S := by
  simp only [program,CommonPaddedPermutation.prefixProgram,
    CommonPaddedPermutation.wrap,CommonChunkExchange.program_charge,bound]

end
end CodedSorting.CommonPaddedChunks
end PaddedChunks
