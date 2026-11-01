import CodedSorting.Shared.Memory.BlockPair
import CodedSorting.Interchange.Framework.Columns.ColumnOperations
import Mathlib.Data.List.FinRange
import CodedSorting.Shared.Programs.MonotoneBlockPairs

section PermutationPairs
/-! A complete finite-disk permutation from a public covering list of
source/target block pairs. Every selected bit is obtained by a real read;
the original source and the target occupy disjoint allocated regions.
The next module generates the covering list and proves its scan bound. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonPermutationPairs
open CommonSortingNormalization CommonStaticSchedule BitWordPacking Circuit
open CommonLeafProgram (Store RAM Disk Machine machine)
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Entry (K : ℕ) := Fin K × (ℕ × ℕ)
abbrev address := CommonColumnSplit.address

def width (q : Configuration) := q.block*q.w
theorem width_pos (q : Configuration) : 0<width q :=
  Nat.mul_pos (CommonLeafProgram.block_positive q) (by have:=q.word_width; omega)

def count (q : Configuration) (V : ℕ) := PhysicalStreamCursor.blockCount (width q) V

theorem bit_block_lt (q : Configuration) {V : ℕ} (y : Fin V) : y.val/width q<count q V := by
  apply (PhysicalStreamCursor.cursor_live_iff (width q) V _ (width_pos q)).2
  exact (Nat.div_mul_le_self _ _).trans_lt y.isLt

def readBit (q : Configuration) (disk : Disk q) (base i : ℕ) : Bit :=
  blockBits q.block q.w (disk (address q base (i/width q)))
    ⟨i%width q,Nat.mod_lt _ (width_pos q)⟩

def select (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (p : Entry K) : CommonBlockPair.Selection q := fun j =>
  if h : p.2.2*width q+j.val<V then
    let x := e.symm ⟨p.2.2*width q+j.val,h⟩
    if key x=p.1 ∧ x.val/width q=p.2.1 then
      some ⟨x.val%width q,Nat.mod_lt _ (width_pos q)⟩
    else none
  else none

def Hit (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (p : Entry K) (y : Fin V) : Prop :=
  key (e.symm y)=p.1 ∧ (e.symm y).val/width q=p.2.1 ∧ y.val/width q=p.2.2

def Fits (q : Configuration) (V : ℕ) {K : ℕ} (p : Entry K) : Prop :=
  p.2.1<count q V ∧ p.2.2<count q V

def stepDisk (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (source target : ℕ) (p : Entry K) (disk : Disk q) : Disk q :=
  Function.update disk (address q target p.2.2)
    (CommonBlockPair.blend q (select q e key p)
      (disk (address q source p.2.1)) (disk (address q target p.2.2)))

def fragment (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (p : Entry K) : List (Instruction q) :=
  CommonBlockPair.code q reader (address q source p.2.1) (address q target p.2.2)
    (select q e key p)

def code (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (ps : List (Entry K)) : List (Instruction q) :=
  ps.flatMap (fragment q reader e key source target)

def applyPairs (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (source target : ℕ) : List (Entry K)→Disk q→Disk q
  | [],disk => disk
  | p::ps,disk => applyPairs q e key source target ps (stepDisk q e key source target p disk)

theorem raw_append (q : Configuration) (xs ys : List (Instruction q)) (s : Machine q) :
    (executeRaw q (xs++ys) s).1=(executeRaw q ys (executeRaw q xs s).1).1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => simp only [List.cons_append,executeRaw,ih]

theorem cost_append (q : Configuration) (xs ys : List (Instruction q)) :
    cost q (xs++ys)=cost q xs+cost q ys := by
  induction xs with
  | nil => simp [cost]
  | cons i xs ih => simp only [List.cons_append,cost,ih,Nat.add_assoc]

theorem code_length (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (ps : List (Entry K)) : (code q reader e key source target ps).length=3*ps.length := by
  induction ps with
  | nil => simp [code]
  | cons p ps ih =>
    change ((fragment q reader e key source target p)++code q reader e key source target ps).length=_
    rw [List.length_append,ih]
    simp only [fragment,CommonBlockPair.length_code,List.length_cons]
    omega

theorem code_cost (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (ps : List (Entry K)) : cost q (code q reader e key source target ps)=3*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change cost q (fragment q reader e key source target p++code q reader e key source target ps)=_
    rw [cost_append,ih]
    simp only [fragment,CommonBlockPair.cost_code,List.length_cons]
    omega

theorem code_safe (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (ps : List (Entry K)) : ∀ i∈code q reader e key source target ps,RespectsPC q i := by
  intro i hi
  obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hi
  exact CommonBlockPair.safe q reader _ _ _ i hp

theorem raw_disk (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (ps : List (Entry K)) (s : Machine q) :
    (executeRaw q (code q reader e key source target ps) s).1.disk=
      applyPairs q e key source target ps s.disk := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    change (executeRaw q (fragment q reader e key source target p++code q reader e key source target ps) s).1.disk=_
    rw [raw_append,ih]
    rw [fragment,CommonBlockPair.raw_disk]
    rfl

theorem select_at (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (p : Entry K) (y : Fin V) (ht : y.val/width q=p.2.2) :
    select q e key p ⟨y.val%width q,Nat.mod_lt _ (width_pos q)⟩=
      if key (e.symm y)=p.1 ∧ (e.symm y).val/width q=p.2.1 then
        some ⟨(e.symm y).val%width q,Nat.mod_lt _ (width_pos q)⟩ else none := by
  have he : p.2.2*width q+y.val%width q=y.val := by
    rw [←ht]; simpa only [Nat.mul_comm] using Nat.div_add_mod y.val (width q)
  simp only [select,he,y.isLt,↓reduceDIte,Fin.eta]

theorem step_target (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (source target : ℕ) (p : Entry K) (disk : Disk q)
    (hf : Fits q V p) (htarget : target+count q V≤q.N^q.exponent) (y : Fin V) :
    readBit q (stepDisk q e key source target p disk) target y.val=
      if Hit q e key p y then readBit q disk source (e.symm y).val
      else readBit q disk target y.val := by
  by_cases ht : y.val/width q=p.2.2
  · have hs := select_at q e key p y ht
    by_cases h : key (e.symm y)=p.1 ∧ (e.symm y).val/width q=p.2.1
    · have hh : Hit q e key p y := ⟨h.1,h.2,ht⟩
      rw [if_pos hh]
      unfold readBit stepDisk
      rw [ht,Function.update_self,CommonBlockPair.blend_bits,hs,if_pos h]
      simp only [h.2]
    · have hh : ¬Hit q e key p y := fun hh => h ⟨hh.1,hh.2.1⟩
      rw [if_neg hh]
      unfold readBit stepDisk
      rw [ht,Function.update_self,CommonBlockPair.blend_bits,hs,if_neg h]
  · have hy := bit_block_lt q y
    have ha : address q target (y.val/width q)≠address q target p.2.2 := by
      intro he
      have hv := congrArg Fin.val he
      rw [CommonColumnSplit.address_val q target _ (by omega),
        CommonColumnSplit.address_val q target _ (by have:=hf.2; omega)] at hv
      omega
    have hh : ¬Hit q e key p y := fun h => ht h.2.2
    simp only [readBit,stepDisk,Function.update_of_ne ha,if_neg hh]

theorem step_outside (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (source target : ℕ) (p : Entry K) (disk : Disk q)
    (hf : Fits q V p) (htarget : target+count q V≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<target ∨ target+count q V≤a.val) :
    stepDisk q e key source target p disk a=disk a := by
  apply Function.update_of_ne
  intro he
  have hv := congrArg Fin.val he
  rw [CommonColumnSplit.address_val q target _ (by have:=hf.2; omega)] at hv
  have:=hf.2
  rcases ha with ha|ha <;> omega

theorem step_source (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (source target : ℕ) (p : Entry K) (disk : Disk q)
    (hf : Fits q V p) (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source) (x : Fin V) :
    readBit q (stepDisk q e key source target p disk) source x.val=
      readBit q disk source x.val := by
  have hx := bit_block_lt q x
  have ha : (address q source (x.val/width q)).val<target ∨
      target+count q V≤(address q source (x.val/width q)).val := by
    simp only [CommonColumnSplit.address_val q source (x.val/width q) (by omega)]
    rcases hsep with hs|hs
    · exact Or.inl (by omega)
    · exact Or.inr (hs.trans (Nat.le_add_right _ _))
  unfold readBit
  rw [step_outside q e key source target p disk hf htarget _ ha]

theorem pairs_target (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (source target : ℕ) (ps : List (Entry K)) (disk : Disk q)
    (hf : ∀ p∈ps,Fits q V p) (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source) (y : Fin V) :
    readBit q (applyPairs q e key source target ps disk) target y.val=
      if ∃ p∈ps,Hit q e key p y then readBit q disk source (e.symm y).val
      else readBit q disk target y.val := by
  induction ps generalizing disk with
  | nil => simp [applyPairs]
  | cons p ps ih =>
    have hp := hf p (by simp)
    have hps : ∀ p∈ps,Fits q V p := fun p h => hf p (by simp [h])
    rw [applyPairs,ih _ hps,step_source q e key source target p disk hp hsource htarget hsep,
      step_target q e key source target p disk hp htarget]
    by_cases ht : ∃ a∈ps,Hit q e key a y
    · have hall : ∃ a∈p::ps,Hit q e key a y := by
        obtain ⟨a,ha,h⟩:=ht; exact ⟨a,by simp [ha],h⟩
      simp only [if_pos ht,if_pos hall]
    · by_cases hh : Hit q e key p y
      · have hall : ∃ a∈p::ps,Hit q e key a y := ⟨p,by simp,hh⟩
        simp only [if_neg ht,if_pos hh,if_pos hall]
      · have hall : ¬∃ a∈p::ps,Hit q e key a y := by
          rintro ⟨a,ha,h⟩
          rcases List.mem_cons.mp ha with rfl|ha
          · exact hh h
          · exact ht ⟨a,ha,h⟩
        simp only [if_neg ht,if_neg hh,if_neg hall]

theorem pairs_outside (q : Configuration) {V K : ℕ} (e : Equiv.Perm (Fin V))
    (key : Fin V→Fin K) (source target : ℕ) (ps : List (Entry K)) (disk : Disk q)
    (hf : ∀ p∈ps,Fits q V p) (htarget : target+count q V≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<target ∨ target+count q V≤a.val) :
    applyPairs q e key source target ps disk a=disk a := by
  induction ps generalizing disk with
  | nil => rfl
  | cons p ps ih =>
    rw [applyPairs,ih _ (fun p h => hf p (by simp [h]))]
    exact step_outside q e key source target p disk (hf p (by simp)) htarget a ha

end
end CodedSorting.CommonPermutationPairs
end PermutationPairs

section ReflectionPairs
/-! Four public source-block candidates per destination block implement
segment reversal through the shared block-pair machine. Clamping unused
candidates keeps all real reads within the source file. A candidate used by
any valid bit is unchanged by this clamp. -/
set_option autoImplicit false
namespace CodedSorting.CommonReflectionPairs
open PhysicalStreamCursor BlockReflection

def key (B T L : ℕ) (x : Fin (T*L)) : Fin 4 :=
  let y := segmentReverseEquiv T L x
  sourceSlot B L (y.val/B) y.val

def entry (B L blocks b : ℕ) (slot : Fin 4) : Fin 4×(ℕ×ℕ) :=
  (slot,(min (sourceBlock B L b slot) (blocks-1),b))

def schedule (B T L : ℕ) : List (Fin 4×(ℕ×ℕ)) :=
  (List.range (blockCount B (T*L))).flatMap
    (fun b => (List.finRange 4).map (entry B L (blockCount B (T*L)) b))

theorem length_schedule (B T L : ℕ) :
    (schedule B T L).length=4*blockCount B (T*L) := by
  have h (bs : List ℕ) :
      (bs.flatMap (fun b => (List.finRange 4).map (entry B L (blockCount B (T*L)) b))).length=
        4*bs.length := by
    induction bs with
    | nil => simp
    | cons b bs ih => simp only [List.flatMap_cons,List.length_append,List.length_map,
        List.length_finRange,ih,List.length_cons]; omega
  simpa only [schedule,List.length_range] using h (List.range (blockCount B (T*L)))

theorem mem_schedule (B T L : ℕ) (p : Fin 4×(ℕ×ℕ)) :
    p∈schedule B T L ↔ ∃ b, b<blockCount B (T*L) ∧
      ∃ slot : Fin 4, entry B L (blockCount B (T*L)) b slot=p := by
  simp [schedule]

theorem bounds (B T L : ℕ) (p : Fin 4×(ℕ×ℕ)) (hp : p∈schedule B T L) :
    p.2.1<blockCount B (T*L) ∧ p.2.2<blockCount B (T*L) := by
  obtain ⟨b,hb,slot,rfl⟩ := (mem_schedule B T L p).1 hp
  dsimp only [entry]
  have hm := Nat.min_le_right (sourceBlock B L b slot) (blockCount B (T*L)-1)
  constructor <;> omega

theorem reverse_again (T L : ℕ) (x : Fin (T*L)) :
    reverseAddress L (segmentReverseEquiv T L x).val=x.val := by
  rw [←segmentReverse_val T L,segmentReverse_involutive]

/-- A valid source bit's job appears among the four candidates for its
unique destination block. The clamp never modifies this chosen job. -/
theorem covers (B T L : ℕ) (hB : 0<B) (hL : 0<L) (x : Fin (T*L)) :
    (key B T L x,(x.val/B,(segmentReverseEquiv T L x).val/B))∈schedule B T L := by
  let y := segmentReverseEquiv T L x
  have hy : y.val/B<blockCount B (T*L) :=
    (cursor_live_iff B (T*L) (y.val/B) hB).2 ((Nat.div_mul_le_self _ _).trans_lt y.isLt)
  have hx : x.val/B<blockCount B (T*L) :=
    (cursor_live_iff B (T*L) (x.val/B) hB).2 ((Nat.div_mul_le_self _ _).trans_lt x.isLt)
  have hlow : y.val/B*B≤y.val := Nat.div_mul_le_self _ _
  have hhigh : y.val<(y.val/B+1)*B := by
    have he := Nat.div_add_mod y.val B
    have hm := Nat.mod_lt y.val hB
    nlinarith
  have hs := sourceSlot_correct B L (y.val/B) y.val hB hL hlow hhigh
  have hr : reverseAddress L y.val=x.val := reverse_again T L x
  rw [hr] at hs
  apply (mem_schedule B T L _).2
  refine ⟨y.val/B,hy,key B T L x,?_⟩
  have hk : key B T L x=sourceSlot B L (y.val/B) y.val := rfl
  simp only [entry,hk,hs,Nat.min_eq_left (show x.val/B≤blockCount B (T*L)-1 by omega)]
  rfl

/-- The schedule is public, bounded, and covers all valid bits. -/
theorem complete_schedule (B T L : ℕ) (hB : 0<B) (hL : 0<L) :
    (∀ p∈schedule B T L, p.2.1<blockCount B (T*L) ∧ p.2.2<blockCount B (T*L)) ∧
    (∀ x : Fin (T*L), (key B T L x,(x.val/B,(segmentReverseEquiv T L x).val/B))∈schedule B T L) ∧
    (schedule B T L).length=4*blockCount B (T*L) :=
  ⟨fun p hp => bounds B T L p hp,covers B T L hB hL,length_schedule B T L⟩
end CodedSorting.CommonReflectionPairs
end ReflectionPairs

section PermutationScan
/-! Complete public finite-RAM programs for coloured monotone permutations.
The block-pair count is derived from monotonicity, not supplied as an
execution/cost oracle. Each actual fragment has three charged transfers. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonPermutationScan
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Store Disk Machine machine)
noncomputable section

/-- Any concrete public cover can use the same real block-pair program.
Coverage is a finite combinatorial property of the dimensions/permutation. -/
theorem raw_cover (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (ps : List (Entry K))
    (hf : ∀ p∈ps,Fits q V p)
    (hcover : ∀ x : Fin V,(key x,(x.val/width q,(e x).val/width q))∈ps)
    (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source)
    (s : Machine q) :
    (∀ y : Fin V,readBit q (executeRaw q (code q reader e key source target ps) s).1.disk
      target y.val=readBit q s.disk source (e.symm y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q V≤a.val →
      (executeRaw q (code q reader e key source target ps) s).1.disk a=s.disk a) := by
  rw [raw_disk]
  constructor
  · intro y
    rw [pairs_target q e key source target ps s.disk hf hsource htarget hsep y]
    apply if_pos
    refine ⟨(key (e.symm y),((e.symm y).val/width q,y.val/width q)),?_,rfl,rfl,rfl⟩
    simpa only [Equiv.apply_symm_apply] using hcover (e.symm y)
  · exact pairs_outside q e key source target ps s.disk hf htarget

theorem complete_cover (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (ps : List (Entry K))
    (hf : ∀ p∈ps,Fits q V p)
    (hcover : ∀ x : Fin V,(key x,(x.val/width q,(e x).val/width q))∈ps)
    (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source)
    (hsize : 3*ps.length≤q.N^q.exponent)
    (s : Machine q) (hpc : pc q s.ram=0) :
    let program := code q reader e key source target ps
    let result := ControlledNormalization.runLogical (policy q program) program.length s
    (∀ y : Fin V,readBit q result.1.disk target y.val=readBit q s.disk source (e.symm y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q V≤a.val → result.1.disk a=s.disk a) ∧
    policy q program result.1.ram=none ∧ result.2=3*ps.length ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have hs : (code q reader e key source target ps).length≤q.N^q.exponent := by
    rw [code_length]; exact hsize
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (code q reader e key source target ps)
    hs (code_safe q reader e key source target ps) s hpc
  obtain ⟨hb,ho⟩ := raw_cover q reader e key source target ps hf hcover hsource htarget hsep s
  exact ⟨by rw [hd]; exact hb,by rw [hd]; exact ho,hh,hc.trans (code_cost ..),hm⟩

def program (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ) : List (Instruction q) :=
  code q reader e key source target (MonotoneBlockPairs.schedule e key (width q))

theorem program_safe (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ) :
    ∀ i∈program q reader e key source target,RespectsPC q i := code_safe q reader e key source target _

theorem program_length (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (hinc : ∀ x y,x<y→key x=key y→e x<e y) :
    (program q reader e key source target).length≤6*K*count q V := by
  unfold program
  rw [code_length]
  have h := MonotoneBlockPairs.schedule_length_le e key hinc (width q) (width_pos q)
  change (MonotoneBlockPairs.schedule e key (width q)).length≤2*K*count q V at h
  nlinarith

theorem program_cost (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (hinc : ∀ x y,x<y→key x=key y→e x<e y) :
    cost q (program q reader e key source target)≤6*K*count q V := by
  change cost q (code q reader e key source target _)≤_
  rw [code_cost,←code_length q reader e key source target]
  exact program_length q reader e key source target hinc

/-- The same finite machine executes the entire permutation, not just one
block. No hypothesis asserts successful execution or a bound on its cost. -/
theorem raw_correct (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K) (source target : ℕ)
    (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source)
    (s : Machine q) :
    (∀ y : Fin V,readBit q (executeRaw q (program q reader e key source target) s).1.disk
      target y.val=readBit q s.disk source (e.symm y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q V≤a.val →
      (executeRaw q (program q reader e key source target) s).1.disk a=s.disk a) :=
  raw_cover q reader e key source target _
    (MonotoneBlockPairs.schedule_bounds e key (width q) (width_pos q))
    (MonotoneBlockPairs.schedule_covers e key (width q)) hsource htarget hsep s

theorem complete (q : Configuration) {V K : ℕ} (reader : Fin q.inventory.readers)
    (e : Equiv.Perm (Fin V)) (key : Fin V→Fin K)
    (hinc : ∀ x y,x<y→key x=key y→e x<e y) (source target : ℕ)
    (hsource : source+count q V≤q.N^q.exponent)
    (htarget : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source)
    (hsize : 6*K*count q V≤q.N^q.exponent)
    (s : Machine q) (hpc : pc q s.ram=0) :
    let code := program q reader e key source target
    let result := ControlledNormalization.runLogical (policy q code) code.length s
    (∀ y : Fin V,readBit q result.1.disk target y.val=readBit q s.disk source (e.symm y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q V≤a.val → result.1.disk a=s.disk a) ∧
    policy q code result.1.ram=none ∧ result.2≤6*K*count q V ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (program q reader e key source target)
    ((program_length q reader e key source target hinc).trans hsize)
    (program_safe q reader e key source target) s hpc
  obtain ⟨hb,ho⟩ := raw_correct q reader e key source target hsource htarget hsep s
  exact ⟨by rw [hd]; exact hb,by rw [hd]; exact ho,hh,
    hc.le.trans (program_cost q reader e key source target hinc),hm⟩

end
end CodedSorting.CommonPermutationScan
end PermutationScan

section Reflection
/-! Segment reversal uses four certified public block-pair jobs per
output block. The same three-transfer primitive as the monotone scans
therefore gives a complete bit-exact reflection with twelve I/Os per
output block and no additional resident buffers. -/
set_option autoImplicit false
namespace CodedSorting.CommonReflection
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine Disk)
open BlockReflection
noncomputable section

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (T L source target : ℕ) : List (Instruction q) :=
  CommonPermutationPairs.code q reader (segmentReverseEquiv T L)
    (CommonReflectionPairs.key (width q) T L) source target
    (CommonReflectionPairs.schedule (width q) T L)

@[simp] theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (T L source target : ℕ) :
    (code q reader T L source target).length=12*count q (T*L) := by
  rw [code,CommonPermutationPairs.code_length,CommonReflectionPairs.length_schedule]
  simp only [count]
  omega

@[simp] theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (T L source target : ℕ) :
    cost q (code q reader T L source target)=12*count q (T*L) := by
  rw [code,CommonPermutationPairs.code_cost,CommonReflectionPairs.length_schedule]
  simp only [count]
  omega

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (T L source target : ℕ) :
    ∀ i∈code q reader T L source target,RespectsPC q i :=
  CommonPermutationPairs.code_safe q reader _ _ _ _ _

theorem reverse_symm (T L : ℕ) : (segmentReverseEquiv T L).symm=segmentReverseEquiv T L := by
  apply Equiv.ext
  intro x
  apply (segmentReverseEquiv T L).injective
  rw [Equiv.apply_symm_apply,segmentReverse_involutive]

theorem schedule_fits (q : Configuration) (T L : ℕ) :
    ∀ p∈CommonReflectionPairs.schedule (width q) T L,Fits q (T*L) p :=
  fun p hp => CommonReflectionPairs.bounds (width q) T L p hp

theorem schedule_hits (q : Configuration) (T L : ℕ) (hL : 0<L) (y : Fin (T*L)) :
    ∃ p∈CommonReflectionPairs.schedule (width q) T L,
      Hit q (segmentReverseEquiv T L) (CommonReflectionPairs.key (width q) T L) p y := by
  let x := (segmentReverseEquiv T L).symm y
  refine ⟨(CommonReflectionPairs.key (width q) T L x,(x.val/width q,y.val/width q)),?_,?_,?_,?_⟩
  · simpa only [x,Equiv.apply_symm_apply] using
      CommonReflectionPairs.covers (width q) T L (width_pos q) hL x
  all_goals rfl

/-- The direct program executes actual disk operations, with a proof of
every valid output bit and of every untouched disk block. -/
theorem raw_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (T L source target : ℕ) (hL : 0<L) (s : Machine q)
    (hsource : source+count q (T*L)≤q.N^q.exponent)
    (htarget : target+count q (T*L)≤q.N^q.exponent)
    (hsep : source+count q (T*L)≤target ∨ target+count q (T*L)≤source) :
    (∀ y : Fin (T*L),readBit q (executeRaw q (code q reader T L source target) s).1.disk target y.val=
      readBit q s.disk source (segmentReverseEquiv T L y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q (T*L)≤a.val →
      (executeRaw q (code q reader T L source target) s).1.disk a=s.disk a) := by
  rw [code,CommonPermutationPairs.raw_disk]
  constructor
  · intro y
    rw [pairs_target q _ _ _ _ _ _ (schedule_fits q T L) hsource htarget hsep y,
      if_pos (schedule_hits q T L hL y),reverse_symm]
  · intro a ha
    exact pairs_outside q _ _ _ _ _ _ (schedule_fits q T L) htarget a ha

/-- Complete execution of the actual fixed finite-RAM reflection policy.
All bit semantics, halt, exact I/O and the memory bound refer to this run. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (T L source target : ℕ) (hL : 0<L) (s : Machine q)
    (hsource : source+count q (T*L)≤q.N^q.exponent)
    (htarget : target+count q (T*L)≤q.N^q.exponent)
    (hsep : source+count q (T*L)≤target ∨ target+count q (T*L)≤source)
    (hsize : 12*count q (T*L)≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let program := code q reader T L source target
    let result := ControlledNormalization.runLogical (policy q program) program.length s
    (∀ y : Fin (T*L),readBit q result.1.disk target y.val=
      readBit q s.disk source (segmentReverseEquiv T L y).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q (T*L)≤a.val → result.1.disk a=s.disk a) ∧
    policy q program result.1.ram=none ∧ result.2=12*count q (T*L) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have hs : (code q reader T L source target).length≤q.N^q.exponent := by
    rw [code_length]; exact hsize
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (code q reader T L source target) hs
    (code_safe q reader T L source target) s hpc
  obtain ⟨hb,ho⟩ := raw_complete q reader T L source target hL s hsource htarget hsep
  exact ⟨by rw [hd]; exact hb,by rw [hd]; exact ho,hh,hc.trans (code_cost ..),hm⟩

end
end CodedSorting.CommonReflection
end Reflection
