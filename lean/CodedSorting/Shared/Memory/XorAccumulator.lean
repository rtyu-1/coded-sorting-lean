import CodedSorting.Shared.Programs.Static.Xor
import CodedSorting.Interchange.Framework.Memory.Reflection

/-! A finite local linear combination executed through actual disk scans.
The generated code contains only public source addresses. All payloads are
read into the existing reader/transfer banks; the scratch is first zeroed
by a real self-XOR and each source is then accumulated in place. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonXorAccumulator
open CommonSortingNormalization CommonStaticSchedule Circuit
open CommonLeafProgram (Disk Machine)
open CommonPermutationPairs (count readBit)
noncomputable section

def foldCode (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) : List (Instruction q) :=
  sources.flatMap (fun source => CommonStaticXor.code q reader V scratch source scratch)

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) : List (Instruction q) :=
  CommonStaticXor.code q reader V scratch scratch scratch ++ foldCode q reader V scratch sources

def Separate (q : Configuration) (V scratch source : ℕ) : Prop :=
  source+count q V≤scratch ∨ scratch+count q V≤source

theorem preserved_bit (q : Configuration) (V scratch source : ℕ)
    (before after : Disk q) (hs : source+count q V≤q.N^q.exponent)
    (hsep : Separate q V scratch source)
    (hout : ∀ a : Fin (q.N^q.exponent),a.val<scratch ∨ scratch+count q V≤a.val → after a=before a)
    (i : Fin V) : readBit q after source i.val=readBit q before source i.val := by
  have hi := CommonPermutationPairs.bit_block_lt q i
  have ha : source+i.val/CommonPermutationPairs.width q<q.N^q.exponent := by omega
  unfold readBit
  rw [hout]
  rw [CommonColumnSplit.address_val q source _ ha]
  rcases hsep with h|h
  · left; omega
  · right; exact h.trans (Nat.le_add_right _ _)

theorem fold_length (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) :
    (foldCode q reader V scratch sources).length=3*sources.length*count q V := by
  induction sources with
  | nil => simp [foldCode]
  | cons source sources ih =>
    rw [foldCode,List.flatMap_cons,List.length_append,CommonStaticXor.code_length]
    change 3*count q V+(foldCode q reader V scratch sources).length=_
    rw [ih,List.length_cons]; ring

theorem fold_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) :
    cost q (foldCode q reader V scratch sources)=3*sources.length*count q V := by
  induction sources with
  | nil => simp [foldCode,cost]
  | cons source sources ih =>
    rw [foldCode,List.flatMap_cons,CommonPermutationPairs.cost_append,CommonStaticXor.code_cost]
    change 3*count q V+cost q (foldCode q reader V scratch sources)=_
    rw [ih,List.length_cons]; ring

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) :
    (code q reader V scratch sources).length=3*(sources.length+1)*count q V := by
  rw [code,List.length_append,CommonStaticXor.code_length,fold_length]
  change 3*count q V+3*sources.length*count q V=_
  ring

theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) :
    cost q (code q reader V scratch sources)=3*(sources.length+1)*count q V := by
  rw [code,CommonPermutationPairs.cost_append,CommonStaticXor.code_cost,fold_cost]
  change 3*count q V+3*sources.length*count q V=_
  ring

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) :
    ∀ i∈code q reader V scratch sources,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact CommonStaticXor.code_safe q reader V scratch scratch scratch i hi
  · obtain ⟨source,_,hi⟩ := List.mem_flatMap.mp hi
    exact CommonStaticXor.code_safe q reader V scratch source scratch i hi

theorem fold_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) (s : Machine q)
    (ht : scratch+count q V≤q.N^q.exponent)
    (hs : ∀ source∈sources,source+count q V≤q.N^q.exponent)
    (hsep : ∀ source∈sources,Separate q V scratch source) :
    let result := executeRaw q (foldCode q reader V scratch sources) s
    (∀ i : Fin V,readBit q result.1.disk scratch i.val=
      readBit q s.disk scratch i.val+(sources.map (fun source => readBit q s.disk source i.val)).sum) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<scratch ∨ scratch+count q V≤a.val → result.1.disk a=s.disk a) := by
  induction sources generalizing s with
  | nil => simp [foldCode,executeRaw]
  | cons source sources ih =>
    let mid := (executeRaw q (CommonStaticXor.code q reader V scratch source scratch) s).1
    have hsource := hs source (List.mem_cons_self ..)
    have hseparate := hsep source (List.mem_cons_self ..)
    have hmid : ∀ a : Fin (q.N^q.exponent),a.val<scratch ∨ scratch+count q V≤a.val → mid.disk a=s.disk a :=
      CommonStaticXor.raw_outside q reader V scratch source scratch s ht
    obtain ⟨hbits,houtside⟩ := ih mid (fun b hb => hs b (List.mem_cons_of_mem _ hb))
      (fun b hb => hsep b (List.mem_cons_of_mem _ hb))
    simp only [foldCode,List.flatMap_cons,CommonPermutationPairs.raw_append]
    change (∀ i : Fin V,readBit q (executeRaw q (foldCode q reader V scratch sources) mid).1.disk scratch i.val=_)
      ∧ (∀ a : Fin (q.N^q.exponent),_ → (executeRaw q (foldCode q reader V scratch sources) mid).1.disk a=_)
    refine ⟨?_,fun a ha => (houtside a ha).trans (hmid a ha)⟩
    intro i
    rw [hbits]
    have hm : readBit q mid.disk scratch i.val=readBit q s.disk scratch i.val+readBit q s.disk source i.val :=
      CommonStaticXor.raw_correct q reader V scratch source scratch s ht hsource ht
        (Or.inl rfl) (Or.inr hseparate) i
    rw [hm]
    have hlist : sources.map (fun b => readBit q mid.disk b i.val)=
        sources.map (fun b => readBit q s.disk b i.val) := by
      apply List.map_congr_left
      intro b hb
      exact preserved_bit q V scratch b s.disk mid.disk (hs b (List.mem_cons_of_mem _ hb))
        (hsep b (List.mem_cons_of_mem _ hb)) hmid i
    rw [hlist,List.map_cons,List.sum_cons,add_assoc]

theorem raw_cost (q : Configuration) (program : List (Instruction q)) (s : Machine q) :
    (executeRaw q program s).2=cost q program := by
  induction program generalizing s with
  | nil => rfl
  | cons i is ih => simp only [executeRaw,cost,ih]

/-- Exact original-source sum, disk frame, and charged I/O of the same
actual instruction execution. Source files may repeat or overlap each
other, but are disjoint from the scratch that is overwritten. -/
theorem raw_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (V scratch : ℕ) (sources : List ℕ) (s : Machine q)
    (ht : scratch+count q V≤q.N^q.exponent)
    (hs : ∀ source∈sources,source+count q V≤q.N^q.exponent)
    (hsep : ∀ source∈sources,Separate q V scratch source) :
    let result := executeRaw q (code q reader V scratch sources) s
    (∀ i : Fin V,readBit q result.1.disk scratch i.val=
      (sources.map (fun source => readBit q s.disk source i.val)).sum) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<scratch ∨ scratch+count q V≤a.val → result.1.disk a=s.disk a) ∧
    result.2=3*(sources.length+1)*count q V := by
  let mid := (executeRaw q (CommonStaticXor.code q reader V scratch scratch scratch) s).1
  have hmid : ∀ a : Fin (q.N^q.exponent),a.val<scratch ∨ scratch+count q V≤a.val → mid.disk a=s.disk a :=
    CommonStaticXor.raw_outside q reader V scratch scratch scratch s ht
  obtain ⟨hbits,houtside⟩ := fold_raw q reader V scratch sources mid ht hs hsep
  refine ⟨?_,?_,(raw_cost q _ s).trans (code_cost q reader V scratch sources)⟩
  · intro i
    change readBit q (executeRaw q (code q reader V scratch sources) s).1.disk scratch i.val=_
    rw [code,CommonPermutationPairs.raw_append]
    change readBit q (executeRaw q (foldCode q reader V scratch sources) mid).1.disk scratch i.val=_
    rw [hbits]
    have hz : readBit q mid.disk scratch i.val=0 := by
      have h := CommonStaticXor.raw_correct q reader V scratch scratch scratch s ht ht ht
        (Or.inl rfl) (Or.inl rfl) i
      exact h.trans (CharTwo.add_self_eq_zero _)
    rw [hz,zero_add]
    congr 1
    apply List.map_congr_left
    intro source hsource
    exact preserved_bit q V scratch source s.disk mid.disk (hs source hsource)
      (hsep source hsource) hmid i
  · intro a ha
    change (executeRaw q (code q reader V scratch sources) s).1.disk a=_
    rw [code,CommonPermutationPairs.raw_append]
    exact (houtside a ha).trans (hmid a ha)

end
end CodedSorting.CommonXorAccumulator
