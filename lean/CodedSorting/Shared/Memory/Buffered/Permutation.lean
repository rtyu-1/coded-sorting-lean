import CodedSorting.Shared.Memory.Buffered.DistributionCorrectness
import CodedSorting.Shared.Memory.Buffered.Schedule
import Mathlib.Data.List.FinRange

section Costs
/-! Actual generated-instruction charges for the buffered base exchange.
The cost is derived from every real read/write instruction and public
transfer events. Free local bit operations are compressed before their
program-counter capacity is bounded. -/
set_option autoImplicit false
namespace CodedSorting.CommonBufferedCosts
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonBufferedSchedule
noncomputable section
attribute [local instance] Classical.propDecidable

 theorem cost_flatMap (q : Configuration) {α : Type*}
    (xs : List α) (f : α→List (Instruction q)) :
    cost q (xs.flatMap f)=(xs.map (fun x => cost q (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,cost_append,List.map_cons,List.sum_cons,ih]

theorem cost_finRange (q : Configuration) (V : ℕ) (f : Fin V→List (Instruction q)) :
    cost q ((List.finRange V).flatMap f)=∑ i : Fin V,cost q (f i) := by
  rw [cost_flatMap,←List.ofFn_eq_map,List.sum_ofFn]

variable {V K L : ℕ}

theorem gather_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (E : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) :
    cost q (CommonBufferedGather.code q hfit reader E arena target)=
      count q V+K*count q L := by
  rw [CommonBufferedGather.code,cost_finRange]
  simp only [CommonBufferedGather.fragment_cost]
  change (∑ i : Fin V,((if starts (width q) (E i).2.val then 1 else 0)+
    (if ends (width q) V i.val then 1 else 0)))=_
  rw [Finset.sum_add_distrib,bucket_start_count E (width q) (width_pos q),
    finish_count (width q) V (width_pos q)]
  change K*count q L+count q V=count q V+K*count q L
  omega

theorem fused_gather_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (E : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) :
    cost q (CommonStaticFusion.fuse q
      (CommonBufferedGather.code q hfit reader E arena target))=
      count q V+K*count q L := by
  rw [CommonStaticFusion.cost_fuse,gather_cost]

theorem fused_gather_length (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (E : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) :
    (CommonStaticFusion.fuse q
      (CommonBufferedGather.code q hfit reader E arena target)).length≤
      count q V+K*count q L+1 := by
  have h := CommonStaticFusion.length_fuse q
    (CommonBufferedGather.code q hfit reader E arena target)
  rwa [gather_cost] at h

/-- This is the cost of the concrete three-part machine fragment: optional
source read, free resident update, and optional bucket write. -/
theorem distribution_fragment_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (E : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent)) (i : Fin V) :
    cost q (CommonBufferedDistribution.fragment q hfit reader E source target i)=
      (if starts (width q) i.val then 1 else 0)+
      (if ends (width q) L (E i).2.val then 1 else 0) := by
  simp only [CommonBufferedDistribution.fragment,cost_append,starts,ends,
    CommonBufferedDistribution.Flush]
  split_ifs <;> rfl

theorem distribution_prefix_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (E : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent)) (n : ℕ) :
    cost q (CommonBufferedDistribution.codePrefix q hfit reader E source target n)=
      ∑ j∈Finset.range n,if h : j<V then
        cost q (CommonBufferedDistribution.fragment q hfit reader E source target ⟨j,h⟩)
      else 0 := by
  induction n with
  | zero => simp only [CommonBufferedDistribution.codePrefix,cost,Finset.range_zero,
      Finset.sum_empty]
  | succ n ih =>
    rw [CommonBufferedDistribution.codePrefix,cost_append,Finset.sum_range_succ,ih]
    split_ifs <;> rfl

theorem distribution_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (E : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent)) :
    cost q (CommonBufferedDistribution.program q hfit reader E source target)=
      count q V+K*count q L := by
  rw [CommonBufferedDistribution.program,distribution_prefix_cost,
    ←Fin.sum_univ_eq_sum_range]
  simp only [Fin.isLt,↓reduceDIte,Fin.eta,distribution_fragment_cost]
  exact distribution_count E (width q) (width_pos q)

/-- The arena is fully distributed before reconstruction writes back to
source. These instructions include every intermediate bucket transfer. -/
def rawCode (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (source arena : ℕ) : List (Instruction q) :=
  CommonBufferedDistribution.program q hfit reader input source
    (fun k j => address q arena (k.val*count q L+j)) ++
  CommonBufferedGather.code q hfit reader output arena source

def code (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (source arena : ℕ) : List (Instruction q) :=
  CommonStaticFusion.fuse q (rawCode q hfit reader input output source arena)

theorem rawCode_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (source arena : ℕ) :
    cost q (rawCode q hfit reader input output source arena)=
      2*count q V+2*K*count q L := by
  rw [rawCode,cost_append,distribution_cost,gather_cost]
  ring

theorem code_cost (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (source arena : ℕ) :
    cost q (code q hfit reader input output source arena)=
      2*count q V+2*K*count q L := by
  rw [code,CommonStaticFusion.cost_fuse,rawCode_cost]

theorem code_cost_le (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (source arena : ℕ) :
    cost q (code q hfit reader input output source arena)≤4*count q V+2*K := by
  have hcard := Fintype.card_congr input
  simp only [Fintype.card_fin,Fintype.card_prod] at hcard
  have hb := CommonBufferedBaseLayout.bucket_blocks_le (width q) K L (width_pos q)
  rw [←hcard] at hb
  change K*count q L≤count q V+K at hb
  rw [code_cost]
  nlinarith

theorem code_length (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (source arena : ℕ) :
    (code q hfit reader input output source arena).length≤
      2*count q V+2*K*count q L+1 := by
  have h := CommonStaticFusion.length_fuse q
    (rawCode q hfit reader input output source arena)
  rwa [rawCode_cost] at h

theorem code_length_le (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (source arena : ℕ) :
    (code q hfit reader input output source arena).length≤4*count q V+2*K+1 := by
  have h := CommonStaticFusion.length_fuse q
    (rawCode q hfit reader input output source arena)
  have hc := code_cost_le q hfit reader input output source arena
  rw [code,CommonStaticFusion.cost_fuse] at hc
  exact h.trans (Nat.add_le_add_right hc 1)

end
end CodedSorting.CommonBufferedCosts
end Costs

section GatherRun
/-! Actual finite-disk reconstruction refines the ordered bucket-buffer
execution. Only live target pages are observed: out-of-range numerical
addresses play no role in the proof. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBufferedGather
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonBlockPair (Block BitIndex Selection)
open CommonPermutationPairs (width count address)
open CommonBufferedAllocation (bucketAddress)
open BitWordPacking Circuit
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V K L : ℕ}

def codePrefix (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) : ℕ → List (Instruction q)
  | 0 => []
  | n+1 => codePrefix q hfit reader e arena target n ++
    if h : n<V then fragment q hfit reader e arena target ⟨n,h⟩ else []

theorem prefix_eq_take (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target n : ℕ) (hn : n≤V) :
    codePrefix q hfit reader e arena target n=
      ((List.finRange V).take n).flatMap (fragment q hfit reader e arena target) := by
  induction n with
  | zero => simp [codePrefix]
  | succ n ih =>
    have hnv : n<V := by omega
    rw [codePrefix,dif_pos hnv,ih (by omega),
      List.take_succ_eq_append_getElem (by simpa using hnv),List.flatMap_append]
    simp

theorem code_eq_prefix (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) :
    code q hfit reader e arena target=codePrefix q hfit reader e arena target V := by
  rw [prefix_eq_take q hfit reader e arena target V le_rfl]
  have ht : (List.finRange V).take V=List.finRange V :=
    List.take_of_length_le (by rw [List.length_finRange])
  rw [ht]
  rfl

def machineRun (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (initial : Machine q) : ℕ → Machine q
  | 0 => initial
  | n+1 => let previous := machineRun q hfit reader e arena target initial n
    if h : n<V then machine q
      (stepStore q hfit reader e arena ⟨n,h⟩ (unpack previous.ram) previous.disk)
      (stepDisk q hfit reader e arena target ⟨n,h⟩ (unpack previous.ram) previous.disk)
    else previous

theorem raw_prefix (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (initial : Machine q) (n : ℕ) :
    (executeRaw q (codePrefix q hfit reader e arena target n) initial).1=
      machineRun q hfit reader e arena target initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [codePrefix,CommonPermutationPairs.raw_append,ih]
    by_cases hn : n<V
    · simp only [hn,dif_pos,machineRun]
      rw [←CommonBlockPair.machine_eta q (machineRun q hfit reader e arena target initial n),
        fragment_run]
      simp only [machine,unpack_pack]
    · simp only [hn,dif_neg,↓reduceDIte,executeRaw,machineRun]

theorem machineRun_frame (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (ht : target+count q V≤q.N^q.exponent)
    (initial : Machine q) (n : ℕ) (a : Fin (q.N^q.exponent))
    (ha : a.val<target ∨ target+count q V≤a.val) :
    (machineRun q hfit reader e arena target initial n).disk a=initial.disk a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n<V
    · simp only [machineRun,hn,dif_pos,machine]
      rw [stepDisk_outside q hfit reader e arena target _ _ _ ht a ha,ih]
    · simpa only [machineRun,hn,dif_neg] using ih

def bucketData (q : Configuration) (arena L : ℕ) (disk : Disk q)
    (k : Fin K) (page : ℕ) : BitIndex q → Bit :=
  blockBits q.block q.w (disk (bucketAddress q arena L k page))

def observe (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (target : ℕ) (s : Machine q) :
    BufferedGatherInvariant.State K (width q) Bit :=
  ⟨fun k => blockBits q.block q.w (CommonBufferedBank.get q hfit k (unpack s.ram)),
    blockBits q.block q.w (CommonBlockPair.buffer q reader (unpack s.ram)),
    fun page => blockBits q.block q.w (s.disk (address q target page))⟩

def Represents (q : Configuration) (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (target V : ℕ) (s : Machine q)
    (p : BufferedGatherInvariant.State K (width q) Bit) : Prop :=
  (observe q hfit reader target s).bank=p.bank ∧
  (observe q hfit reader target s).output=p.output ∧
  ∀ page, page<count q V → (observe q hfit reader target s).disk page=p.disk page

theorem loaded_bank_bits (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (e : Fin V ≃ Fin K × Fin L) (arena : ℕ) (i : Fin V)
    (s : Store q) (disk initial : Disk q)
    (bank : Fin K → BitIndex q → Bit)
    (hb : (fun k => blockBits q.block q.w (CommonBufferedBank.get q hfit k s))=bank)
    (hd : ∀ (k : Fin K) (page : ℕ), page<count q L →
      disk (bucketAddress q arena L k page)=initial (bucketAddress q arena L k page)) :
    (fun k => blockBits q.block q.w (CommonBufferedBank.get q hfit k
      (loaded q e arena i s disk)))=
      BufferedGatherInvariant.loadBank e (bucketData q arena L initial) i bank := by
  funext k
  rw [congrFun (loaded_bank q hfit e arena i s disk) k]
  unfold BufferedGatherInvariant.loadBank
  simp only [width]
  by_cases hz : (e i).2.val%(q.block*q.w)=0
  · simp only [if_pos hz]
    by_cases hk : k=(e i).1
    · subst k
      rw [Function.update_self,Function.update_self]
      rw [hd (e i).1 ((e i).2.val/(q.block*q.w))
        (CommonPermutationPairs.bit_block_lt q (e i).2)]
      rfl
    · rw [Function.update_of_ne hk,Function.update_of_ne hk]
      exact congrFun hb k
  · simp only [if_neg hz]
    exact congrFun hb k

theorem step_represents (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (ht : target+count q V≤q.N^q.exponent)
    (i : Fin V) (s : Machine q) (initial : Disk q)
    (p : BufferedGatherInvariant.State K (width q) Bit)
    (hr : Represents q hfit reader target V s p)
    (hd : ∀ (k : Fin K) (page : ℕ), page<count q L →
      s.disk (bucketAddress q arena L k page)=initial (bucketAddress q arena L k page)) :
    Represents q hfit reader target V
      (machine q (stepStore q hfit reader e arena i (unpack s.ram) s.disk)
        (stepDisk q hfit reader e arena target i (unpack s.ram) s.disk))
      (BufferedGatherInvariant.step (CommonPermutationPairs.width_pos q) e
        (bucketData q arena L initial) i p) := by
  have hb := loaded_bank_bits q hfit e arena i (unpack s.ram) s.disk initial p.bank hr.1 hd
  have ho : blockBits q.block q.w (CommonBlockPair.buffer q reader
      (assembled q hfit reader e arena i (unpack s.ram) s.disk))=
      Function.update p.output (position q i.val)
        (BufferedGatherInvariant.loadBank e (bucketData q arena L initial) i p.bank
          (e i).1 (position q (e i).2.val)) := by
    rw [assembled,assemble_buffer,loaded_buffer]
    change Function.update ((observe q hfit reader target s).output) _ _ = _
    rw [hr.2.1,←hb]
  refine ⟨?_,?_,?_⟩
  · funext k
    simp only [observe,machine,unpack_pack,stepStore_bank,BufferedGatherInvariant.step]
    exact congrFun hb k
  · simp only [observe,machine,unpack_pack]
    rw [stepStore_buffer]
    exact ho
  · intro page hp
    change blockBits q.block q.w (stepDisk q hfit reader e arena target i
      (unpack s.ram) s.disk (address q target page)) = _
    rw [stepDisk_at q hfit reader e arena target i (unpack s.ram) s.disk ht page hp]
    by_cases hf : i.val%width q=width q-1 ∨ i.val+1=V
    · have hfp : BufferedGatherInvariant.Flush (width q) V i.val := hf
      simp only [BufferedGatherInvariant.step,if_pos hfp]
      by_cases he : page=i.val/width q
      · subst page
        simp only [hf,true_and,if_pos,Function.update_self]
        exact ho
      · rw [if_neg (by tauto),Function.update_of_ne he]
        exact hr.2.2 page hp
    · have hfp : ¬BufferedGatherInvariant.Flush (width q) V i.val := hf
      simp only [BufferedGatherInvariant.step,if_neg hfp,if_neg (by tauto :
        ¬((i.val%width q=width q-1 ∨ i.val+1=V) ∧ page=i.val/width q))]
      exact hr.2.2 page hp

theorem machineRun_arena (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (ht : target+count q V≤q.N^q.exponent)
    (ha : arena+K*count q L≤q.N^q.exponent) (hs : target+count q V≤arena)
    (initial : Machine q) (n : ℕ) (k : Fin K) (page : ℕ) (hp : page<count q L) :
    (machineRun q hfit reader e arena target initial n).disk
      (bucketAddress q arena L k page)=initial.disk (bucketAddress q arena L k page) := by
  apply machineRun_frame q hfit reader e arena target ht initial n
  have hb := CommonBufferedAllocation.bucketAddress_bounds q arena L k page hp ha
  exact Or.inr (by omega)

theorem prefix_represents (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (arena target : ℕ) (ht : target+count q V≤q.N^q.exponent)
    (ha : arena+K*count q L≤q.N^q.exponent) (hs : target+count q V≤arena)
    (initial : Machine q) (n : ℕ) :
    Represents q hfit reader target V (machineRun q hfit reader e arena target initial n)
      (BufferedGatherInvariant.run (CommonPermutationPairs.width_pos q) e
        (bucketData q arena L initial.disk) (observe q hfit reader target initial) n) := by
  induction n with
  | zero => exact ⟨rfl,rfl,fun _ _ => rfl⟩
  | succ n ih =>
    by_cases hn : n<V
    · simp only [machineRun,hn,dif_pos,BufferedGatherInvariant.run]
      apply step_represents q hfit reader e arena target ht ⟨n,hn⟩ _ initial.disk _ ih
      exact fun k page hp => machineRun_arena q hfit reader e arena target ht ha hs
        initial n k page hp
    · simpa only [machineRun,hn,dif_neg,BufferedGatherInvariant.run] using ih

/-- Correct reconstruction and disk frame for the actual generated finite
machine code. The bucket arena is kept intact throughout the run. -/
theorem raw_correct (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (ho : BufferedGatherInvariant.Ordered e) (arena target : ℕ) (initial : Machine q)
    (ht : target+count q V≤q.N^q.exponent)
    (ha : arena+K*count q L≤q.N^q.exponent) (hs : target+count q V≤arena) :
    (∀ i : Fin V, CommonPermutationPairs.readBit q
      (executeRaw q (code q hfit reader e arena target) initial).1.disk target i.val=
      blockBits q.block q.w (initial.disk
        (bucketAddress q arena L (e i).1 ((e i).2.val/width q)))
        (position q (e i).2.val)) ∧
    (∀ a : Fin (q.N^q.exponent), (a.val<target ∨ target+count q V≤a.val) →
      (executeRaw q (code q hfit reader e arena target) initial).1.disk a=initial.disk a) := by
  rw [code_eq_prefix,raw_prefix]
  constructor
  · intro i
    have hr := prefix_represents q hfit reader e arena target ht ha hs initial V
    have hd := congrFun (hr.2.2 (i.val/width q) (CommonPermutationPairs.bit_block_lt q i))
      (position q i.val)
    have hc := BufferedGatherInvariant.run_correct (CommonPermutationPairs.width_pos q)
      e ho (bucketData q arena L initial.disk) (observe q hfit reader target initial) i
    exact hd.trans hc
  · exact fun a h => machineRun_frame q hfit reader e arena target ht initial V a h

end
end CodedSorting.CommonBufferedGather
end GatherRun

section Permutation
/-! Concrete buffered permutation: distribute to a disjoint bucket arena,
then reconstruct in place. The instruction fusion compiler preserves this
entire execution, including its actual finite disk and I/O count. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBufferedCosts
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonBufferedAllocation (bucketAddress)
noncomputable section
variable {V K L : ℕ}

theorem code_safe (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (source arena : ℕ) :
    ∀ i∈code q hfit reader input output source arena,RespectsPC q i := by
  apply CommonStaticFusion.fuse_safe
  intro i hi
  rcases List.mem_append.mp hi with hd|hg
  · exact CommonBufferedDistribution.program_safe q hfit reader input source
      (fun k j => address q arena (k.val*count q L+j)) i hd
  · exact CommonBufferedGather.code_safe q hfit reader output arena source i hg

/-- The same concrete fused program produces the requested permutation
and leaves every block outside its source and scratch arena unchanged. -/
theorem code_correct (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (input output : Fin V ≃ Fin K × Fin L)
    (hi : BufferedScatterInvariant.Ordered input)
    (ho : BufferedGatherInvariant.Ordered output)
    (source arena : ℕ) (initial : Machine q)
    (hs : source+count q V≤q.N^q.exponent)
    (ha : arena+K*count q L≤q.N^q.exponent)
    (hsep : source+count q V≤arena) :
    (∀ i : Fin V, readBit q
      (executeRaw q (code q hfit reader input output source arena) initial).1.disk
      source i.val=readBit q initial.disk source (input.symm (output i)).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q V≤a.val) →
      (a.val<arena ∨ arena+K*count q L≤a.val) →
      (executeRaw q (code q hfit reader input output source arena) initial).1.disk a=
        initial.disk a) := by
  let mid := (executeRaw q
    (CommonBufferedDistribution.program q hfit reader input source
      (bucketAddress q arena L)) initial).1
  obtain ⟨hd,hdf⟩ := CommonBufferedDistribution.raw_correct q hfit reader input hi
    source arena initial hs ha (Or.inl hsep)
  obtain ⟨hg,hgf⟩ := CommonBufferedGather.raw_correct q hfit reader output ho
    arena source mid hs ha hsep
  rw [code,CommonStaticFusion.executeRaw_fuse,rawCode,raw_append]
  constructor
  · intro i
    exact (hg i).trans (hd (output i).1 (output i).2)
  · intro a has haa
    exact (hgf a has).trans (hdf a haa)

end
end CodedSorting.CommonBufferedCosts
end Permutation

section Base
/-! The actual buffered scalar exchange, returned directly to its source.
All bucket transfers are charged; the K block buffers occupy the existing
leaf bank. The additive K term accounts for partial bucket boundary blocks.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBufferedBase
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open PhysicalFieldPacking RecursiveExchange Circuit Address
open CommonBufferedBaseLayout
noncomputable section

theorem input_ordered (P Q G S : ℕ) :
    BufferedScatterInvariant.Ordered (indexEquiv P Q G S) := by
  intro k r s hrs
  exact (inverse_lt_iff P Q G S k r s).2 hrs

theorem output_ordered (P Q G S : ℕ) :
    BufferedGatherInvariant.Ordered (outputIndexEquiv P Q G S) := by
  intro k r s hrs
  exact (output_inverse_lt_iff P Q G S k r s).2 hrs

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer : ℕ)
    (hfit : ((radix^f)*(radix^f))*q.block≤CommonExchangeLeaf.bankWords q) :
    List (Instruction q) :=
  CommonBufferedCosts.code q hfit reader (indexEquiv P (radix^f) G S)
    (outputIndexEquiv P (radix^f) G S) source buffer

def charge (q : Configuration) (f P G S : ℕ) : ℕ :=
  4*count q (ScalarVolume f P G S)+2*((radix^f)*(radix^f))+1

theorem bucket_space (q : Configuration) (f P G S : ℕ) :
    ((radix^f)*(radix^f))*count q (bucketSize P G S)≤
      count q (ScalarVolume f P G S)+(radix^f)*(radix^f) :=
  exchange_bucket_blocks_le P (radix^f) G S (width q) (width_pos q)

theorem code_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer limit : ℕ)
    (hfit : ((radix^f)*(radix^f))*q.block≤CommonExchangeLeaf.bankWords q)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+count q (ScalarVolume f P G S)+(radix^f)*(radix^f)≤limit)
    (hl : limit≤q.N^q.exponent) (initial : Machine q) :
    (∀ a : CommonRecursiveExchange.ScalarAddress f P G S,
      readBit q (executeRaw q (code q reader f P G S source buffer hfit) initial).1.disk
        source (scalarLayout f P G S a).val =
      readBit q initial.disk source (scalarLayout f P G S (exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (ScalarVolume f P G S)≤a.val) →
      (a.val<buffer ∨ limit≤a.val) →
      (executeRaw q (code q reader f P G S source buffer hfit) initial).1.disk a=
        initial.disk a) := by
  have hb := bucket_space q f P G S
  have hsource : source+count q (ScalarVolume f P G S)≤q.N^q.exponent := by omega
  have harena : buffer+((radix^f)*(radix^f))*count q (bucketSize P G S)≤
      q.N^q.exponent := by omega
  obtain ⟨hbits,hframe⟩ := CommonBufferedCosts.code_correct q hfit reader
    (indexEquiv P (radix^f) G S) (outputIndexEquiv P (radix^f) G S)
    (input_ordered P (radix^f) G S) (output_ordered P (radix^f) G S)
    source buffer initial hsource harena hs
  constructor
  · intro a
    have h := hbits (scalarLayout f P G S a)
    have hp : (indexEquiv P (radix^f) G S).symm
        (outputIndexEquiv P (radix^f) G S (scalarLayout f P G S a)) =
        scalarLayout f P G S (exchange a) := by
      simp only [outputIndexEquiv,Equiv.trans_apply,Equiv.symm_apply_apply]
      exact CommonRecursiveBase.permutation_inverse_encoded f P G S a
    simpa only [hp] using h
  · intro a hout hwork
    exact hframe a hout (by omega)

/-- A fully proved recursive-program leaf. No source payload or execution
correctness predicate is an input to the constructor. -/
def program (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer limit : ℕ)
    (hfit : ((radix^f)*(radix^f))*q.block≤CommonExchangeLeaf.bankWords q)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+count q (ScalarVolume f P G S)+(radix^f)*(radix^f)≤limit)
    (hl : limit≤q.N^q.exponent) :
    CommonRecursiveExchange.Program q f P G S source buffer limit where
  instructions := code q reader f P G S source buffer hfit
  charge := charge q f P G S
  correct := fun s => (code_correct q reader f P G S source buffer limit hfit hs hw hl s).1
  frame := fun s => (code_correct q reader f P G S source buffer limit hfit hs hw hl s).2
  safe := CommonBufferedCosts.code_safe q hfit reader _ _ source buffer
  cost_le := (CommonBufferedCosts.code_cost_le q hfit reader _ _ source buffer).trans
    (Nat.le_succ _)
  length_le := CommonBufferedCosts.code_length_le q hfit reader _ _ source buffer

end
end CodedSorting.CommonBufferedBase
end Base
