import CodedSorting.Shared.Memory.Buffered.GatherProgram
import CodedSorting.Shared.Programs.BufferedGatherInvariant

section Distribution
/-! Actual finite-machine distribution into payload-only bucket files.
Every source block is read once. The resident leaf bank holds one block per
bucket; a bucket block is written only when full or at its final live bit.
Public positions determine the code, and payload enters only through reads.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBufferedDistribution
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonBlockPair (Block BitIndex Selection buffer)
open BitWordPacking Circuit
noncomputable section

variable {V K L : ℕ}

def slot (q : Configuration) (r : ℕ) : BitIndex q :=
  ⟨r%width q,Nat.mod_lt _ (width_pos q)⟩

def selection (q : Configuration) (i r : ℕ) : Selection q :=
  fun j => if j=slot q r then some (slot q i) else none

def Flush (q : Configuration) (L r : ℕ) : Prop :=
  r%width q=width q-1 ∨ r+1=L

instance (q : Configuration) (L r : ℕ) : Decidable (Flush q L r) :=
  inferInstanceAs (Decidable (_ ∨ _))

def fragment (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (i : Fin V) : List (Instruction q) :=
  (if i.val%width q=0 then [CommonBlockPair.sourceRead q reader
      (address q source (i.val/width q))] else []) ++
  [CommonBufferedBank.blendInstruction q hfit reader (e i).1
      (selection q i.val (e i).2.val)] ++
  (if Flush q L (e i).2.val then CommonBufferedBank.writeCode q hfit (e i).1
      (target (e i).1 ((e i).2.val/width q)) else [])

def loaded (q : Configuration) (reader : Fin q.inventory.readers)
    (source i : ℕ) (s : Store q) (disk : Disk q) : Store q :=
  if i%width q=0 then
    CommonBlockPair.stash q reader (disk (address q source (i/width q)))
      {s with transfer:=disk (address q source (i/width q))}
  else s

def blended (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (i : Fin V) (s : Store q) (disk : Disk q) : Store q :=
  CommonBufferedBank.blendStore q hfit reader (e i).1
    (selection q i.val (e i).2.val) (loaded q reader source i.val s disk)

def afterStore (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (i : Fin V) (s : Store q) (disk : Disk q) : Store q :=
  let out := blended q hfit reader e source i s disk
  if Flush q L (e i).2.val then {out with transfer:=CommonBufferedBank.get q hfit (e i).1 out}
  else out

def afterDisk (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (i : Fin V) (s : Store q) (disk : Disk q) : Disk q :=
  if Flush q L (e i).2.val then Function.update disk
    (target (e i).1 ((e i).2.val/width q))
    (CommonBufferedBank.get q hfit (e i).1 (blended q hfit reader e source i s disk))
  else disk

theorem fragment_run (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (i : Fin V) (s : Store q) (disk : Disk q) :
    (executeRaw q (fragment q hfit reader e source target i) (machine q s disk)).1 =
      machine q (afterStore q hfit reader e source i s disk)
        (afterDisk q hfit reader e source target i s disk) := by
  by_cases hr : i.val%width q=0 <;> by_cases hf : Flush q L (e i).2.val <;>
    simp only [fragment,hr,hf,if_pos,if_neg,↓reduceIte,List.nil_append,List.singleton_append,
      List.cons_append,
      CommonBufferedBank.writeCode,executeRaw,CommonBlockPair.sourceRead_step,
      CommonBufferedBank.blendInstruction_step,CommonBufferedBank.prepareInstruction_step,
      CommonBlockPair.targetWrite_step,afterStore,afterDisk,blended,loaded,
      List.append_nil]

theorem loaded_bank (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (source i : ℕ)
    (s : Store q) (disk : Disk q) (k : Fin K) :
    CommonBufferedBank.get q hfit k (loaded q reader source i s disk)=
      CommonBufferedBank.get q hfit k s := by
  unfold loaded
  split <;> simp

theorem afterStore_buffer (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (i : Fin V) (s : Store q) (disk : Disk q) :
    buffer q reader (afterStore q hfit reader e source i s disk)=
      buffer q reader (loaded q reader source i.val s disk) := by
  unfold afterStore
  split <;> rfl

theorem fragment_safe (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent)) (i : Fin V) :
    ∀ op∈fragment q hfit reader e source target i,RespectsPC q op := by
  intro op hop
  simp only [fragment,List.mem_append,List.mem_singleton] at hop
  rcases hop with (hr|hb)|hw
  · by_cases h : i.val%width q=0
    · simp only [h,if_pos,List.mem_singleton] at hr
      subst op
      exact CommonBlockPair.sourceRead_respectsPC q reader _
    · simp only [h,if_neg,↓reduceIte,List.not_mem_nil] at hr
  · subst op
    exact CommonBufferedBank.blendInstruction_respectsPC q hfit reader _ _
  · by_cases h : Flush q L (e i).2.val
    · simp only [h,if_pos] at hw
      exact CommonBufferedBank.writeCode_safe q hfit _ _ op hw
    · simp only [h,if_neg,↓reduceIte,List.not_mem_nil] at hw

def codePrefix (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent)) : ℕ→List (Instruction q)
  | 0 => []
  | n+1 => codePrefix q hfit reader e source target n ++
    if h : n<V then fragment q hfit reader e source target ⟨n,h⟩ else []

def program (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent)) : List (Instruction q) :=
  codePrefix q hfit reader e source target V

theorem prefix_safe (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent)) (n : ℕ) :
    ∀ op∈codePrefix q hfit reader e source target n,RespectsPC q op := by
  induction n with
  | zero => simp [codePrefix]
  | succ n ih =>
    intro op hop
    rw [codePrefix,List.mem_append] at hop
    rcases hop with hop|hop
    · exact ih op hop
    · by_cases h : n<V
      · simp only [h,dif_pos] at hop
        exact fragment_safe q hfit reader e source target _ op hop
      · simp only [h,dif_neg,↓reduceDIte,List.not_mem_nil] at hop

theorem program_safe (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent)) :
    ∀ op∈program q hfit reader e source target,RespectsPC q op :=
  prefix_safe q hfit reader e source target V

def machineRun (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (initial : Machine q) : ℕ→Machine q
  | 0 => initial
  | n+1 => let previous := machineRun q hfit reader e source target initial n
    if h : n<V then machine q
      (afterStore q hfit reader e source ⟨n,h⟩ (unpack previous.ram) previous.disk)
      (afterDisk q hfit reader e source target ⟨n,h⟩ (unpack previous.ram) previous.disk)
    else previous

theorem raw_prefix (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (initial : Machine q) (n : ℕ) :
    (executeRaw q (codePrefix q hfit reader e source target n) initial).1=
      machineRun q hfit reader e source target initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [codePrefix,CommonPermutationPairs.raw_append,ih]
    by_cases h : n<V
    · simp only [h,dif_pos,machineRun]
      rw [←CommonBlockPair.machine_eta q (machineRun q hfit reader e source target initial n),
        fragment_run]
      simp only [machine,unpack_pack]
    · simp only [h,dif_neg,↓reduceDIte,executeRaw,machineRun]

end
end CodedSorting.CommonBufferedDistribution
end Distribution

section DistributionStep
/-! One-step refinement from finite-machine RAM and disk to the abstract
buffered scatter. Only allocated bucket pages participate in the relation. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBufferedDistribution
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonBlockPair (Block BitIndex Selection buffer)
open BitWordPacking Circuit
noncomputable section

variable {V K L : ℕ}

def Refines (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q) (L : ℕ)
    (target : Fin K→ℕ→Fin (q.N^q.exponent)) (a : Machine q)
    (p : BufferedScatterInvariant.State K (width q) Bit) : Prop :=
  (∀ k j, blockBits q.block q.w (CommonBufferedBank.get q hfit k (unpack a.ram)) j=p.bank k j) ∧
  (∀ k b, b<count q L → ∀ j,
    blockBits q.block q.w (a.disk (target k b)) j=p.disk k b j)

theorem blended_bank_refines (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (i : Fin V) (s : Store q) (disk : Disk q)
    (F : Fin V→Bit) (p : BufferedScatterInvariant.State K (width q) Bit)
    (hb : ∀ k j,blockBits q.block q.w (CommonBufferedBank.get q hfit k s) j=p.bank k j)
    (hin : blockBits q.block q.w (buffer q reader (loaded q reader source i.val s disk))
      (slot q i.val)=F i) (k : Fin K) (j : BitIndex q) :
    blockBits q.block q.w (CommonBufferedBank.get q hfit k
      (blended q hfit reader e source i s disk)) j=
    (BufferedScatterInvariant.step (width_pos q) e F i p).bank k j := by
  by_cases hk : k=(e i).1
  · subst k
    rw [blended,CommonBufferedBank.blendStore_get]
    by_cases hj : j=slot q (e i).2.val
    · simp only [selection,hj,if_pos]
      change blockBits q.block q.w (buffer q reader (loaded q reader source i.val s disk))
        (slot q i.val)=_
      rw [hin]
      simp [BufferedScatterInvariant.step,BufferedScatterInvariant.slot,slot] at hj ⊢
    · simp only [selection,hj,if_neg]
      rw [loaded_bank,hb]
      simpa only [BufferedScatterInvariant.step,Function.update_self] using
        (Function.update_of_ne hj (F i) (p.bank (e i).1)).symm
  · rw [blended,CommonBufferedBank.blendStore_other q hfit reader _ k hk,loaded_bank,hb]
    simp only [BufferedScatterInvariant.step,Function.update_of_ne hk]

theorem afterStore_bank_refines (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (i : Fin V) (s : Store q) (disk : Disk q)
    (F : Fin V→Bit) (p : BufferedScatterInvariant.State K (width q) Bit)
    (hb : ∀ k j,blockBits q.block q.w (CommonBufferedBank.get q hfit k s) j=p.bank k j)
    (hin : blockBits q.block q.w (buffer q reader (loaded q reader source i.val s disk))
      (slot q i.val)=F i) (k : Fin K) (j : BitIndex q) :
    blockBits q.block q.w (CommonBufferedBank.get q hfit k
      (afterStore q hfit reader e source i s disk)) j=
    (BufferedScatterInvariant.step (width_pos q) e F i p).bank k j := by
  unfold afterStore
  split <;> simpa only [CommonBufferedBank.get_transfer] using
    blended_bank_refines q hfit reader e source i s disk F p hb hin k j

theorem step_refines (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (htarget : ∀ k k' b b', b<count q L → b'<count q L →
      target k b=target k' b' → k=k' ∧ b=b')
    (i : Fin V) (a : Machine q) (F : Fin V→Bit)
    (p : BufferedScatterInvariant.State K (width q) Bit)
    (href : Refines q hfit L target a p)
    (hin : blockBits q.block q.w
      (buffer q reader (loaded q reader source i.val (unpack a.ram) a.disk))
      (slot q i.val)=F i) :
    Refines q hfit L target
      (machine q (afterStore q hfit reader e source i (unpack a.ram) a.disk)
        (afterDisk q hfit reader e source target i (unpack a.ram) a.disk))
      (BufferedScatterInvariant.step (width_pos q) e F i p) := by
  constructor
  · intro k j
    simp only [machine,unpack_pack]
    exact afterStore_bank_refines q hfit reader e source i _ _ F p href.1 hin k j
  · intro k b hblt j
    change blockBits q.block q.w
      (afterDisk q hfit reader e source target i (unpack a.ram) a.disk (target k b)) j=_
    have hcurr : (e i).2.val/width q<count q L := bit_block_lt q (e i).2
    have hiff : target k b=target (e i).1 ((e i).2.val/width q) ↔
        k=(e i).1 ∧ b=(e i).2.val/width q := by
      constructor
      · exact htarget k (e i).1 b _ hblt hcurr
      · rintro ⟨rfl,rfl⟩; rfl
    by_cases hf : Flush q L (e i).2.val
    · have hf' : BufferedScatterInvariant.Flush (width q) L (e i).2.val := hf
      by_cases heq : target k b=target (e i).1 ((e i).2.val/width q)
      · obtain ⟨hk,hb⟩ := hiff.mp heq
        subst k
        subst b
        simp only [afterDisk,hf,if_pos,Function.update_self]
        rw [blended_bank_refines q hfit reader e source i _ _ F p href.1 hin]
        simp only [BufferedScatterInvariant.step,hf',if_pos,Function.update_self]
      · rw [afterDisk,if_pos hf,Function.update_of_ne heq,href.2 k b hblt j]
        by_cases hk : k=(e i).1
        · subst k
          have hb : b≠(e i).2.val/width q := fun hb => heq (by rw [hb])
          simp only [BufferedScatterInvariant.step,hf',if_pos,Function.update_self,
            Function.update_of_ne hb]
        · simp only [BufferedScatterInvariant.step,hf',if_pos,Function.update_of_ne hk]
    · have hf' : ¬BufferedScatterInvariant.Flush (width q) L (e i).2.val := hf
      rw [afterDisk,if_neg hf,href.2 k b hblt j]
      simp only [BufferedScatterInvariant.step,hf',if_neg,↓reduceIte]

end
end CodedSorting.CommonBufferedDistribution
end DistributionStep

section DistributionCorrectness
/-! Source-cache preservation and the complete finite-machine distribution.
The protected source file is read in order, while only allocated bucket
blocks may be changed. The correctness argument allows arbitrary initial
resident and disk contents.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonBufferedDistribution
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Store RAM Disk Machine machine)
open CommonBlockPair (Block BitIndex Selection buffer)
open BitWordPacking Circuit
noncomputable section
variable {V K L : ℕ}

def SourceSeparated (q : Configuration) (V L source : ℕ)
    (target : Fin K→ℕ→Fin (q.N^q.exponent)) : Prop :=
  ∀ (k : Fin K) (p : ℕ),p<count q L → ∀ j : ℕ,j<count q V →
    target k p≠address q source j

/-- All blocks outside the bucket allocation are unchanged at every prefix. -/
theorem prefix_outside (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (initial : Machine q) (n : ℕ) (a : Fin (q.N^q.exponent))
    (ha : ∀ (k : Fin K) (p : ℕ),p<count q L → a≠target k p) :
    (machineRun q hfit reader e source target initial n).disk a=initial.disk a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n<V
    · rw [machineRun,dif_pos h]
      change afterDisk q hfit reader e source target ⟨n,h⟩ _ _ a=initial.disk a
      unfold afterDisk
      split
      · rw [Function.update_of_ne (ha (e ⟨n,h⟩).1 _ (bit_block_lt q (e ⟨n,h⟩).2))]
        exact ih
      · exact ih
    · rw [machineRun,dif_neg h]
      exact ih

theorem prefix_source (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (hsep : SourceSeparated q V L source target)
    (initial : Machine q) (n j : ℕ) (hj : j<count q V) :
    (machineRun q hfit reader e source target initial n).disk (address q source j)=
      initial.disk (address q source j) :=
  prefix_outside q hfit reader e source target initial n _
    (fun k p hp => (hsep k p hp j hj).symm)

/-- If the next bit is not a block boundary, its source block is already in
the existing reader cache; no hidden reload is needed. -/
theorem prefix_cache (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (hsep : SourceSeparated q V L source target)
    (initial : Machine q) (n : ℕ) (hn : n≤V) (hmod : n%width q≠0) :
    buffer q reader (unpack (machineRun q hfit reader e source target initial n).ram)=
      initial.disk (address q source (n/width q)) := by
  induction n with
  | zero => exact (hmod (Nat.zero_mod _)).elim
  | succ n ih =>
    have hnV : n<V := by omega
    have hdiv : (n+1)/width q=n/width q := Nat.succ_div_of_mod_ne_zero hmod
    rw [machineRun,dif_pos hnV]
    simp only [machine,unpack_pack,afterStore_buffer]
    rw [hdiv]
    by_cases hread : n%width q=0
    · rw [loaded,if_pos hread,CommonBlockPair.buffer_stash]
      exact prefix_source q hfit reader e source target hsep initial n _
        (bit_block_lt q ⟨n,hnV⟩)
    · rw [loaded,if_neg hread]
      exact ih (by omega) hread

theorem loaded_cache (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (hsep : SourceSeparated q V L source target)
    (initial : Machine q) (i : Fin V) :
    buffer q reader (loaded q reader source i.val
      (unpack (machineRun q hfit reader e source target initial i.val).ram)
      (machineRun q hfit reader e source target initial i.val).disk)=
      initial.disk (address q source (i.val/width q)) := by
  by_cases hread : i.val%width q=0
  · rw [loaded,if_pos hread,CommonBlockPair.buffer_stash]
    exact prefix_source q hfit reader e source target hsep initial i.val _ (bit_block_lt q i)
  · rw [loaded,if_neg hread]
    exact prefix_cache q hfit reader e source target hsep initial i.val (Nat.le_of_lt i.isLt) hread

theorem loaded_value (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (hsep : SourceSeparated q V L source target)
    (initial : Machine q) (i : Fin V) :
    blockBits q.block q.w (buffer q reader (loaded q reader source i.val
      (unpack (machineRun q hfit reader e source target initial i.val).ram)
      (machineRun q hfit reader e source target initial i.val).disk)) (slot q i.val)=
      readBit q initial.disk source i.val := by
  rw [loaded_cache q hfit reader e source target hsep initial i]
  rfl

def observed (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (target : Fin K→ℕ→Fin (q.N^q.exponent)) (a : Machine q) :
    BufferedScatterInvariant.State K (width q) Bit where
  bank k := blockBits q.block q.w (CommonBufferedBank.get q hfit k (unpack a.ram))
  disk k b := blockBits q.block q.w (a.disk (target k b))

theorem observed_refines (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q) (L : ℕ)
    (target : Fin K→ℕ→Fin (q.N^q.exponent)) (a : Machine q) :
    Refines q hfit L target a (observed q hfit target a) := by
  exact ⟨fun _ _ => rfl,fun _ _ _ _ => rfl⟩

theorem prefix_refines (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (htarget : ∀ k k' b b', b<count q L → b'<count q L →
      target k b=target k' b' → k=k' ∧ b=b')
    (hsep : SourceSeparated q V L source target)
    (initial : Machine q) (n : ℕ) :
    Refines q hfit L target (machineRun q hfit reader e source target initial n)
      (BufferedScatterInvariant.run (width_pos q) e
        (fun i => readBit q initial.disk source i.val) (observed q hfit target initial) n) := by
  induction n with
  | zero => exact observed_refines q hfit L target initial
  | succ n ih =>
    by_cases hn : n<V
    · rw [machineRun,dif_pos hn,BufferedScatterInvariant.run,dif_pos hn]
      exact step_refines q hfit reader e source target htarget ⟨n,hn⟩ _ _ _ ih
        (loaded_value q hfit reader e source target hsep initial ⟨n,hn⟩)
    · rw [machineRun,dif_neg hn,BufferedScatterInvariant.run,dif_neg hn]
      exact ih

theorem raw_bucket_correct (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (ho : BufferedScatterInvariant.Ordered e)
    (source : ℕ) (target : Fin K→ℕ→Fin (q.N^q.exponent))
    (htarget : ∀ k k' b b', b<count q L → b'<count q L →
      target k b=target k' b' → k=k' ∧ b=b')
    (hsep : SourceSeparated q V L source target)
    (initial : Machine q) (k : Fin K) (r : Fin L) :
    blockBits q.block q.w
      ((executeRaw q (program q hfit reader e source target) initial).1.disk
        (target k (r.val/width q))) (slot q r.val)=
      readBit q initial.disk source (e.symm (k,r)).val := by
  rw [program,raw_prefix]
  have h := (prefix_refines q hfit reader e source target htarget hsep initial V).2
    k (r.val/width q) (bit_block_lt q r) (slot q r.val)
  rw [h]
  exact BufferedScatterInvariant.run_correct (width_pos q) e ho _ _ k r

/-- The allocated finite disk implementation, with its exact payload output
and disk frame. Every source read and bucket write is an actual instruction. -/
theorem raw_correct (q : Configuration)
    (hfit : K*q.block≤CommonExchangeLeaf.bankWords q)
    (reader : Fin q.inventory.readers) (e : Fin V ≃ Fin K × Fin L)
    (ho : BufferedScatterInvariant.Ordered e)
    (source arena : ℕ) (initial : Machine q)
    (hs : source+count q V≤q.N^q.exponent)
    (ha : arena+K*count q L≤q.N^q.exponent)
    (hsep : source+count q V≤arena ∨ arena+K*count q L≤source) :
    let out := (executeRaw q (program q hfit reader e source
      (CommonBufferedAllocation.bucketAddress q arena L)) initial).1
    (∀ (k : Fin K) (r : Fin L),blockBits q.block q.w
      (out.disk (CommonBufferedAllocation.bucketAddress q arena L k (r.val/width q)))
        (slot q r.val)=readBit q initial.disk source (e.symm (k,r)).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<arena ∨ arena+K*count q L≤a.val →
      out.disk a=initial.disk a) := by
  constructor
  · intro k r
    apply raw_bucket_correct q hfit reader e ho source _ _ _ initial k r
    · intro k k' b b' hb hb' he
      exact CommonBufferedAllocation.bucketAddress_injective q arena L k k' b b' hb hb' ha he
    · intro k b hb j hj
      exact CommonBufferedAllocation.bucketAddress_ne_source q source arena V L k b j
        hb hj hs ha hsep
  · intro a hout
    rw [program,raw_prefix]
    apply prefix_outside q hfit reader e source _ initial V a
    intro k b hb
    exact (CommonBufferedAllocation.bucketAddress_ne_outside q arena L k b hb ha a hout).symm

end
end CodedSorting.CommonBufferedDistribution
end DistributionCorrectness
