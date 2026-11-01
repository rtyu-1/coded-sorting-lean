import CodedSorting.Shared.Records.RecordOperations

section DirectoryScan
/-! A runtime bucket histogram on the counted common machine.  Each input
block is physically read once.  The continuation inspects only that block
and the K multiword counters in the existing leaf bank.  In the ordinary
three-word record encoding, positions congruent to one modulo three are
key words; no key, bucket length, or input array is captured in the program. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDDirectoryScan
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store RAM Disk Machine machine)
noncomputable section
variable {K : ℕ}

def counterWords (q : Configuration) (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (s : Store q) (k : Fin K) : Words q.digits q.w := fun j =>
  ResidentLeafBank.raw s.leaf ((finProdFinEquiv (k,j)).castLE hfit)

def counter (q : Configuration) (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (s : Store q) (k : Fin K) : ℕ := decodeWords (counterWords q hfit s k)

def putCounters (q : Configuration) (values : Fin K → ℕ) (s : Store q) : Store q :=
  {s with leaf := (ResidentLeafBank.putBlock 0 (K*q.digits)
    (CommonSortingNormalization.family (fun k => PhysicalStreamCursor.encodeNat q.digits q.w (values k))) s.leaf)}

@[simp] theorem counterWords_put (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (values : Fin K → ℕ) (s : Store q) (k : Fin K) :
    counterWords q hfit (putCounters q values s) k =
      PhysicalStreamCursor.encodeNat q.digits q.w (values k) := by
  funext j
  unfold counterWords putCounters
  dsimp only
  rw [ResidentLeafBank.raw_putBlock_inside 0 (K*q.digits) _ _ _ (by omega)
    (by simpa using (finProdFinEquiv (k,j)).isLt) le_rfl]
  simp only [Nat.sub_zero,CommonSortingNormalization.family]
  exact congrArg (fun p => PhysicalStreamCursor.encodeNat q.digits q.w (values p.1) p.2)
    (finProdFinEquiv.symm_apply_apply (k,j))

@[simp] theorem counter_put (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (values : Fin K → ℕ) (s : Store q) (k : Fin K)
    (hv : values k < (2^q.w)^q.digits) :
    counter q hfit (putCounters q values s) k=values k := by
  unfold counter
  rw [counterWords_put]
  exact PhysicalStreamCursor.decodeNat_encode _ _ _ hv

def blockCounts (q : Configuration) (key : Word q.w → Fin K)
    (n i : ℕ) (block : Words q.block q.w) (k : Fin K) : ℕ :=
  ∑ j : Fin q.block, if i*q.block+j.val<3*n ∧
    (i*q.block+j.val)%3=1 ∧ key (block j)=k then 1 else 0

def afterBlock (q : Configuration) (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (n i : ℕ) (s : Store q) : Store q :=
  putCounters q (fun k => counter q hfit s k+blockCounts q key n i s.transfer k) s

def readAt (q : Configuration) (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n i : ℕ) : Instruction q :=
  if h : source+i<q.N^q.exponent then
    ⟨.read ⟨source+i,h⟩ (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
      fun ram => pack (afterBlock q hfit key n i (unpack ram))⟩
  else ⟨.localOp id,id⟩

def initCounters (q : Configuration) (K : ℕ) : Instruction q :=
  ⟨.localOp (fun ram => pack (putCounters q (fun _ : Fin K => 0) (unpack ram))),id⟩

def readCode (q : Configuration) (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n blocks : ℕ) : List (Instruction q) :=
  (List.range blocks).map (readAt q hfit key source n)

def code (q : Configuration) (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n : ℕ) : List (Instruction q) :=
  initCounters q K :: readCode q hfit key source n (CommonRecordProgram.recordBlocks q n)

def counts (q : Configuration) (key : Word q.w → Fin K)
    (source n blocks : ℕ) (disk : Disk q) (k : Fin K) : ℕ :=
  ∑ i ∈ Finset.range blocks,
    blockCounts q key n i (disk (CommonPermutationPairs.address q source i)) k

theorem readAt_step (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n i : ℕ)
    (h : source+i<q.N^q.exponent) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (readAt q hfit key source n i) (machine q s disk)=
      machine q (afterBlock q hfit key n i {s with transfer:=disk ⟨source+i,h⟩}) disk := by
  simp only [readAt,dif_pos h,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,CommonLeafWindow.load_transfer,unpack_pack]

theorem initCounters_step (q : Configuration) (K : ℕ) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (initCounters q K) (machine q s disk)=
      machine q (putCounters q (fun _ : Fin K => 0) s) disk := by
  simp only [initCounters,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,
    unpack_pack,id_eq]

theorem counts_succ (q : Configuration) (key : Word q.w → Fin K)
    (source n blocks : ℕ) (disk : Disk q) (k : Fin K) :
    counts q key source n (blocks+1) disk k=counts q key source n blocks disk k+
      blockCounts q key n blocks (disk (CommonPermutationPairs.address q source blocks)) k := by
  exact Finset.sum_range_succ _ _

theorem blockCounts_le (q : Configuration) (key : Word q.w → Fin K)
    (n i : ℕ) (block : Words q.block q.w) (k : Fin K) :
    blockCounts q key n i block k≤q.block := by
  unfold blockCounts
  calc
    _ ≤ ∑ _j : Fin q.block, 1 := Finset.sum_le_sum fun j _ => by split <;> omega
    _ = q.block := by simp

theorem counts_le (q : Configuration) (key : Word q.w → Fin K)
    (source n blocks : ℕ) (disk : Disk q) (k : Fin K) :
    counts q key source n blocks disk k≤blocks*q.block := by
  unfold counts
  calc
    _ ≤ ∑ _i ∈ Finset.range blocks, q.block :=
      Finset.sum_le_sum fun i _ => blockCounts_le q key n i _ k
    _ = blocks*q.block := by simp

theorem read_prefix (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n blocks : ℕ)
    (s : Store q) (disk : Disk q)
    (hs : source+blocks≤q.N^q.exponent)
    (hc : blocks*q.block < (2^q.w)^q.digits)
    (hzero : ∀ k, counter q hfit s k=0) :
    ∃ final : Store q,
      executeRaw q (readCode q hfit key source n blocks) (machine q s disk)=
        (machine q final disk,blocks) ∧
      (∀ k, counter q hfit final k=counts q key source n blocks disk k) := by
  induction blocks with
  | zero => exact ⟨s,rfl,by simpa [counts] using hzero⟩
  | succ blocks ih =>
    obtain ⟨prev,hr,hprev⟩ := ih (by omega) (by nlinarith)
    have ha : source+blocks<q.N^q.exponent := by omega
    have haddress : CommonPermutationPairs.address q source blocks=⟨source+blocks,ha⟩ := by
      simp [CommonPermutationPairs.address,CommonColumnSplit.address,ha]
    let final := afterBlock q hfit key n blocks {prev with transfer:=disk ⟨source+blocks,ha⟩}
    refine ⟨final,?_,?_⟩
    · have hcode : readCode q hfit key source n (blocks+1)=
          readCode q hfit key source n blocks++[readAt q hfit key source n blocks] := by
        simp [readCode,List.range_succ]
      rw [hcode,CommonStaticLeaf.raw_append,hr]
      dsimp only
      simp only [executeRaw]
      rw [readAt_step q hfit key source n blocks ha]
      simp only [readAt,dif_pos ha,Normalization.transferCost,Nat.add_zero]
      rfl
    · intro k
      have hp : counter q hfit {prev with transfer:=disk ⟨source+blocks,ha⟩} k=
          counts q key source n blocks disk k := hprev k
      have hb : counter q hfit {prev with transfer:=disk ⟨source+blocks,ha⟩} k+
          blockCounts q key n blocks (disk ⟨source+blocks,ha⟩) k < (2^q.w)^q.digits := by
        rw [hp,←haddress,←counts_succ]
        exact (counts_le q key source n (blocks+1) disk k).trans_lt hc
      unfold final afterBlock
      rw [counter_put q hfit _ _ k hb,hp,counts_succ,haddress]

/-- Output directory values come from the input blocks read in this very
execution; the external disk is unchanged and the charge is one scan. -/
theorem raw_complete (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n : ℕ) (s : Store q) (disk : Disk q)
    (hs : source+CommonRecordProgram.recordBlocks q n≤q.N^q.exponent)
    (hc : CommonRecordProgram.recordBlocks q n*q.block<(2^q.w)^q.digits) :
    ∃ final : Store q,
      executeRaw q (code q hfit key source n) (machine q s disk)=
        (machine q final disk,CommonRecordProgram.recordBlocks q n) ∧
      (∀ k, counter q hfit final k=
        counts q key source n (CommonRecordProgram.recordBlocks q n) disk k) := by
  obtain ⟨final,hr,hv⟩ := read_prefix q hfit key source n _
    (putCounters q (fun _ : Fin K => 0) s) disk hs hc
    (fun k => counter_put q hfit _ s k (by positivity))
  refine ⟨final,?_,hv⟩
  rw [code,executeRaw,initCounters_step]
  simpa only [initCounters,Normalization.transferCost,Nat.zero_add,Prod.eta] using hr


theorem sum_blockCounts_le (q : Configuration) (key : Word q.w → Fin K)
    (n i : ℕ) (block : Words q.block q.w) :
    ∑ k : Fin K, blockCounts q key n i block k ≤ q.block := by
  unfold blockCounts
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j : Fin q.block, 1 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : i*q.block+j.val<3*n ∧ (i*q.block+j.val)%3=1
      · simp only [show ∀ k : Fin K,
          (i*q.block+j.val<3*n ∧ (i*q.block+j.val)%3=1 ∧ key (block j)=k) ↔
          key (block j)=k from fun k => by tauto]
        simp
      · simp only [show ∀ k : Fin K,
          ¬(i*q.block+j.val<3*n ∧ (i*q.block+j.val)%3=1 ∧ key (block j)=k)
          from fun k => by tauto,if_false,Finset.sum_const_zero]
        omega
    _ = q.block := by simp

theorem sum_counts_le (q : Configuration) (key : Word q.w → Fin K)
    (source n blocks : ℕ) (disk : Disk q) :
    ∑ k : Fin K, counts q key source n blocks disk k ≤ blocks*q.block := by
  unfold counts
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i ∈ Finset.range blocks, q.block :=
      Finset.sum_le_sum fun i _ => sum_blockCounts_le q key n i _
    _ = blocks*q.block := by simp

theorem readAt_safe (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n i : ℕ) :
    RespectsPC q (readAt q hfit key source n i) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  by_cases h : source+i<q.N^q.exponent
  · simp only [readAt_step q hfit key source n i h,CommonBlockPair.erasePC_machine]
    rfl
  · simp only [readAt,dif_neg h,ControlledNormalization.logicalStep,
      Normalization.logicalStep,id_eq]

theorem initCounters_safe (q : Configuration) (K : ℕ) :
    RespectsPC q (initCounters q K) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [initCounters_step,CommonBlockPair.erasePC_machine]
  rfl

theorem code_safe (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n : ℕ) :
    ∀ i ∈ code q hfit key source n, RespectsPC q i := by
  intro i hi
  simp only [code,List.mem_cons] at hi
  rcases hi with rfl | hi
  · exact initCounters_safe q K
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    exact readAt_safe q hfit key source n j

theorem code_length (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n : ℕ) :
    (code q hfit key source n).length=CommonRecordProgram.recordBlocks q n+1 := by
  simp [code,readCode]

theorem readCode_cost (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n blocks : ℕ)
    (hs : source+blocks≤q.N^q.exponent) :
    cost q (readCode q hfit key source n blocks)=blocks := by
  induction blocks with
  | zero => rfl
  | succ blocks ih =>
    have ha : source+blocks<q.N^q.exponent := by omega
    have hcode : readCode q hfit key source n (blocks+1)=
        readCode q hfit key source n blocks++[readAt q hfit key source n blocks] := by
      simp [readCode,List.range_succ]
    rw [hcode,CommonStaticLeaf.cost_append,ih (by omega)]
    simp [cost,readAt,ha,Normalization.transferCost]

theorem code_cost (q : Configuration)
    (hfit : K*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n : ℕ)
    (hs : source+CommonRecordProgram.recordBlocks q n≤q.N^q.exponent) :
    cost q (code q hfit key source n)=CommonRecordProgram.recordBlocks q n := by
  simp only [code,cost,initCounters,Normalization.transferCost,Nat.zero_add]
  exact readCode_cost q hfit key source n _ hs

end
end CodedSorting.CommonMSDDirectoryScan
end DirectoryScan

section CountSemantics
/-! The histogram obtained by reading the physical input blocks counts
exactly the ordinary records in each radix bucket. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonMSDCountSemantics
open CommonSortingNormalization CommonMSDDirectoryScan CommonRecordProgram
open CommonRecordEncoding CommonLeafProgram KeyRecordWords WordControl
noncomputable section
variable {K : ℕ}

theorem keyword_sum (n volume : ℕ) (hcover : 3*n≤volume)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ j : Fin volume, if j.val<3*n ∧ j.val%3=1 ∧ P j.val then 1 else 0) =
      ∑ i : Fin n, if P (i.val*3+1) then 1 else 0 := by
  classical
  rw [←Finset.sum_filter,←Finset.sum_filter]
  apply Finset.sum_bij
    (fun j hj => (⟨j.val/3,by
      have h := (Finset.mem_filter.mp hj).2
      omega⟩ : Fin n))
  · intro j hj
    have h := (Finset.mem_filter.mp hj).2
    have he : j.val/3*3+1=j.val := by omega
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    simpa only [he] using h.2.2
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have he := congrArg Fin.val hab
    apply Fin.ext
    dsimp only at he
    omega
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hj : i.val*3+1<volume := by have := i.isLt; omega
    refine ⟨⟨i.val*3+1,hj⟩,?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨by have := i.isLt; omega,by omega,hi'⟩
    · apply Fin.ext
      dsimp only
      omega
  · intros
    rfl

theorem disk_word_at_block (q : Configuration) (disk : Disk q)
    (source blocks : ℕ) (hs : source+blocks≤q.N^q.exponent)
    (i : Fin blocks) (j : Fin q.block) :
    disk (CommonPermutationPairs.address q source i.val) j =
      CommonMarginTransform.wordAt q disk source (i.val*q.block+j.val) := by
  have hb := block_positive q
  have hd : (i.val*q.block+j.val)/q.block=i.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hb,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have hm : (i.val*q.block+j.val)%q.block=j.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt] <;> omega
  have hi : source+i.val<q.N^q.exponent := by have := i.isLt; omega
  simp only [CommonPermutationPairs.address,CommonColumnSplit.address,hi,↓reduceDIte,
    CommonMarginTransform.wordAt,CommonLeafBatchProgram.extendDisk,hd,hm]

theorem counts_eq_word_sum (q : Configuration) (key : Word q.w → Fin K)
    (source n blocks : ℕ) (disk : Disk q)
    (hs : source+blocks≤q.N^q.exponent) (k : Fin K) :
    counts q key source n blocks disk k =
      ∑ j : Fin (blocks*q.block),
        if j.val<3*n ∧ j.val%3=1 ∧
          key (CommonMarginTransform.wordAt q disk source j.val)=k then 1 else 0 := by
  unfold counts blockCounts
  rw [←Fin.sum_univ_eq_sum_range]
  simp_rw [disk_word_at_block q disk source blocks hs]
  calc
    _ = ∑ p : Fin blocks × Fin q.block,
        if p.1.val*q.block+p.2.val<3*n ∧ (p.1.val*q.block+p.2.val)%3=1 ∧
          key (CommonMarginTransform.wordAt q disk source (p.1.val*q.block+p.2.val))=k
          then 1 else 0 := (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv finProdFinEquiv
      intro i
      rw [BitWordPacking.bit_address]

theorem counts_eq_key_sum (q : Configuration) (key : Word q.w → Fin K)
    (source n : ℕ) (disk : Disk q) (f : Records q n)
    (hs : source+recordBlocks q n≤q.N^q.exponent)
    (hf : WordsEncoded q disk source f) (k : Fin K) :
    counts q key source n (recordBlocks q n) disk k =
      ∑ i : Fin n, if key (encode q.w (by have := q.word_width; omega) (f i) 1)=k
        then 1 else 0 := by
  rw [counts_eq_word_sum q key source n _ disk hs k]
  have hc : 3*n≤recordBlocks q n*q.block := by
    rw [recordBlocks_eq_words]
    exact LayoutConversion.blockCount_covers (3*n) q.block (block_positive q)
  rw [keyword_sum n _ hc (fun j => key (CommonMarginTransform.wordAt q disk source j)=k)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show i.val*3+1=i.val*3+(1 : Fin 3).val from rfl,hf]

theorem filter_length_sum {α : Type*} (xs : List α) (p : α → Bool) :
    (xs.filter p).length=(xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp [hp,ih,Nat.add_comm]

theorem counts_eq_bucket_length (q : Configuration) (key : Word q.w → Fin K)
    (source n : ℕ) (disk : Disk q) (keys payloads : Fin n → Word q.w)
    (hs : source+recordBlocks q n≤q.N^q.exponent)
    (hf : WordsEncoded q disk source (fun i => Record.data (keys i) (payloads i)))
    (k : Fin K) :
    counts q key source n (recordBlocks q n) disk k =
      (BucketMachine.bucket key (List.ofFn keys) k).length := by
  rw [counts_eq_key_sum q key source n disk _ hs hf k]
  rw [BucketMachine.bucket,filter_length_sum,List.map_ofFn,List.sum_ofFn]
  simp [encode]

/-- The same count can be read as a bucket of full records; payloads are
retained rather than replaced by their key words. -/
theorem counts_eq_record_bucket_length (q : Configuration) (key : Word q.w → Fin K)
    (source n : ℕ) (disk : Disk q) (f : Records q n)
    (hs : source+recordBlocks q n≤q.N^q.exponent)
    (hf : WordsEncoded q disk source f) (k : Fin K) :
    counts q key source n (recordBlocks q n) disk k =
      (BucketMachine.bucket
        (fun r => key (encode q.w (by have := q.word_width; omega) r 1))
        (List.ofFn f) k).length := by
  rw [counts_eq_key_sum q key source n disk f hs hf k]
  rw [BucketMachine.bucket,filter_length_sum,List.map_ofFn,List.sum_ofFn]
  simp only [beq_iff_eq,Function.comp_apply]

end
end CodedSorting.CommonMSDCountSemantics
end CountSemantics
