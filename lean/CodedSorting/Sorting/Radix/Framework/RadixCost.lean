import CodedSorting.Sorting.Radix.Framework.Chunks

section ChunkCost
/-! Scan overhead and the final short chunk preserve the proved local
sorting rate. This bounds the charge of the actual common-machine program. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace CodedSorting.CommonMSDChunks
open CommonSortingNormalization CommonRecordProgram
open CommonGroupedLeafCost CommonLocalBudgetRate
noncomputable section

theorem padded_size_le (q : Configuration) (n : ℕ) :
    paddedSize q n≤n+chunkSize q := by
  exact LocalSortingCost.blockCount_capacity (chunkSize q) (chunk_positive q) n

theorem block_le_chunk (q : Configuration) : q.block≤chunkSize q := by
  have hh := CommonLocalRecursion.height_pos q
  have hb := CommonLocalRecursion.block_le_height q
  dsimp only [chunkSize]
  nlinarith

theorem charge_bound_of_local (q : Configuration) (n L : ℕ)
    (hn : chunkSize q≤n)
    (hlocal : CommonLocalBudget.budget q 3 (chunkSize q)*q.block≤L*(chunkSize q+q.block)) :
    charge q n*q.block≤(4*L+129)*n := by
  let C := chunkCount q n
  let R := chunkSize q
  let M := paddedSize q n
  have hpad : C*R≤2*n := by
    have h := padded_size_le q n
    change C*R≤n+R at h
    omega
  have hBR : q.block≤R := block_le_chunk q
  have hBn : q.block≤n := hBR.trans hn
  have hc : recordBlocks q R*q.block≤3*R+q.block := by
    rw [recordBlocks_eq]
    exact LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) _
  have hchunk : C*recordBlocks q R*q.block≤8*n := by
    have h := Nat.mul_le_mul_left C hc
    have h' := Nat.mul_le_mul_left C hBR
    nlinarith only [h,h',hpad]
  have hpm : recordBlocks q M*q.block≤7*n := by
    have h := LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) (3*M)
    rw [←recordBlocks_eq] at h
    change recordBlocks q M*q.block≤3*(C*R)+q.block at h
    omega
  have hin : recordBlocks q n*q.block≤4*n := by
    have h := LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) (3*n)
    rw [←recordBlocks_eq] at h
    omega
  have hkids : C*CommonLocalBudget.budget q 3 R*q.block≤4*L*n := by
    have h := Nat.mul_le_mul_left C hlocal
    have h' := Nat.mul_le_mul_left C hBR
    have h'' := Nat.mul_le_mul_left L (show C*(R+q.block)≤4*n by nlinarith only [h',hpad])
    change C*(CommonLocalBudget.budget q 3 R*q.block)≤C*(L*(R+q.block)) at h
    nlinarith only [h,h'']
  change (3*recordBlocks q M+C*(CommonLocalBudget.budget q 3 R+12*recordBlocks q R)+
    3*recordBlocks q n)*q.block≤_
  nlinarith only [hpm,hchunk,hin,hkids]

/-- Uniform actual preparation charge per record at an MSD node larger
than the local threshold. -/
theorem integer_charge_bound (q : Configuration) (n : ℕ)
    (hn : chunkSize q≤n)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block) :
    charge q n*q.block≤
      (4*(22194000000*(GlobalSortingBound.localRate q.height K
        (Real.log ((q.height : ℝ)/q.block)) tau+2))+129)*n := by
  apply charge_bound_of_local q n _ hn
  exact CommonLocalBudgetRate.integer_bound q (chunkSize q) (chunk_positive q) le_rfl hnormal

end
end CodedSorting.CommonMSDChunks
end ChunkCost

section DirectorySemantics
/-! The directory written by the actual machine contains the lengths and
prefix starts of the actual input-record buckets, not a supplied histogram. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDDirectorySemantics
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonRecordEncoding CommonMSDDirectory CommonMSDDirectoryScan
open CommonLeafProgram (Store Disk machine)
open KeyRecordWords WordControl
noncomputable section
variable {K : ℕ}

def recordKey (q : Configuration) (key : Word q.w → Fin K) : Record q.w → Fin K :=
  fun r => key (encode q.w (by have := q.word_width; omega) r 1)

def lengths (q : Configuration) (key : Word q.w → Fin K) {n : ℕ}
    (f : Records q n) : Fin K → ℕ :=
  fun k => (BucketMachine.bucket (recordKey q key) (List.ofFn f) k).length

theorem counts_eq_lengths (q : Configuration) (key : Word q.w → Fin K)
    (source n : ℕ) (disk : Disk q) (f : Records q n)
    (hs : source+recordBlocks q n≤q.N^q.exponent)
    (hf : WordsEncoded q disk source f) :
    counts q key source n (recordBlocks q n) disk=lengths q key f := by
  funext k
  exact CommonMSDCountSemantics.counts_eq_record_bucket_length q key source n disk f hs hf k

theorem raw_complete (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ)
    (s : Store q) (disk : Disk q) (f : Records q n)
    (hs : source+recordBlocks q n≤q.N^q.exponent)
    (ht : target+blocks q K≤q.N^q.exponent)
    (hc : recordBlocks q n*q.block<(2^q.w)^q.digits)
    (hf : WordsEncoded q disk source f) :
    ∃ (final : Store q) (out : Disk q),
      executeRaw q (code q hfit key source n target) (machine q s disk)=
        (machine q final out,recordBlocks q n+blocks q K) ∧
      (∀ k : Fin K, entry q out target k 0=start (lengths q key f) k) ∧
      (∀ k : Fin K, entry q out target k 1=lengths q key f k) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+blocks q K≤a.val → out a=disk a) := by
  simpa only [counts_eq_lengths q key source n disk f hs hf] using
    CommonMSDDirectory.raw_complete q hfit key source n target s disk hs ht hc

/-- Directory meanings, I/O, halt, frame, and resident-memory bound all
refer to the same concrete finite-disk execution. -/
theorem complete (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ)
    (s : Store q) (disk : Disk q) (f : Records q n)
    (hs : source+recordBlocks q n≤q.N^q.exponent)
    (ht : target+blocks q K≤q.N^q.exponent)
    (hc : recordBlocks q n*q.block<(2^q.w)^q.digits)
    (hf : Encoded q disk source f)
    (hsize : (code q hfit key source n target).length≤q.N^q.exponent)
    (hpc : pc q (pack s)=0) :
    let program := code q hfit key source n target
    let result := ControlledNormalization.runLogical (CommonStaticSchedule.policy q program)
      program.length (machine q s disk)
    CommonStaticSchedule.policy q program result.1.ram=none ∧
    result.2=recordBlocks q n+blocks q K ∧
    (∀ k : Fin K, entry q result.1.disk target k 0=start (lengths q key f) k) ∧
    (∀ k : Fin K, entry q result.1.disk target k 1=lengths q key f k) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+blocks q K≤a.val →
      result.1.disk a=disk a) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  have hw := (encoded_iff_words q disk source f hs).1 hf
  simpa only [counts_eq_lengths q key source n disk f hs hw] using
    CommonMSDDirectory.complete q hfit key source n target s disk hs ht hc hsize hpc

private theorem bucket_start_cons {α : Type*} (key : α → Fin K)
    (a : α) (xs : List α) (k : Fin K) :
    start (fun j => (BucketMachine.bucket key (a::xs) j).length) k =
      (if key a<k then 1 else 0)+start (fun j => (BucketMachine.bucket key xs j).length) k := by
  have hb (j : Fin K) : (BucketMachine.bucket key (a::xs) j).length=
      (if key a=j then 1 else 0)+(BucketMachine.bucket key xs j).length := by
    by_cases he : key a=j <;> simp [BucketMachine.bucket,he,Nat.add_comm]
  change (∑ j : Fin K, if j<k then (BucketMachine.bucket key (a::xs) j).length else 0)=_
  simp_rw [hb]
  calc
    _ = (∑ j : Fin K,if key a=j then (if j<k then 1 else 0) else 0)+
        ∑ j : Fin K,if j<k then (BucketMachine.bucket key xs j).length else 0 := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j<k <;> by_cases he : key a=j <;> simp [hj,he]
    _ = _ := by simp [start]

private theorem bucket_start_zero {α : Type*} (key : α → Fin K)
    (xs : List α) (k : Fin K) (hs : ∀ x∈xs,k≤key x) :
    start (fun j => (BucketMachine.bucket key xs j).length) k=0 := by
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j<k
  · have he : BucketMachine.bucket key xs j=[] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hn : key x≠j := ne_of_gt (lt_of_lt_of_le hj (hs x hx))
      simpa using hn
    simp [hj,he]
  · simp [hj]

/-- For a row sorted by its current digit, the computed prefix start and
bucket length specify its literal contiguous input interval. -/
theorem sorted_bucket_slice {α : Type*} (key : α → Fin K) (xs : List α)
    (hs : xs.Pairwise (fun x y => key x≤key y)) (k : Fin K) :
    (xs.drop (start (fun j => (BucketMachine.bucket key xs j).length) k)).take
      (BucketMachine.bucket key xs k).length=BucketMachine.bucket key xs k := by
  induction xs with
  | nil => simp [start,BucketMachine.bucket]
  | cons a xs ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    by_cases hlt : key a<k
    · have hne : key a≠k := ne_of_lt hlt
      rw [bucket_start_cons,if_pos hlt]
      rw [Nat.one_add,List.drop_succ_cons]
      simpa [hlt,hne,BucketMachine.bucket] using ih htail
    · by_cases heq : key a=k
      · have hzero := bucket_start_zero key xs k (fun x hx => by
          simpa only [heq] using hhead x hx)
        have hi := ih htail
        rw [hzero,List.drop_zero] at hi
        rw [bucket_start_cons,if_neg hlt,Nat.zero_add,hzero,List.drop_zero]
        simpa [BucketMachine.bucket,heq] using congrArg (List.cons a) hi
      · have hgreater : k<key a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
        have he : BucketMachine.bucket key (a::xs) k=[] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          have hax : key a≤key x := by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact le_rfl
            · exact hhead x hx
          have hn : key x≠k := ne_of_gt (lt_of_lt_of_le hgreater hax)
          simpa using hn
        rw [he]
        simp

/-- These are the exact source slices described by the directory entries
produced during this execution. -/
theorem complete_slices (q : Configuration)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w → Fin K) (source n target : ℕ)
    (s : Store q) (disk : Disk q) (f : Records q n)
    (hs : source+recordBlocks q n≤q.N^q.exponent)
    (ht : target+blocks q K≤q.N^q.exponent)
    (hc : recordBlocks q n*q.block<(2^q.w)^q.digits)
    (hf : Encoded q disk source f)
    (horder : (List.ofFn f).Pairwise (fun x y => recordKey q key x≤recordKey q key y))
    (hsize : (code q hfit key source n target).length≤q.N^q.exponent)
    (hpc : pc q (pack s)=0) :
    let program := code q hfit key source n target
    let result := ControlledNormalization.runLogical (CommonStaticSchedule.policy q program)
      program.length (machine q s disk)
    ∀ k : Fin K,
      ((List.ofFn f).drop (entry q result.1.disk target k 0)).take
        (entry q result.1.disk target k 1)=BucketMachine.bucket (recordKey q key) (List.ofFn f) k := by
  have hh := complete q hfit key source n target s disk f hs ht hc hf hsize hpc
  dsimp only at hh ⊢
  intro k
  rw [hh.2.2.1 k,hh.2.2.2.1 k]
  exact sorted_bucket_slice (recordKey q key) (List.ofFn f) horder k

end
end CodedSorting.CommonMSDDirectorySemantics
end DirectorySemantics

section SemanticCost
/-! Cost composition for recursive sorting by successive groups of key digits. The local-sort and preparation costs come from the common-machine programs; the gather cost is an explicit parameter of the composition theorem. 


-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonMSDSemanticCost
open CommonMSDSemantics ExternalMSD BucketMachine
variable {α : Type*}

/-- This accounting follows the very child lists of `CommonMSDSemantics.sort`.
`nodeCharge` covers preparation and gathering at each nonterminal node. -/
def budget (key : α → ℕ) (base : ℕ) (hb : 0<base) (H : ℕ) (hH : 0<H)
    (localSort : List α → List α) (localCharge nodeCharge : ℕ → ℕ) :
    ℕ → List α → ℕ
  | 0,_ => 0
  | fuel+1,xs =>
      if xs.length≤H^2 then localCharge xs.length
      else nodeCharge xs.length+
        ((List.finRange base).map fun k =>
          budget key base hb H hH localSort localCharge nodeCharge fuel
            (child (CommonMSDSemantics.digit key base hb fuel)
              (CommonMSDSemantics.prepare H hH localSort xs) k)).sum

private theorem sum_affine_bound {β : Type*} (items : List β)
    (f size : β → ℕ) (B C D : ℕ)
    (h : ∀ x∈items,f x*B≤C*size x+D) :
    (items.map f).sum*B≤C*(items.map size).sum+D*items.length := by
  induction items with
  | nil => simp
  | cons x rest ih =>
    have hx := h x (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- One startup allowance per child is absorbed by `base*B≤H²<n`.
No scan bound is inserted for the overall recursion. -/
theorem budget_depth_bound (key : α → ℕ) (base : ℕ) (hb : 0<base)
    (B H : ℕ) (hH : 0<H) (hBH : B≤H) (hbase : base≤H)
    (localSort : List α → List α) (hc : LocalCorrect key localSort)
    (localCharge nodeCharge : ℕ → ℕ) (L A : ℕ)
    (hl : ∀ n,n≤H^2 → localCharge n*B≤L*(n+B))
    (ha : ∀ n,H^2<n → nodeCharge n*B≤A*n)
    (fuel : ℕ) (xs : List α) :
    budget key base hb H hH localSort localCharge nodeCharge fuel xs*B≤
      ((A+L)*fuel+L)*xs.length+L*B := by
  induction fuel generalizing xs with
  | zero => simp [budget]
  | succ fuel ih =>
    rw [budget]
    split
    · rename_i hsmall
      have hh := hl xs.length hsmall
      have hm := Nat.mul_le_mul_right xs.length
        (show L≤(A+L)*(fuel+1)+L by omega)
      nlinarith only [hh,hm]
    · rename_i hlarge
      have hnode := ha xs.length (by omega)
      have hKB : base*B≤xs.length := by
        have hmul := Nat.mul_le_mul hbase hBH
        nlinarith only [hmul,show H^2<xs.length by omega]
      have hchildren := sum_affine_bound (List.finRange base)
        (fun k => budget key base hb H hH localSort localCharge nodeCharge fuel
          (child (CommonMSDSemantics.digit key base hb fuel)
            (CommonMSDSemantics.prepare H hH localSort xs) k))
        (fun k => (child (CommonMSDSemantics.digit key base hb fuel)
          (CommonMSDSemantics.prepare H hH localSort xs) k).length)
        B ((A+L)*fuel+L) (L*B) (fun k _ => ih _)
      rw [children_volume,(CommonMSDSemantics.prepare_perm key H hH localSort hc xs).length_eq,
        List.length_finRange] at hchildren
      have hstart := Nat.mul_le_mul_left L hKB
      nlinarith only [hnode,hchildren,hstart]

open CommonSortingNormalization
noncomputable section

/-- Exactly the integer local rate established for the actual Round-14
machine, with its three-word records and all movement overhead. -/
def localRate (q : Configuration) : ℕ :=
  22194000000*(GlobalSortingBound.localRate q.height CommonLocalBudgetRate.K
    (Real.log ((q.height : ℝ)/q.block)) CommonLocalBudgetRate.tau+2)

theorem actual_local_charge (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (n : ℕ) (hn : n≤q.height^2) :
    CommonLocalBudget.budget q 3 n*q.block≤localRate q*(n+q.block) := by
  by_cases hz : n=0
  · subst n
    rw [CommonLocalBudget.budget_small q 3 0 (Nat.zero_le _)]
    have he : CommonRecordProgram.recordBlocks q 0=0 := by
      rw [CommonRecordEncoding.recordBlocks_eq_words]
      simp [PhysicalStreamCursor.blockCount,CommonLeafProgram.block_positive q]
    rw [he]
    have hL : 1≤localRate q := by unfold localRate; omega
    simpa using Nat.mul_le_mul_right q.block hL
  · exact CommonLocalBudgetRate.integer_bound q n (by omega) hn hnormal

/-- Actual chunk preparation plus a separately verified gather charge has
one linear nonterminal budget. The gather implementation is not assumed here. -/
theorem actual_node_charge (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (gatherCharge : ℕ → ℕ) (G : ℕ)
    (hg : ∀ n,q.height^2<n → gatherCharge n*q.block≤G*n)
    (n : ℕ) (hn : q.height^2<n) :
    (CommonMSDChunks.charge q n+gatherCharge n)*q.block≤(4*localRate q+129+G)*n := by
  have hprep := CommonMSDChunks.integer_charge_bound q n (by exact Nat.le_of_lt hn) hnormal
  have hgat := hg n hn
  change CommonMSDChunks.charge q n*q.block≤(4*localRate q+129)*n at hprep
  nlinarith only [hprep,hgat]

/-- This is a bound for the semantic recursion using the actual local and
preparation budgets. Connecting the remaining gather/controller execution
is still required before interpreting it as a complete machine theorem. -/
theorem actual_budget_depth (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (gatherCharge : ℕ → ℕ) (G : ℕ)
    (hg : ∀ n,q.height^2<n → gatherCharge n*q.block≤G*n)
    (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) :
    budget CommonWordMSD.key q.height (CommonLocalRecursion.height_pos q)
      q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
      (CommonLocalBudget.budget q 3) (fun n => CommonMSDChunks.charge q n+gatherCharge n)
      fuel xs*q.block≤
      ((5*localRate q+129+G)*fuel+localRate q)*xs.length+localRate q*q.block := by
  have h := budget_depth_bound CommonWordMSD.key q.height (CommonLocalRecursion.height_pos q)
    q.block q.height (CommonLocalRecursion.height_pos q)
    (CommonLocalRecursion.block_le_height q) le_rfl CommonWordMSD.localSort
    (record_local_correct q.w) (CommonLocalBudget.budget q 3)
    (fun n => CommonMSDChunks.charge q n+gatherCharge n)
    (localRate q) (4*localRate q+129+G)
    (actual_local_charge q hnormal) (actual_node_charge q hnormal gatherCharge G hg) fuel xs
  have he : 4*localRate q+129+G+localRate q=5*localRate q+129+G := by ring
  simpa only [he] using h

end
end CodedSorting.CommonMSDSemanticCost
end SemanticCost

section RecordDigits
/-! The physical directory reads the stored key word. For ordinary input
records this is exactly the original key used by the MSD semantics. Top
and bottom sentinels are confined to local padding; permutation proofs
ensure they do not appear in the returned live records. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDRecordDigits
open CommonSortingNormalization CommonRecordProgram KeyRecordWords WordControl
open CommonMSDSemantics CommonMSDDirectorySemantics BucketMachine
noncomputable section

/-- An input record has a genuine key and payload, rather than a sentinel. -/
def Ordinary {w : ℕ} (r : Record w) : Prop := ∃ k x,r=Record.data k x

def OrdinaryList {w : ℕ} (xs : List (Record w)) : Prop := ∀ r∈xs,Ordinary r

theorem ordinary_key_lt {w : ℕ} (r : Record w) (hr : Ordinary r) :
    CommonWordMSD.key r<2^w := by
  obtain ⟨k,x,rfl⟩ := hr
  exact k.isLt

def wordDigit (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ) :
    Word q.w→Fin base := fun x => MSD.digit base hb fuel x.val

theorem record_digit_eq (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    (r : Record q.w) (hr : Ordinary r) :
    recordKey q (wordDigit q base hb fuel) r=
      CommonMSDSemantics.digit CommonWordMSD.key base hb fuel r := by
  obtain ⟨k,x,rfl⟩ := hr
  simp [recordKey,wordDigit,CommonMSDSemantics.digit,CommonWordMSD.key,encode]

theorem perm_ordinary {w : ℕ} {xs ys : List (Record w)}
    (hp : ys.Perm xs) (ho : OrdinaryList xs) : OrdinaryList ys :=
  fun r hr => ho r (hp.mem_iff.mp hr)

theorem local_ordinary {w : ℕ} (xs : List (Record w)) (ho : OrdinaryList xs) :
    OrdinaryList (CommonWordMSD.localSort xs) :=
  perm_ordinary (CommonWordMSD.localSort_perm xs) ho

theorem prepare_ordinary (q : Configuration) (xs : List (Record q.w))
    (ho : OrdinaryList xs) :
    OrdinaryList (CommonMSDSemantics.prepare q.height (CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort xs).flatten :=
  perm_ordinary (CommonMSDSemantics.prepare_perm CommonWordMSD.key q.height
    (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
    (record_local_correct q.w) xs) ho

theorem prepare_row_ordinary (q : Configuration) (xs : List (Record q.w))
    (ho : OrdinaryList xs) (row : List (Record q.w))
    (hr : row∈CommonMSDSemantics.prepare q.height (CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort xs) : OrdinaryList row := by
  intro r hmem
  exact prepare_ordinary q xs ho r (List.mem_flatten.mpr ⟨row,hr,hmem⟩)

theorem chunks_ordinary (q : Configuration) (n : ℕ) (f : Records q n)
    (ho : OrdinaryList (List.ofFn f)) :
    OrdinaryList (List.ofFn (CommonMSDChunks.operation q n f)) :=
  perm_ordinary (CommonMSDChunksSemantic.operation_perm q n f) ho

theorem bucket_eq (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    (xs : List (Record q.w)) (ho : OrdinaryList xs) (k : Fin base) :
    bucket (recordKey q (wordDigit q base hb fuel)) xs k=
      bucket (CommonMSDSemantics.digit CommonWordMSD.key base hb fuel) xs k := by
  apply List.filter_congr
  intro r hr
  rw [record_digit_eq q base hb fuel r (ho r hr)]

theorem lengths_eq (q : Configuration) (base : ℕ) (hb : 0<base) (fuel n : ℕ)
    (f : Records q n) (ho : OrdinaryList (List.ofFn f)) :
    lengths q (wordDigit q base hb fuel) f=
      fun k => (bucket (CommonMSDSemantics.digit CommonWordMSD.key base hb fuel)
        (List.ofFn f) k).length := by
  funext k
  exact congrArg List.length (bucket_eq q base hb fuel (List.ofFn f) ho k)

/-- Thus an actual directory scan of a returned live row sees its current
MSD digits in sorted order, even though local sorting retains full keys. -/
theorem prepare_stored_digit_sorted (q : Configuration) (base : ℕ) (hb : 0<base)
    (fuel p : ℕ) (xs : List (Record q.w)) (ho : OrdinaryList xs)
    (hp : Prefix CommonWordMSD.key base (fuel+1) p xs)
    (row : List (Record q.w))
    (hr : row∈CommonMSDSemantics.prepare q.height (CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort xs) :
    row.Pairwise (fun x y => recordKey q (wordDigit q base hb fuel) x≤
      recordKey q (wordDigit q base hb fuel) y) := by
  have hs := prepare_digit_sorted CommonWordMSD.key base hb fuel p q.height
    (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
    (record_local_correct q.w) xs hp row hr
  have hord := prepare_row_ordinary q xs ho row hr
  apply hs.imp_of_mem
  intro x y hx hy hxy
  simpa only [record_digit_eq q base hb fuel x (hord x hx),
    record_digit_eq q base hb fuel y (hord y hy)] using hxy

/-- The stored-key directory's contiguous source intervals are precisely
those of the semantic MSD buckets, without assuming sentinel key equality. -/
theorem prepare_bucket_slice (q : Configuration) (base : ℕ) (hb : 0<base)
    (fuel p : ℕ) (xs : List (Record q.w)) (ho : OrdinaryList xs)
    (hp : Prefix CommonWordMSD.key base (fuel+1) p xs)
    (row : List (Record q.w))
    (hr : row∈CommonMSDSemantics.prepare q.height (CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort xs) (k : Fin base) :
    (row.drop (CommonMSDDirectory.start
      (fun j => (bucket (CommonMSDSemantics.digit CommonWordMSD.key base hb fuel) row j).length) k)).take
      (bucket (CommonMSDSemantics.digit CommonWordMSD.key base hb fuel) row k).length=
        bucket (CommonMSDSemantics.digit CommonWordMSD.key base hb fuel) row k := by
  have hs := prepare_stored_digit_sorted q base hb fuel p xs ho hp row hr
  have h := sorted_bucket_slice (recordKey q (wordDigit q base hb fuel)) row hs k
  simpa only [bucket_eq q base hb fuel row (prepare_row_ordinary q xs ho row hr)] using h

end
end CodedSorting.CommonMSDRecordDigits
end RecordDigits

section RowDirectory
/-! Directory construction for a row beginning at an arbitrary record
offset. The row is physically copied to aligned scratch before scanning;
no free rebasing of a block-unaligned row is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonMSDRowDirectory
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonRecordEncoding CommonMarginTransform
open CommonLeafProgram (Machine Disk)
noncomputable section
variable {K : ℕ}

def slice {q : Configuration} {n : ℕ} (O L : ℕ) (h : O+L≤n)
    (f : Records q n) : Records q L := fun i => f ⟨O+i.val,by have:=i.isLt;omega⟩

theorem copy_encoded (q : Configuration) (reader : Fin q.inventory.readers)
    {n : ℕ} (O L source scratch : ℕ) (hrow : O+L≤n)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hs : source+recordBlocks q n+2≤scratch)
    (ht : scratch+recordBlocks q L≤q.N^q.exponent) :
    Encoded q
      (executeRaw q (CommonIntervalCopy.code q reader (3*O) 0 (3*L) source scratch) s).1.disk
      scratch (slice O L hrow f) := by
  have hmono : recordBlocks q (O+L)≤recordBlocks q n :=
    CommonFinitePadding.count_mono q (Nat.mul_le_mul_right _ hrow)
  have hc : PhysicalStreamCursor.blockCount q.block (3*O+3*L)=recordBlocks q (O+L) := by
    rw [recordBlocks_eq_words,Nat.mul_add]
  have hp : CommonIntervalCopy.pages q 0 (3*L)=recordBlocks q L := by
    simp only [CommonIntervalCopy.pages,Nat.zero_mod,Nat.zero_add,recordBlocks_eq_words]
  have hin := (encoded_iff_words q s.disk source f (by omega)).1 hf
  apply (encoded_iff_words q _ scratch _ ht).2
  intro i j
  have hi : 3*i.val+j.val<3*L := by have:=i.isLt;have:=j.isLt;omega
  have hword := CommonIntervalCopyBounds.raw_word q reader (3*O) 0 (3*L) source scratch s
    (by rw [hc];omega) (by simpa only [Nat.zero_div,hp,Nat.add_zero] using ht)
    (Or.inl (by rw [hc,Nat.zero_div,Nat.add_zero];exact (Nat.add_le_add_right (Nat.add_le_add_left hmono source) 2).trans hs))
    (3*i.val+j.val) (by
      have h := word_fits q L scratch (3*i.val+j.val) ht hi
      exact h)
  simp only [Nat.zero_le,Nat.zero_add,Nat.sub_zero,true_and,if_pos hi] at hword
  rw [show i.val*3+j.val=3*i.val+j.val by omega,hword]
  have he : 3*O+(3*i.val+j.val)=(O+i.val)*3+j.val := by ring
  rw [he]
  exact hin ⟨O+i.val,by have:=i.isLt;omega⟩ j

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (O L source scratch target : ℕ) : List (Instruction q) :=
  CommonIntervalCopy.code q reader (3*O) 0 (3*L) source scratch ++
    CommonMSDDirectory.code q hfit key scratch L target

theorem pages_zero (q : Configuration) (L : ℕ) :
    CommonIntervalCopy.pages q 0 (3*L)=recordBlocks q L := by
  simp only [CommonIntervalCopy.pages,Nat.zero_mod,Nat.zero_add,recordBlocks_eq_words]

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (O L source scratch target : ℕ) :
    ∀ i∈code q reader hfit key O L source scratch target,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact CommonIntervalCopy.code_safe q reader _ _ _ _ _ i hi
  · exact CommonMSDDirectory.code_safe q hfit key _ _ _ i hi

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (O L source scratch target : ℕ) :
    (code q reader hfit key O L source scratch target).length=
      7*recordBlocks q L+2*CommonMSDDirectory.blocks q K+2 := by
  rw [code,List.length_append,CommonIntervalCopy.code_length,pages_zero,CommonMSDDirectory.code_length]
  omega

theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (O L source scratch target : ℕ)
    (hs : scratch+recordBlocks q L≤q.N^q.exponent)
    (ht : target+CommonMSDDirectory.blocks q K≤q.N^q.exponent) :
    cost q (code q reader hfit key O L source scratch target)=
      7*recordBlocks q L+CommonMSDDirectory.blocks q K := by
  rw [code,CommonPermutationPairs.cost_append,CommonIntervalCopy.code_cost,pages_zero,
    CommonMSDDirectory.code_cost q hfit key scratch L target hs ht]
  omega

theorem raw_complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) {n : ℕ} (O L source scratch target : ℕ)
    (hrow : O+L≤n) (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hs : source+recordBlocks q n+2≤scratch)
    (hst : scratch+recordBlocks q L≤target)
    (ht : target+CommonMSDDirectory.blocks q K≤q.N^q.exponent)
    (hc : recordBlocks q L*q.block<(2^q.w)^q.digits) :
    let out := (executeRaw q (code q reader hfit key O L source scratch target) s).1.disk
    (∀ k : Fin K,CommonMSDDirectory.entry q out target k 0=
      CommonMSDDirectory.start (CommonMSDDirectorySemantics.lengths q key (slice O L hrow f)) k) ∧
    (∀ k : Fin K,CommonMSDDirectory.entry q out target k 1=
      CommonMSDDirectorySemantics.lengths q key (slice O L hrow f) k) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<scratch ∨ scratch+recordBlocks q L≤a.val) →
      (a.val<target ∨ target+CommonMSDDirectory.blocks q K≤a.val) → out a=s.disk a) := by
  let mid := (executeRaw q (CommonIntervalCopy.code q reader (3*O) 0 (3*L) source scratch) s).1
  have hmid : Encoded q mid.disk scratch (slice O L hrow f) :=
    copy_encoded q reader O L source scratch hrow s f hf hs (by omega)
  obtain ⟨final,out,hr,hstart,hcount,hframe⟩ :=
    CommonMSDDirectorySemantics.raw_complete q hfit key scratch L target
      (unpack mid.ram) mid.disk (slice O L hrow f) (by omega) ht hc
      ((encoded_iff_words q mid.disk scratch _ (by omega)).1 hmid)
  rw [CommonBlockPair.machine_eta q mid] at hr
  change (∀ k,CommonMSDDirectory.entry q
      (executeRaw q (code q reader hfit key O L source scratch target) s).1.disk target k 0=_) ∧ _
  rw [code,CommonPermutationPairs.raw_append]
  change (∀ k,CommonMSDDirectory.entry q
      (executeRaw q (CommonMSDDirectory.code q hfit key scratch L target) mid).1.disk target k 0=_) ∧ _
  rw [hr]
  refine ⟨hstart,hcount,?_⟩
  intro a ha hb
  change out a=s.disk a
  rw [hframe a hb]
  have hmono : recordBlocks q (O+L)≤recordBlocks q n :=
    CommonFinitePadding.count_mono q (Nat.mul_le_mul_right _ hrow)
  have he : PhysicalStreamCursor.blockCount q.block (3*O+3*L)=recordBlocks q (O+L) := by
    rw [recordBlocks_eq_words,Nat.mul_add]
  have hcopy := CommonIntervalCopy.raw q reader (3*O) 0 (3*L) source scratch s
    (by simpa only [Nat.zero_div,Nat.add_zero,pages_zero] using
      (show scratch+recordBlocks q L≤q.N^q.exponent by omega))
    (CommonIntervalCopyBounds.readsOutside q (3*O) 0 (3*L) source scratch
      (by rw [he];omega) (Or.inl (by rw [he,Nat.zero_div,Nat.add_zero];omega)))
  exact hcopy.outside a (by simpa only [Nat.zero_div,Nat.add_zero,Nat.zero_add,pages_zero] using ha)

theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) {n : ℕ} (O L source scratch target : ℕ)
    (hrow : O+L≤n) (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hs : source+recordBlocks q n+2≤scratch)
    (hst : scratch+recordBlocks q L≤target)
    (ht : target+CommonMSDDirectory.blocks q K≤q.N^q.exponent)
    (hc : recordBlocks q L*q.block<(2^q.w)^q.digits)
    (hsize : 7*recordBlocks q L+2*CommonMSDDirectory.blocks q K+2≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := code q reader hfit key O L source scratch target
    let result := ControlledNormalization.runLogical (policy q p) p.length s
    (∀ k : Fin K,CommonMSDDirectory.entry q result.1.disk target k 0=
      CommonMSDDirectory.start (CommonMSDDirectorySemantics.lengths q key (slice O L hrow f)) k) ∧
    (∀ k : Fin K,CommonMSDDirectory.entry q result.1.disk target k 1=
      CommonMSDDirectorySemantics.lengths q key (slice O L hrow f) k) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<scratch ∨ scratch+recordBlocks q L≤a.val) →
      (a.val<target ∨ target+CommonMSDDirectory.blocks q K≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p result.1.ram=none ∧
    result.2=7*recordBlocks q L+CommonMSDDirectory.blocks q K ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hcost,hm⟩ := run_code_disk q (code q reader hfit key O L source scratch target)
    (by rw [code_length];exact hsize) (code_safe q reader hfit key O L source scratch target) s hpc
  obtain ⟨hstart,hcount,hframe⟩ := raw_complete q reader hfit key O L source scratch target
    hrow s f hf hs hst ht hc
  refine ⟨?_,?_,?_,hh,?_,hm⟩
  · simpa only [hd] using hstart
  · simpa only [hd] using hcount
  · simpa only [hd] using hframe
  · exact hcost.trans (code_cost q reader hfit key O L source scratch target (by omega) ht)

end
end CodedSorting.CommonMSDRowDirectory
end RowDirectory

section RadixCost
/-! Apply the recursive cost formula to the radix used by the node programs. The theorem takes the stated node-cost bound and the correspondence with the global controller as hypotheses. 

-/
set_option autoImplicit false
namespace CodedSorting.CommonMSDRadixCost
open CommonSortingNormalization CommonMSDParameters CommonMSDSemanticCost
noncomputable section

def radixPositive (q : Configuration) : 0<radix q := lt_of_lt_of_le (by decide : 0<2) (radix_two q)

def depth (q : Configuration) : ℕ := GlobalSortingBound.depth (radix q) q.w

theorem depth_covers (q : Configuration) : 2^q.w≤radix q^depth q :=
  GlobalSortingBound.depth_covers (radix q) q.w (radix_two q)

theorem depth_log_bound (q : Configuration) :
    (depth q : ℝ)≤(q.w : ℝ)*Real.log 2/Real.log (radix q : ℝ)+1 :=
  GlobalSortingBound.depth_log_bound (radix q) q.w (radix_two q)

theorem semantic_correct (q : Configuration) (xs : List (KeyRecordWords.Record q.w))
    (ho : CommonMSDRecordDigits.OrdinaryList xs) :
    (CommonMSDSemantics.recordSort q.w (radix q) (radixPositive q) q.height
      (CommonLocalRecursion.height_pos q) (depth q) xs).Perm xs ∧
    (CommonMSDSemantics.recordSort q.w (radix q) (radixPositive q) q.height
      (CommonLocalRecursion.height_pos q) (depth q) xs).Pairwise
        (fun x y => CommonWordMSD.key x≤CommonWordMSD.key y) := by
  apply CommonMSDSemantics.recordSort_correct
  intro x hx
  exact (CommonMSDRecordDigits.ordinary_key_lt x (ho x hx)).trans_le (depth_covers q)

theorem budget_bound (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio RecursiveExchange.radix 1 Parameters.W≤q.height/q.block)
    (nodeExtraCharge : ℕ→ℕ) (G : ℕ)
    (hg : ∀ n,q.height^2<n → nodeExtraCharge n*q.block≤G*n)
    (fuel : ℕ) (xs : List (KeyRecordWords.Record q.w)) :
    budget CommonWordMSD.key (radix q) (radixPositive q)
      q.height (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort
      (CommonLocalBudget.budget q 3) (fun n => CommonMSDChunks.charge q n+nodeExtraCharge n)
      fuel xs*q.block≤
      ((5*localRate q+129+G)*fuel+localRate q)*xs.length+localRate q*q.block := by
  have h := budget_depth_bound CommonWordMSD.key (radix q) (radixPositive q)
    q.block q.height (CommonLocalRecursion.height_pos q)
    (CommonLocalRecursion.block_le_height q) (radix_le_height q) CommonWordMSD.localSort
    (CommonMSDSemantics.record_local_correct q.w) (CommonLocalBudget.budget q 3)
    (fun n => CommonMSDChunks.charge q n+nodeExtraCharge n)
    (localRate q) (4*localRate q+129+G)
    (actual_local_charge q hnormal) (actual_node_charge q hnormal nodeExtraCharge G hg) fuel xs
  have he : 4*localRate q+129+G+localRate q=5*localRate q+129+G := by ring
  simpa only [he] using h

end
end CodedSorting.CommonMSDRadixCost
end RadixCost

section PublicWordBounds
/-! The word-width upper bound used for the sorting rate also supplies
a fixed natural coefficient for the polynomial capacity estimates. -/
set_option autoImplicit false
namespace CodedSorting.CommonMSDPublicWordBounds
open CommonSortingNormalization
noncomputable section

def wordFactor (κ : ℝ) : ℕ := max 1 ⌈κ⌉₊

theorem factor_one (κ : ℝ) : 1≤wordFactor κ := Nat.le_max_left _ _

theorem factor_covers (κ : ℝ) : κ≤(wordFactor κ : ℝ) :=
  (Nat.le_ceil κ).trans (Nat.cast_le.mpr (Nat.le_max_right _ _))

theorem log_nat_le (N : ℕ) (hN : 0<N) :
    Real.log (N : ℝ)≤(N : ℝ)*Real.log 2 := by
  have hnR : (0 : ℝ)<N := by exact_mod_cast hN
  have hp : (N : ℝ)≤(2 : ℝ)^N := by exact_mod_cast (Nat.le_of_lt N.lt_two_pow_self)
  have hh := Real.log_le_log hnR hp
  simpa only [Real.log_pow] using hh

/-- The input-dependent word length is bounded with a coefficient chosen
solely from the fixed public word-width convention. -/
theorem word_linear (q : Configuration) (κ : ℝ)
    (hword : (q.w : ℝ)*Real.log 2≤κ*Real.log (q.N : ℝ)) :
    q.w≤wordFactor κ*q.N := by
  have hN : 0<q.N := by have:=q.input_large;omega
  have hlog : 0≤Real.log (q.N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤q.N by omega))
  have hκ := mul_le_mul_of_nonneg_right (factor_covers κ) hlog
  have hl := mul_le_mul_of_nonneg_left (log_nat_le q.N hN)
    (Nat.cast_nonneg (wordFactor κ) : (0 : ℝ)≤wordFactor κ)
  have h2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hwR : (q.w : ℝ)≤(wordFactor κ : ℝ)*(q.N : ℝ) := by
    nlinarith only [hword,hκ,hl,h2]
  exact_mod_cast hwR

end
end CodedSorting.CommonMSDPublicWordBounds
end PublicWordBounds

section RadixLogBounds
/-! The directory-aware radix loses only a descriptor-dependent constant
in logarithmic depth. No additional memory threshold is needed: K>=2
and H<4dK already compare log K with log H. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonMSDRadixLogBounds
open CommonSortingNormalization CommonMSDParameters
noncomputable section

def factor (q : Configuration) : ℝ := 1+Real.log (4*(q.digits : ℝ))/Real.log 2

theorem height_le (q : Configuration) : q.height≤4*q.digits*radix q := by
  have hd:=digits_positive q
  have hk:=radix_two q
  have hh:=Nat.lt_mul_div_succ q.height (show 0<2*q.digits by omega)
  change q.height<2*q.digits*(radix q+1) at hh
  have hm:=Nat.mul_le_mul_left (2*q.digits) (show radix q+1≤2*radix q by omega)
  nlinarith

theorem height_two (q : Configuration) : 2≤q.height :=
  (radix_two q).trans (radix_le_height q)

theorem factor_one (q : Configuration) : 1≤factor q := by
  have hd : (1:ℝ)≤q.digits := by exact_mod_cast digits_positive q
  have hl : 0≤Real.log (4*(q.digits : ℝ)) := Real.log_nonneg (by linarith)
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  unfold factor
  exact le_add_of_nonneg_right (div_nonneg hl h2.le)

theorem log_height (q : Configuration) :
    Real.log (q.height : ℝ)≤factor q*Real.log (radix q : ℝ) := by
  have hd : (0:ℝ)<q.digits := by exact_mod_cast digits_positive q
  have hk : (1:ℝ)<radix q := by exact_mod_cast radix_two q
  have hH : (0:ℝ)<q.height := by exact_mod_cast (show 0<q.height by have:=height_two q;omega)
  have hbound : (q.height : ℝ)≤4*(q.digits : ℝ)*(radix q : ℝ) := by exact_mod_cast height_le q
  have hh := Real.log_le_log hH hbound
  rw [Real.log_mul (by positivity : 4*(q.digits : ℝ)≠0) (by linarith : (radix q : ℝ)≠0)] at hh
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (2:ℝ)≤Real.log (radix q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast radix_two q)
  have hdlog : 0≤Real.log (4*(q.digits : ℝ)) :=
    Real.log_nonneg (by
      have hdn : (1:ℝ)≤q.digits := by exact_mod_cast digits_positive q
      linarith)
  have hm := mul_le_mul_of_nonneg_left hlog (div_nonneg hdlog h2.le)
  rw [div_mul_cancel₀ _ h2.ne'] at hm
  unfold factor
  nlinarith only [hh,hm]

/-- Replacing radix H by floor(H/(2d)) changes the depth coefficient,
while retaining the denominator log H needed for exponent cancellation. -/
theorem depth_bound (q : Configuration) (κ z : ℝ)
    (hword : (q.w : ℝ)*Real.log 2≤κ*z) :
    (CommonMSDRadixCost.depth q : ℝ)+1≤2+(κ*factor q)*z/Real.log (q.height : ℝ) := by
  have hk : 0<Real.log (radix q : ℝ) :=
    Real.log_pos (by exact_mod_cast radix_two q)
  have hH : 0<Real.log (q.height : ℝ) :=
    Real.log_pos (by exact_mod_cast height_two q)
  have hD : 0≤factor q := (by linarith [factor_one q])
  have hw : 0≤(q.w : ℝ)*Real.log 2 := by positivity
  have hr : (q.w : ℝ)*Real.log 2/Real.log (radix q : ℝ)≤
      factor q*((q.w : ℝ)*Real.log 2)/Real.log (q.height : ℝ) := by
    apply (div_le_div_iff₀ hk hH).2
    have h := mul_le_mul_of_nonneg_left (log_height q) hw
    nlinarith only [h]
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hword hD) hH.le
  have hc := CommonMSDRadixCost.depth_log_bound q
  have he : factor q*(κ*z)/Real.log (q.height : ℝ)=
      (κ*factor q)*z/Real.log (q.height : ℝ) := by ring
  rw [he] at hm
  linarith

end
end CodedSorting.CommonMSDRadixLogBounds
end RadixLogBounds
