import CodedSorting.Sorting.Radix.Framework.ChunkRows

section Layout
/-! Canonical key-major, row-minor enumeration of the actual row-directory
entries. Every controller interval is obtained from those stored fields. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDNodeLayout
open CommonSortingNormalization (Configuration)
open CommonRecordProgram CommonMSDChunks CommonMSDRowDirectory
open CommonMSDDirectorySemantics BucketMachine WordControl KeyRecordWords
open CommonLeafProgram (Disk)
noncomputable section
variable {K : ℕ}

def rowRecords (q : Configuration) {n : ℕ} (f : Records q n)
    (j : Fin (chunkCount q n)) : Records q (CommonMSDChunkRows.row q n j).length :=
  slice (CommonMSDChunkRows.row q n j).offset (CommonMSDChunkRows.row q n j).length
    (CommonMSDChunkRows.row q n j).fits f

def rowsList (q : Configuration) {n : ℕ} (f : Records q n) : List (List (Record q.w)) :=
  List.ofFn (fun j => List.ofFn (rowRecords q f j))

def rowLengths (q : Configuration) (key : Word q.w → Fin K) {n : ℕ}
    (f : Records q n) (j : Fin (chunkCount q n)) : Fin K → ℕ :=
  lengths q key (rowRecords q f j)

def slot (q : Configuration) (n K : ℕ) (i : Fin (K*chunkCount q n)) :
    Fin K × Fin (chunkCount q n) := finProdFinEquiv.symm i

def layout (q : Configuration) (n K source directory target : ℕ) :
    CommonMSDGatherController.Layout (K*chunkCount q n) where
  source := fun _ => source
  offset := fun i => 3*(CommonMSDChunkRows.row q n (slot q n K i).2).offset
  directory := fun i => CommonMSDRowDirectoryBatch.target q K directory (slot q n K i).2.val
  entry := fun i => (slot q n K i).1.val
  target := target

def fragment (q : Configuration) (key : Word q.w → Fin K) {n : ℕ}
    (f : Records q n) (i : Fin (K*chunkCount q n)) : List (Record q.w) :=
  bucket (recordKey q key) (List.ofFn (rowRecords q f (slot q n K i).2)) (slot q n K i).1

def start (q : Configuration) (key : Word q.w → Fin K) {n : ℕ}
    (f : Records q n) (i : Fin (K*chunkCount q n)) : ℕ :=
  3*((CommonMSDChunkRows.row q n (slot q n K i).2).offset+
    CommonMSDDirectory.start (rowLengths q key f (slot q n K i).2) (slot q n K i).1)

def count (q : Configuration) (key : Word q.w → Fin K) {n : ℕ}
    (f : Records q n) (i : Fin (K*chunkCount q n)) : ℕ :=
  3*rowLengths q key f (slot q n K i).2 (slot q n K i).1

theorem lengths_sum (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) : (∑ k : Fin K,lengths q key f k)=n := by
  have h := total_bucket_lengths (recordKey q key) (List.ofFn f)
  simpa only [←List.ofFn_eq_map,List.sum_ofFn,List.length_ofFn,lengths] using h

theorem start_length_le (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) (k : Fin K) :
    CommonMSDDirectory.start (lengths q key f) k+lengths q key f k≤n := by
  calc
    _ = ∑ j : Fin K, ((if j<k then lengths q key f j else 0)+
        (if j=k then lengths q key f j else 0)) := by
      simp [CommonMSDDirectory.start,Finset.sum_add_distrib]
    _ ≤ ∑ j : Fin K,lengths q key f j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases he : j=k
      · subst j;simp
      · by_cases hlt : j<k
        · rw [if_pos hlt,if_neg he,Nat.add_zero]
        · rw [if_neg hlt,if_neg he];omega
    _ = n := lengths_sum q key f

theorem extent_le (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) (i : Fin (K*chunkCount q n)) :
    start q key f i+count q key f i≤3*n := by
  have h := start_length_le q key (rowRecords q f (slot q n K i).2) (slot q n K i).1
  have hr := (CommonMSDChunkRows.row q n (slot q n K i).2).fits
  unfold start count rowLengths
  omega

theorem total_count (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) :
    CommonMSDGatherSequence.total (count q key f) (List.finRange (K*chunkCount q n))=3*n := by
  unfold CommonMSDGatherSequence.total
  rw [←List.ofFn_eq_map,List.sum_ofFn]
  have he : (∑ p : Fin K × Fin (chunkCount q n),
      3*rowLengths q key f p.2 p.1)=∑ i : Fin (K*chunkCount q n),count q key f i := by
    apply Fintype.sum_equiv finProdFinEquiv
    intro p
    simp only [count,slot,Equiv.symm_apply_apply]
  rw [←he,Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [←Finset.mul_sum,rowLengths,lengths_sum]
  have hv := CommonMSDChunkRows.volume_eq q n
  simp only [CommonMSDRowDirectoryBatch.volume,←List.ofFn_eq_map,List.sum_ofFn] at hv
  rw [hv]

theorem plan (q : Configuration) (key : Word q.w → Fin K) {n : ℕ}
    (f : Records q n) (disk : Disk q) (source directory target : ℕ)
    (hstart : ∀ j : Fin (chunkCount q n),∀ k : Fin K,
      CommonMSDDirectory.entry q disk (CommonMSDRowDirectoryBatch.target q K directory j.val) k 0=
        CommonMSDDirectory.start (lengths q key (rowRecords q f j)) k)
    (hcount : ∀ j : Fin (chunkCount q n),∀ k : Fin K,
      CommonMSDDirectory.entry q disk (CommonMSDRowDirectoryBatch.target q K directory j.val) k 1=
        lengths q key (rowRecords q f j) k)
    (hsource : source+recordBlocks q n+2≤target)
    (hdir : directory+chunkCount q n*CommonMSDDirectory.blocks q K≤target)
    (hcap : target+2*PhysicalStreamCursor.blockCount q.block (3*n)+2≤q.N^q.exponent) :
    CommonMSDGatherComparison.Plan q (layout q n K source directory target) (3*n)
      disk (start q key f) (count q key f) := by
  have ht : target≤q.N^q.exponent := by omega
  refine ⟨?_,?_,?_,?_,?_,hcap⟩
  · intro i
    simp only [layout,CommonMSDDirectoryRead.stored_entry,hstart,start,rowLengths]
    ring
  · intro i
    simp only [layout,CommonMSDDirectoryRead.stored_entry,hcount,count,rowLengths]
  · intro i
    let j := (slot q n K i).2
    let k := (slot q n K i).1
    have he := CommonMSDDirectoryBounds.covered_end q k.val
    have hc : CommonMSDDirectoryRead.offset q k.val+2*q.digits≤(K*2)*q.digits := by
      have hk := k.isLt
      unfold CommonMSDDirectoryRead.offset
      nlinarith
    have hb := CommonMSDGatherSequence.blockCount_mono q.block _ _ hc
    change _≤CommonMSDDirectory.blocks q K at hb
    have hrow := CommonMSDRowDirectoryBatch.target_end q (K:=K) (base:=directory) j
    change CommonMSDRowDirectoryBatch.target q K directory j.val+
      CommonMSDDirectoryRead.offset q k.val/q.block+CommonMSDDirectoryRead.blocks q k.val≤target
    omega
  · intro i
    have he := extent_le q key f i
    have hb := CommonMSDGatherSequence.blockCount_mono q.block _ _ he
    rw [←CommonRecordEncoding.recordBlocks_eq_words] at hb
    change source+_+2≤target
    omega
  · intro i
    have he := extent_le q key f i
    omega

theorem prepared_rows (q : Configuration) (n : ℕ) (f : Records q n) :
    rowsList q (operation q n f)=CommonMSDSemantics.prepare q.height
      (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (List.ofFn f) := by
  apply List.ext_getElem
  · simp only [rowsList,List.length_ofFn,CommonMSDSemantics.prepare,ExternalMSD.sortedChunks,
      List.length_map,pack_count,List.length_ofFn,chunkCount,chunkSize,PhysicalStreamCursor.blockCount]
  · intro j hj hk
    simp only [rowsList,List.getElem_ofFn]
    rw [show List.ofFn (rowRecords q (operation q n f) ⟨j,by simpa [rowsList] using hj⟩)=_
      from CommonMSDChunkRows.operation_row q n f ⟨j,by simpa [rowsList] using hj⟩]
    exact List.getD_eq_getElem _ _ hk

private theorem child_length_ofFn {α : Type*} {J : ℕ} (key : α → Fin K)
    (rows : Fin J → List α) (k : Fin K) :
    (ExternalMSD.child key (List.ofFn rows) k).length=
      ∑ j : Fin J,(bucket key (rows j) k).length := by
  simp only [ExternalMSD.child,List.length_flatMap,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem child_length (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) (k : Fin K) :
    (ExternalMSD.child (recordKey q key) (rowsList q f) k).length=
      ∑ j : Fin (chunkCount q n),rowLengths q key f j k := by
  exact child_length_ofFn (recordKey q key) (fun j => List.ofFn (rowRecords q f j)) k

end
end CodedSorting.CommonMSDNodeLayout
end Layout

section Contents
/-! The canonical controller fragments encode exactly the key-major
concatenation of the live record buckets, including payload words. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDNodeContents
open CommonSortingNormalization (Configuration)
open CommonMSDNodeLayout CommonRecordProgram CommonRecordEncoding CommonMSDRowDirectory
open CommonMSDDirectorySemantics CommonMSDChunks KeyRecordWords WordControl BucketMachine
open CommonLeafProgram (Disk)
noncomputable section
variable {K : ℕ}

theorem fragment_slice (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) (i : Fin (K*chunkCount q n))
    (horder : (List.ofFn (rowRecords q f (slot q n K i).2)).Pairwise
      (fun x y => recordKey q key x≤recordKey q key y)) :
    ((List.ofFn f).drop
      ((CommonMSDChunkRows.row q n (slot q n K i).2).offset+
        CommonMSDDirectory.start (rowLengths q key f (slot q n K i).2) (slot q n K i).1)).take
      (rowLengths q key f (slot q n K i).2 (slot q n K i).1)=fragment q key f i := by
  have h := sorted_bucket_slice (recordKey q key)
    (List.ofFn (rowRecords q f (slot q n K i).2)) horder (slot q n K i).1
  change ((List.ofFn (rowRecords q f (slot q n K i).2)).drop
    (CommonMSDDirectory.start (rowLengths q key f (slot q n K i).2) (slot q n K i).1)).take
      (rowLengths q key f (slot q n K i).2 (slot q n K i).1)=_ at h
  have hsize := start_length_le q key (rowRecords q f (slot q n K i).2) (slot q n K i).1
  change CommonMSDDirectory.start (rowLengths q key f (slot q n K i).2) (slot q n K i).1+
    rowLengths q key f (slot q n K i).2 (slot q n K i).1≤_ at hsize
  rw [rowRecords,CommonMSDChunkRows.slice_list,List.drop_take,List.take_take,List.drop_drop] at h
  rw [Nat.min_eq_left (by omega)] at h
  simpa only [fragment,rowRecords,CommonMSDChunkRows.slice_list] using h

theorem words_at (q : Configuration) {n : ℕ} (f : Records q n) (i : Fin n) (j : Fin 3) :
    (words q.w (by have:=q.word_width;omega) (List.ofFn f)).getD (i.val*3+j.val) 0=
      encode q.w (by have:=q.word_width;omega) (f i) j := by
  rw [CommonLeafBatchCPU.words_ofFn_numeric]
  have hi : i.val*3+j.val<n*3 := by have:=i.isLt;have:=j.isLt;omega
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),List.getElem_ofFn]
  have he : (⟨i.val*3+j.val,hi⟩ : Fin (n*3))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    omega
  rw [he,Equiv.symm_apply_apply]

theorem slice_word (q : Configuration) {n : ℕ} (f : Records q n) (disk : Disk q)
    (source O L : ℕ) (hfit : O+L≤n) (hf : WordsEncoded q disk source f)
    (j : ℕ) (hj : j<3*L) :
    CommonMarginTransform.wordAt q disk source (3*O+j)=
      (words q.w (by have:=q.word_width;omega) (List.ofFn (slice O L hfit f))).getD j 0 := by
  let i : Fin L := ⟨j/3,by omega⟩
  let t : Fin 3 := ⟨j%3,by omega⟩
  have he : i.val*3+t.val=j := by dsimp only [i,t];omega
  rw [←he,words_at]
  have hh : 3*O+(i.val*3+t.val)=(O+i.val)*3+t.val := by ring
  rw [hh]
  exact hf ⟨O+i.val,by have:=i.isLt;omega⟩ t

theorem fragment_word (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) (disk : Disk q) (source : ℕ)
    (hf : WordsEncoded q disk source f) (i : Fin (K*chunkCount q n))
    (horder : (List.ofFn (rowRecords q f (slot q n K i).2)).Pairwise
      (fun x y => recordKey q key x≤recordKey q key y))
    (j : ℕ) (hj : j<count q key f i) :
    CommonMarginTransform.wordAt q disk source (start q key f i+j)=
      (words q.w (by have:=q.word_width;omega) (fragment q key f i)).getD j 0 := by
  let O := (CommonMSDChunkRows.row q n (slot q n K i).2).offset+
    CommonMSDDirectory.start (rowLengths q key f (slot q n K i).2) (slot q n K i).1
  let L := rowLengths q key f (slot q n K i).2 (slot q n K i).1
  have hfit : O+L≤n := by
    have he := extent_le q key f i
    change 3*O+3*L≤3*n at he
    omega
  have hslice : List.ofFn (slice O L hfit f)=fragment q key f i :=
    (CommonMSDChunkRows.slice_list q O L hfit f).trans (fragment_slice q key f i horder)
  have hw := slice_word q f disk source O L hfit hf j hj
  rwa [hslice] at hw

private theorem ofFn_product {α : Type*} (K J : ℕ) (F : Fin K → Fin J → α) :
    List.ofFn (fun i : Fin (K*J) => F (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)=
      (List.ofFn (fun k => List.ofFn (F k))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext k
  apply congrArg List.ofFn
  funext j
  have he : (⟨k.val*J+j.val,by have:=k.isLt;have:=j.isLt;nlinarith⟩ : Fin (K*J))=
      finProdFinEquiv (k,j) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [he,Equiv.symm_apply_apply]

theorem fragments_gather (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) :
    (List.finRange (K*chunkCount q n)).flatMap (fragment q key f)=
      ExternalMSD.gather (recordKey q key) (rowsList q f) := by
  rw [List.flatMap,←List.ofFn_eq_map]
  change (List.ofFn (fun i => (fun k j =>
    bucket (recordKey q key) (List.ofFn (rowRecords q f j)) k)
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)).flatten=_
  rw [ofFn_product K (chunkCount q n)
    (fun k j => bucket (recordKey q key) (List.ofFn (rowRecords q f j)) k),List.flatten_flatten]
  simp only [ExternalMSD.gather,rowsList,List.flatMap,List.map_ofFn,
    ←List.ofFn_eq_map,Function.comp_apply]
  rfl

private theorem contents_lists (q : Configuration) {F : ℕ}
    (source start count : Fin F → ℕ) (disk : Disk q) (pieces : Fin F → List (Word q.w))
    (hlen : ∀ i,(pieces i).length=count i)
    (hword : ∀ i j,j<count i →
      CommonMarginTransform.wordAt q disk (source i) (start i+j)=(pieces i).getD j 0)
    (is : List (Fin F)) (j : ℕ) :
    CommonMSDGatherSequence.contents q source start count disk is j=
      (is.flatMap pieces).getD j 0 := by
  induction is generalizing j with
  | nil => simp [CommonMSDGatherSequence.contents]
  | cons i is ih =>
    rw [CommonMSDGatherSequence.contents,List.flatMap_cons]
    by_cases hj : j<count i
    · rw [if_pos hj,List.getD_append _ _ _ _ (by rw [hlen];exact hj)]
      exact hword i j hj
    · rw [if_neg hj,List.getD_append_right _ _ _ _ (by rw [hlen];omega),hlen,ih]

theorem contents_gather (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) (disk : Disk q) (source directory target : ℕ)
    (hf : WordsEncoded q disk source f)
    (horder : ∀ r : Fin (chunkCount q n),(List.ofFn (rowRecords q f r)).Pairwise
      (fun x y => recordKey q key x≤recordKey q key y)) (j : ℕ) :
    CommonMSDGatherSequence.contents q (layout q n K source directory target).source
      (start q key f) (count q key f) disk (List.finRange (K*chunkCount q n)) j=
      (words q.w (by have:=q.word_width;omega)
        (ExternalMSD.gather (recordKey q key) (rowsList q f))).getD j 0 := by
  have he := contents_lists q (layout q n K source directory target).source
    (start q key f) (count q key f) disk
    (fun i => words q.w (by have:=q.word_width;omega) (fragment q key f i))
    (fun i => show (words q.w (by have:=q.word_width;omega) (fragment q key f i)).length=
      count q key f i from words_length _ _ _)
    (fun i j hj => fragment_word q key f disk source hf i (horder _) j hj)
    (List.finRange (K*chunkCount q n)) j
  rw [he]
  rw [←fragments_gather]
  simp only [words,List.flatMap_assoc]

private theorem total_lengths {α : Type*} {F : ℕ} (pieces : Fin F → List α)
    (is : List (Fin F)) :
    CommonMSDGatherSequence.total (fun i => 3*(pieces i).length) is=
      3*(is.flatMap pieces).length := by
  simp only [CommonMSDGatherSequence.total,List.length_flatMap,List.sum_map_mul_left,Function.comp_apply]

theorem gather_length (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) :
    (ExternalMSD.gather (recordKey q key) (rowsList q f)).length=n := by
  have ht := total_count q key f
  have he := total_lengths (fragment q key f) (List.finRange (K*chunkCount q n))
  change CommonMSDGatherSequence.total (count q key f) _=_ at he
  rw [fragments_gather] at he
  omega

def gatherRecords (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) : Records q n := fun i =>
  (ExternalMSD.gather (recordKey q key) (rowsList q f))[i.val]'(by
    rw [gather_length]
    exact i.isLt)

theorem gatherRecords_list (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) :
    List.ofFn (gatherRecords q key f)=ExternalMSD.gather (recordKey q key) (rowsList q f) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,gather_length]
  · intro i hi hj
    simp only [List.getElem_ofFn,gatherRecords]

/-- The word-level postcondition of the actual gather controller entails
the original bit-level record encoding, with every payload preserved. -/
theorem encoded_gather (q : Configuration) (key : Word q.w → Fin K)
    {n : ℕ} (f : Records q n) (before after : Disk q) (source directory target : ℕ)
    (hf : WordsEncoded q before source f)
    (horder : ∀ r : Fin (chunkCount q n),(List.ofFn (rowRecords q f r)).Pairwise
      (fun x y => recordKey q key x≤recordKey q key y))
    (ht : target+recordBlocks q n≤q.N^q.exponent)
    (hcopy : ∀ j,j<3*n → CommonMarginTransform.wordAt q after target j=
      CommonMSDGatherSequence.contents q (layout q n K source directory target).source
        (start q key f) (count q key f) before (List.finRange (K*chunkCount q n)) j) :
    Encoded q after target (gatherRecords q key f) := by
  apply (encoded_iff_words q after target _ ht).2
  intro i j
  rw [hcopy _ (by have:=i.isLt;have:=j.isLt;omega),
    contents_gather q key f before source directory target hf horder,
    ←gatherRecords_list q key f,words_at]

end
end CodedSorting.CommonMSDNodeContents
end Contents

section Semantic
/-! The concrete full-key row sort and stored-word radix directory yield
exactly the children in the already proved MSD recursion. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDNodeSemantic
open CommonSortingNormalization (Configuration)
open CommonRecordProgram CommonMSDChunks CommonMSDNodeLayout CommonMSDNodeContents
open CommonMSDRecordDigits CommonMSDDirectorySemantics CommonMSDSemantics
open KeyRecordWords WordControl BucketMachine
noncomputable section

def children (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    {n : ℕ} (f : Records q n) : Fin base → List (Record q.w) :=
  CommonMSDChildren.nodeChildren CommonWordMSD.key base hb q.height
    (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort fuel (List.ofFn f)

theorem child_eq (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    {n : ℕ} (f : Records q n) (ho : OrdinaryList (List.ofFn f)) (k : Fin base) :
    ExternalMSD.child (recordKey q (wordDigit q base hb fuel))
      (rowsList q (operation q n f)) k=children q base hb fuel f k := by
  rw [prepared_rows]
  change ExternalMSD.child _ _ k=ExternalMSD.child _ _ k
  unfold ExternalMSD.child
  apply List.flatMap_congr
  intro row hr
  exact bucket_eq q base hb fuel row (prepare_row_ordinary q (List.ofFn f) ho row hr) k

theorem row_order (q : Configuration) (base : ℕ) (hb : 0<base) (fuel p : ℕ)
    {n : ℕ} (f : Records q n) (ho : OrdinaryList (List.ofFn f))
    (hp : Prefix CommonWordMSD.key base (fuel+1) p (List.ofFn f))
    (j : Fin (chunkCount q n)) :
    (List.ofFn (rowRecords q (operation q n f) j)).Pairwise
      (fun x y => recordKey q (wordDigit q base hb fuel) x≤
        recordKey q (wordDigit q base hb fuel) y) :=
  prepare_stored_digit_sorted q base hb fuel p (List.ofFn f) ho hp _
    (CommonMSDChunkRows.operation_row_mem q n f j)

/-- The actual row-directory fields sum to the exact child size. -/
theorem child_count (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    {n : ℕ} (f : Records q n) (ho : OrdinaryList (List.ofFn f)) (k : Fin base) :
    (∑ j : Fin (chunkCount q n),rowLengths q (wordDigit q base hb fuel) (operation q n f) j k)=
      (children q base hb fuel f k).length := by
  rw [←CommonMSDNodeLayout.child_length,child_eq q base hb fuel f ho k]

/-- Prefix sums of those actual counts give the child offset in records. -/
theorem child_start (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    {n : ℕ} (f : Records q n) (ho : OrdinaryList (List.ofFn f)) (k : Fin base) :
    CommonMSDDirectory.start
      (fun l => ∑ j : Fin (chunkCount q n),
        rowLengths q (wordDigit q base hb fuel) (operation q n f) j l) k=
      (CommonMSDChildren.front (children q base hb fuel f) k.val).length := by
  simp_rw [child_count q base hb fuel f ho]
  exact (CommonMSDChildren.front_length_start (children q base hb fuel f) k).symm

theorem output_list (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    {n : ℕ} (f : Records q n) (ho : OrdinaryList (List.ofFn f)) :
    List.ofFn (gatherRecords q (wordDigit q base hb fuel) (operation q n f))=
      (List.finRange base).flatMap (children q base hb fuel f) := by
  rw [gatherRecords_list]
  change (List.finRange base).flatMap (ExternalMSD.child _ _)=_
  apply List.flatMap_congr
  intro k _
  exact child_eq q base hb fuel f ho k

theorem children_perm (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    {n : ℕ} (f : Records q n) :
    ((List.finRange base).flatMap (children q base hb fuel f)).Perm (List.ofFn f) :=
  (ExternalMSD.gather_perm _ _).trans
    (CommonMSDSemantics.prepare_perm CommonWordMSD.key q.height
      (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (record_local_correct q.w) _)

theorem output_ordinary (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    {n : ℕ} (f : Records q n) (ho : OrdinaryList (List.ofFn f)) :
    OrdinaryList (List.ofFn (gatherRecords q (wordDigit q base hb fuel) (operation q n f))) := by
  rw [output_list q base hb fuel f ho]
  exact perm_ordinary (children_perm q base hb fuel f) ho

theorem child_ordinary (q : Configuration) (base : ℕ) (hb : 0<base) (fuel : ℕ)
    {n : ℕ} (f : Records q n) (ho : OrdinaryList (List.ofFn f)) (k : Fin base) :
    OrdinaryList (children q base hb fuel f k) := by
  intro r hr
  exact ho r ((children_perm q base hb fuel f).mem_iff.mp
    (List.mem_flatMap.mpr ⟨k,by simp,hr⟩))

theorem child_prefix (q : Configuration) (base : ℕ) (hb : 0<base) (fuel p : ℕ)
    {n : ℕ} (f : Records q n)
    (hp : Prefix CommonWordMSD.key base (fuel+1) p (List.ofFn f)) (k : Fin base) :
    Prefix CommonWordMSD.key base fuel (p*base+k.val) (children q base hb fuel f k) :=
  CommonMSDSemantics.child_prefix CommonWordMSD.key base hb fuel p _
    (prepare_prefix CommonWordMSD.key base (fuel+1) p q.height
      (CommonLocalRecursion.height_pos q) CommonWordMSD.localSort (record_local_correct q.w) _ hp) k

end
end CodedSorting.CommonMSDNodeSemantic
end Semantic
