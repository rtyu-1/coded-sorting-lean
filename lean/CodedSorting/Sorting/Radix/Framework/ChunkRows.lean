import CodedSorting.Sorting.Radix.Framework.RadixCost
import Mathlib.Data.List.GetD

section RowDirectoryBatch
/-! All publicly delimited rows are copied and scanned successively on
one disk. Directory slots are disjoint; one aligned scratch row is reused. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace CodedSorting.CommonMSDRowDirectoryBatch
open WordControl CommonSortingNormalization CommonStaticSchedule CommonRecordProgram
open CommonPermutationPairs CommonRecordEncoding CommonMSDRowDirectory
open CommonLeafProgram (Machine Disk)
noncomputable section

structure Row (n : ℕ) where
  offset : ℕ
  length : ℕ
  fits : offset+length≤n

def target (q : Configuration) (K base c : ℕ) := base+c*CommonMSDDirectory.blocks q K

theorem target_end (q : Configuration) {K C base : ℕ} (c : Fin C) :
    target q K base c.val+CommonMSDDirectory.blocks q K≤base+C*CommonMSDDirectory.blocks q K := by
  have h := Nat.mul_le_mul_right (CommonMSDDirectory.blocks q K) (Nat.succ_le_of_lt c.isLt)
  unfold target
  nlinarith

theorem target_disjoint (q : Configuration) {K C base : ℕ} (c d : Fin C) (hne : c≠d)
    {a : ℕ} (ha : target q K base c.val≤a) (hb : a<target q K base c.val+CommonMSDDirectory.blocks q K) :
    a<target q K base d.val ∨ target q K base d.val+CommonMSDDirectory.blocks q K≤a := by
  have hv : c.val≠d.val := fun h => hne (Fin.ext h)
  unfold target at *
  rcases lt_or_gt_of_ne hv with h|h
  · have ht := Nat.mul_le_mul_right (CommonMSDDirectory.blocks q K) (Nat.succ_le_of_lt h)
    left;nlinarith
  · have ht := Nat.mul_le_mul_right (CommonMSDDirectory.blocks q K) (Nat.succ_le_of_lt h)
    right;nlinarith

theorem encoded_of_disk_eq (q : Configuration) {n source : ℕ} (f : Records q n)
    (before after : Disk q) (hs : source+recordBlocks q n≤q.N^q.exponent)
    (hf : Encoded q before source f)
    (he : ∀ a : Fin (q.N^q.exponent),source≤a.val →a.val<source+recordBlocks q n →after a=before a) :
    Encoded q after source f := by
  intro i
  have hi := bit_block_lt q i
  change i.val/width q<recordBlocks q n at hi
  have ha : (address q source (i.val/width q)).val=source+i.val/width q :=
    CommonColumnSplit.address_val q source _ (by omega)
  unfold readBit
  have hlo : source≤(address q source (i.val/width q)).val := by
    rw [ha]
    exact Nat.le_add_right _ _
  have hhi : (address q source (i.val/width q)).val<source+recordBlocks q n := by
    rw [ha]
    exact Nat.add_lt_add_left hi source
  rw [he _ hlo hhi]
  exact hf i

theorem entry_of_disk_eq (q : Configuration) {K base : ℕ} (before after : Disk q)
    (he : ∀ a : Fin (q.N^q.exponent),base≤a.val →a.val<base+CommonMSDDirectory.blocks q K →after a=before a)
    (k : Fin K) (field : Fin 2) :
    CommonMSDDirectory.entry q after base k field=CommonMSDDirectory.entry q before base k field := by
  apply congrArg decodeWords
  funext j
  unfold CommonMSDDirectory.entryWords CommonLeafLoad.diskWord
  split_ifs with ha
  · have hi : (k.val*2+field.val)*q.digits+j.val<(K*2)*q.digits := by
      have h := (finProdFinEquiv (finProdFinEquiv (k,field),j)).isLt
      simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.mul_left_comm,Nat.add_comm] using h
    have hp : ((k.val*2+field.val)*q.digits+j.val)/q.block<CommonMSDDirectory.blocks q K := by
      apply (PhysicalStreamCursor.cursor_live_iff q.block ((K*2)*q.digits) _
        (CommonLeafProgram.block_positive q)).2
      exact (Nat.div_mul_le_self _ _).trans_lt hi
    rw [he _ (by simp) (by dsimp;omega)]
  · rfl

def code (q : Configuration) (reader : Fin q.inventory.readers) {K C n : ℕ}
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (rows : Fin C→Row n) (source scratch directory : ℕ)
    (cs : List (Fin C)) : List (Instruction q) := cs.flatMap fun c =>
  CommonMSDRowDirectory.code q reader hfit key (rows c).offset (rows c).length source scratch
    (target q K directory c.val)

theorem raw_complete (q : Configuration) (reader : Fin q.inventory.readers) {K C n : ℕ}
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (rows : Fin C→Row n) (source scratch directory cap : ℕ)
    (hlen : ∀ c,(rows c).length≤cap)
    (hs : source+recordBlocks q n+2≤scratch)
    (hsc : scratch+recordBlocks q cap≤directory)
    (hd : directory+C*CommonMSDDirectory.blocks q K≤q.N^q.exponent)
    (hc : recordBlocks q cap*q.block<(2^q.w)^q.digits)
    (cs : List (Fin C)) (hcs : cs.Nodup) (s : Machine q) (f : Records q n)
    (hf : Encoded q s.disk source f) :
    let out := (executeRaw q (code q reader hfit key rows source scratch directory cs) s).1.disk
    Encoded q out source f ∧
    (∀ c∈cs,∀ k : Fin K,CommonMSDDirectory.entry q out (target q K directory c.val) k 0=
      CommonMSDDirectory.start (CommonMSDDirectorySemantics.lengths q key
        (slice (rows c).offset (rows c).length (rows c).fits f)) k) ∧
    (∀ c∈cs,∀ k : Fin K,CommonMSDDirectory.entry q out (target q K directory c.val) k 1=
      CommonMSDDirectorySemantics.lengths q key (slice (rows c).offset (rows c).length (rows c).fits f) k) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<scratch ∨ scratch+recordBlocks q cap≤a.val) →
      (∀ c∈cs,a.val<target q K directory c.val ∨
        target q K directory c.val+CommonMSDDirectory.blocks q K≤a.val) → out a=s.disk a) := by
  induction cs generalizing s with
  | nil => exact ⟨hf,by simp,by simp,by intros;rfl⟩
  | cons c cs ih =>
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hcs
    have hlen' : recordBlocks q (rows c).length≤recordBlocks q cap :=
      CommonFinitePadding.count_mono q (Nat.mul_le_mul_right _ (hlen c))
    have ht := target_end q (K:=K) (base:=directory) c
    have htd : directory≤target q K directory c.val := by unfold target;omega
    let mid := (executeRaw q (CommonMSDRowDirectory.code q reader hfit key
      (rows c).offset (rows c).length source scratch (target q K directory c.val)) s).1
    obtain ⟨hstart,hcount,hframe⟩ := CommonMSDRowDirectory.raw_complete q reader hfit key
      (rows c).offset (rows c).length source scratch (target q K directory c.val) (rows c).fits
      s f hf hs (by omega) (ht.trans hd) (by nlinarith)
    have hmid : Encoded q mid.disk source f := by
      apply encoded_of_disk_eq q f s.disk mid.disk (by omega) hf
      intro a ha hb
      exact hframe a (Or.inl (by omega)) (Or.inl (by omega))
    obtain ⟨hout,hstarts,hcounts,hframes⟩ := ih hnd mid hmid
    rw [code,List.flatMap_cons,raw_append]
    change Encoded q (executeRaw q (code q reader hfit key rows source scratch directory cs) mid).1.disk source f ∧ _
    have hold (field : Fin 2) (k : Fin K) :
        CommonMSDDirectory.entry q
          (executeRaw q (code q reader hfit key rows source scratch directory cs) mid).1.disk
          (target q K directory c.val) k field=
        CommonMSDDirectory.entry q mid.disk (target q K directory c.val) k field := by
      apply entry_of_disk_eq q
      intro a ha hb
      apply hframes a (Or.inr (by omega))
      intro d hdcs
      exact target_disjoint q c d (by intro he;subst d;exact hnot hdcs) ha hb
    refine ⟨hout,?_,?_,?_⟩
    · intro d hdmem k
      rcases List.mem_cons.mp hdmem with rfl|hdmem
      · exact (hold 0 k).trans (hstart k)
      · exact hstarts d hdmem k
    · intro d hdmem k
      rcases List.mem_cons.mp hdmem with rfl|hdmem
      · exact (hold 1 k).trans (hcount k)
      · exact hcounts d hdmem k
    · intro a ha hb
      change (executeRaw q (code q reader hfit key rows source scratch directory cs) mid).1.disk a=s.disk a
      rw [hframes a ha (fun d hdmem => hb d (by simp [hdmem]))]
      exact hframe a (by rcases ha with ha|ha;exact Or.inl ha;exact Or.inr (by omega))
        (hb c (by simp))

def rowBlocks (q : Configuration) {C n : ℕ} (rows : Fin C→Row n) (cs : List (Fin C)) : ℕ :=
  (cs.map (fun c => recordBlocks q (rows c).length)).sum

def volume {C n : ℕ} (rows : Fin C→Row n) (cs : List (Fin C)) : ℕ :=
  (cs.map (fun c => (rows c).length)).sum

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers) {K C n : ℕ}
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (rows : Fin C→Row n) (source scratch directory : ℕ)
    (cs : List (Fin C)) :
    ∀ i∈code q reader hfit key rows source scratch directory cs,RespectsPC q i := by
  intro i hi
  obtain ⟨c,_,hi⟩ := List.mem_flatMap.mp hi
  exact CommonMSDRowDirectory.code_safe q reader hfit key _ _ _ _ _ i hi

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers) {K C n : ℕ}
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (rows : Fin C→Row n) (source scratch directory : ℕ)
    (cs : List (Fin C)) :
    (code q reader hfit key rows source scratch directory cs).length=
      7*rowBlocks q rows cs+(2*CommonMSDDirectory.blocks q K+2)*cs.length := by
  induction cs with
  | nil => simp [code,rowBlocks]
  | cons c cs ih =>
    rw [code,List.flatMap_cons,List.length_append,CommonMSDRowDirectory.code_length]
    change _+(code q reader hfit key rows source scratch directory cs).length=_
    rw [ih]
    simp only [rowBlocks,List.map_cons,List.sum_cons,List.length_cons]
    ring

theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers) {K C n : ℕ}
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (rows : Fin C→Row n) (source scratch directory cap : ℕ)
    (hlen : ∀ c,(rows c).length≤cap)
    (hsc : scratch+recordBlocks q cap≤directory)
    (hd : directory+C*CommonMSDDirectory.blocks q K≤q.N^q.exponent)
    (cs : List (Fin C)) :
    cost q (code q reader hfit key rows source scratch directory cs)=
      7*rowBlocks q rows cs+CommonMSDDirectory.blocks q K*cs.length := by
  induction cs with
  | nil => simp [code,rowBlocks,cost]
  | cons c cs ih =>
    have hlen' : recordBlocks q (rows c).length≤recordBlocks q cap :=
      CommonFinitePadding.count_mono q (Nat.mul_le_mul_right _ (hlen c))
    have ht := target_end q (K:=K) (base:=directory) c
    rw [code,List.flatMap_cons,cost_append,CommonMSDRowDirectory.code_cost q reader hfit key
      (rows c).offset (rows c).length source scratch (target q K directory c.val) (by omega) (ht.trans hd)]
    change _+cost q (code q reader hfit key rows source scratch directory cs)=_
    rw [ih]
    simp only [rowBlocks,List.map_cons,List.sum_cons,List.length_cons]
    ring

theorem rowBlocks_bound (q : Configuration) {C n : ℕ} (rows : Fin C→Row n) (cs : List (Fin C)) :
    rowBlocks q rows cs*q.block≤3*volume rows cs+q.block*cs.length := by
  induction cs with
  | nil => simp [rowBlocks,volume]
  | cons c cs ih =>
    have h := LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) (3*(rows c).length)
    rw [←CommonGroupedLeafCost.recordBlocks_eq] at h
    simp only [rowBlocks,volume,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

/-- Row rounding, actual alignment copies and the persisted directory
remain linear in payload volume plus one directory per row. -/
theorem code_cost_bound (q : Configuration) (reader : Fin q.inventory.readers) {K C n : ℕ}
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (rows : Fin C→Row n) (source scratch directory cap : ℕ)
    (hlen : ∀ c,(rows c).length≤cap)
    (hsc : scratch+recordBlocks q cap≤directory)
    (hd : directory+C*CommonMSDDirectory.blocks q K≤q.N^q.exponent)
    (cs : List (Fin C)) :
    cost q (code q reader hfit key rows source scratch directory cs)*q.block≤
      21*volume rows cs+(8*q.block+2*K*q.digits)*cs.length := by
  rw [code_cost q reader hfit key rows source scratch directory cap hlen hsc hd cs]
  have hr := rowBlocks_bound q rows cs
  have hm := LocalSortingCost.blockCount_capacity q.block (CommonLeafProgram.block_positive q) ((K*2)*q.digits)
  change CommonMSDDirectory.blocks q K*q.block≤(K*2)*q.digits+q.block at hm
  have hmul := Nat.mul_le_mul_right cs.length hm
  nlinarith only [hr,hmul]

/-- Build every row directory using one actual finite-machine run. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers) {K C n : ℕ}
    (hfit : (K*2)*q.digits≤CommonExchangeLeaf.bankWords q)
    (key : Word q.w→Fin K) (rows : Fin C→Row n) (source scratch directory cap : ℕ)
    (hlen : ∀ c,(rows c).length≤cap)
    (hs : source+recordBlocks q n+2≤scratch)
    (hsc : scratch+recordBlocks q cap≤directory)
    (hd : directory+C*CommonMSDDirectory.blocks q K≤q.N^q.exponent)
    (hc : recordBlocks q cap*q.block<(2^q.w)^q.digits)
    (s : Machine q) (f : Records q n) (hf : Encoded q s.disk source f)
    (hsize : 7*rowBlocks q rows (List.finRange C)+(2*CommonMSDDirectory.blocks q K+2)*C≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := code q reader hfit key rows source scratch directory (List.finRange C)
    let result := ControlledNormalization.runLogical (policy q p) p.length s
    Encoded q result.1.disk source f ∧
    (∀ c : Fin C,∀ k : Fin K,CommonMSDDirectory.entry q result.1.disk (target q K directory c.val) k 0=
      CommonMSDDirectory.start (CommonMSDDirectorySemantics.lengths q key
        (slice (rows c).offset (rows c).length (rows c).fits f)) k) ∧
    (∀ c : Fin C,∀ k : Fin K,CommonMSDDirectory.entry q result.1.disk (target q K directory c.val) k 1=
      CommonMSDDirectorySemantics.lengths q key (slice (rows c).offset (rows c).length (rows c).fits f) k) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<scratch ∨ scratch+recordBlocks q cap≤a.val) →
      (a.val<directory ∨ directory+C*CommonMSDDirectory.blocks q K≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p result.1.ram=none ∧
    result.2=7*rowBlocks q rows (List.finRange C)+CommonMSDDirectory.blocks q K*C ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hDisk,hhalt,hcost,hm⟩ := run_code_disk q
    (code q reader hfit key rows source scratch directory (List.finRange C))
    (by rw [code_length,List.length_finRange];exact hsize)
    (code_safe q reader hfit key rows source scratch directory (List.finRange C)) s hpc
  obtain ⟨hout,hstarts,hcounts,hframes⟩ := raw_complete q reader hfit key rows source scratch directory cap
    hlen hs hsc hd hc (List.finRange C) (List.nodup_finRange C) s f hf
  refine ⟨?_,?_,?_,?_,hhalt,?_,hm⟩
  · simpa only [hDisk] using hout
  · intro c k
    simpa only [hDisk] using hstarts c (by simp) k
  · intro c k
    simpa only [hDisk] using hcounts c (by simp) k
  · intro a ha hb
    rw [hDisk]
    apply hframes a ha
    intro c _
    have ht := target_end q (K:=K) (base:=directory) c
    have hbase : directory≤target q K directory c.val := by unfold target;omega
    rcases hb with hb|hb
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · exact hcost.trans (by
      simpa only [List.length_finRange] using
        (code_cost q reader hfit key rows source scratch directory cap hlen hsc hd (List.finRange C)))

end
end CodedSorting.CommonMSDRowDirectoryBatch
end RowDirectoryBatch

section ChunkRows
/-! The public H² row descriptors partition exactly the live records.
Their slices after the actual chunk sorter are the rows of MSD.prepare. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace CodedSorting.CommonMSDChunkRows
open CommonSortingNormalization (Configuration)
open CommonMSDChunks CommonRecordProgram
open CommonMSDRowDirectoryBatch CommonMSDRowDirectory BucketMachine
noncomputable section

def row (q : Configuration) (n : ℕ) (j : Fin (chunkCount q n)) : Row n where
  offset := j.val*chunkSize q
  length := min (chunkSize q) (n-j.val*chunkSize q)
  fits := by
    have hj : j.val*chunkSize q<n :=
      (PhysicalStreamCursor.cursor_live_iff (chunkSize q) n j.val (chunk_positive q)).1 j.isLt
    omega

theorem length_le (q : Configuration) (n : ℕ) (j : Fin (chunkCount q n)) :
    (row q n j).length≤chunkSize q := Nat.min_le_left _ _

theorem count_le (q : Configuration) (n : ℕ) : chunkCount q n≤n := by
  apply LayoutConversion.blockCount_minimal _ _ _ (chunk_positive q)
  have h := Nat.mul_le_mul_left n (chunk_positive q)
  simpa only [Nat.mul_one] using h

theorem slice_list (q : Configuration) {n : ℕ} (O L : ℕ) (h : O+L≤n)
    (f : Records q n) :
    List.ofFn (slice O L h f)=((List.ofFn f).drop O).take L := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_take,List.getElem_drop,slice]

private theorem take_min_length {α : Type*} (xs : List α) (r : ℕ) :
    xs.take (min r xs.length)=xs.take r := by
  rw [←List.take_take,List.take_length]

theorem row_list_getD (q : Configuration) {α : Type} (xs : List α)
    (j : Fin (chunkCount q xs.length)) :
    (xs.drop (row q xs.length j).offset).take (row q xs.length j).length=
      (pack (chunkSize q) (chunk_positive q) xs).getD j.val [] := by
  rw [PhysicalRecursiveExchange.pack_getD]
  simp only [row,Nat.mul_comm (chunkSize q) j.val]
  have h := take_min_length (xs.drop (j.val*chunkSize q)) (chunkSize q)
  simpa only [List.length_drop] using h

theorem packed_rows (q : Configuration) {α : Type} (xs : List α) :
    List.ofFn (fun j : Fin (chunkCount q xs.length) =>
      (xs.drop (row q xs.length j).offset).take (row q xs.length j).length)=
        pack (chunkSize q) (chunk_positive q) xs := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,pack_count,chunkCount,PhysicalStreamCursor.blockCount]
  · intro i hi hj
    rw [List.getElem_ofFn,row_list_getD,List.getD_eq_getElem _ _ hj]

private theorem length_sum (r n J : ℕ) :
    (∑ j ∈ Finset.range J,min r (n-j*r))=n-(n-J*r) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ,ih,Nat.succ_mul]
    omega

theorem volume_eq (q : Configuration) (n : ℕ) :
    volume (row q n) (List.finRange (chunkCount q n))=n := by
  change ((List.finRange (chunkCount q n)).map
    (fun j => min (chunkSize q) (n-j.val*chunkSize q))).sum=n
  rw [←List.ofFn_eq_map,List.sum_ofFn,
    Fin.sum_univ_eq_sum_range (fun j => min (chunkSize q) (n-j*chunkSize q)),length_sum]
  have h := padded_covers q n
  unfold paddedSize at h
  omega

private theorem pack_full_prefix {α : Type*} (r : ℕ) (hr : 0<r)
    (front back : List α) (hf : front.length=r) :
    pack r hr (front++back)=front::pack r hr back := by
  cases front with
  | nil => simp only [List.length_nil] at hf;omega
  | cons a rest =>
    rw [List.cons_append,pack]
    change (a::rest++back).take r::pack r hr ((a::rest++back).drop r)=_
    rw [List.take_left' hf,List.drop_left' hf]

private theorem pack_single {α : Type*} (r : ℕ) (hr : 0<r)
    (xs : List α) (hpos : 0<xs.length) (hlen : xs.length≤r) : pack r hr xs=[xs] := by
  cases xs with
  | nil => simp at hpos
  | cons a rest =>
    rw [pack,List.take_of_length_le hlen,List.drop_eq_nil_of_le hlen,pack]

/-- Length-preserving per-chunk operations leave the same row boundaries. -/
theorem repack {α : Type*} (r : ℕ) (hr : 0<r) (F : List α → List α)
    (hF : ∀ xs,(F xs).length=xs.length) (xs : List α) :
    pack r hr (((pack r hr xs).map F).flatten)=(pack r hr xs).map F := by
  induction xs using pack.induct r hr with
  | case1 => simp [pack]
  | case2 a rest ih =>
    let xs := a::rest
    by_cases hshort : xs.length≤r
    · have hp := pack_single r hr xs (by simp [xs]) hshort
      have hfp := pack_single r hr (F xs) (by rw [hF];simp [xs]) (by rw [hF];exact hshort)
      change pack r hr (((pack r hr xs).map F).flatten)=(pack r hr xs).map F
      rw [hp]
      simpa using hfp
    · have hlong : r≤xs.length := by omega
      have hlen : (F (xs.take r)).length=r := by rw [hF,List.length_take,Nat.min_eq_left hlong]
      change pack r hr (((pack r hr (a::rest)).map F).flatten)=(pack r hr (a::rest)).map F
      rw [pack,List.map_cons,List.flatten_cons,pack_full_prefix r hr _ _ hlen,ih]

theorem operation_row (q : Configuration) (n : ℕ) (f : Records q n)
    (j : Fin (chunkCount q n)) :
    List.ofFn (slice (row q n j).offset (row q n j).length (row q n j).fits
      (operation q n f))=
      (CommonMSDSemantics.prepare q.height (CommonLocalRecursion.height_pos q)
        CommonWordMSD.localSort (List.ofFn f)).getD j.val [] := by
  rw [slice_list]
  change ((List.ofFn (operation q n f)).drop (j.val*chunkSize q)).take
    (min (chunkSize q) (n-j.val*chunkSize q))=_
  have ht := take_min_length ((List.ofFn (operation q n f)).drop (j.val*chunkSize q)) (chunkSize q)
  simp only [List.length_drop,List.length_ofFn] at ht
  rw [ht,←Nat.mul_comm (chunkSize q) j.val,
    ←PhysicalRecursiveExchange.pack_getD,CommonMSDChunksSemantic.operation_list]
  rw [CommonMSDSemantics.prepare,ExternalMSD.sortedChunks]
  change (pack (chunkSize q) (chunk_positive q)
    ((pack (chunkSize q) (chunk_positive q) (List.ofFn f)).map CommonWordMSD.localSort).flatten).getD j.val []=_
  rw [repack _ (chunk_positive q) CommonWordMSD.localSort
    (fun xs => (CommonWordMSD.localSort_perm xs).length_eq)]
  rfl

theorem operation_row_mem (q : Configuration) (n : ℕ) (f : Records q n)
    (j : Fin (chunkCount q n)) :
    List.ofFn (slice (row q n j).offset (row q n j).length (row q n j).fits
      (operation q n f))∈
      CommonMSDSemantics.prepare q.height (CommonLocalRecursion.height_pos q)
        CommonWordMSD.localSort (List.ofFn f) := by
  rw [operation_row]
  have hj : j.val<(CommonMSDSemantics.prepare q.height (CommonLocalRecursion.height_pos q)
      CommonWordMSD.localSort (List.ofFn f)).length := by
    simpa only [CommonMSDSemantics.prepare,ExternalMSD.sortedChunks,List.length_map,
      pack_count,List.length_ofFn,chunkCount,chunkSize,PhysicalStreamCursor.blockCount] using j.isLt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

end
end CodedSorting.CommonMSDChunkRows
end ChunkRows
