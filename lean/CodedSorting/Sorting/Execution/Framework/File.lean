import CodedSorting.Sorting.Radix.Framework.SortingPower

section File
/-! Raw word files and the ordinary three-word records used by the actual
sorter. These are specifications only: conversion instructions must read the
input words from the common disk. -/
set_option autoImplicit false
namespace CodedSorting.CommonIntegerFile
open WordControl CommonSortingNormalization KeyRecordWords
open CommonLeafProgram (Disk)
noncomputable section

def WordFile (q : Configuration) (disk : Disk q) (base O : ℕ)
    (xs : List (Word q.w)) : Prop :=
  ∀ i : Fin xs.length, CommonMarginTransform.wordAt q disk base (O+i.val)=xs.get i

def input {w : ℕ} (xs : List (Word w)) : List (Record w) :=
  xs.map (fun x => .data x x)

def keyWord {w : ℕ} : Record w → Word w
  | .bottom => 0
  | .data k _ => k
  | .top => 0

def project {w : ℕ} (rs : List (Record w)) : List (Word w) := rs.map keyWord

theorem encoded_key {w : ℕ} (hw : 2≤w) (r : Record w) :
    encode w hw r (1 : Fin 3)=keyWord r := by
  cases r <;> simp [encode,keyWord]

@[simp] theorem input_length {w : ℕ} (xs : List (Word w)) :
    (input xs).length=xs.length := List.length_map _

@[simp] theorem project_length {w : ℕ} (rs : List (Record w)) :
    (project rs).length=rs.length := List.length_map _

@[simp] theorem project_input {w : ℕ} (xs : List (Word w)) : project (input xs)=xs := by
  simp [project,input,List.map_map,Function.comp_def,keyWord]

theorem input_ordinary {w : ℕ} (xs : List (Word w)) :
    CommonMSDRecordDigits.OrdinaryList (input xs) := by
  intro r hr
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
  exact ⟨x,x,rfl⟩

theorem keyWord_val {w : ℕ} (r : Record w)
    (hr : CommonMSDRecordDigits.Ordinary r) :
    (keyWord r).val=CommonWordMSD.key r := by
  obtain ⟨k,x,rfl⟩ := hr
  rfl

theorem project_perm {w : ℕ} (xs : List (Word w)) (rs : List (Record w))
    (hp : rs.Perm (input xs)) : (project rs).Perm xs := by
  have h : (project rs).Perm (project (input xs)) := hp.map keyWord
  simpa only [project_input] using h

theorem project_sorted {w : ℕ} (rs : List (Record w))
    (ho : CommonMSDRecordDigits.OrdinaryList rs)
    (hs : rs.Pairwise (fun x y=>CommonWordMSD.key x≤CommonWordMSD.key y)) :
    (project rs).Pairwise (·≤·) := by
  rw [project,List.pairwise_map]
  exact hs.imp_of_mem (fun {a b} ha hb hab => by
    change (keyWord a).val≤(keyWord b).val
    rw [keyWord_val a (ho a ha),keyWord_val b (ho b hb)]
    exact hab)

theorem project_correct {w : ℕ} (xs : List (Word w)) (rs : List (Record w))
    (hp : rs.Perm (input xs))
    (hs : rs.Pairwise (fun x y=>CommonWordMSD.key x≤CommonWordMSD.key y)) :
    (project rs).Perm xs ∧ (project rs).Pairwise (·≤·) :=
  ⟨project_perm xs rs hp,
    project_sorted rs (CommonMSDRecordDigits.perm_ordinary hp (input_ordinary xs)) hs⟩

def output (q : Configuration) (xs : List (Word q.w)) : List (Word q.w) :=
  project (CommonMSDSortingRun.output q (input xs))

theorem output_correct (q : Configuration) (xs : List (Word q.w)) :
    (output q xs).Perm xs ∧ (output q xs).Pairwise (·≤·) := by
  have h := CommonMSDRadixCost.semantic_correct q (input xs) (input_ordinary xs)
  exact project_correct xs _ h.1 h.2

theorem WordFile.congr (q : Configuration) (before after : Disk q) (base O : ℕ)
    (xs : List (Word q.w)) (hx : WordFile q before base O xs)
    (he : ∀ i : Fin xs.length,
      CommonMarginTransform.wordAt q after base (O+i.val)=
      CommonMarginTransform.wordAt q before base (O+i.val)) :
    WordFile q after base O xs := fun i => (he i).trans (hx i)

end
end CodedSorting.CommonIntegerFile
end File

section ProjectionChunk
/-! One physical projection block: read three blocks of records, select
their key words in the existing resident bank, and write one block. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonIntegerProjectionChunk
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store Disk Machine machine)
open CommonStaticLeaf
noncomputable section

theorem bank_fits (q : Configuration) : 3*q.block≤CommonExchangeLeaf.bankWords q := by
  have h := CommonLocalRecursion.block_le_height q
  unfold CommonExchangeLeaf.bankWords
  omega

def keyIndex (q : Configuration) (j : Fin q.block) : Fin (CommonExchangeLeaf.bankWords q) :=
  ⟨3*j.val+1,by have:=bank_fits q;have:=j.isLt;omega⟩

def selected (q : Configuration) (s : Store q) : Words q.block q.w :=
  fun j => ResidentLeafBank.raw s.leaf (keyIndex q j)

def produce (q : Configuration) (disk : Disk q) (k : ℕ) : Words q.block q.w :=
  fun j => CommonLeafLoad.diskWord q disk (3*k) (3*j.val+1)

def select (q : Configuration) : Instruction q :=
  ⟨.localOp (fun ram => let s := unpack ram;
    pack {s with transfer:=selected q s}),id⟩

def code (q : Configuration) (k : ℕ) : List (Instruction q) :=
  readCode q (3*k) (3*q.block) 3 ++ [select q,writeAt q k 0]

theorem select_step (q : Configuration) (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (select q) (machine q s disk)=
      machine q {s with transfer:=selected q s} disk := by
  simp only [select,ControlledNormalization.logicalStep,Normalization.logicalStep,
    machine,unpack_pack,id_eq]

theorem select_safe (q : Configuration) : RespectsPC q (select q) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [select_step,CommonBlockPair.erasePC_machine]
  rfl

theorem safe (q : Configuration) (k : ℕ) :
    ∀i∈code q k,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    exact readAt_safe q (3*k) (3*q.block) j
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · exact select_safe q
    · exact writeAt_safe q k 0

theorem length_code (q : Configuration) (k : ℕ) : (code q k).length=5 := by
  simp only [code,List.length_append,readCode_length,List.length_cons,List.length_nil]

theorem cost_code (q : Configuration) (k : ℕ) (hcap : 3*k+3≤q.N^q.exponent) :
    cost q (code q k)=4 := by
  rw [code,cost_append,readCode_cost q (3*k) (3*q.block) 3 hcap]
  simp only [cost,select,writeAt,dif_pos (show k+0<q.N^q.exponent by omega),
    CommonBlockPair.targetWrite,Normalization.transferCost]

theorem raw (q : Configuration) (k : ℕ) (s : Store q) (disk : Disk q)
    (hcap : 3*k+3≤q.N^q.exponent) :
    ∃final : Store q,executeRaw q (code q k) (machine q s disk)=
      (machine q final (Function.update disk ⟨k,by omega⟩ (produce q disk k)),4) := by
  have hb := CommonLeafProgram.block_positive q
  have hcover := LayoutConversion.blockCount_covers (3*q.block) q.block hb
  change 3*q.block≤PhysicalStreamCursor.blockCount q.block (3*q.block)*q.block at hcover
  have h3 : 3≤PhysicalStreamCursor.blockCount q.block (3*q.block) := by nlinarith
  obtain ⟨loaded,hr,hread,_,_⟩ := read_prefix q (3*k) (3*q.block) 3 s disk hcap h3
  have hkey : selected q loaded=produce q disk k := by
    funext j
    apply hread (keyIndex q j)
    simp only [keyIndex,Nat.min_self]
    have:=j.isLt
    omega
  refine ⟨{loaded with transfer:=selected q loaded},?_⟩
  rw [code,raw_append,hr]
  dsimp only
  simp only [executeRaw]
  rw [select_step,writeAt_step q k 0 (show k+0<q.N^q.exponent by omega)]
  simp only [select,writeAt,Nat.add_zero,dif_pos (show k<q.N^q.exponent by omega),
    CommonBlockPair.targetWrite,Normalization.transferCost,Nat.add_zero,Nat.zero_add,hkey]

theorem raw_disk (q : Configuration) (k : ℕ) (s : Machine q)
    (hcap : 3*k+3≤q.N^q.exponent) :
    (executeRaw q (code q k) s).1.disk=
      Function.update s.disk ⟨k,by omega⟩ (produce q s.disk k) := by
  obtain ⟨final,h⟩ := raw q k (unpack s.ram) s.disk hcap
  rw [CommonBlockPair.machine_eta q s] at h
  exact congrArg (fun x => x.1.disk) h

theorem frame (q : Configuration) (k : ℕ) (s : Machine q)
    (hcap : 3*k+3≤q.N^q.exponent) (a : Fin (q.N^q.exponent)) (ha : a.val≠k) :
    (executeRaw q (code q k) s).1.disk a=s.disk a := by
  rw [raw_disk q k s hcap,Function.update_of_ne]
  exact fun h => ha (congrArg Fin.val h)

end
end CodedSorting.CommonIntegerProjectionChunk
end ProjectionChunk

section ExpandBlock
/-! One real block read expands its words into ordinary three-word
records. The input block stays in an existing reader buffer while each
output block is formed in the existing transfer buffer and written. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonIntegerExpandBlock
open WordControl CommonSortingNormalization CommonStaticSchedule CommonBlockPair
open CommonLeafProgram (Store RAM Disk Machine machine)
open KeyRecordWords
noncomputable section

def expanded (q : Configuration) (block : Block q) (j : ℕ) : Block q := fun i =>
  let z := j*q.block+i.val
  let x := block ⟨(z/3)%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩
  encode q.w (by have:=q.word_width;omega) (.data x x) ⟨z%3,Nat.mod_lt _ (by omega)⟩

def stage (q : Configuration) (reader : Fin q.inventory.readers) (j : ℕ) : Instruction q :=
  ⟨.localOp (fun ram => let s:=unpack ram;
    pack {s with transfer:=expanded q (buffer q reader s) j}),id⟩

theorem stage_step (q : Configuration) (reader : Fin q.inventory.readers) (j : ℕ)
    (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (stage q reader j) (machine q s disk)=
      machine q {s with transfer:=expanded q (buffer q reader s) j} disk := by
  simp only [stage,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,unpack_pack,id_eq]

theorem stage_safe (q : Configuration) (reader : Fin q.inventory.readers) (j : ℕ) :
    RespectsPC q (stage q reader j) := by
  apply respectsPC_of_commutes
  intro s
  rw [←machine_eta q s]
  simp only [stage_step,erasePC_machine]
  rfl

def code (q : Configuration) (reader : Fin q.inventory.readers) (base k : ℕ) :
    List (Instruction q) :=
  if h : base+3*k+3≤q.N^q.exponent then
    [sourceRead q reader ⟨base+k,by omega⟩,
      stage q reader 0,targetWrite q ⟨base+3*k,by omega⟩,
      stage q reader 1,targetWrite q ⟨base+3*k+1,by omega⟩,
      stage q reader 2,targetWrite q ⟨base+3*k+2,by omega⟩]
  else []

theorem safe (q : Configuration) (reader : Fin q.inventory.readers) (base k : ℕ) :
    ∀ i∈code q reader base k,RespectsPC q i := by
  unfold code
  split
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact sourceRead_respectsPC q reader _
    · exact stage_safe q reader 0
    · exact targetWrite_respectsPC q _
    · exact stage_safe q reader 1
    · exact targetWrite_respectsPC q _
    · exact stage_safe q reader 2
    · exact targetWrite_respectsPC q _
  · simp

theorem length (q : Configuration) (reader : Fin q.inventory.readers) (base k : ℕ)
    (hfit : base+3*k+3≤q.N^q.exponent) : (code q reader base k).length=7 := by
  simp only [code,dif_pos hfit,List.length_cons,List.length_nil]

theorem cost_eq (q : Configuration) (reader : Fin q.inventory.readers) (base k : ℕ)
    (hfit : base+3*k+3≤q.N^q.exponent) : cost q (code q reader base k)=4 := by
  simp only [code,dif_pos hfit,cost,sourceRead,stage,targetWrite,Normalization.transferCost]

theorem raw_disk (q : Configuration) (reader : Fin q.inventory.readers) (base k : ℕ)
    (s : Machine q) (hfit : base+3*k+3≤q.N^q.exponent) :
    (executeRaw q (code q reader base k) s).1.disk=
      CommonLeafDisk.writePrefix (base+3*k)
        (expanded q (s.disk ⟨base+k,by omega⟩)) 3 s.disk := by
  rw [←machine_eta q s]
  simp only [code,dif_pos hfit,executeRaw,sourceRead_step,stage_step,targetWrite_step]
  simp only [show ∀ (s : Store q) (b : Block q), buffer q reader {s with transfer:=b}=buffer q reader s from fun _ _ => rfl, buffer_stash]
  simp only [CommonLeafDisk.writePrefix,CommonLeafDisk.writeAt,Nat.add_zero,
    show base+3*k<q.N^q.exponent by omega,
    show base+3*k+1<q.N^q.exponent by omega,
    show base+3*k+2<q.N^q.exponent by omega,↓reduceDIte,Nat.add_zero]
  rfl

theorem frame (q : Configuration) (reader : Fin q.inventory.readers) (base k : ℕ)
    (s : Machine q) (hfit : base+3*k+3≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<base+3*k ∨ base+3*k+3≤a.val) :
    (executeRaw q (code q reader base k) s).1.disk a=s.disk a := by
  rw [raw_disk q reader base k s hfit]
  exact CommonLeafDisk.prefix_outside _ _ _ _ a ha

theorem word_block (q : Configuration) (disk : Disk q) (base k : ℕ)
    (ha : base+k<q.N^q.exponent) (i : Fin q.block) :
    CommonMarginTransform.wordAt q disk base (k*q.block+i.val)=disk ⟨base+k,ha⟩ i := by
  rw [CommonRecordEncoding.wordAt_eq_diskWord]
  exact CommonLeafLoad.diskWord_block q disk base k ha i

theorem expanded_at (q : Configuration) (block : Block q) (i : Fin q.block) (j : Fin 3) :
    expanded q block ((3*i.val+j.val)/q.block)
      ⟨(3*i.val+j.val)%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩=
      encode q.w (by have:=q.word_width;omega) (.data (block i) (block i)) j := by
  have he : (3*i.val+j.val)/q.block*q.block+(3*i.val+j.val)%q.block=3*i.val+j.val :=
    by simpa only [Nat.mul_comm] using Nat.div_add_mod (3*i.val+j.val) q.block
  have hd : (3*i.val+j.val)/3=i.val := by omega
  have hm : (3*i.val+j.val)%3=j.val := by omega
  simp only [expanded,he,hd,hm,Nat.mod_eq_of_lt i.isLt,Fin.eta]

theorem word (q : Configuration) (reader : Fin q.inventory.readers) (base k : ℕ)
    (s : Machine q) (hfit : base+3*k+3≤q.N^q.exponent) (i : Fin q.block) (j : Fin 3) :
    CommonMarginTransform.wordAt q (executeRaw q (code q reader base k) s).1.disk base
      (3*(k*q.block+i.val)+j.val)=
      encode q.w (by have:=q.word_width;omega)
        (.data (s.disk ⟨base+k,by omega⟩ i) (s.disk ⟨base+k,by omega⟩ i)) j := by
  let d := (3*i.val+j.val)/q.block
  let r : Fin q.block := ⟨(3*i.val+j.val)%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩
  have hd : d<3 := by
    apply (Nat.div_lt_iff_lt_mul (CommonLeafProgram.block_positive q)).2
    have:=i.isLt;have:=j.isLt;omega
  have he : 3*(k*q.block+i.val)+j.val=(3*k+d)*q.block+r.val := by
    have ht := Nat.div_add_mod (3*i.val+j.val) q.block
    dsimp only [d,r]
    nlinarith only [ht]
  rw [he,word_block q _ base (3*k+d) (by omega) r,raw_disk q reader base k s hfit]
  have hx : (⟨base+(3*k+d),by omega⟩ : Fin (q.N^q.exponent))=
      ⟨(base+3*k)+d,by omega⟩ := by apply Fin.ext; simp only [Nat.add_assoc]
  rw [hx,CommonLeafDisk.prefix_at _ _ 3 _ hfit d hd]
  exact expanded_at q _ i j

end
end CodedSorting.CommonIntegerExpandBlock
end ExpandBlock

section Projection
/-! The public forward scan contracts three-word records to their integer
keys in place. Each iteration reads its complete source chunk before
writing one earlier block. The untouched suffix invariant prevents an
output write from corrupting a later input. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonIntegerProjection
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine Disk)
open CommonRecordIntervalList CommonIntegerFile
noncomputable section

abbrev blocks (q : Configuration) (n : ℕ) := PhysicalStreamCursor.blockCount q.block n

def scanPrefix (q : Configuration) (k : ℕ) : List (Instruction q) :=
  (List.range k).flatMap (CommonIntegerProjectionChunk.code q)

def code (q : Configuration) (n : ℕ) : List (Instruction q) := scanPrefix q (blocks q n)

theorem prefix_succ (q : Configuration) (k : ℕ) :
    scanPrefix q (k+1)=scanPrefix q k++CommonIntegerProjectionChunk.code q k := by
  simp only [scanPrefix,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem produce_unchanged (q : Configuration) (original : Disk q) (k : ℕ) :
    CommonIntegerProjectionChunk.produce q
      (CommonLeafDisk.writePrefix 0 (CommonIntegerProjectionChunk.produce q original) k original) k=
      CommonIntegerProjectionChunk.produce q original k := by
  funext j
  unfold CommonIntegerProjectionChunk.produce CommonLeafLoad.diskWord
  split_ifs with h
  · rw [CommonLeafDisk.prefix_outside 0 _ k original _ (Or.inr (by
      simp only [Fin.val_mk,Nat.zero_add]
      exact (show k≤3*k from by omega).trans (Nat.le_add_right _ _)))]
  · rfl

theorem prefix_disk (q : Configuration) (k : ℕ) (s : Machine q)
    (hcap : 3*k≤q.N^q.exponent) :
    (executeRaw q (scanPrefix q k) s).1.disk=
      CommonLeafDisk.writePrefix 0 (CommonIntegerProjectionChunk.produce q s.disk) k s.disk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev : 3*k≤q.N^q.exponent := by omega
    have hk : 0+k<q.N^q.exponent := by omega
    rw [prefix_succ,CommonStaticLeaf.raw_append]
    dsimp only
    rw [CommonIntegerProjectionChunk.raw_disk q k _ (by omega),ih hprev]
    rw [produce_unchanged,CommonLeafDisk.prefix_succ_of_lt hk]
    simp only [Nat.zero_add]

theorem prefix_length (q : Configuration) (k : ℕ) : (scanPrefix q k).length=5*k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [prefix_succ,List.length_append,ih,CommonIntegerProjectionChunk.length_code];omega

theorem prefix_cost (q : Configuration) (k : ℕ) (hcap : 3*k≤q.N^q.exponent) :
    cost q (scanPrefix q k)=4*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prefix_succ,CommonStaticLeaf.cost_append,ih (by omega),
      CommonIntegerProjectionChunk.cost_code q k (by omega)]
    omega

theorem safe (q : Configuration) (n : ℕ) : ∀ i∈code q n,RespectsPC q i := by
  intro i hi
  change i∈(List.range (blocks q n)).flatMap (CommonIntegerProjectionChunk.code q) at hi
  obtain ⟨k,hk,hi⟩ := List.mem_flatMap.mp hi
  exact CommonIntegerProjectionChunk.safe q k i hi

theorem length_code (q : Configuration) (n : ℕ) : (code q n).length=5*blocks q n :=
  prefix_length q _

theorem cost_code (q : Configuration) (n : ℕ) (hcap : 3*blocks q n≤q.N^q.exponent) :
    cost q (code q n)=4*blocks q n := prefix_cost q _ hcap

theorem frame (q : Configuration) (n : ℕ) (s : Machine q)
    (hcap : 3*blocks q n≤q.N^q.exponent) (a : Fin (q.N^q.exponent))
    (ha : blocks q n≤a.val) :
    (executeRaw q (code q n) s).1.disk a=s.disk a := by
  rw [code,prefix_disk q _ s hcap]
  exact CommonLeafDisk.prefix_outside 0 _ _ s.disk a (Or.inr (by simpa only [Nat.zero_add] using ha))

/-- Literal word equation for every live output location. -/
theorem raw_word (q : Configuration) (n : ℕ) (s : Machine q)
    (hcap : 3*blocks q n≤q.N^q.exponent) (i : ℕ) (hi : i<n) :
    CommonMarginTransform.wordAt q (executeRaw q (code q n) s).1.disk 0 i=
      CommonMarginTransform.wordAt q s.disk 0 (3*i+1) := by
  let k := i/q.block
  let j : Fin q.block := ⟨i%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩
  have hdecomp : k*q.block+j.val=i := by
    dsimp only [k,j]
    exact Nat.div_add_mod' i q.block
  have hk : k<blocks q n :=
    (PhysicalStreamCursor.cursor_live_iff q.block n k (CommonLeafProgram.block_positive q)).2
      ((Nat.div_mul_le_self i q.block).trans_lt hi)
  have hfit : 0+blocks q n≤q.N^q.exponent := by omega
  rw [code,prefix_disk q _ s hcap,CommonRecordEncoding.wordAt_eq_diskWord,
    ←hdecomp,CommonLeafLoad.diskWord_block q _ 0 k (by omega) j]
  rw [CommonLeafDisk.prefix_at 0 _ _ s.disk hfit k hk]
  unfold CommonIntegerProjectionChunk.produce
  rw [show 3*k=0+3*k by omega,CommonMSDDirectoryRead.diskWord_shift,
    CommonRecordEncoding.wordAt_eq_diskWord]
  congr 1
  ring

/-- The output file is the projection of the actual encoded record file;
no source list is supplied to the generated instructions. -/
theorem raw_complete (q : Configuration) (rs : List (KeyRecordWords.Record q.w))
    (s : Machine q) (hin : EncodedListAt q s.disk 0 0 rs)
    (hcap : 3*blocks q rs.length≤q.N^q.exponent) :
    WordFile q (executeRaw q (code q rs.length) s).1.disk 0 0 (project rs) := by
  intro i
  have hi : i.val<rs.length := by simpa only [project_length] using i.isLt
  have hr := hin ⟨i.val,hi⟩ (1 : Fin 3)
  rw [show 0+i.val=i.val by omega,raw_word q rs.length s hcap i.val hi]
  simp only [CommonRecordInterval.EncodedAt,Nat.mul_zero,Nat.zero_add] at hr
  rw [show 3*i.val+1=i.val*3+(1 : Fin 3).val by norm_num; omega,hr,encoded_key]
  simp only [project,List.get_eq_getElem,List.getElem_map]

/-- The public size conditions already imply every three-block read fits. -/
theorem capacity (q : Configuration) (n : ℕ) (hn : n≤q.N) (he : 2≤q.exponent) :
    3*blocks q n≤q.N^q.exponent := by
  have hb : blocks q n≤n := CommonLeafGrouping.blockCount_le_of_fits
    (CommonLeafProgram.block_positive q) (Nat.le_mul_of_pos_right _ (CommonLeafProgram.block_positive q))
  have hH := CommonLocalDescriptorBounds.height_scaled_le_input q
  have hHp := CommonLocalRecursion.height_pos q
  have hN : 3≤q.N := by nlinarith
  have hp : q.N^2≤q.N^q.exponent := Nat.pow_le_pow_right (by have:=q.input_large;omega) he
  nlinarith

theorem instruction_capacity (q : Configuration) (n : ℕ) (hn : n≤q.N) (he : 2≤q.exponent) :
    (code q n).length≤q.N^q.exponent := by
  rw [length_code]
  have hb : blocks q n≤n := CommonLeafGrouping.blockCount_le_of_fits
    (CommonLeafProgram.block_positive q) (Nat.le_mul_of_pos_right _ (CommonLeafProgram.block_positive q))
  have hH := CommonLocalDescriptorBounds.height_scaled_le_input q
  have hHp := CommonLocalRecursion.height_pos q
  have hN : 5≤q.N := by nlinarith
  have hp : q.N^2≤q.N^q.exponent := Nat.pow_le_pow_right (by have:=q.input_large;omega) he
  nlinarith

/-- One compiled, halting scan on the counted RAM and finite disk. -/
theorem complete (q : Configuration) (rs : List (KeyRecordWords.Record q.w))
    (hn : rs.length≤q.N) (he : 2≤q.exponent) (s : Machine q)
    (hin : EncodedListAt q s.disk 0 0 rs) (hpc : pc q s.ram=0) :
    let out := ControlledNormalization.runLogical (policy q (code q rs.length))
      (code q rs.length).length s
    WordFile q out.1.disk 0 0 (project rs) ∧
    (∀ a : Fin (q.N^q.exponent),blocks q rs.length≤a.val → out.1.disk a=s.disk a) ∧
    policy q (code q rs.length) out.1.ram=none ∧
    out.2=4*blocks q rs.length ∧ Fintype.card (ResidentIndex q)≤q.M := by
  dsimp only
  have hc := capacity q rs.length hn he
  obtain ⟨hd,hh,hi,hm⟩ := run_code_disk q (code q rs.length)
    (instruction_capacity q rs.length hn he) (safe q rs.length) s hpc
  refine ⟨?_,?_,hh,hi.trans (cost_code q rs.length hc),hm⟩
  · rw [hd]
    exact raw_complete q rs s hin hc
  · intro a ha
    rw [hd]
    exact frame q rs.length s hc a ha

end
end CodedSorting.CommonIntegerProjection
end Projection

section Expand
/-! A real backward scan expands a raw integer file into ordinary
three-word records in place. Higher blocks are read before any writes
from lower blocks can reach them. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CodedSorting.CommonIntegerExpand
open WordControl CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Disk Machine)
open CommonMarginTransform (wordAt)
open KeyRecordWords CommonIntegerFile
noncomputable section

def loops (q : Configuration) (reader : Fin q.inventory.readers) (base : ℕ) :
    ℕ→List (Instruction q)
  | 0 => []
  | K+1 => CommonIntegerExpandBlock.code q reader base K++loops q reader base K

def blocks (q : Configuration) (n : ℕ) : ℕ := PhysicalStreamCursor.blockCount q.block n

def code (q : Configuration) (reader : Fin q.inventory.readers) (n base : ℕ) :
    List (Instruction q) := loops q reader base (blocks q n)

theorem loops_safe (q : Configuration) (reader : Fin q.inventory.readers) (base K : ℕ) :
    ∀ i∈loops q reader base K,RespectsPC q i := by
  induction K with
  | zero => simp only [loops,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ K ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact CommonIntegerExpandBlock.safe q reader base K i hi
    · exact ih i hi

theorem safe (q : Configuration) (reader : Fin q.inventory.readers) (n base : ℕ) :
    ∀ i∈code q reader n base,RespectsPC q i := loops_safe q reader base _

theorem loops_length (q : Configuration) (reader : Fin q.inventory.readers) (base K : ℕ)
    (hfit : base+3*K≤q.N^q.exponent) : (loops q reader base K).length=7*K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [loops,List.length_append,CommonIntegerExpandBlock.length q reader base K (by omega),
      ih (by omega)]
    omega

theorem length (q : Configuration) (reader : Fin q.inventory.readers) (n base : ℕ)
    (hfit : base+3*blocks q n≤q.N^q.exponent) : (code q reader n base).length=7*blocks q n :=
  loops_length q reader base _ hfit

theorem loops_cost (q : Configuration) (reader : Fin q.inventory.readers) (base K : ℕ)
    (hfit : base+3*K≤q.N^q.exponent) : cost q (loops q reader base K)=4*K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [loops,cost_append,CommonIntegerExpandBlock.cost_eq q reader base K (by omega),
      ih (by omega)]
    omega

theorem cost_eq (q : Configuration) (reader : Fin q.inventory.readers) (n base : ℕ)
    (hfit : base+3*blocks q n≤q.N^q.exponent) : cost q (code q reader n base)=4*blocks q n :=
  loops_cost q reader base _ hfit

theorem loops_frame (q : Configuration) (reader : Fin q.inventory.readers) (base K : ℕ)
    (s : Machine q) (hfit : base+3*K≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<base ∨ base+3*K≤a.val) :
    (executeRaw q (loops q reader base K) s).1.disk a=s.disk a := by
  induction K generalizing s with
  | zero => rfl
  | succ K ih =>
    rw [loops,raw_append]
    have ht := ih (executeRaw q (CommonIntegerExpandBlock.code q reader base K) s).1
      (by omega) (by omega)
    exact ht.trans (CommonIntegerExpandBlock.frame q reader base K s (by omega) a (by omega))

theorem frame (q : Configuration) (reader : Fin q.inventory.readers) (n base : ℕ)
    (s : Machine q) (hfit : base+3*blocks q n≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent)) (ha : a.val<base ∨ base+3*blocks q n≤a.val) :
    (executeRaw q (code q reader n base) s).1.disk a=s.disk a :=
  loops_frame q reader base _ s hfit a ha

theorem word_disk_congr (q : Configuration) (before after : Disk q) (base i : ℕ)
    (he : ∀ a : Fin (q.N^q.exponent),a.val=base+i/q.block → after a=before a) :
    wordAt q after base i=wordAt q before base i := by
  rw [CommonRecordEncoding.wordAt_eq_diskWord,CommonRecordEncoding.wordAt_eq_diskWord]
  unfold CommonLeafLoad.diskWord
  split
  · exact congrFun (he _ rfl) _
  · rfl

/-- Every live word is copied from the original disk, including the
parts whose source and output ranges overlap. -/
theorem loops_word (q : Configuration) (reader : Fin q.inventory.readers) (base K : ℕ)
    (s : Machine q) (hfit : base+3*K≤q.N^q.exponent)
    (i : ℕ) (hi : i<K*q.block) (j : Fin 3) :
    wordAt q (executeRaw q (loops q reader base K) s).1.disk base (3*i+j.val)=
      encode q.w (by have:=q.word_width;omega)
        (.data (wordAt q s.disk base i) (wordAt q s.disk base i)) j := by
  induction K generalizing s i with
  | zero => omega
  | succ K ih =>
    let first := (executeRaw q (CommonIntegerExpandBlock.code q reader base K) s).1
    have hf : base+3*K+3≤q.N^q.exponent := by omega
    rw [loops,raw_append]
    change wordAt q (executeRaw q (loops q reader base K) first).1.disk base (3*i+j.val)=_
    by_cases hil : i<K*q.block
    · have hread : wordAt q first.disk base i=wordAt q s.disk base i := by
        apply word_disk_congr
        intro a ha
        apply CommonIntegerExpandBlock.frame q reader base K s hf a
        have hdiv : i/q.block<K := (Nat.div_lt_iff_lt_mul (CommonLeafProgram.block_positive q)).2 hil
        left
        omega
      rw [ih first (by omega) i hil,hread]
    · have hlo : K*q.block≤ i := by omega
      let r : Fin q.block := ⟨i-K*q.block,by
        have his : i<K*q.block+q.block := by nlinarith only [hi]
        omega⟩
      have hir : i=K*q.block+r.val := by dsimp only [r];omega
      have hout : wordAt q (executeRaw q (loops q reader base K) first).1.disk base (3*i+j.val)=
          wordAt q first.disk base (3*i+j.val) := by
        apply word_disk_congr
        intro a ha
        apply loops_frame q reader base K first (by omega) a
        right
        have hdiv : 3*K≤(3*i+j.val)/q.block :=
          (Nat.le_div_iff_mul_le (CommonLeafProgram.block_positive q)).2 (by nlinarith only [hlo])
        omega
      rw [hout,hir]
      have hw := CommonIntegerExpandBlock.word q reader base K s hf r j
      have hs := CommonIntegerExpandBlock.word_block q s.disk base K (by omega) r
      simpa only [first,hs] using hw

theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers) (n base : ℕ)
    (s : Machine q) (xs : List (Word q.w)) (hlen : xs.length=n)
    (hx : WordFile q s.disk base 0 xs)
    (hfit : base+3*blocks q n≤q.N^q.exponent) :
    CommonRecordIntervalList.EncodedListAt q (executeRaw q (code q reader n base) s).1.disk
      base 0 (input xs) := by
  intro i j
  have hi : i.val<xs.length := by simpa only [input_length] using i.isLt
  have hc : n≤blocks q n*q.block :=
    LayoutConversion.blockCount_covers n q.block (CommonLeafProgram.block_positive q)
  have h := loops_word q reader base (blocks q n) s hfit i.val (by omega) j
  have hw := hx ⟨i.val,hi⟩
  simp only [Nat.zero_add] at hw
  change wordAt q _ base (3*0+i.val*3+j.val)=_
  rw [hw] at h
  simpa only [code,Nat.mul_zero,Nat.zero_add,Nat.mul_comm i.val 3,input,
    List.get_eq_getElem,List.getElem_map] using h

end
end CodedSorting.CommonIntegerExpand
end Expand
