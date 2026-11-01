import CodedSorting.Sorting.Local.Framework.Semantic

section SlabBatchChildren
/-! Sequential child programs on disjoint column slabs. All children use
one common workspace, and consume the actual machine returned previously. -/
set_option autoImplicit false
namespace CodedSorting.CommonSlabBatch
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonRecordProgram
open CommonLeafProgram (Disk Machine)
noncomputable section

abbrev recordBase (q : Configuration) (r buffer c : ℕ) := base q (r*3) buffer c

theorem record_blocks (q : Configuration) (r : ℕ) : recordBlocks q r=stride q (r*3) := by
  unfold recordBlocks
  rw [←Nat.mul_assoc]
  exact word_count q (r*3)

variable {q : Configuration} {C r buffer work limit : ℕ}
variable {F : Records q r→Records q r}

abbrev Children (q : Configuration) (C r buffer work limit : ℕ)
    (F : Records q r→Records q r) :=
  (c : Fin C) → Program q r (recordBase q r buffer c.val) work limit F

def childrenCode (p : Children q C r buffer work limit F) (cs : List (Fin C)) :=
  cs.flatMap (fun c=>(p c).instructions)

def childrenCharge (p : Children q C r buffer work limit F) (cs : List (Fin C)) :=
  (cs.map (fun c=>(p c).charge)).sum

theorem child_other (p : Children q C r buffer work limit F)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (c d : Fin C) (hne : c≠d) (s : Machine q) (i : Fin (r*(3*q.w))) :
    readBit q (executeRaw q (p d).instructions s).1.disk (recordBase q r buffer c.val) i.val=
      readBit q s.disk (recordBase q r buffer c.val) i.val := by
  let j : Fin ((r*3)*q.w) := ⟨i.val,by simpa only [Nat.mul_assoc] using i.isLt⟩
  unfold readBit
  rw [(p d).frame]
  · simpa only [record_blocks] using bit_outside_other q hw hwl hl c d hne j
  · exact Or.inl (bit_before_work q hw hwl hl c j)

theorem children_other (p : Children q C r buffer work limit F)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (cs : List (Fin C)) (c : Fin C) (hc : c∉cs) (s : Machine q)
    (i : Fin (r*(3*q.w))) :
    readBit q (executeRaw q (childrenCode p cs) s).1.disk (recordBase q r buffer c.val) i.val=
      readBit q s.disk (recordBase q r buffer c.val) i.val := by
  induction cs generalizing s with
  | nil => rfl
  | cons d ds ih =>
    have hcd : c≠d := fun he=>hc (by simp [he])
    have hcs : c∉ds := fun hh=>hc (by simp [hh])
    rw [childrenCode,List.flatMap_cons,raw_append]
    exact (ih hcs _).trans (child_other p hw hwl hl c d hcd s i)

theorem children_correct (p : Children q C r buffer work limit F)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (cs : List (Fin C)) (hcs : cs.Nodup) (c : Fin C) (hc : c∈cs)
    (s : Machine q) (f : Records q r)
    (hf : Encoded q s.disk (recordBase q r buffer c.val) f) :
    Encoded q (executeRaw q (childrenCode p cs) s).1.disk (recordBase q r buffer c.val) (F f) := by
  induction cs generalizing s with
  | nil => simp at hc
  | cons d ds ih =>
    obtain ⟨hd,hds⟩:=List.nodup_cons.mp hcs
    rw [childrenCode,List.flatMap_cons,raw_append]
    by_cases he : c=d
    · subst d
      intro i
      exact (children_other p hw hwl hl ds c hd _ i).trans ((p c).correct s f hf i)
    · have hm : c∈ds := by simpa only [List.mem_cons,he,false_or] using hc
      apply ih hds hm
      intro i
      exact (child_other p hw hwl hl c d he s i).trans (hf i)

theorem children_frame (p : Children q C r buffer work limit F)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit)
    (cs : List (Fin C)) (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<buffer ∨ limit≤a.val) :
    (executeRaw q (childrenCode p cs) s).1.disk a=s.disk a := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rw [childrenCode,List.flatMap_cons,raw_append]
    change (executeRaw q (childrenCode p cs) (executeRaw q (p c).instructions s).1).1.disk a=s.disk a
    rw [ih]
    apply (p c).frame s a
    · rw [record_blocks]
      have he:=base_end q (n:=r*3) (buffer:=buffer) c
      have hb : buffer≤recordBase q r buffer c.val := Nat.le_add_right _ _
      dsimp only [recordBase] at *
      rcases ha with h|h <;> omega
    · have hb : buffer≤work := (Nat.le_add_right _ _).trans hw
      rcases ha with h|h <;> omega

theorem children_safe (p : Children q C r buffer work limit F) (cs : List (Fin C)) :
    ∀ i∈childrenCode p cs,RespectsPC q i := by
  intro i hi
  obtain ⟨c,_,hi⟩:=List.mem_flatMap.mp hi
  exact (p c).safe i hi

theorem children_cost (p : Children q C r buffer work limit F) (cs : List (Fin C)) :
    cost q (childrenCode p cs)≤childrenCharge p cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [childrenCode,List.flatMap_cons,cost_append,childrenCharge,List.map_cons,List.sum_cons] at *
    exact Nat.add_le_add (p c).cost_le ih

theorem children_length (p : Children q C r buffer work limit F) (cs : List (Fin C)) :
    (childrenCode p cs).length≤childrenCharge p cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [childrenCode,List.flatMap_cons,List.length_append,childrenCharge,List.map_cons,List.sum_cons] at *
    exact Nat.add_le_add (p c).length_le ih

end
end CodedSorting.CommonSlabBatch
end SlabBatchChildren

section SlabBatch
/-! An actual recursive column batch: split the packed parent once, run
all children in their own slabs with one shared workspace, and join once.
The two slab scans cost twelve I/Os per allocated column block. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonSlabBatch
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonRecordProgram PhysicalLocalSortPadding
open CommonLeafProgram (Disk Machine)
noncomputable section

variable {q : Configuration} {C r source buffer work limit : ℕ}
variable {F : Records q r→Records q r}

def batchOutput (F : Records q r→Records q r) (f : Records q (C*r)) : Records q (C*r) :=
  flattenColumns C r (fun c=>F (CommonLocalSemantic.columns C r f c))

def splitCode (q : Configuration) (reader : Fin q.inventory.readers) (C r source buffer : ℕ) :=
  CommonStaticSlabSplit.code q reader C (r*3) source (slabMap q buffer)

def joinCode (q : Configuration) (reader : Fin q.inventory.readers) (C r source buffer : ℕ) :=
  CommonStaticSlabJoinMapped.code q reader (r*3) C source (slabMap q buffer)

def code (reader : Fin q.inventory.readers) (source : ℕ)
    (p : Children q C r buffer work limit F) :=
  splitCode q reader C r source buffer ++ childrenCode p (List.finRange C) ++
    joinCode q reader C r source buffer

theorem split_encoded (reader : Fin q.inventory.readers)
    (hs : source+recordBlocks q (C*r)≤buffer)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q (C*r)) (hf : Encoded q s.disk source f) (c : Fin C) :
    Encoded q (executeRaw q (splitCode q reader C r source buffer) s).1.disk
      (recordBase q r buffer c.val) (CommonLocalSemantic.columns C r f c) := by
  have hs' : source+stride q (C*(r*3))≤buffer := by simpa only [record_blocks,Nat.mul_assoc] using hs
  have hcap : buffer+C*stride q (r*3)≤limit := hw.trans hwl
  apply (encoded_iff q _ _ _).2
  intro i j
  let x : Fin ((r*3)*q.w) := ⟨i.val*(3*q.w)+j.val,by have:=i.isLt; have:=j.isLt; nlinarith⟩
  have hb:=CommonSlabReadBits.split_column_bits q reader (slabMap q buffer)
    (fun c:Fin C=>recordBase q r buffer c.val) s (slabMap_injective q hcap hl)
    (slabMap_separate q hs' hcap hl) (fun c k _=>slabMap_eq q (r*3) buffer c.val k) c x
  change readBit q (executeRaw q (splitCode q reader C r source buffer) s).1.disk
    (recordBase q r buffer c.val) x.val=_
  dsimp only [splitCode]
  rw [hb]
  have he : c.val*((r*3)*q.w)+x.val=(finProdFinEquiv (c,i)).val*(3*q.w)+j.val := by
    simp only [x,finProdFinEquiv_apply_val]
    ring
  rw [he]
  exact (encoded_iff q _ _ _).1 hf (finProdFinEquiv (c,i)) j

theorem join_encoded (reader : Fin q.inventory.readers)
    (hs : source+recordBlocks q (C*r)≤buffer)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Fin C→Records q r)
    (hf : ∀c,Encoded q s.disk (recordBase q r buffer c.val) (f c)) :
    Encoded q (executeRaw q (joinCode q reader C r source buffer) s).1.disk source
      (flattenColumns C r f) := by
  have hs' : source+stride q (C*(r*3))≤buffer := by simpa only [record_blocks,Nat.mul_assoc] using hs
  have hcap : buffer+C*stride q (r*3)≤limit := hw.trans hwl
  apply (encoded_iff q _ _ _).2
  intro z j
  obtain ⟨⟨c,i⟩,rfl⟩:=finProdFinEquiv.surjective z
  let x : Fin ((r*3)*q.w) := ⟨i.val*(3*q.w)+j.val,by have:=i.isLt; have:=j.isLt; nlinarith⟩
  have hb:=CommonSlabReadBits.join_column_bits q reader (slabMap q buffer)
    (fun c:Fin C=>recordBase q r buffer c.val) s
    (hs'.trans ((Nat.le_add_right _ _).trans (hcap.trans hl)))
    (slabMap_after_source q hs' hcap hl) (fun c k _=>slabMap_eq q (r*3) buffer c.val k) c x
  have he : c.val*((r*3)*q.w)+x.val=(finProdFinEquiv (c,i)).val*(3*q.w)+j.val := by
    simp only [x,finProdFinEquiv_apply_val]
    ring
  rw [he] at hb
  dsimp only [joinCode]
  rw [hb]
  simpa only [flattenColumns,Equiv.symm_apply_apply] using (encoded_iff q _ _ _).1 (hf c) i j

theorem raw_correct (reader : Fin q.inventory.readers)
    (p : Children q C r buffer work limit F)
    (hs : source+recordBlocks q (C*r)≤buffer)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (f : Records q (C*r)) (hf : Encoded q s.disk source f) :
    Encoded q (executeRaw q (code reader source p) s).1.disk source (batchOutput F f) := by
  rw [code,raw_append,raw_append]
  apply join_encoded reader hs hw hwl hl
  intro c
  apply children_correct p hw hwl hl (List.finRange C) (List.nodup_finRange C) c (by simp)
  exact split_encoded reader hs hw hwl hl s f hf c

theorem raw_frame (reader : Fin q.inventory.readers)
    (p : Children q C r buffer work limit F)
    (hs : source+recordBlocks q (C*r)≤buffer)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent)
    (s : Machine q) (a : Fin (q.N^q.exponent))
    (ha : a.val<source ∨ source+recordBlocks q (C*r)≤a.val)
    (hb : a.val<buffer ∨ limit≤a.val) :
    (executeRaw q (code reader source p) s).1.disk a=s.disk a := by
  have hs' : source+stride q (C*(r*3))≤buffer := by simpa only [record_blocks,Nat.mul_assoc] using hs
  have ha' : a.val<source ∨ source+stride q (C*(r*3))≤a.val := by
    simpa only [record_blocks,Nat.mul_assoc] using ha
  have hcap : buffer+C*stride q (r*3)≤limit := hw.trans hwl
  rw [code,raw_append,raw_append]
  dsimp only [joinCode]
  rw [CommonStaticSlabJoinMapped.raw_outside q reader (r*3) C source (slabMap q buffer)
    _ (hs'.trans ((Nat.le_add_right _ _).trans (hcap.trans hl))) (slabMap_after_source q hs' hcap hl) a ha']
  rw [children_frame p hw hwl _ _ a hb]
  apply CommonStaticSlabSplit.raw_outside
  intro k hk he
  change k<C*stride q (r*3) at hk
  have hv:=congrArg Fin.val he
  rw [slabMap_val q hcap hl hk] at hv
  rcases hb with h|h <;> omega

theorem code_safe (reader : Fin q.inventory.readers) (p : Children q C r buffer work limit F) :
    ∀ i∈code reader source p,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · rcases List.mem_append.mp hi with hi|hi
    · exact CommonStaticSlabSplit.code_safe q reader C (r*3) source (slabMap q buffer) i hi
    · exact children_safe p _ i hi
  · exact CommonStaticSlabJoinMapped.code_safe q reader (r*3) C source (slabMap q buffer) i hi

theorem code_cost (reader : Fin q.inventory.readers) (p : Children q C r buffer work limit F) :
    cost q (code reader source p)≤childrenCharge p (List.finRange C)+12*(C*stride q (r*3)) := by
  rw [code,cost_append,cost_append]
  have hs:=CommonStaticSlabSplit.code_cost q reader C (r*3) source (slabMap q buffer)
  have hj:=CommonStaticSlabJoinMapped.code_cost q reader (r*3) C source (slabMap q buffer)
  have hc:=children_cost p (List.finRange C)
  change cost q (splitCode q reader C r source buffer)+cost q (childrenCode p (List.finRange C))+
    cost q (joinCode q reader C r source buffer)≤_
  dsimp only [splitCode,joinCode]
  rw [hs,hj]
  dsimp only [stride]
  omega

theorem code_length (reader : Fin q.inventory.readers) (p : Children q C r buffer work limit F) :
    (code reader source p).length≤childrenCharge p (List.finRange C)+12*(C*stride q (r*3)) := by
  rw [code,List.length_append,List.length_append]
  have hs:=CommonStaticSlabSplit.code_length q reader C (r*3) source (slabMap q buffer)
  have hj:=CommonStaticSlabJoinMapped.code_length q reader (r*3) C source (slabMap q buffer)
  have hc:=children_length p (List.finRange C)
  change (splitCode q reader C r source buffer).length+(childrenCode p (List.finRange C)).length+
    (joinCode q reader C r source buffer).length≤_
  dsimp only [splitCode,joinCode]
  rw [hs,hj]
  dsimp only [stride]
  omega

def program (reader : Fin q.inventory.readers) (p : Children q C r buffer work limit F)
    (hs : source+recordBlocks q (C*r)≤buffer)
    (hw : buffer+C*stride q (r*3)≤work) (hwl : work≤limit) (hl : limit≤q.N^q.exponent) :
    Program q (C*r) source buffer limit (batchOutput F) where
  instructions:=code reader source p
  charge:=childrenCharge p (List.finRange C)+12*(C*stride q (r*3))
  correct:=raw_correct reader p hs hw hwl hl
  frame:=raw_frame reader p hs hw hwl hl
  safe:=code_safe reader p
  cost_le:=code_cost reader p
  length_le:=code_length reader p

end
end CodedSorting.CommonSlabBatch
end SlabBatch
