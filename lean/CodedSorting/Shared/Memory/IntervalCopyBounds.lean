import CodedSorting.Shared.Programs.Static.MarginGather

section IntervalCopy
/-! Block-unaligned interval copying on the common finite machine.
Each destination block uses two public source pages. Two read/read/write
fragments preserve the words outside the live destination interval. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace CodedSorting.CommonIntervalCopy
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine Disk Store machine)
open CommonMarginTransform (wordAt)
noncomputable section

abbrev Block (q : Configuration) := Words q.block q.w
abbrev address := CommonColumnSplit.address

def firstPage (q : Configuration) (O D k : ℕ) := (O+(k*q.block-D))/q.block

def selected (q : Configuration) (O D N k p : ℕ) (a b : Block q) : Block q := fun i =>
  let j := k*q.block+i.val
  if D≤j ∧ j<D+N ∧ (O+(j-D))/q.block=p then
    a ⟨(O+(j-D))%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩
  else b i

def pairCode (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k p : ℕ) : List (Instruction q) :=
  [CommonBlockPair.sourceRead q reader (address q source p),
   CommonStaticMarginGather.secondRead q reader (address q target k) (selected q O D N k p),
   CommonBlockPair.targetWrite q (address q target k)]

theorem pair_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k p : ℕ) (s : Machine q) :
    (executeRaw q (pairCode q reader O D N source target k p) s).1.disk=
      Function.update s.disk (address q target k)
        (selected q O D N k p (s.disk (address q source p)) (s.disk (address q target k))) := by
  rw [←CommonBlockPair.machine_eta q s]
  simp only [pairCode,executeRaw,CommonBlockPair.sourceRead_step,
    CommonStaticMarginGather.secondRead_step,CommonBlockPair.targetWrite_step,
    CommonBlockPair.buffer_stash]
  rfl

def fragment (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k : ℕ) : List (Instruction q) :=
  pairCode q reader O D N source target k (firstPage q O D k) ++
    pairCode q reader O D N source target k (firstPage q O D k+1)

def assembled (q : Configuration) (O D N source target k : ℕ) (disk : Disk q) : Block q :=
  selected q O D N k (firstPage q O D k+1)
    (disk (address q source (firstPage q O D k+1)))
    (selected q O D N k (firstPage q O D k)
      (disk (address q source (firstPage q O D k))) (disk (address q target k)))

theorem fragment_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k : ℕ) (s : Machine q)
    (hsep : address q source (firstPage q O D k+1)≠address q target k) :
    (executeRaw q (fragment q reader O D N source target k) s).1.disk=
      Function.update s.disk (address q target k) (assembled q O D N source target k s.disk) := by
  rw [fragment,CommonPermutationPairs.raw_append,pair_raw,pair_raw]
  rw [Function.update_of_ne hsep,Function.update_self,Function.update_idem]
  rfl

theorem assembled_word (q : Configuration) (O D N source target k : ℕ)
    (disk : Disk q) (i : Fin q.block) :
    assembled q O D N source target k disk i=
      if D≤k*q.block+i.val ∧ k*q.block+i.val<D+N then
        disk (address q source ((O+(k*q.block+i.val-D))/q.block))
          ⟨(O+(k*q.block+i.val-D))%q.block,
            Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩
      else disk (address q target k) i := by
  have htwo := CommonMarginTransform.two_blocks q.block D O k i.val
    (CommonLeafProgram.block_positive q) i.isLt
  unfold assembled selected firstPage
  dsimp only
  by_cases h : D≤k*q.block+i.val ∧ k*q.block+i.val<D+N
  · rcases htwo with htwo|htwo
    · have hne : (O+(k*q.block+i.val-D))/q.block ≠ (O+(k*q.block-D))/q.block+1 := by omega
      simp [h.1,h.2,htwo,hne]
    · simp [h.1,h.2,htwo]
  · simp only [h,if_false]
    by_cases hl : D≤k*q.block+i.val
    · have hn : ¬k*q.block+i.val<D+N := by tauto
      simp [hl,hn]
    · simp [hl]

theorem pair_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k p : ℕ) :
    ∀ i∈pairCode q reader O D N source target k p,RespectsPC q i := by
  intro i hi
  simp only [pairCode,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl
  · exact CommonBlockPair.sourceRead_respectsPC q reader _
  · exact CommonStaticMarginGather.secondRead_safe q reader _ _
  · exact CommonBlockPair.targetWrite_respectsPC q _

theorem fragment_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k : ℕ) :
    ∀ i∈fragment q reader O D N source target k,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact pair_safe q reader O D N source target k _ i hi
  · exact pair_safe q reader O D N source target k _ i hi

def codeFrom (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) : ℕ → ℕ → List (Instruction q)
  | _,0 => []
  | k,n+1 => fragment q reader O D N source target k ++
    codeFrom q reader O D N source target (k+1) n

def pages (q : Configuration) (D N : ℕ) :=
  PhysicalStreamCursor.blockCount q.block (D%q.block+N)

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) : List (Instruction q) :=
  codeFrom q reader O D N source target (D/q.block) (pages q D N)

theorem codeFrom_length (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k n : ℕ) :
    (codeFrom q reader O D N source target k n).length=6*n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [codeFrom,List.length_append,ih]
    simp [fragment,pairCode]
    omega

theorem codeFrom_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k n : ℕ) :
    cost q (codeFrom q reader O D N source target k n)=6*n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [codeFrom,CommonPermutationPairs.cost_append,ih]
    have h : cost q (fragment q reader O D N source target k)=6 := rfl
    rw [h];omega

theorem codeFrom_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k n : ℕ) :
    ∀ i∈codeFrom q reader O D N source target k n,RespectsPC q i := by
  induction n generalizing k with
  | zero => simp [codeFrom]
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact fragment_safe q reader O D N source target k i hi
    · exact ih (k+1) i hi

structure Written (q : Configuration) (O D N source target start stop : ℕ)
    (original current : Disk q) : Prop where
  written : ∀ k,start≤k → k<stop → ∀ hk : target+k<q.N^q.exponent,
    current ⟨target+k,hk⟩=assembled q O D N source target k original
  outside : ∀ a : Fin (q.N^q.exponent),
    a.val<target+start ∨ target+stop≤a.val → current a=original a

def ReadsOutside (q : Configuration) (O D source target start stop : ℕ) : Prop :=
  ∀ k,start≤k → k<stop →
    ((address q source (firstPage q O D k)).val<target+start ∨
      target+stop≤(address q source (firstPage q O D k)).val) ∧
    ((address q source (firstPage q O D k+1)).val<target+start ∨
      target+stop≤(address q source (firstPage q O D k+1)).val)

theorem written_succ (q : Configuration) (O D N source target start k : ℕ)
    (original current : Disk q) (h : Written q O D N source target start k original current)
    (hsk : start≤k) (ht : target+k<q.N^q.exponent) :
    Written q O D N source target start (k+1) original
      (Function.update current ⟨target+k,ht⟩ (assembled q O D N source target k original)) := by
  constructor
  · intro j hj hjk hfit
    by_cases he : j=k
    · subst j;exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by intro heq;have:=congrArg Fin.val heq;dsimp at this;omega)]
      exact h.written j hj (by omega) hfit
  · intro a ha
    rw [Function.update_of_ne (by intro heq;have:=congrArg Fin.val heq;dsimp at this;omega)]
    exact h.outside a (by omega)

theorem raw_from (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target start k n stop : ℕ) (s : Machine q) (original : Disk q)
    (hsk : start≤k) (hlen : k+n=stop) (ht : target+stop≤q.N^q.exponent)
    (hsep : ReadsOutside q O D source target start stop)
    (hinv : Written q O D N source target start k original s.disk) :
    Written q O D N source target start stop original
      (executeRaw q (codeFrom q reader O D N source target k n) s).1.disk := by
  induction n generalizing k s with
  | zero => simpa only [codeFrom,executeRaw,Nat.add_zero] using hlen ▸ hinv
  | succ n ih =>
    rw [codeFrom,CommonPermutationPairs.raw_append]
    apply ih (k+1) _ (by omega) (by omega)
    have hk : k<stop := by omega
    have htk : target+k<q.N^q.exponent := by omega
    have hsrc := hsep k hsk hk
    have hr1 := hinv.outside (address q source (firstPage q O D k)) (by
      rcases hsrc.1 with h|h
      · exact Or.inl h
      · exact Or.inr (by omega))
    have hr2 := hinv.outside (address q source (firstPage q O D k+1)) (by
      rcases hsrc.2 with h|h
      · exact Or.inl h
      · exact Or.inr (by omega))
    have ha : address q target k=⟨target+k,htk⟩ := by simp [address,CommonColumnSplit.address,htk]
    have hrt := hinv.outside (address q target k) (by rw [ha];exact Or.inr (by simp))
    have hne : address q source (firstPage q O D k+1)≠address q target k := by
      intro he
      have hv := congrArg Fin.val he
      rw [ha] at hv
      dsimp at hv
      rcases hsrc.2 with h|h <;> omega
    rw [fragment_raw q reader O D N source target k s hne]
    have hb : assembled q O D N source target k s.disk=
        assembled q O D N source target k original := by
      simp only [assembled,hr1,hr2,hrt]
    rw [hb,ha]
    exact written_succ q O D N source target start k original s.disk hinv hsk htk

theorem raw (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) (s : Machine q)
    (ht : target+D/q.block+pages q D N≤q.N^q.exponent)
    (hsep : ReadsOutside q O D source target (D/q.block) (D/q.block+pages q D N)) :
    Written q O D N source target (D/q.block) (D/q.block+pages q D N) s.disk
      (executeRaw q (code q reader O D N source target) s).1.disk := by
  apply raw_from q reader O D N source target (D/q.block) (D/q.block) (pages q D N)
    (D/q.block+pages q D N) s s.disk le_rfl rfl (by omega) hsep
  exact ⟨by intros;omega,by intros;rfl⟩

theorem pair_leaf (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k p : ℕ) (s : Machine q) :
    (unpack (executeRaw q (pairCode q reader O D N source target k p) s).1.ram).leaf=
      (unpack s.ram).leaf := by
  rw [←CommonBlockPair.machine_eta q s]
  simp only [pairCode,executeRaw,CommonBlockPair.sourceRead_step,
    CommonStaticMarginGather.secondRead_step,CommonBlockPair.targetWrite_step,
    CommonBlockPair.buffer_stash]
  simp only [machine,unpack_pack]
  rfl

theorem codeFrom_leaf (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k n : ℕ) (s : Machine q) :
    (unpack (executeRaw q (codeFrom q reader O D N source target k n) s).1.ram).leaf=
      (unpack s.ram).leaf := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    rw [codeFrom,CommonPermutationPairs.raw_append,ih]
    rw [fragment,CommonPermutationPairs.raw_append,pair_leaf,pair_leaf]


theorem disk_word (q : Configuration) (disk : Disk q) (base j : ℕ)
    (hj : base+j/q.block<q.N^q.exponent) :
    disk (address q base (j/q.block))
      ⟨j%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩=wordAt q disk base j := by
  simp [address,CommonColumnSplit.address,hj,wordAt,CommonLeafBatchProgram.extendDisk]

theorem written_word (q : Configuration) (O D N source target : ℕ)
    (original current : Disk q)
    (hw : Written q O D N source target (D/q.block) (D/q.block+pages q D N) original current)
    (hs : source+PhysicalStreamCursor.blockCount q.block (O+N)≤q.N^q.exponent)
    (hcover : ∀ j,D≤j → j<D+N → D/q.block≤j/q.block ∧ j/q.block<D/q.block+pages q D N)
    (j : ℕ) (hj : target+j/q.block<q.N^q.exponent) :
    wordAt q current target j=
      if D≤j ∧ j<D+N then wordAt q original source (O+(j-D)) else wordAt q original target j := by
  have hdiv : j/q.block*q.block+j%q.block=j := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod j q.block
  rw [←disk_word q current target j hj]
  by_cases hp : D/q.block≤j/q.block ∧ j/q.block<D/q.block+pages q D N
  · have ha : address q target (j/q.block)=⟨target+j/q.block,hj⟩ := by
      simp [address,CommonColumnSplit.address,hj]
    rw [ha,hw.written (j/q.block) hp.1 hp.2 hj,assembled_word]
    simp only [Fin.val_mk,hdiv]
    by_cases hl : D≤j ∧ j<D+N
    · rw [if_pos hl,if_pos hl]
      have hj' : O+(j-D)<O+N := by omega
      have hb : (O+(j-D))/q.block<PhysicalStreamCursor.blockCount q.block (O+N) := by
        apply (PhysicalStreamCursor.cursor_live_iff q.block (O+N) _
          (CommonLeafProgram.block_positive q)).2
        exact (Nat.div_mul_le_self _ _).trans_lt hj'
      exact disk_word q original source (O+(j-D)) (by omega)
    · rw [if_neg hl,if_neg hl]
      exact disk_word q original target j hj
  · have hl : ¬(D≤j ∧ j<D+N) := fun h => hp (hcover j h.1 h.2)
    rw [if_neg hl]
    have ha : (address q target (j/q.block)).val=target+j/q.block :=
      CommonColumnSplit.address_val q target (j/q.block) hj
    rw [hw.outside (address q target (j/q.block)) (by rw [ha];omega)]
    exact disk_word q original target j hj

/-- Same-run copying, including preservation of unused words in boundary
blocks. The source and destination offsets are word offsets. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) (s : Machine q)
    (hs : source+PhysicalStreamCursor.blockCount q.block (O+N)≤q.N^q.exponent)
    (ht : target+D/q.block+pages q D N≤q.N^q.exponent)
    (hsep : ReadsOutside q O D source target (D/q.block) (D/q.block+pages q D N))
    (hcover : ∀ j,D≤j → j<D+N → D/q.block≤j/q.block ∧ j/q.block<D/q.block+pages q D N)
    (hsize : 6*pages q D N≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let instructions := code q reader O D N source target
    let result := ControlledNormalization.runLogical (policy q instructions) instructions.length s
    (∀ j,target+j/q.block<q.N^q.exponent → wordAt q result.1.disk target j=
      if D≤j ∧ j<D+N then wordAt q s.disk source (O+(j-D)) else wordAt q s.disk target j) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target+D/q.block ∨
      target+D/q.block+pages q D N≤a.val → result.1.disk a=s.disk a) ∧
    policy q instructions result.1.ram=none ∧ result.2=6*pages q D N ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q (code q reader O D N source target)
    (by simpa only [code,codeFrom_length] using hsize)
    (codeFrom_safe q reader O D N source target _ _) s hpc
  have hw := raw q reader O D N source target s ht hsep
  refine ⟨?_,?_,hh,?_,hm⟩
  · intro j hj
    rw [hd]
    exact written_word q O D N source target s.disk _ hw hs hcover j hj
  · intro a ha
    rw [hd]
    exact hw.outside a (by omega)
  · exact hc.trans (codeFrom_cost q reader O D N source target _ _)


@[simp] theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) :
    (code q reader O D N source target).length=6*pages q D N :=
  codeFrom_length q reader O D N source target _ _

@[simp] theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) : cost q (code q reader O D N source target)=6*pages q D N :=
  codeFrom_cost q reader O D N source target _ _

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) :
    ∀ i∈code q reader O D N source target,RespectsPC q i :=
  codeFrom_safe q reader O D N source target _ _

theorem pair_preserved (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k p : ℕ) (s : Machine q) :
    CommonMovementPolicy.Preserved q (unpack s.ram)
      (unpack (executeRaw q (pairCode q reader O D N source target k p) s).1.ram) := by
  rw [←CommonBlockPair.machine_eta q s]
  simp only [pairCode,executeRaw,CommonBlockPair.sourceRead_step,
    CommonStaticMarginGather.secondRead_step,CommonBlockPair.targetWrite_step,
    CommonBlockPair.buffer_stash]
  simp only [machine,unpack_pack]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem codeFrom_preserved (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target k n : ℕ) (s : Machine q) :
    CommonMovementPolicy.Preserved q (unpack s.ram)
      (unpack (executeRaw q (codeFrom q reader O D N source target k n) s).1.ram) := by
  induction n generalizing k s with
  | zero => exact CommonMovementPolicy.Preserved.refl q _
  | succ n ih =>
    rw [codeFrom,CommonPermutationPairs.raw_append]
    apply CommonMovementPolicy.Preserved.trans q ?_ (ih (k+1) _)
    rw [fragment,CommonPermutationPairs.raw_append]
    exact CommonMovementPolicy.Preserved.trans q
      (pair_preserved q reader O D N source target k _ s)
      (pair_preserved q reader O D N source target k _ _)

theorem code_preserved (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) (s : Machine q) :
    CommonMovementPolicy.Preserved q (unpack s.ram)
      (unpack (executeRaw q (code q reader O D N source target) s).1.ram) :=
  codeFrom_preserved q reader O D N source target _ _ s

end
end CodedSorting.CommonIntervalCopy
end IntervalCopy

section IntervalCopyBounds
/-! Block arithmetic for copying an arbitrary live word interval. Two
source guard pages suffice, and destination misalignment adds at most one
page to the scan. -/
set_option autoImplicit false
namespace CodedSorting.CommonIntervalCopyBounds
open CommonSortingNormalization CommonIntervalCopy
open CommonStaticSchedule
open CommonLeafProgram (Machine Disk)
open CommonMarginTransform (wordAt)
noncomputable section

theorem pages_le (q : Configuration) (D N : ℕ) :
    pages q D N≤PhysicalStreamCursor.blockCount q.block N+1 := by
  have hb := CommonLeafProgram.block_positive q
  have hm := Nat.mod_lt D hb
  have hc := LayoutConversion.blockCount_covers N q.block hb
  unfold pages PhysicalStreamCursor.blockCount
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hb).2
  change N≤((N+q.block-1)/q.block)*q.block at hc
  have ht : D%q.block+N+q.block-1<D%q.block+N+q.block := by omega
  nlinarith

theorem page_start_lt (q : Configuration) (D N k : ℕ)
    (hk : k<D/q.block+pages q D N) : k*q.block<D+N+q.block := by
  have hb := CommonLeafProgram.block_positive q
  have he := Nat.div_add_mod D q.block
  have hc := LocalSortingCost.blockCount_capacity q.block hb (D%q.block+N)
  change pages q D N*q.block≤D%q.block+N+q.block at hc
  have hm := Nat.mul_lt_mul_of_pos_right hk hb
  nlinarith

theorem live_page (q : Configuration) (D N j : ℕ)
    (hl : D≤j) (hr : j<D+N) :
    D/q.block≤j/q.block ∧ j/q.block<D/q.block+pages q D N := by
  have hb := CommonLeafProgram.block_positive q
  have he := Nat.div_add_mod D q.block
  have hc := LayoutConversion.blockCount_covers (D%q.block+N) q.block hb
  change D%q.block+N≤pages q D N*q.block at hc
  refine ⟨Nat.div_le_div_right hl,?_⟩
  apply (Nat.div_lt_iff_lt_mul hb).2
  nlinarith

theorem source_pages (q : Configuration) (O D N k : ℕ)
    (hk : k<D/q.block+pages q D N) :
    firstPage q O D k<PhysicalStreamCursor.blockCount q.block (O+N)+2 ∧
    firstPage q O D k+1<PhysicalStreamCursor.blockCount q.block (O+N)+2 := by
  have hb := CommonLeafProgram.block_positive q
  have hstart := page_start_lt q D N k hk
  have ht : k*q.block-D<N+q.block := by omega
  have hc := LayoutConversion.blockCount_covers (O+N) q.block hb
  change O+N≤PhysicalStreamCursor.blockCount q.block (O+N)*q.block at hc
  have hfirst : firstPage q O D k≤PhysicalStreamCursor.blockCount q.block (O+N) := by
    unfold firstPage
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hb).2
    nlinarith
  omega

theorem readsOutside (q : Configuration) (O D N source target : ℕ)
    (hs : source+PhysicalStreamCursor.blockCount q.block (O+N)+2≤q.N^q.exponent)
    (hsep : source+PhysicalStreamCursor.blockCount q.block (O+N)+2≤target+D/q.block ∨
      target+D/q.block+pages q D N≤source) :
    ReadsOutside q O D source target (D/q.block) (D/q.block+pages q D N) := by
  intro k _ hk
  obtain ⟨hfirst,hsecond⟩ := source_pages q O D N k hk
  rw [CommonColumnSplit.address_val q source _ (by omega),
    CommonColumnSplit.address_val q source _ (by omega)]
  omega

/-- The arithmetic coverage condition is automatic. Separation is stated
for public source and destination extents, including two harmless guards. -/
theorem raw_word (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) (s : Machine q)
    (hs : source+PhysicalStreamCursor.blockCount q.block (O+N)+2≤q.N^q.exponent)
    (ht : target+D/q.block+pages q D N≤q.N^q.exponent)
    (hsep : source+PhysicalStreamCursor.blockCount q.block (O+N)+2≤target+D/q.block ∨
      target+D/q.block+pages q D N≤source)
    (j : ℕ) (hj : target+j/q.block<q.N^q.exponent) :
    wordAt q (executeRaw q (code q reader O D N source target) s).1.disk target j=
      if D≤j ∧ j<D+N then wordAt q s.disk source (O+(j-D))
      else wordAt q s.disk target j := by
  exact written_word q O D N source target s.disk _
    (raw q reader O D N source target s ht (readsOutside q O D N source target hs hsep))
    (by omega) (live_page q D N) j hj

theorem cost_le (q : Configuration) (reader : Fin q.inventory.readers)
    (O D N source target : ℕ) :
    cost q (code q reader O D N source target)≤
      6*(PhysicalStreamCursor.blockCount q.block N+1) := by
  rw [code_cost]
  exact Nat.mul_le_mul_left 6 (pages_le q D N)

end
end CodedSorting.CommonIntervalCopyBounds
end IntervalCopyBounds
