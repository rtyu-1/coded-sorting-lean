import CodedSorting.Interchange.Framework.Memory.PhysicalNormalizationLayout

/-! The inverse layout converter, on the same finite bank-disk model.
Eight fixed phases perform one source read and two read-modify-write pairs.
A spare target block makes the second access of the last logical block valid;
it is harmless when the logical block does not cross a physical boundary.
-/
set_option autoImplicit false
namespace CodedSorting.PhysicalNormalizationCompact
open WordControl PhysicalNormalizationLayout
variable {R B b d w : ℕ}

def step (p : Program R B b d w) (s : State R B b d w) : State R B b d w × ℕ :=
  let j := current s
  if j<p.blocks then
    match s.phase.val with
    | 0 => (nextPhase p 1 {s with buffer := s.disk (.inl (index p j))},1)
    | 1 => (nextPhase p 2 {s with scratch := fun i => s.buffer (i.castLE p.block_ratio)},0)
    | 2 => (nextPhase p 3 {s with buffer := s.disk (.inr (index p (j*b/B)))},1)
    | 3 => (nextPhase p 4 {s with buffer := LayoutConversion.patchBuffer B b (j*b) (j*b/B) s.scratch s.buffer},0)
    | 4 => (nextPhase p 5 {s with disk := Function.update s.disk (.inr (index p (j*b/B))) s.buffer},1)
    | 5 => (nextPhase p 6 {s with buffer := s.disk (.inr (index p (j*b/B+1)))},1)
    | 6 => (nextPhase p 7 {s with buffer := LayoutConversion.patchBuffer B b (j*b) (j*b/B+1) s.scratch s.buffer},0)
    | 7 => (nextPhase p 0 {s with counter := counterCode d w (j+1), disk := Function.update s.disk (.inr (index p (j*b/B+1))) s.buffer},1)
    | _ => (s,0)
  else (s,0)

def run (p : Program R B b d w) : ℕ → State R B b d w → State R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)

def patch (p : Program R B b d w) (disk : Disk R B w) (start block : ℕ)
    (scratch : Words b w) : Disk R B w :=
  Function.update disk (.inr (index p block))
    (LayoutConversion.patchBuffer B b start block scratch (disk (.inr (index p block))))

def compacted (p : Program R B b d w) (disk : Disk R B w) (j : ℕ) : Disk R B w :=
  let scratch : Words b w := fun i => disk (.inl (index p j)) (i.castLE p.block_ratio)
  patch p (patch p disk (j*b) (j*b/B) scratch) (j*b) (j*b/B+1) scratch

theorem run_add (p : Program R B b d w) (n m : ℕ) (s : State R B b d w) :
    run p (n+m) s =
      ((run p m (run p n s).1).1,(run p n s).2+(run p m (run p n s).1).2) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => rw [Nat.succ_add]; simp only [run,ih,Nat.add_assoc]

theorem eight_steps (p : Program R B b d w) (s : State R B b d w)
    (j : ℕ) (hj : j<p.blocks) (hc : current s=j) (hp : s.phase=phaseCode p 0) :
    (run p 8 s).1.disk=compacted p s.disk j ∧
    current (run p 8 s).1=j+1 ∧
    (run p 8 s).1.phase=phaseCode p 0 ∧ (run p 8 s).2=5 := by
  simp only [run,step,current,nextPhase,phaseCode] at *
  simp only [hc,hj,↓reduceIte,hp]
  norm_num
  simp only [compacted,patch,decode_counterCode]
  constructor
  · simp [Function.update_apply]
  · exact Nat.mod_eq_of_lt (show j+1<(2^w)^d by have := p.counter_bound; omega)

def compactedLoop (p : Program R B b d w) : ℕ → Disk R B w → Disk R B w
  | 0,disk => disk
  | n+1,disk => compacted p (compactedLoop p n disk) n

theorem loop_refines (p : Program R B b d w) (disk : Disk R B w)
    (n : ℕ) (hn : n≤p.blocks) :
    (run p (8*n) (initial p 0 disk)).1.disk=compactedLoop p n disk ∧
    current (run p (8*n) (initial p 0 disk)).1=n ∧
    (run p (8*n) (initial p 0 disk)).1.phase=phaseCode p 0 ∧
    (run p (8*n) (initial p 0 disk)).2=5*n := by
  induction n with
  | zero => simp [run,initial,current,compactedLoop]
  | succ n ih =>
    have prev := ih (by omega)
    have hs := eight_steps p (run p (8*n) (initial p 0 disk)).1 n
      (by omega) prev.2.1 prev.2.2.1
    rw [show 8*(n+1)=8*n+8 by omega,run_add]
    refine ⟨?_,hs.2.1,hs.2.2.1,?_⟩
    · rw [hs.1,prev.1]
      rfl
    · rw [prev.2.2.2,hs.2.2.2]
      omega

theorem patch_source (p : Program R B b d w) (disk : Disk R B w)
    (start block : ℕ) (scratch : Words b w) (i : Fin R) :
    patch p disk start block scratch (.inl i)=disk (.inl i) := by simp [patch]

theorem compacted_source (p : Program R B b d w) (disk : Disk R B w)
    (j : ℕ) (i : Fin R) : compacted p disk j (.inl i)=disk (.inl i) := by
  simp only [compacted,patch_source]

theorem compactedLoop_source (p : Program R B b d w) (disk : Disk R B w)
    (n : ℕ) (i : Fin R) : compactedLoop p n disk (.inl i)=disk (.inl i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [compactedLoop,compacted_source,ih]

def targetWord (p : Program R B b d w) (disk : Disk R B w) : BlockReflection.Disk (Word w) :=
  fun y => disk (.inr (index p (y/B))) ⟨y%B,Nat.mod_lt _ p.positive_block⟩

/-- A physical read-modify-write changes precisely its logical interval,
and retains every other word of that physical block. -/
theorem patch_target (p : Program R B b d w) (disk : Disk R B w)
    (start block y : ℕ) (scratch : Words b w) (hk : block<R) (hy : y/B<R) :
    targetWord p (patch p disk start block scratch) y =
      if y/B=block then LayoutConversion.overlay start scratch (targetWord p disk) y
        else targetWord p disk y := by
  by_cases he : y/B=block
  · have hi : index p (y/B)=index p block := congrArg (index p) he
    have hm : block*B+y%B=y := by
      rw [←he]
      simpa [Nat.mul_comm] using Nat.div_add_mod y B
    simp only [targetWord,patch,hi,Function.update_self,if_pos he,
      LayoutConversion.patchBuffer,hm,LayoutConversion.overlay]
  · have hi : index p (y/B)≠index p block := by
      intro hh
      have hv := congrArg Fin.val hh
      rw [index_val p (y/B) hy,index_val p block hk] at hv
      exact he hv
    simp only [targetWord,patch,Function.update_of_ne (show Sum.inr (index p (y/B))≠Sum.inr (index p block) from fun h => hi (Sum.inr.inj h)),if_neg he]

/-- The extra target block makes both neighbouring block accesses ordinary
in-range physical addresses, including the last logical block. -/
theorem neighbour_bound (p : Program R B b d w) (hspare : p.blocks<R)
    (j : ℕ) (hj : j<p.blocks) : j*b/B+1<R := by
  have hm : j*b≤j*B := Nat.mul_le_mul_left j p.block_ratio
  have hd := Nat.div_le_div_right (c:=B) hm
  have he : j*B/B=j := Nat.mul_div_cancel j p.positive_block
  rw [he] at hd
  omega

/-- Both actual block patches together are precisely the desired overwrite
of b consecutive words; no surrounding target word is lost. -/
theorem compacted_target (p : Program R B b d w) (hspare : p.blocks<R)
    (disk : Disk R B w) (j : ℕ) (hj : j<p.blocks) (y : ℕ) (hy : y/B<R) :
    targetWord p (compacted p disk j) y =
      LayoutConversion.overlay (j*b)
        (fun i : Fin b => disk (.inl (index p j)) (i.castLE p.block_ratio))
        (targetWord p disk) y := by
  have hn := neighbour_bound p hspare j hj
  unfold compacted
  rw [patch_target p _ (j*b) (j*b/B+1) y _ hn hy]
  by_cases hint : j*b≤y ∧ y<j*b+b
  · have hc := LayoutConversion.two_blocks B b (j*b) (y-j*b) p.positive_block
      p.block_ratio (by omega)
    have he : j*b+(y-j*b)=y := by omega
    rw [he] at hc
    rcases hc with hc|hc
    · rw [if_neg (by omega),patch_target p _ (j*b) (j*b/B) y _ (by omega) hy,
        if_pos hc]
    · simp only [if_pos hc,LayoutConversion.overlay,dif_pos hint]
  · simp only [LayoutConversion.overlay,dif_neg hint]
    split_ifs <;> rw [patch_target p _ (j*b) (j*b/B) y _ (by omega) hy] <;>
      simp [LayoutConversion.overlay,hint]

theorem compactedLoop_target (p : Program R B b d w) (hspare : p.blocks<R)
    (disk : Disk R B w) (n : ℕ) (hn : n≤p.blocks) (j : ℕ) (hj : j<n)
    (i : Fin b) :
    targetWord p (compactedLoop p n disk) (j*b+i.val) =
      disk (.inl (index p j)) (i.castLE p.block_ratio) := by
  have hy : (j*b+i.val)/B<R := by
    apply (Nat.div_lt_iff_lt_mul p.positive_block).2
    have hm := Nat.mul_le_mul_right b (show j+1≤p.blocks by omega)
    have hnR := Nat.mul_le_mul_right b p.block_bound
    have hbR := Nat.mul_le_mul_left R p.block_ratio
    have hi := i.isLt
    nlinarith
  induction n with
  | zero => omega
  | succ n ih =>
    rw [compactedLoop,compacted_target p hspare _ n (by omega) _ hy]
    by_cases he : j=n
    · subst j
      have hint : n*b≤n*b+i.val ∧ n*b+i.val<n*b+b := by
        constructor <;> have := i.isLt <;> omega
      simp only [LayoutConversion.overlay,dif_pos hint]
      simp only [Nat.add_sub_cancel_left,Fin.eta,compactedLoop_source]
    · have hm := Nat.mul_le_mul_right b (show j+1≤n by omega)
      have hnot : ¬(n*b≤j*b+i.val ∧ j*b+i.val<n*b+b) := by
        rintro ⟨hlo,_⟩
        have := i.isLt
        nlinarith
      rw [LayoutConversion.overlay,dif_neg hnot]
      exact ih (by omega) (by omega)

/-- No unrelated compact target word is overwritten, including the unused
suffix of the last block and the reserved neighbouring block. -/
theorem compactedLoop_outside (p : Program R B b d w) (hspare : p.blocks<R)
    (disk : Disk R B w) (n : ℕ) (hn : n≤p.blocks) (y : ℕ)
    (hy : y/B<R) (hout : n*b≤y) :
    targetWord p (compactedLoop p n disk) y=targetWord p disk y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [compactedLoop,compacted_target p hspare _ n (by omega) y hy]
    have hnot : ¬(n*b≤y ∧ y<n*b+b) := by
      rintro ⟨_,hhi⟩
      nlinarith
    rw [LayoutConversion.overlay,dif_neg hnot]
    exact ih (by omega) (by nlinarith)

/-- Correctness and cost of the SAME fixed eight-phase execution, with both
source preservation and preservation of untouched target words. -/
theorem actual_compaction (p : Program R B b d w) (hspare : p.blocks<R)
    (disk : Disk R B w) :
    let result := run p (8*p.blocks) (initial p 0 disk)
    (∀ j : Fin p.blocks,∀ i : Fin b,
      targetWord p result.1.disk (j.val*b+i.val)=
        disk (.inl (index p j.val)) (i.castLE p.block_ratio)) ∧
    (∀ i : Fin R,result.1.disk (.inl i)=disk (.inl i)) ∧
    (∀ y,p.blocks*b≤y → y/B<R → targetWord p result.1.disk y=targetWord p disk y) ∧
    current result.1=p.blocks ∧ result.1.phase=phaseCode p 0 ∧ result.2=5*p.blocks := by
  dsimp only
  have h := loop_refines p disk p.blocks (le_refl _)
  refine ⟨?_,?_,?_,h.2.1,h.2.2.1,h.2.2.2⟩
  · intro j i
    rw [h.1]
    exact compactedLoop_target p hspare disk p.blocks (le_refl _) j.val j.isLt i
  · intro i
    rw [h.1,compactedLoop_source]
  · intro y hout hy
    rw [h.1]
    exact compactedLoop_outside p hspare disk p.blocks (le_refl _) y hy hout

theorem completed_halts (p : Program R B b d w) (hspare : p.blocks<R)
    (disk : Disk R B w) :
    step p (run p (8*p.blocks) (initial p 0 disk)).1 =
      ((run p (8*p.blocks) (initial p 0 disk)).1,0) := by
  have h := (actual_compaction p hspare disk).2.2.2.1
  simp [step,h]

/-- A fixed address renaming exchanges the two regions of the SAME disk.
It is a change of address interface, not a copy of either disk region. -/
def swapped (disk : Disk R B w) : Disk R B w := fun a => disk a.swap

@[simp] theorem swapped_twice (disk : Disk R B w) : swapped (swapped disk)=disk := by
  funext a
  cases a <;> rfl

/-- A complete actual roundtrip: expansion first, then compaction with source
and target address roles exchanged. No intermediate mathematical source disk
is supplied to the second execution; it reads the first execution's result. -/
theorem actual_roundtrip (p : Program R B b d w) (hspare : p.blocks<R)
    (disk : Disk R B w) :
    let expandedRun := PhysicalNormalizationLayout.run p (7*p.blocks) (initial p 0 disk)
    let compactRun := run p (8*p.blocks) (initial p 0 (swapped expandedRun.1.disk))
    (∀ j : Fin p.blocks,∀ i : Fin b,
      targetWord p compactRun.1.disk (j.val*b+i.val)=sourceWord p disk (j.val*b+i.val)) ∧
    expandedRun.2+compactRun.2=8*p.blocks := by
  dsimp only
  have he := actual_expansion p disk
  have hc := actual_compaction p hspare
    (swapped (PhysicalNormalizationLayout.run p (7*p.blocks) (initial p 0 disk)).1.disk)
  constructor
  · intro j i
    rw [hc.1 j i]
    change (PhysicalNormalizationLayout.run p (7*p.blocks) (initial p 0 disk)).1.disk
      (.inr (index p j.val)) (i.castLE p.block_ratio)=_
    simpa only [Fin.coe_castLE,if_pos i.isLt] using he.1 j (i.castLE p.block_ratio)
  · rw [he.2.2.2.2,hc.2.2.2.2.2]
    omega

/-- The concrete input-independent compactor also exposes its fixed-program
quantifier order directly. -/
theorem one_program_all_inputs (p : Program R B b d w) (hspare : p.blocks<R) :
    ∃ machine : ℕ → State R B b d w → State R B b d w × ℕ,
      ∀ disk : Disk R B w,
      (∀ j : Fin p.blocks,∀ i : Fin b,
        targetWord p (machine (8*p.blocks) (initial p 0 disk)).1.disk (j.val*b+i.val)=
          disk (.inl (index p j.val)) (i.castLE p.block_ratio)) ∧
      (machine (8*p.blocks) (initial p 0 disk)).2=5*p.blocks := by
  refine ⟨run p,?_⟩
  intro disk
  have h := actual_compaction p hspare disk
  exact ⟨h.1,h.2.2.2.2.2⟩

end CodedSorting.PhysicalNormalizationCompact
