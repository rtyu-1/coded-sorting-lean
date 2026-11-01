import CodedSorting.Interchange.Framework.Fields.PhysicalExchange

section Compose
/-! Sequential machine composition for two physical field chunks.  The second
instruction list runs on the first list's actual resulting machine. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonChunkExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonChunkLayout CommonFinitePermutation
noncomputable section

theorem head_word_volume (P Q R G S w : ℕ) :
    Volume P Q (R*G) ((R*S)*w)=Volume P (Q*R) G (S*w) := by
  unfold Volume BaseExchangeProgram.Volume
  ring

theorem tail_word_volume (P Q R G S w : ℕ) :
    Volume (P*Q) R (G*Q) (S*w)=Volume P (Q*R) G (S*w) := by
  unfold Volume BaseExchangeProgram.Volume
  ring

def emptyProgram (q : Configuration) (P G S source buffer limit : ℕ) :
    Program q (Volume P 1 G (S*q.w)) source buffer limit
      (swap P 1 G (S*q.w)) where
  instructions := []
  charge := 0
  correct := by intro s y; simp only [swap_one]; rfl
  frame := fun _ _ _ _ => rfl
  safe := by simp
  cost_le := Nat.le_refl 0
  length_le := Nat.le_refl 0

def combine (q : Configuration) (P Q R G S source buffer limit : ℕ)
    (p₁ : Program q (Volume P Q (R*G) ((R*S)*q.w)) source buffer limit
      (swap P Q (R*G) ((R*S)*q.w)))
    (p₂ : Program q (Volume (P*Q) R (G*Q) (S*q.w)) source buffer limit
      (swap (P*Q) R (G*Q) (S*q.w))) :
    Program q (Volume P (Q*R) G (S*q.w)) source buffer limit
      (swap P (Q*R) G (S*q.w)) where
  instructions := p₁.instructions++p₂.instructions
  charge := p₁.charge+p₂.charge
  correct := by
    intro s y
    rw [raw_append]
    exact head_tail_correct_words P Q R G S q.w
      (readBit q s.disk source)
      (readBit q (executeRaw q p₁.instructions s).1.disk source)
      (readBit q (executeRaw q p₂.instructions
        (executeRaw q p₁.instructions s).1).1.disk source)
      (p₁.correct s) (p₂.correct _) y
  frame := by
    intro s a hs hw
    have hs₁ : a.val<source ∨
        source+count q (Volume P Q (R*G) ((R*S)*q.w))≤a.val := by
      simpa only [head_word_volume] using hs
    have hs₂ : a.val<source ∨
        source+count q (Volume (P*Q) R (G*Q) (S*q.w))≤a.val := by
      simpa only [tail_word_volume] using hs
    rw [raw_append,p₂.frame _ a hs₂ hw,p₁.frame s a hs₁ hw]
  safe := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact p₁.safe i hi
    · exact p₂.safe i hi
  cost_le := by
    rw [cost_append]
    exact Nat.add_le_add p₁.cost_le p₂.cost_le
  length_le := by
    rw [List.length_append]
    exact Nat.add_le_add p₁.length_le p₂.length_le

@[simp] theorem combine_charge (q : Configuration) (P Q R G S source buffer limit : ℕ)
    (p₁ : Program q (Volume P Q (R*G) ((R*S)*q.w)) source buffer limit
      (swap P Q (R*G) ((R*S)*q.w)))
    (p₂ : Program q (Volume (P*Q) R (G*Q) (S*q.w)) source buffer limit
      (swap (P*Q) R (G*Q) (S*q.w))) :
    (combine q P Q R G S source buffer limit p₁ p₂).charge=p₁.charge+p₂.charge := rfl

end
end CodedSorting.CommonChunkExchange
end Compose

section Cost
/-! Arithmetic for unequal-width chunks executed by the common machine.
The recurrence is the common machine's resident/buffered recurrence;
only the established geometric identities are reused from the file model.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonChunkCost
open Circuit RecursiveExchange ArbitrarySchedule
open PhysicalChunkBound
noncomputable section

def totalBound (cutoff b : ℕ) (cs : List ArbitraryRecursive.Call) (V : ℕ) : ℕ :=
  (cs.map fun c => CommonRecursiveExchange.Pruned.costBound b cutoff c.depth V).sum

@[simp] theorem totalBound_nil (cutoff b V : ℕ) : totalBound cutoff b [] V=0 := rfl

@[simp] theorem totalBound_cons (cutoff b V : ℕ) (c : ArbitraryRecursive.Call)
    (cs : List ArbitraryRecursive.Call) :
    totalBound cutoff b (c::cs) V=
      CommonRecursiveExchange.Pruned.costBound b cutoff c.depth V+
      totalBound cutoff b cs V := rfl

theorem totalBound_improved (cutoff b V : ℕ) (hb : 0<b)
    (hcut : Parameters.W*b≤cutoff) (cs : List ArbitraryRecursive.Call) :
    (totalBound cutoff b cs V : ℝ)≤CommonRecursiveExchange.Pruned.boundConstant*
      (1+(V : ℝ)/b)*weight cs := by
  induction cs with
  | nil => simp [totalBound,weight]
  | cons c cs ih =>
    have hcost := CommonRecursiveExchange.Pruned.costBound_transfers b cutoff c.depth V hb hcut
    rw [ratio_power] at hcost
    have hp : (1 : ℝ)≤ratio^c.depth := one_le_pow₀ ratio_gt_one.le
    have hstep : (CommonRecursiveExchange.Pruned.costBound b cutoff c.depth V : ℝ)≤
        CommonRecursiveExchange.Pruned.boundConstant*(1+(V : ℝ)/b)*ratio^c.depth := by
      have hh := mul_le_mul_of_nonneg_left
        (show 1+(V : ℝ)/b*ratio^c.depth≤(1+(V : ℝ)/b)*ratio^c.depth by nlinarith)
        CommonRecursiveExchange.Pruned.boundConstant_nonneg
      simpa only [mul_assoc] using hcost.trans hh
    simp only [totalBound,List.map_cons,List.sum_cons,Nat.cast_add,weight] at ih ⊢
    nlinarith

theorem calls_totalBound (cutoff b V base k e : ℕ) (hb : 0<b)
    (hcut : Parameters.W*b≤cutoff) (he : e/base<Parameters.m^(k+1)) :
    (totalBound cutoff b (ArbitraryRecursive.calls base k e) V : ℝ)≤
      CommonRecursiveExchange.Pruned.boundConstant*(1+(V : ℝ)/b)*Parameters.m*
        geometric ratio k := by
  have hC : 0≤CommonRecursiveExchange.Pruned.boundConstant*(1+(V : ℝ)/b) :=
    mul_nonneg CommonRecursiveExchange.Pruned.boundConstant_nonneg (by positivity)
  have hs := mul_le_mul_of_nonneg_left (calls_weight_bound base k e he) hC
  exact (totalBound_improved cutoff b V hb hcut _).trans
    (by simpa only [mul_assoc] using hs)

theorem base_totalBound (cutoff b V base e : ℕ) :
    totalBound cutoff b (ArbitraryRecursive.baseCalls base e) V=
      (e/base+1)*(20*(V/b+1)) := by
  simp [totalBound,ArbitraryRecursive.baseCalls,CommonRecursiveExchange.Pruned.costBound,
    List.sum_replicate,smul_eq_mul]
  ring

theorem fallback_bound (cutoff b V base e k : ℕ)
    (he : e≤borrowedWidth radix Parameters.W k) :
    (totalBound cutoff b (ArbitraryRecursive.baseCalls base e) V : ℝ)≤
      (20*(PhysicalArbitraryBound.borrowing+1))*PhysicalArbitraryBound.scan b V*
        geometric ratio k := by
  have hdiv : e/base≤borrowedWidth radix Parameters.W k := (Nat.div_le_self _ _).trans he
  have hr : ((e/base : ℕ) : ℝ)≤borrowedWidth radix Parameters.W k := by exact_mod_cast hdiv
  have hρ := PhysicalArbitraryBound.rho_bound k
  have hg := PhysicalArbitraryBound.geometric_one k
  have hn : ((e/base+1 : ℕ) : ℝ)≤(PhysicalArbitraryBound.borrowing+1)*geometric ratio k := by
    push_cast
    nlinarith
  have hm := mul_le_mul hn (PhysicalArbitraryBound.nat_scan_le b V)
    (by positivity : (0 : ℝ)≤(V/b+1 : ℕ))
    (by have := PhysicalArbitraryBound.borrowing_nonneg
        have := geometric_nonneg ratio (by have := ratio_gt_one; linarith) k
        positivity)
  rw [base_totalBound]
  push_cast at hm ⊢
  nlinarith only [hm]

end
end CodedSorting.CommonChunkCost
end Cost

section Exchange
/-! Actual common-machine code for an arbitrary list of field chunks.
The source file is updated in place and the shared scratch interval is reused.
All execution premises are discharged by the constructed programs; the public
conditions concern only numerical dimensions and machine capacities. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace CodedSorting.CommonChunkExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonRecursiveExchange PhysicalChunkExchange RecursiveExchange Circuit
open CommonChunkLayout CommonFinitePermutation
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m Pruned.canonicalProgram

def generated (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
    (cs : List Call) (P G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S) (h : Conditions q cutoff cs P)
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P G S hG hS h≤limit)
    (hl : limit≤q.N^q.exponent) :
    {p : Program q (Volume P (fieldCount cs) G (S*q.w)) source buffer limit
      (swap P (fieldCount cs) G (S*q.w)) //
      p.charge=CommonChunkCost.totalBound cutoff (width q) cs
        (Volume P (fieldCount cs) G (S*q.w))} := by
  induction cs generalizing P G S with
  | nil => exact ⟨emptyProgram q P G S source buffer limit,rfl⟩
  | cons c cs ih =>
    have hs₁ : source+count q
        (Volume P (radix^c.width) (fieldCount cs*G) ((fieldCount cs*S)*q.w))≤buffer := by
      simpa only [head_word_volume,fieldCount] using hs
    have hs₂ : source+count q
        (Volume (P*radix^c.width) (fieldCount cs) (G*radix^c.width) (S*q.w))≤buffer := by
      simpa only [tail_word_volume,fieldCount] using hs
    let p₁ := oneProgram q reader cutoff c P (fieldCount cs*G) (fieldCount cs*S)
      source buffer limit (Nat.mul_pos (fieldCount_pos cs) hG)
      (Nat.mul_pos (fieldCount_pos cs) hS) h.resident (h.buffers c (by simp))
      (h.startup c (by simp)) (h.divisible c (by simp)) hs₁
      (head_workspace q cutoff c cs P G S buffer limit hG hS h hw) hl
    let p₂ := ih (P*radix^c.width) (G*radix^c.width) S
      (Nat.mul_pos hG (pow_pos radix_prime.pos _)) hS
      (h.tail q cutoff c cs P) hs₂
      (tail_workspace q cutoff c cs P G S buffer limit hG hS h hw)
    refine ⟨combine q P (radix^c.width) (fieldCount cs) G S
      source buffer limit p₁ p₂.val,?_⟩
    change p₁.charge+p₂.val.charge=_
    rw [p₂.property]
    dsimp only [p₁]
    rw [oneProgram_charge,head_word_volume,tail_word_volume]
    rfl

def program (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : ℕ)
    (cs : List Call) (P G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S) (h : Conditions q cutoff cs P)
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P G S hG hS h≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (fieldCount cs) G (S*q.w)) source buffer limit
      (swap P (fieldCount cs) G (S*q.w)) :=
  (generated q reader cutoff cs P G S source buffer limit hG hS h hs hw hl).val

@[simp] theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List Call) (P G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S) (h : Conditions q cutoff cs P)
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P G S hG hS h≤limit)
    (hl : limit≤q.N^q.exponent) :
    (program q reader cutoff cs P G S source buffer limit hG hS h hs hw hl).charge=
      CommonChunkCost.totalBound cutoff (width q) cs
        (Volume P (fieldCount cs) G (S*q.w)) :=
  (generated q reader cutoff cs P G S source buffer limit hG hS h hs hw hl).property

end
end CodedSorting.CommonChunkExchange
end Exchange
