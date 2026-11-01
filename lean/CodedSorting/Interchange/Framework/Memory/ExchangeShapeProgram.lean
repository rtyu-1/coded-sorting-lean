import CodedSorting.Interchange.Framework.Chunks.Layout

section FinitePermutation
/-! A numeric-index specification of an actual in-place permutation program.
The permutation is an output-to-input map. Composition keeps the original
instructions, charges all of them, and passes the actual intermediate machine.
-/
set_option autoImplicit false
namespace CodedSorting.CommonFinitePermutation
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
noncomputable section

structure Program (q : Configuration) (V source buffer limit : ℕ)
    (π : Equiv.Perm (Fin V)) where
  instructions : List (Instruction q)
  charge : ℕ
  correct : ∀ (s : Machine q) (y : Fin V),
    readBit q (executeRaw q instructions s).1.disk source y.val =
      readBit q s.disk source (π y).val
  frame : ∀ (s : Machine q) (a : Fin (q.N^q.exponent)),
    (a.val<source ∨ source+count q V≤a.val) →
    (a.val<buffer ∨ limit≤a.val) →
    (executeRaw q instructions s).1.disk a=s.disk a
  safe : ∀ i∈instructions,RespectsPC q i
  cost_le : cost q instructions≤charge
  length_le : instructions.length≤charge

namespace Program
variable {q : Configuration} {V V' source buffer limit : ℕ}
variable {π π' π₁ π₂ : Equiv.Perm (Fin V)}

def identity (q : Configuration) (V source buffer limit : ℕ) :
    Program q V source buffer limit (Equiv.refl (Fin V)) where
  instructions := []
  charge := 0
  correct := fun _ _ => rfl
  frame := fun _ _ _ _ => rfl
  safe := by simp
  cost_le := Nat.le_refl 0
  length_le := Nat.le_refl 0

def append (p₁ : Program q V source buffer limit π₁)
    (p₂ : Program q V source buffer limit π₂) :
    Program q V source buffer limit (π₂.trans π₁) where
  instructions := p₁.instructions ++ p₂.instructions
  charge := p₁.charge+p₂.charge
  correct := by
    intro s y
    rw [raw_append,p₂.correct,p₁.correct]
    rfl
  frame := by
    intro s a hs hb
    rw [raw_append,p₂.frame _ a hs hb,p₁.frame s a hs hb]
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

def changePermutation (p : Program q V source buffer limit π) (h : π=π') :
    Program q V source buffer limit π' := h ▸ p

def castVolume (p : Program q V source buffer limit π) (h : V=V') :
    Program q V' source buffer limit
      ((finCongr h).symm.trans (π.trans (finCongr h))) where
  instructions := p.instructions
  charge := p.charge
  correct := by
    subst V'
    simpa using p.correct
  frame := by
    subst V'
    exact p.frame
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

end Program

theorem complete (q : Configuration) {V source buffer limit : ℕ}
    {π : Equiv.Perm (Fin V)} (p : Program q V source buffer limit π)
    (s : Machine q) (hsize : p.charge≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin V,readBit q result.1.disk source y.val=
      readBit q s.disk source (π y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q V≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧ result.2≤p.charge ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hd,hh,hc,hm⟩ := run_code_disk q p.instructions
    (p.length_le.trans hsize) p.safe s hpc
  exact ⟨by rw [hd]; exact p.correct s,by rw [hd]; exact p.frame s,
    hh,hc.trans_le p.cost_le,hm⟩

end
end CodedSorting.CommonFinitePermutation
end FinitePermutation

section ExchangeShapeProgram
/-! Changing equal public dimensions changes no instruction or charge. -/
set_option autoImplicit false
namespace CodedSorting.CommonExchangeShapeProgram
open CommonSortingNormalization CommonPermutationPairs CommonChunkLayout
open CommonFinitePermutation
noncomputable section

def reshape (q : Configuration) {P Q G S P' Q' G' S' source buffer limit : ℕ}
    (hP : P=P') (hQ : Q=Q') (hG : G=G') (hS : S=S')
    (p : Program q (Volume P Q G S) source buffer limit (swap P Q G S)) :
    Program q (Volume P' Q' G' S') source buffer limit (swap P' Q' G' S') where
  instructions := p.instructions
  charge := p.charge
  correct := fun s => numeric_correct_cast P Q G S P' Q' G' S' hP hQ hG hS
    (readBit q s.disk source)
    (readBit q (CommonStaticSchedule.executeRaw q p.instructions s).1.disk source)
    (p.correct s)
  frame := by
    intro s a ha hb
    exact p.frame s a (by simpa only [hP,hQ,hG,hS] using ha) hb
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

@[simp] theorem reshape_charge (q : Configuration)
    {P Q G S P' Q' G' S' source buffer limit : ℕ}
    (hP : P=P') (hQ : Q=Q') (hG : G=G') (hS : S=S')
    (p : Program q (Volume P Q G S) source buffer limit (swap P Q G S)) :
    (reshape q hP hQ hG hS p).charge=p.charge := rfl

end
end CodedSorting.CommonExchangeShapeProgram
end ExchangeShapeProgram
