import CodedSorting.Interchange.Framework.Memory.Reflection

/-! Predicate transport for chronological execution is proved with abstract
programs, so composition never needs to evaluate a concrete instruction list. -/
set_option autoImplicit false
namespace CodedSorting.CommonRawComposition
open CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Machine)
noncomputable section

theorem two (q : Configuration) (xs ys : List (Instruction q)) (s : Machine q)
    (P : Machine q → Prop)
    (h : P (executeRaw q ys (executeRaw q xs s).1).1) :
    P (executeRaw q (xs++ys) s).1 :=
  (congrArg P (CommonPermutationPairs.raw_append q xs ys s)).mpr h

theorem five (q : Configuration) (c1 c2 c3 c4 c5 : List (Instruction q))
    (s : Machine q) (P : Machine q → Prop)
    (h : P (executeRaw q c5 (executeRaw q c4 (executeRaw q c3
      (executeRaw q c2 (executeRaw q c1 s).1).1).1).1).1) :
    P (executeRaw q (c1++c2++c3++c4++c5) s).1 := by
  have hr : (executeRaw q (c1++c2++c3++c4++c5) s).1=
      (executeRaw q c5 (executeRaw q c4 (executeRaw q c3
        (executeRaw q c2 (executeRaw q c1 s).1).1).1).1).1 := by
    simp only [CommonPermutationPairs.raw_append]
  exact (congrArg P hr).mpr h

theorem congr (q : Configuration) (xs ys : List (Instruction q)) (heq : xs=ys)
    (s : Machine q) (P : Machine q → Prop) (h : P (executeRaw q ys s).1) :
    P (executeRaw q xs s).1 :=
  (congrArg (fun cs => P (executeRaw q cs s).1) heq).mpr h

/-- Both stage rules quantify over arbitrary machines, so their composition
is checked before a concrete predecessor state is substituted. -/
theorem hoare_two (q : Configuration) (xs ys : List (Instruction q))
    (P Q R : Machine q → Prop)
    (hA : ∀ s,P s → Q (executeRaw q xs s).1)
    (hB : ∀ s,Q s → R (executeRaw q ys s).1) :
    ∀ s,P s → R (executeRaw q (xs++ys) s).1 := by
  intro s hs
  exact two q xs ys s R (hB _ (hA s hs))

theorem hoare_five (q : Configuration) (c1 c2 c3 c4 c5 : List (Instruction q))
    (P0 P1 P2 P3 P4 P5 : Machine q → Prop)
    (h1 : ∀ s,P0 s → P1 (executeRaw q c1 s).1)
    (h2 : ∀ s,P1 s → P2 (executeRaw q c2 s).1)
    (h3 : ∀ s,P2 s → P3 (executeRaw q c3 s).1)
    (h4 : ∀ s,P3 s → P4 (executeRaw q c4 s).1)
    (h5 : ∀ s,P4 s → P5 (executeRaw q c5 s).1) :
    ∀ s,P0 s → P5 (executeRaw q (c1++c2++c3++c4++c5) s).1 := by
  have h12 := hoare_two q c1 c2 P0 P1 P2 h1 h2
  have h123 := hoare_two q (c1++c2) c3 P0 P2 P3 h12 h3
  have h1234 := hoare_two q (c1++c2++c3) c4 P0 P3 P4 h123 h4
  exact hoare_two q (c1++c2++c3++c4) c5 P0 P4 P5 h1234 h5

end
end CodedSorting.CommonRawComposition
