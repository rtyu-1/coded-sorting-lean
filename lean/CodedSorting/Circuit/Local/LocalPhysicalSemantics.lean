import CodedSorting.Circuit.Composition.ScatterCopies

/-!
# The 670-register local physical program

There are exactly 661 original registers carrying independent values and
nine temporary registers. Temporaries are numbered 661 through 669 and copy
the retained helpers numbered 472 through 480 immediately before scatter.

The correctness theorem consumes both the scalar replay certificate and an
exact decomposition of that word into before/scatter/after. The concrete
decomposition is supplied by `ConcreteLocalProgram`, and the replay is
instantiated in `Theorem32/Coding.lean`. Matrix labeling, rank cost 63
for moving the nine rank-seven copies, and tensor composition are handled
by the corresponding labeling and composition modules.
-/

set_option autoImplicit false

namespace CodedSorting.Construction.LocalPhysicalSemantics

open CodedSorting.Circuit CodedSorting.CircuitProgram
open CodedSorting.Construction.FiniteCertificate CodedSorting.Construction.SymbolicXor
open CodedSorting.Construction.FiniteSemantics CodedSorting.Construction.ExplicitCopies
open CodedSorting.Construction.ScatterCopies

abbrev OriginalReg := Fin registerCount
abbrev TemporaryReg := Fin 9
abbrev PhysicalReg := OriginalReg ⊕ TemporaryReg

/-- The usual contiguous numbering: originals 0--660, temporaries 661--669. -/
def physicalIndex : PhysicalReg ≃ Fin 670 := finSumFinEquiv

def originalIndex (r : OriginalReg) : Fin 670 := physicalIndex (.inl r)

def temporaryIndex (t : TemporaryReg) : Fin 670 := physicalIndex (.inr t)

@[simp] theorem originalIndex_val (r : OriginalReg) : (originalIndex r).val = r.val := rfl

@[simp] theorem temporaryIndex_val (t : TemporaryReg) :
    (temporaryIndex t).val = 661 + t.val := rfl

theorem physical_register_count : Fintype.card PhysicalReg = 670 := by
  simp [PhysicalReg, OriginalReg, TemporaryReg, registerCount]

theorem original_session_count : Fintype.card OriginalReg = 661 := by
  simp [OriginalReg, registerCount]

/-- These are the nine retained helpers used by the concrete Construction word. The
exact word decomposition below is still required as a certificate premise. -/
def retainedHelper : TemporaryReg ↪ OriginalReg where
  toFun t := ⟨472 + t.val, by have ht := t.isLt; change 472 + t.val < 661; omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 472 + a.val = 472 + b.val at hv
    omega

@[simp] theorem retainedHelper_val (t : TemporaryReg) :
    (retainedHelper t).val = 472 + t.val := rfl

def allTemporaries : List TemporaryReg := List.finRange 9

theorem allTemporaries_complete (t : TemporaryReg) : t ∈ allTemporaries := by
  simp [allTemporaries]

noncomputable def localPhysicalProgram (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg)) : List (XorGate PhysicalReg) :=
  expandedProgram retainedHelper allTemporaries before after rows

noncomputable def numberedPhysicalProgram (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg)) : List (XorGate (Fin 670)) :=
  (localPhysicalProgram before after rows).map (XorGate.lift physicalIndex.toEmbedding)

/-- Every scatter destination in the second 111-port block is disjoint from
all retained helpers. Only the upper bound is needed for this fact. -/
theorem scatter_safe_of_target_bound (rows : List (ScatterRow OriginalReg TemporaryReg))
    (htarget : ∀ row ∈ rows, row.destination.val < 222) :
    ∀ row ∈ rows, ∀ t, retainedHelper t ≠ row.destination := by
  intro row hr t heq
  have hd := htarget row hr
  have he := congrArg Fin.val heq
  simp only [retainedHelper_val] at he
  omega

/-- Conditional finite-certificate consumer for the actual expanded program.
The initial state includes arbitrary dirty helper and temporary values. -/
theorem localPhysical_correct_of_certificate (word : Array Gate)
    (hreplay : runCoefficients word = coefficientExpected)
    (hnodup : ∀ g ∈ word.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ word.toList, ∀ s ∈ g.sources, s < registerCount)
    (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg))
    (hdecompose : compileProgram registerCount word =
      reducedProgram retainedHelper before after rows)
    (hsafe : ∀ row ∈ rows, ∀ t, retainedHelper t ≠ row.destination)
    (state : PhysicalReg → Bit) :
    originalState (runProgram (localPhysicalProgram before after rows) state) =
      localOutput (originalState state) := by
  unfold localPhysicalProgram
  rw [expandedProgram_original retainedHelper allTemporaries allTemporaries_complete
    before after rows hsafe, ← hdecompose]
  exact localProgram_correct_of_certificate word hreplay hnodup hbound (originalState state)

/-- The same theorem on literal register numbers 0--669. No initial value
at indices 661--669 appears in the original-register output formula. -/
theorem numberedPhysical_correct_of_certificate (word : Array Gate)
    (hreplay : runCoefficients word = coefficientExpected)
    (hnodup : ∀ g ∈ word.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ word.toList, ∀ s ∈ g.sources, s < registerCount)
    (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg))
    (hdecompose : compileProgram registerCount word =
      reducedProgram retainedHelper before after rows)
    (hsafe : ∀ row ∈ rows, ∀ t, retainedHelper t ≠ row.destination)
    (state : Fin 670 → Bit) (r : OriginalReg) :
    runProgram (numberedPhysicalProgram before after rows) state (originalIndex r) =
      localOutput (fun i => state (originalIndex i)) r := by
  have hlift := runProgram_lift_restrict physicalIndex.toEmbedding
    (localPhysicalProgram before after rows) state
  have hphysical := localPhysical_correct_of_certificate word hreplay hnodup hbound
    before after rows hdecompose hsafe (state ∘ physicalIndex)
  exact (congrFun hlift (.inl r)).trans (congrFun hphysical r)

/-- Arbitrary initial temporaries are permitted explicitly. They are
auxiliary state, while the independent input vector has exactly 661 entries. -/
def withDirtyTemporaries (input : OriginalReg → Bit) (dirty : TemporaryReg → Bit) :
    PhysicalReg → Bit := Sum.elim input dirty

theorem localPhysical_dirty_independent
    (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg))
    (hsafe : ∀ row ∈ rows, ∀ t, retainedHelper t ≠ row.destination)
    (input : OriginalReg → Bit) (dirty₁ dirty₂ : TemporaryReg → Bit) :
    originalState (runProgram (localPhysicalProgram before after rows)
      (withDirtyTemporaries input dirty₁)) =
    originalState (runProgram (localPhysicalProgram before after rows)
      (withDirtyTemporaries input dirty₂)) := by
  exact expandedProgram_independent_of_dirty retainedHelper allTemporaries
    allTemporaries_complete before after rows hsafe _ _ rfl

end CodedSorting.Construction.LocalPhysicalSemantics
