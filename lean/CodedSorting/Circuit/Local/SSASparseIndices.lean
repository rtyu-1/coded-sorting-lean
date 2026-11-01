import CodedSorting.Circuit.Local.SSAFunctionCertificate

/-! Check changed register indices; reuse one proof for every untouched register. -/
namespace CodedSorting.Construction.SSAFunctionCertificate

def writtenRegisters (es : List Step) : List Nat :=
  es.map (fun e => e.gate.destination)

theorem runIds_unchanged (es : List Step) (ids : Nat → Nat) (r : Nat)
    (h : r ∉ writtenRegisters es) : runIds es ids r = ids r := by
  induction es generalizing ids with
  | nil => rfl
  | cons e es ih =>
    have hne : r ≠ e.gate.destination := by
      intro he
      exact h (by simp [writtenRegisters, he])
    have htail : r ∉ writtenRegisters es := by
      intro hr
      exact h (by simpa only [writtenRegisters, List.map_cons, List.mem_cons] using Or.inr hr)
    change runIds es (stepIds ids e) r = ids r
    rw [ih _ htail]
    simp only [stepIds, if_neg hne]

theorem runIds_eq_of_sparse (es : List Step) (before after : Nat → Nat) (n : Nat)
    (hchanged : ∀ r ∈ writtenRegisters es, runIds es before r = after r)
    (houtside : ∀ r : Fin n, before r.val = after r.val ∨ r.val ∈ writtenRegisters es) :
    ∀ r : Fin n, runIds es before r.val = after r.val := by
  intro r
  by_cases h : r.val ∈ writtenRegisters es
  · exact hchanged r.val h
  · exact (runIds_unchanged es before r.val h).trans ((houtside r).resolve_right h)

end CodedSorting.Construction.SSAFunctionCertificate
