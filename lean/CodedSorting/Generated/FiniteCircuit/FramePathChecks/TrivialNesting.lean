import CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch00

/-! Zero and identity matrices need no instance-by-instance matrix products. -/
namespace CodedSorting.Construction.PhysicalFramePaths
open FiniteCertificate

theorem nestingIdentity_denominator : nestingProjection001.denominator = 1 := rfl

theorem nestingEntries_zero : nestingEntries000 = (fun _ => 0) := by
  funext n
  simp [nestingEntries000]

theorem nestingIdentity_entries (n : Nat) :
    nestingProjection001.numerator[n]! = identityEntries n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  have h : n / 8 ≠ n % 8 := by omega
  simp [identityEntries, h]

end CodedSorting.Construction.PhysicalFramePaths
