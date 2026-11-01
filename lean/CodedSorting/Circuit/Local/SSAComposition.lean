import CodedSorting.Circuit.Local.SSAFunctionCertificate

namespace CodedSorting.Construction.FiniteSSA.Verified
open CodedSorting.Construction.SSAFunctionCertificate
set_option autoImplicit false

def WellFormed (e : Step) : Prop :=
  e.gate.destination < 661 ∧ (∀ s ∈ e.gate.sources, s < 661) ∧
    e.gate.sources.Nodup ∧ e.gate.destination ∉ e.gate.sources

theorem wellFormed_of_checks (es : List Step)
    (bounds : es.all (fun e => e.gate.destination < 661 &&
      e.gate.sources.all (fun s => s < 661)) = true)
    (nodup : ∀ e ∈ es, e.gate.sources.Nodup)
    (noSelf : es.all (fun e => !e.gate.sources.contains e.gate.destination) = true) :
    ∀ e ∈ es, WellFormed e := by
  intro e he
  have hb := (List.all_eq_true.mp bounds) e he
  have hn := (List.all_eq_true.mp noSelf) e he
  have hb' : e.gate.destination < 661 ∧ (∀ s ∈ e.gate.sources, s < 661) := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using hb
  exact ⟨hb'.1, hb'.2, nodup e he, by simpa using hn⟩

theorem wellFormed_append (a b : List Step)
    (ha : ∀ e ∈ a, WellFormed e) (hb : ∀ e ∈ b, WellFormed e) :
    ∀ e ∈ a ++ b, WellFormed e := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact hb e he

end CodedSorting.Construction.FiniteSSA.Verified

#print axioms CodedSorting.Construction.FiniteSSA.Verified.wellFormed_of_checks
#print axioms CodedSorting.Construction.FiniteSSA.Verified.wellFormed_append
