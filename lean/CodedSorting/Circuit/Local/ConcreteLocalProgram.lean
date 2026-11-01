import CodedSorting.Circuit.Composition.TensorNetworkGeometry
import CodedSorting.Generated.FiniteCircuit.GateSegments

/-!
# Concrete before/scatter/after binding of the Construction certificate

This file binds the exact 5583-gate finite data to the physical local-word
consumer. The nine copies are inserted at the declared scatter boundary.
Payload replay is an explicit certificate parameter, instantiated by
`scalarCoefficientReplay` in `NetworkCoding/Theorem32/Coding.lean`.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace CodedSorting.Construction.ConcreteLocalProgram

open CodedSorting.Circuit CodedSorting.CircuitProgram
open FiniteCertificate SymbolicXor ExplicitCopies ScatterCopies LocalPhysicalSemantics
open TensorLiftProgram LocalPhysicalContract TensorNetwork ReverseLocalProgram

noncomputable section

def prefixGates : List Gate := gates.toList.take beforeScatterCount
def scatterGates : List Gate := (gates.toList.drop beforeScatterCount).take portCount
def suffixGates : List Gate := gates.toList.drop (beforeScatterCount + portCount)

def before : List (XorGate OriginalReg) := prefixGates.map (compileGate registerCount)
def after : List (XorGate OriginalReg) := suffixGates.map (compileGate registerCount)

def scatterRow (g : Gate) : ScatterRow OriginalReg TemporaryReg where
  destination := ⟨g.destination % registerCount, Nat.mod_lt _ (by decide)⟩
  sources := Finset.univ.filter (fun t => (retainedHelper t).val ∈ g.sources)

def rows : List (ScatterRow OriginalReg TemporaryReg) := scatterGates.map scatterRow

def forward : List (XorGate LocalReg) := certificateForward before after rows
def middle : List (XorGate LocalReg) := certificateMiddle before after rows

/-- Boolean reflection avoids constructing a quadratic bounded-forall
Decidable proof over the large gate list. This is still a kernel decision. -/
theorem scatterShape_check : scatterGates.all (fun g => decide
    (111 ≤ g.destination ∧ g.destination < 222 ∧
      ∀ s ∈ g.sources, 472 ≤ s ∧ s < 481)) = true := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
  unfold scatterGates
  rw [scatter_by_chunks]
  simp only [scatterChunks, List.all_append]
  decide +kernel

theorem scatterShape : ∀ g ∈ scatterGates,
    111 ≤ g.destination ∧ g.destination < 222 ∧
      ∀ s ∈ g.sources, 472 ≤ s ∧ s < 481 := by
  intro g hg
  exact of_decide_eq_true (List.all_eq_true.mp scatterShape_check g hg)

/-- The precise contiguous scatter segment is the only special frame. -/
theorem scatter_frames_check : scatterGates.all (fun g => decide (g.frame = scatterFrame)) = true := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
  unfold scatterGates
  rw [scatter_by_chunks]
  simp only [scatterChunks, List.all_append]
  decide +kernel

theorem scatter_frames : ∀ g ∈ scatterGates, g.frame = scatterFrame := by
  intro g hg
  exact of_decide_eq_true (List.all_eq_true.mp scatter_frames_check g hg)

theorem prefix_frames_check : prefixGates.all (fun g => decide (g.frame < scatterFrame)) = true := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
  unfold prefixGates
  rw [prefix_by_chunks]
  simp only [prefixChunks, List.all_append]
  decide +kernel

theorem prefix_frames : ∀ g ∈ prefixGates, g.frame < scatterFrame := by
  intro g hg
  exact of_decide_eq_true (List.all_eq_true.mp prefix_frames_check g hg)

theorem suffix_frames_check : suffixGates.all (fun g => decide (g.frame < scatterFrame)) = true := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
  unfold suffixGates
  rw [suffix_by_chunks]
  simp only [suffixChunks, List.all_append]
  decide +kernel

theorem suffix_frames : ∀ g ∈ suffixGates, g.frame < scatterFrame := by
  intro g hg
  exact of_decide_eq_true (List.all_eq_true.mp suffix_frames_check g hg)

theorem gateList_decomposition : gates.toList = prefixGates ++ scatterGates ++ suffixGates := by
  unfold prefixGates scatterGates suffixGates
  rw [← List.drop_drop]
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

private theorem xorGate_ext {R : Type*} [DecidableEq R] (g h : XorGate R)
    (hp : g.ports = h.ports) (ht : g.targets = h.targets) (hc : g.controls = h.controls) : g = h := by
  cases g
  cases h
  cases hp
  cases ht
  cases hc
  rfl

theorem scatterRow_destination (g : Gate) (hg : g.destination < registerCount) :
    (scatterRow g).destination.val = g.destination := Nat.mod_eq_of_lt hg

theorem scatterRow_sources (g : Gate)
    (hs : ∀ s ∈ g.sources, 472 ≤ s ∧ s < 481) :
    (scatterRow g).sources.map retainedHelper = sourceRegisters registerCount g := by
  ext r
  simp only [scatterRow, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    sourceRegisters]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hr
    have hb := hs r.val hr
    let t : TemporaryReg := ⟨r.val - 472, by omega⟩
    have he : retainedHelper t = r := by
      apply Fin.ext
      change 472 + (r.val - 472) = r.val
      omega
    exact ⟨t, by simpa [he] using hr, he⟩

theorem compile_scatterRow (g : Gate) (hd : g.destination < registerCount)
    (hs : ∀ s ∈ g.sources, 472 ≤ s ∧ s < 481) :
    compileGate registerCount g = originalScatter retainedHelper (scatterRow g) := by
  apply xorGate_ext
  · ext r
    simp only [compileGate, originalScatter, scatterRow_sources g hs, Finset.mem_union,
      Finset.mem_singleton, sourceRegisters, Finset.mem_filter, Finset.mem_univ, true_and]
    have he : r = (scatterRow g).destination ↔ r.val = g.destination := by
      rw [← scatterRow_destination g hd]
      exact Fin.ext_iff
    rw [he]
  · ext r
    simp only [compileGate, originalScatter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [← scatterRow_destination g hd]
    exact Fin.ext_iff.symm
  · funext r
    exact (scatterRow_sources g hs).symm

theorem scatterProgram_decomposition :
    scatterGates.map (compileGate registerCount) = reducedScatter retainedHelper rows := by
  unfold reducedScatter rows
  rw [List.map_map]
  apply List.map_congr_left
  intro g hg
  have hs := scatterShape g hg
  exact compile_scatterRow g (by change g.destination < 661; omega) hs.2.2

theorem concrete_decomposition :
    compileProgram registerCount gates = reducedProgram retainedHelper before after rows := by
  change gates.toList.map (compileGate registerCount) = _
  rw [gateList_decomposition, List.map_append, List.map_append, scatterProgram_decomposition]
  rfl

theorem scatter_safe : ∀ row ∈ rows, ∀ t, retainedHelper t ≠ row.destination := by
  apply scatter_safe_of_target_bound
  intro row hr
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
  have hs := scatterShape g hg
  rw [scatterRow_destination g (by change g.destination < 661; omega)]
  exact hs.2.1

theorem forward_correct
    (hreplay : runCoefficients gates = coefficientExpected)
    (hnodup : ∀ g ∈ gates.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ gates.toList, ∀ s ∈ g.sources, s < registerCount) :
    LocalCorrect forward :=
  localCorrect_of_physical _ (localPhysical_correct_of_certificate gates hreplay hnodup hbound
    before after rows concrete_decomposition scatter_safe)

theorem middle_correct
    (hreplay : runCoefficients gates = coefficientExpected)
    (hnodup : ∀ g ∈ gates.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ gates.toList, ∀ s ∈ g.sources, s < registerCount)
    (hnot : ∀ g ∈ gates.toList, g.destination ∉ g.sources) :
    LocalCorrect middle :=
  localCorrect_of_physical _ (reverseLocalPhysical_correct_of_certificate gates hreplay hnodup hbound
    hnot before after rows concrete_decomposition scatter_safe)

end
end CodedSorting.Construction.ConcreteLocalProgram
