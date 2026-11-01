import CodedSorting.Circuit.Composition.TensorFrameProgram
import CodedSorting.Circuit.MemoryAccess.PhysicalFrameEventProperties
import CodedSorting.Circuit.Local.ConcreteLocalProgram

section PhysicalFrameCostLemmas
set_option autoImplicit false
namespace CodedSorting.Construction.PhysicalFramePaths
open CodedSorting.TensorLabels CodedSorting.RankMetric
open ThreeCopySchedule TensorLiftProgram TensorFrameGeometry
noncomputable section

theorem constant_path_cost (P Q : GlobalMatrix) (n : Nat) :
    chainCost P (List.replicate n Q ++ [Q]) = (Q - P).rank := by
  induction n generalizing P with
  | zero => simp [chainCost]
  | succ n ih => simp [chainCost, List.replicate_succ, ih]

theorem copy_path_cost (P Q : GlobalMatrix) (n : Nat) :
    chainCost P ((P :: List.replicate n Q) ++ [Q]) = (Q - P).rank := by
  simp [chainCost, constant_path_cost]

theorem copiedFrame_global_cost (round : TensorLiftProgram.Round) (block : Block) (P : LocalMatrix)
    (n : Nat) (hp : P * P = P) :
    chainCost (globalFrame round block P)
      ((globalFrame round block P :: List.replicate n (globalFrame round block 0)) ++
        [globalFrame round block 0]) = P.rank := by
  rw [copy_path_cost, globalFrame_reverse_difference_rank round block _ 0 hp
    (by simp) (by simp) (by simp)]
  rw [matrix_rank_sub_symm, sub_zero]

theorem copiedComplement_global_cost (round : TensorLiftProgram.Round) (block : Block) (P : LocalMatrix)
    (n : Nat) (hp : P * P = P) :
    chainCost (globalFrame round block (1-P))
      ((globalFrame round block (1-P) :: List.replicate n (globalFrame round block 1)) ++
        [globalFrame round block 1]) = P.rank := by
  rw [copy_path_cost, globalFrame_difference_rank round block _ 1
    (complement_idempotent _ hp) (by simp) (by simp) (by simp)]
  have he : (1 : LocalMatrix) - (1-P) = P := by abel
  rw [he]

end
end CodedSorting.Construction.PhysicalFramePaths
end PhysicalFrameCostLemmas

section PhysicalFrameTemporaryEvents
namespace CodedSorting.Construction.PhysicalFramePaths
open FiniteCertificate

theorem ordinary_temporary_events_nil (t : Fin 9) (xs : List Gate)
    (hb : ∀ g ∈ xs, g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    eventVisits (661 + t.val) (xs.map ordinaryEvent) = [] := by
  apply eventVisits_eq_nil
  intro e he
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  have h := hb g hg
  change g.destination < 661 ∧ ∀ s ∈ g.sources, s < 661 at h
  simp only [ordinaryEvent, List.mem_cons]
  rintro (he | he)
  · omega
  · have hs := h.2 _ he; omega

theorem copy_temporary_events (t : Fin 9) :
    eventVisits (661 + t.val) ((List.range 9).map copyEvent) = [510 + t.val] := by
  have h : ∀ u : Fin 9,
      eventVisits (661 + u.val) ((List.range 9).map copyEvent) = [510 + u.val] := by
    decide +kernel
  exact h t

theorem eventVisits_uniform (r f : Nat) (xs : List FrameEvent)
    (hf : ∀ e ∈ xs, e.frame = f) :
    eventVisits r xs = List.replicate (eventVisits r xs).length f := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    have he := hf e (by simp)
    have hs := ih (fun a ha => hf a (by simp [ha]))
    by_cases hr : r ∈ e.ports
    · simpa [eventVisits, hr, he, List.replicate_succ] using congrArg (fun ys => f :: ys) hs
    · simpa [eventVisits, hr] using hs

theorem scatter_events_uniform (r : Nat) (xs : List Gate) :
    eventVisits r (xs.map scatterEvent) =
      List.replicate (eventVisits r (xs.map scatterEvent)).length 0 := by
  apply eventVisits_uniform
  intro e he
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  rfl

theorem forward_temporary_events (t : Fin 9)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    ∃ n : Nat, eventVisits (661 + t.val) forwardEvents =
      (510 + t.val) :: List.replicate n 0 := by
  have hp : ∀ g ∈ physicalPrefix,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount :=
    fun g hg => hb g (List.mem_of_mem_take hg)
  have hs : ∀ g ∈ physicalSuffix,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount :=
    fun g hg => hb g (List.mem_of_mem_drop hg)
  refine ⟨(eventVisits (661+t.val) (physicalScatter.map scatterEvent)).length, ?_⟩
  simp only [forwardEvents, eventVisits_append, ordinary_temporary_events_nil t _ hp,
    ordinary_temporary_events_nil t _ hs, copy_temporary_events,
    List.nil_append, List.append_nil, List.singleton_append]
  rw [scatter_events_uniform]
  simp only [List.length_replicate]

theorem middle_temporary_events (t : Fin 9)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    ∃ n : Nat, eventVisits (661 + t.val) middleEvents =
      (510 + t.val) :: List.replicate n 0 := by
  have hp : ∀ g ∈ physicalPrefix.reverse,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount :=
    fun g hg => hb g (List.mem_of_mem_take (List.mem_reverse.mp hg))
  have hs : ∀ g ∈ physicalSuffix.reverse,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount :=
    fun g hg => hb g (List.mem_of_mem_drop (List.mem_reverse.mp hg))
  refine ⟨(eventVisits (661+t.val) (physicalScatter.reverse.map scatterEvent)).length, ?_⟩
  simp only [middleEvents, eventVisits_append, ordinary_temporary_events_nil t _ hp,
    ordinary_temporary_events_nil t _ hs, copy_temporary_events,
    List.nil_append, List.append_nil, List.singleton_append]
  rw [scatter_events_uniform]
  simp only [List.length_replicate]


end CodedSorting.Construction.PhysicalFramePaths
end PhysicalFrameTemporaryEvents

section PhysicalPortChecks
set_option autoImplicit false

namespace CodedSorting.Construction.PhysicalPortChecks

open CodedSorting.CircuitProgram
open FiniteCertificate SymbolicXor ScatterCopies LocalPhysicalSemantics ExplicitCopies
open PhysicalFramePaths

theorem ordinary_original (g : Gate) (a : OriginalReg) :
    Sum.inl a ∈ ((compileGate registerCount g).lift
      (originalEmbedding (T := TemporaryReg))).ports ↔
      a.val ∈ (ordinaryEvent g).ports := by
  simp [XorGate.lift, compileGate, originalEmbedding, ordinaryEvent, eq_comm]

theorem ordinary_temporary (g : Gate) (t : TemporaryReg)
    (hbound : g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    Sum.inr t ∈ ((compileGate registerCount g).lift
      (originalEmbedding (T := TemporaryReg))).ports ↔
      661 + t.val ∈ (ordinaryEvent g).ports := by
  have ht : ¬ (661 + t.val = g.destination ∨ 661 + t.val ∈ g.sources) := by
    intro h
    rcases h with h | h
    · have hd := hbound.1; change g.destination < 661 at hd; omega
    · have hs := hbound.2 _ h; change 661 + t.val < 661 at hs; omega
  simp [XorGate.lift, originalEmbedding, ordinaryEvent, ht]

theorem copy_original (t : TemporaryReg) (a : OriginalReg) :
    Sum.inl a ∈ (copyGate retainedHelper t).ports ↔ a.val ∈ (copyEvent t.val).ports := by
  have ha := a.isLt
  change a.val < 661 at ha
  simp [copyGate, NetworkAdapter.overwriteCopy, copyEvent, retainedHelper, Fin.ext_iff,
    show a.val ≠ 661 + t.val by omega, eq_comm]

theorem copy_temporary (t u : TemporaryReg) :
    Sum.inr u ∈ (copyGate retainedHelper t).ports ↔ 661 + u.val ∈ (copyEvent t.val).ports := by
  have ht := t.isLt
  simp [copyGate, NetworkAdapter.overwriteCopy, copyEvent, Fin.ext_iff,
    show 661 + u.val ≠ 472 + t.val by omega, eq_comm]

theorem scatter_original (g : Gate) (a : OriginalReg) (hbound : g.destination < 661) :
    Sum.inl a ∈ (copiedScatter (ConcreteLocalProgram.scatterRow g)).ports ↔
      a.val ∈ (scatterEvent g).ports := by
  have ha := a.isLt
  change a.val < 661 at ha
  simp [copiedScatter, ConcreteLocalProgram.scatterRow, scatterEvent, temporaryEmbedding,
    Fin.ext_iff, Nat.mod_eq_of_lt hbound, registerCount,
    show ∀ t : Nat, a.val ≠ 661 + t by omega, eq_comm]

theorem scatter_temporary (g : Gate) (t : TemporaryReg) (hbound : g.destination < 661) :
    Sum.inr t ∈ (copiedScatter (ConcreteLocalProgram.scatterRow g)).ports ↔
      661 + t.val ∈ (scatterEvent g).ports := by
  have ht := t.isLt
  simp [copiedScatter, ConcreteLocalProgram.scatterRow, scatterEvent, temporaryEmbedding,
    Fin.ext_iff, show 661 + t.val ≠ g.destination by omega, retainedHelper, ht]
  constructor
  · rintro ⟨a, ha, he⟩
    simpa only [he] using ha
  · intro h
    exact ⟨t, h, rfl⟩

end CodedSorting.Construction.PhysicalPortChecks
end PhysicalPortChecks

section PhysicalFrameWord
/-! The frame annotations below erase to the actual physical forward and
middle gate words. The middle word creates fresh copies, then complements
its matrix labels; it does not reverse overwrite operations. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace CodedSorting.Construction.PhysicalFramePaths

open CodedSorting.Circuit CodedSorting.CircuitProgram
open FiniteCertificate SymbolicXor ExplicitCopies ScatterCopies LocalPhysicalSemantics
open TensorLiftProgram LocalPhysicalContract TensorNetwork ReverseLocalProgram
open TensorFrameGeometry TensorFrameProgram

attribute [local irreducible] gates projections startFrames finalFrames

noncomputable section

def annotatePhysical (g : XorGate PhysicalReg) (P : LocalMatrix) : FramedGate :=
  ⟨g.lift localPhysicalIndex.symm.toEmbedding, P⟩

def framedOrdinary (g : Gate) : FramedGate :=
  annotatePhysical ((compileGate registerCount g).lift originalEmbedding) (frameMatrix g.frame)

def framedCopy (t : TemporaryReg) : FramedGate :=
  annotatePhysical (copyGate retainedHelper t) (frameMatrix (510 + t.val))

def framedScatter (g : Gate) : FramedGate :=
  annotatePhysical (copiedScatter (ConcreteLocalProgram.scatterRow g)) (frameMatrix 0)

def complementFrame (g : FramedGate) : FramedGate := ⟨g.gate, 1 - g.frame⟩

def forwardWord : List FramedGate :=
  physicalPrefix.map framedOrdinary ++ allTemporaries.map framedCopy ++
    physicalScatter.map framedScatter ++ physicalSuffix.map framedOrdinary

def middleRawWord : List FramedGate :=
  physicalSuffix.reverse.map framedOrdinary ++ allTemporaries.map framedCopy ++
    physicalScatter.reverse.map framedScatter ++ physicalPrefix.reverse.map framedOrdinary

def middleWord : List FramedGate := middleRawWord.map complementFrame

theorem annotatedProgram_erasure (before after scatter : List Gate) :
    (before.map framedOrdinary ++ allTemporaries.map framedCopy ++
      scatter.map framedScatter ++ after.map framedOrdinary).map FramedGate.gate =
      structuredProgram (localPhysicalProgram
        (before.map (compileGate registerCount)) (after.map (compileGate registerCount))
        (scatter.map ConcreteLocalProgram.scatterRow)) := by
  unfold structuredProgram localPhysicalProgram expandedProgram copyProgram
    ScatterCopies.physicalScatter
  simp only [List.map_append, List.map_map]
  rfl

theorem forwardWord_program : forwardWord.map FramedGate.gate = ConcreteLocalProgram.forward := by
  unfold forwardWord ConcreteLocalProgram.forward certificateForward
    ConcreteLocalProgram.before ConcreteLocalProgram.after ConcreteLocalProgram.rows
    ConcreteLocalProgram.prefixGates ConcreteLocalProgram.suffixGates ConcreteLocalProgram.scatterGates
  exact annotatedProgram_erasure physicalPrefix physicalSuffix physicalScatter

theorem annotatedMiddle_erasure (before after scatter : List Gate) :
    ((after.reverse.map framedOrdinary ++ allTemporaries.map framedCopy ++
      scatter.reverse.map framedScatter ++ before.reverse.map framedOrdinary).map
        complementFrame).map FramedGate.gate =
      structuredProgram (reverseLocalPhysicalProgram
        (before.map (compileGate registerCount)) (after.map (compileGate registerCount))
        (scatter.map ConcreteLocalProgram.scatterRow)) := by
  unfold structuredProgram reverseLocalPhysicalProgram localPhysicalProgram
    expandedProgram copyProgram ScatterCopies.physicalScatter
  simp only [List.map_append, List.map_map, List.map_reverse]
  rfl

theorem middleWord_program : middleWord.map FramedGate.gate = ConcreteLocalProgram.middle := by
  unfold middleWord middleRawWord ConcreteLocalProgram.middle certificateMiddle
    ConcreteLocalProgram.before ConcreteLocalProgram.after ConcreteLocalProgram.rows
    ConcreteLocalProgram.prefixGates ConcreteLocalProgram.suffixGates ConcreteLocalProgram.scatterGates
  exact annotatedMiddle_erasure physicalPrefix physicalSuffix physicalScatter

def localNumber (r : LocalReg) : Nat := (physicalIndex (localPhysicalIndex r)).val

@[simp] theorem localNumber_original (r : OriginalReg) :
    localNumber (localPhysicalIndex.symm (.inl r)) = r.val := by
  simp only [localNumber, Equiv.apply_symm_apply]
  rfl

@[simp] theorem localNumber_temporary (t : TemporaryReg) :
    localNumber (localPhysicalIndex.symm (.inr t)) = 661 + t.val := by
  simp only [localNumber, Equiv.apply_symm_apply]
  rfl

@[simp] theorem localNumber_source (a : ThreeCopySchedule.Line) :
    localNumber (.inl (0, a)) = a.val := by
  simp only [localNumber, index_source]
  rfl

@[simp] theorem localNumber_target (a : ThreeCopySchedule.Line) :
    localNumber (.inl (1, a)) = 111 + a.val := by
  simp only [localNumber, index_target]
  rfl

@[simp] theorem localNumber_helper (h : Fin 439) :
    localNumber (.inr (.inl h)) = 222 + h.val := rfl

@[simp] theorem localNumber_temp (t : Fin 9) :
    localNumber (.inr (.inr t)) = 661 + t.val := rfl

theorem localNumber_data (bank : Fin 2) (a : ThreeCopySchedule.Line) :
    localNumber (.inl (bank, a)) = 111 * bank.val + a.val := by
  have h : bank = 0 ∨ bank = 1 := by omega
  rcases h with rfl | rfl <;> simp

theorem annotatePhysical_ports (g : XorGate PhysicalReg) (P : LocalMatrix) (r : LocalReg) :
    r ∈ (annotatePhysical g P).gate.ports ↔ localPhysicalIndex r ∈ g.ports := by
  simp [annotatePhysical, XorGate.lift]

theorem framedOrdinary_ports (g : Gate) (r : LocalReg)
    (hbound : g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    r ∈ (framedOrdinary g).gate.ports ↔ localNumber r ∈ (ordinaryEvent g).ports := by
  rw [framedOrdinary, annotatePhysical_ports]
  generalize he : localPhysicalIndex r = p
  cases p with
  | inl a =>
    simpa only [localNumber, he, physicalIndex, finSumFinEquiv] using
      PhysicalPortChecks.ordinary_original g a
  | inr t =>
    simpa only [localNumber, he, physicalIndex, finSumFinEquiv] using
      PhysicalPortChecks.ordinary_temporary g t hbound

theorem framedCopy_ports (t : TemporaryReg) (r : LocalReg) :
    r ∈ (framedCopy t).gate.ports ↔ localNumber r ∈ (copyEvent t.val).ports := by
  rw [framedCopy, annotatePhysical_ports]
  generalize he : localPhysicalIndex r = p
  cases p with
  | inl a =>
    simpa only [localNumber, he, physicalIndex, finSumFinEquiv] using
      PhysicalPortChecks.copy_original t a
  | inr u =>
    simpa only [localNumber, he, physicalIndex, finSumFinEquiv] using
      PhysicalPortChecks.copy_temporary t u

theorem framedScatter_ports (g : Gate) (r : LocalReg) (hbound : g.destination < 661) :
    r ∈ (framedScatter g).gate.ports ↔ localNumber r ∈ (scatterEvent g).ports := by
  rw [framedScatter, annotatePhysical_ports]
  generalize he : localPhysicalIndex r = p
  cases p with
  | inl a =>
    simpa only [localNumber, he, physicalIndex, finSumFinEquiv] using
      PhysicalPortChecks.scatter_original g a hbound
  | inr t =>
    simpa only [localNumber, he, physicalIndex, finSumFinEquiv] using
      PhysicalPortChecks.scatter_temporary g t hbound

theorem middle_original_visits_reverse (r : OriginalReg) :
    (eventVisits r.val middleEvents).reverse = eventVisits r.val forwardEvents :=
  middle_original_visits_reverse_of_shape r
    (fun g hg => (ConcreteLocalProgram.scatterShape g hg).2.1)

theorem middlePathValid_of_forward (r : OriginalReg) :
    middlePathValid r.val = forwardPathValid r.val := by
  unfold middlePathValid forwardPathValid
  rw [middle_original_visits_reverse r]

theorem localVisits_append (xs ys : List FramedGate) (r : LocalReg) :
    localVisits (xs ++ ys) r = localVisits xs r ++ localVisits ys r := by
  simp [localVisits]

theorem visits_map_eq {A : Type*} (xs : List A)
    (annotate : A → FramedGate) (event : A → FrameEvent) (r : LocalReg)
    (hports : ∀ a ∈ xs,
      r ∈ (annotate a).gate.ports ↔ localNumber r ∈ (event a).ports)
    (hframes : ∀ a ∈ xs, (annotate a).frame = frameMatrix (event a).frame) :
    localVisits (xs.map annotate) r =
      (eventVisits (localNumber r) (xs.map event)).map frameMatrix := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hp := hports x (by simp)
    have hf := hframes x (by simp)
    have hi := ih (fun a ha => hports a (by simp [ha]))
      (fun a ha => hframes a (by simp [ha]))
    by_cases h : localNumber r ∈ (event x).ports
    · have hg := hp.mpr h
      simpa [localVisits, eventVisits, hg, h, hf] using congrArg (fun ys => frameMatrix (event x).frame :: ys) hi
    · have hg : r ∉ (annotate x).gate.ports := fun hr => h (hp.mp hr)
      simpa [localVisits, eventVisits, hg, h] using hi

theorem framedOrdinary_visits (xs : List Gate) (r : LocalReg)
    (hb : ∀ g ∈ xs, g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    localVisits (xs.map framedOrdinary) r =
      (eventVisits (localNumber r) (xs.map ordinaryEvent)).map frameMatrix :=
  visits_map_eq xs _ _ r (fun g hg => framedOrdinary_ports g r (hb g hg))
    (fun _ _ => rfl)

theorem framedCopy_visits (r : LocalReg) :
    localVisits (allTemporaries.map framedCopy) r =
      (eventVisits (localNumber r) ((List.range 9).map copyEvent)).map frameMatrix := by
  have h := visits_map_eq allTemporaries framedCopy (fun t => copyEvent t.val) r
    (fun t _ => framedCopy_ports t r) (fun _ _ => rfl)
  have he : allTemporaries.map (fun t => copyEvent t.val) = (List.range 9).map copyEvent := by
    rfl
  rw [he] at h
  exact h

theorem framedScatter_visits (xs : List Gate) (r : LocalReg)
    (hb : ∀ g ∈ xs, g.destination < 661) :
    localVisits (xs.map framedScatter) r =
      (eventVisits (localNumber r) (xs.map scatterEvent)).map frameMatrix :=
  visits_map_eq xs _ _ r (fun g hg => framedScatter_ports g r (hb g hg))
    (fun _ _ => rfl)

theorem visits_components (before scatter after : List Gate) (r : LocalReg)
    (hb : ∀ g ∈ before, g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount)
    (hm : ∀ g ∈ scatter, g.destination < 661)
    (ha : ∀ g ∈ after, g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    localVisits (before.map framedOrdinary ++ allTemporaries.map framedCopy ++
      scatter.map framedScatter ++ after.map framedOrdinary) r =
      (eventVisits (localNumber r) (before.map ordinaryEvent ++ (List.range 9).map copyEvent ++
        scatter.map scatterEvent ++ after.map ordinaryEvent)).map frameMatrix := by
  simp only [localVisits_append, eventVisits_append, List.map_append]
  rw [framedOrdinary_visits before r hb, framedCopy_visits r,
    framedScatter_visits scatter r hm, framedOrdinary_visits after r ha]

theorem forwardWord_visits (r : LocalReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    localVisits forwardWord r = (eventVisits (localNumber r) forwardEvents).map frameMatrix := by
  have hp : ∀ g ∈ physicalPrefix,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount :=
    fun g hg => hb g (List.mem_of_mem_take (l := gates.toList) (i := beforeScatterCount) hg)
  have hs : ∀ g ∈ physicalSuffix,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount :=
    fun g hg => hb g (List.mem_of_mem_drop (l := gates.toList) (i := beforeScatterCount + portCount) hg)
  have hm : ∀ g ∈ physicalScatter, g.destination < 661 := by
    intro g hg
    exact (hb g (List.mem_of_mem_drop (l := gates.toList) (i := beforeScatterCount)
      (List.mem_of_mem_take (l := gates.toList.drop beforeScatterCount) (i := portCount) hg))).1
  unfold forwardWord forwardEvents
  exact visits_components physicalPrefix physicalScatter physicalSuffix r hp hm hs

theorem middleRawWord_visits (r : LocalReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    localVisits middleRawWord r = (eventVisits (localNumber r) middleEvents).map frameMatrix := by
  have hp : ∀ g ∈ physicalPrefix.reverse,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount :=
    fun g hg => hb g (List.mem_of_mem_take (l := gates.toList) (i := beforeScatterCount)
      ((List.mem_reverse (as := physicalPrefix)).mp hg))
  have hs : ∀ g ∈ physicalSuffix.reverse,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount :=
    fun g hg => hb g (List.mem_of_mem_drop (l := gates.toList) (i := beforeScatterCount + portCount)
      ((List.mem_reverse (as := physicalSuffix)).mp hg))
  have hm : ∀ g ∈ physicalScatter.reverse, g.destination < 661 := by
    intro g hg
    exact (hb g (List.mem_of_mem_drop (l := gates.toList) (i := beforeScatterCount)
      (List.mem_of_mem_take (l := gates.toList.drop beforeScatterCount) (i := portCount)
        ((List.mem_reverse (as := physicalScatter)).mp hg)))).1
  unfold middleRawWord middleEvents
  exact visits_components physicalSuffix.reverse physicalScatter.reverse physicalPrefix.reverse r hs hm hp

theorem complementFrame_visits (word : List FramedGate) (r : LocalReg) :
    localVisits (word.map complementFrame) r = (localVisits word r).map (fun P => 1 - P) := by
  simp [localVisits, complementFrame, List.filter_map, List.map_map, Function.comp_def]

theorem middleWord_visits (r : LocalReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    localVisits middleWord r =
      (eventVisits (localNumber r) middleEvents).map (fun f => 1 - frameMatrix f) := by
  rw [middleWord, complementFrame_visits, middleRawWord_visits r hb, List.map_map]
  rfl

theorem climbPath_endpoint_chain (start finish : Nat) (visits : List Nat)
    (hv : ∀ f ∈ start :: visits ++ [finish], IntegerProjection.ProjectionEquations projections[f]!)
    (hc : climbPath start (visits ++ [finish]) = true) :
    LocalChain (frameMatrix start) (visits.map frameMatrix ++ [frameMatrix finish]) := by
  have h := localChain_of_climbPath start (visits ++ [finish]) hv hc
  simpa only [List.map_append, List.map_cons, List.map_nil] using h

theorem reverse_complement_frame_chain (start finish : Nat) (visits reversed : List Nat)
    (hp : LocalChain (frameMatrix start) (visits.map frameMatrix ++ [frameMatrix finish]))
    (he : reversed.reverse = visits) :
    LocalChain (1 - frameMatrix finish)
      (reversed.map (fun f => 1 - frameMatrix f) ++ [1 - frameMatrix start]) := by
  have hm := localChain_reverse_complement (frameMatrix start) (frameMatrix finish)
    (visits.map frameMatrix) hp
  have hr := (List.reverse_eq_iff (as := reversed) (bs := visits)).mp he
  rw [hr]
  simpa only [← List.map_reverse, List.map_map, Function.comp_apply] using hm

theorem forward_original_chain (r : OriginalReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount)
    (hv : ∀ f ∈ startFrames[r.val]! :: eventVisits r.val forwardEvents ++ [finalFrames[r.val]!],
      IntegerProjection.ProjectionEquations projections[f]!)
    (hc : forwardPathValid r.val = true) :
    LocalChain (frameMatrix startFrames[r.val]!)
      (localVisits forwardWord (localPhysicalIndex.symm (.inl r)) ++ [frameMatrix finalFrames[r.val]!]) := by
  rw [forwardWord_visits (localPhysicalIndex.symm (.inl r)) hb, localNumber_original]
  unfold forwardPathValid at hc
  exact climbPath_endpoint_chain startFrames[r.val]! finalFrames[r.val]!
    (eventVisits r.val forwardEvents) hv hc

theorem middle_original_chain (r : OriginalReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount)
    (hv : ∀ f ∈ startFrames[r.val]! :: eventVisits r.val forwardEvents ++ [finalFrames[r.val]!],
      IntegerProjection.ProjectionEquations projections[f]!)
    (hc : forwardPathValid r.val = true) :
    LocalChain (1 - frameMatrix finalFrames[r.val]!)
      (localVisits middleWord (localPhysicalIndex.symm (.inl r)) ++ [1 - frameMatrix startFrames[r.val]!]) := by
  rw [middleWord_visits (localPhysicalIndex.symm (.inl r)) hb, localNumber_original]
  unfold forwardPathValid at hc
  have hp := climbPath_endpoint_chain startFrames[r.val]! finalFrames[r.val]!
    (eventVisits r.val forwardEvents) hv hc
  exact reverse_complement_frame_chain startFrames[r.val]! finalFrames[r.val]!
    (eventVisits r.val forwardEvents) (eventVisits r.val middleEvents) hp
    (middle_original_visits_reverse r)

theorem forward_temporary_visits (t : TemporaryReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    ∃ n : Nat, localVisits forwardWord (localPhysicalIndex.symm (.inr t)) =
      frameMatrix (510+t.val) :: List.replicate n (frameMatrix 0) := by
  obtain ⟨n, hn⟩ := forward_temporary_events t hb
  refine ⟨n, ?_⟩
  rw [forwardWord_visits (localPhysicalIndex.symm (.inr t)) hb, localNumber_temporary]
  rw [hn]
  simp

theorem middle_temporary_visits (t : TemporaryReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount) :
    ∃ n : Nat, localVisits middleWord (localPhysicalIndex.symm (.inr t)) =
      (1 - frameMatrix (510+t.val)) :: List.replicate n (1 - frameMatrix 0) := by
  obtain ⟨n, hn⟩ := middle_temporary_events t hb
  refine ⟨n, ?_⟩
  rw [middleWord_visits (localPhysicalIndex.symm (.inr t)) hb, localNumber_temporary]
  rw [hn]
  simp

end
end CodedSorting.Construction.PhysicalFramePaths
end PhysicalFrameWord

section PhysicalFrameTemporaryCost
/-! Rank cost of actual retained-copy temporary paths. The source label is
the copy label and the terminal label is the scatter label. These auxiliary
registers are not independent sessions, so no endpoint-separation claim is
attached to their source or terminal labels. -/

set_option autoImplicit false

namespace CodedSorting.Construction.PhysicalFramePaths

open CodedSorting.TensorLabels CodedSorting.RankMetric
open ThreeCopySchedule TensorLiftProgram TensorFrameGeometry TensorFrameProgram
open LocalPhysicalSemantics FiniteCertificate

noncomputable section

theorem forward_temporary_global_cost (round : TensorLiftProgram.Round) (block : Block) (t : TemporaryReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount)
    (hzero : frameMatrix 0 = 0)
    (hf : IntegerProjection.ProjectionEquations projections[510+t.val]!)
    (hdim : projections[510+t.val]!.dimension = 7) :
    chainCost (globalFrame round block (frameMatrix (510+t.val)))
      ((localVisits forwardWord (localPhysicalIndex.symm (.inr t))).map
        (globalFrame round block) ++ [globalFrame round block 0]) = 7 := by
  obtain ⟨n, hn⟩ := forward_temporary_visits t hb
  rw [hn, List.map_cons, List.map_replicate, hzero,
    copiedFrame_global_cost round block _ n (frameMatrix_idempotent _ hf)]
  exact (IntegerProjection.certificate_rank _ hf).trans hdim

theorem middle_temporary_global_cost (round : TensorLiftProgram.Round) (block : Block) (t : TemporaryReg)
    (hb : ∀ g ∈ gates.toList,
      g.destination < registerCount ∧ ∀ s ∈ g.sources, s < registerCount)
    (hzero : frameMatrix 0 = 0)
    (hf : IntegerProjection.ProjectionEquations projections[510+t.val]!)
    (hdim : projections[510+t.val]!.dimension = 7) :
    chainCost (globalFrame round block (1-frameMatrix (510+t.val)))
      ((localVisits middleWord (localPhysicalIndex.symm (.inr t))).map
        (globalFrame round block) ++ [globalFrame round block 1]) = 7 := by
  obtain ⟨n, hn⟩ := middle_temporary_visits t hb
  rw [hn, List.map_cons, List.map_replicate, hzero, sub_zero,
    copiedComplement_global_cost round block _ n (frameMatrix_idempotent _ hf)]
  exact (IntegerProjection.certificate_rank _ hf).trans hdim

end
end CodedSorting.Construction.PhysicalFramePaths
end PhysicalFrameTemporaryCost
