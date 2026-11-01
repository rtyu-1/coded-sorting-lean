import CodedSorting.Interchange.Framework.Recursion.RecursiveExchange

/-! Explicit incoming-port lists for the local XOR map of each physical edge.
The lists contain actual network ports; no off-port register value is read. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.CommonNetworkInputs

open Circuit CircuitProgram ProgramNetwork RecursiveExchange
open scoped BigOperators

noncomputable section

variable {R : Type*} [DecidableEq R]

def gatePort (p : List (XorGate R)) (t : Fin p.length) (r : R)
    (hr : r ∈ (p.get t).ports) : InputPort p (.gate t) :=
  .inr ⟨incomingWire p t r,
    (incomingWire_head p t r).trans (stageVertex_gate p t r hr)⟩

theorem gateInputMap_apply (p : List (XorGate R)) (t : Fin p.length)
    (r : R) (hr : r ∈ (p.get t).ports) (values : InputPort p (.gate t) → Bit) :
    gateInputMap p t values r = values (gatePort p t r hr) := by
  simp only [gateInputMap, LinearMap.pi_apply, dif_pos hr, LinearMap.proj_apply,
    gatePort]

def gateInputs (p : List (XorGate R)) (t : Fin p.length) (r : R)
    (hr : r ∈ (p.get t).ports) : List (InputPort p (.gate t)) :=
  gatePort p t r hr ::
    if ht : r ∈ (p.get t).targets then
      (p.get t).controls r |>.attach.toList.map (fun c =>
        gatePort p t c.val ((p.get t).controls_subset r ht c.property))
    else []

theorem gateInputs_sum (p : List (XorGate R)) (t : Fin p.length) (r : R)
    (hr : r ∈ (p.get t).ports) (values : InputPort p (.gate t) → Bit) :
    (p.get t).eval (gateInputMap p t values) r =
      ((gateInputs p t r hr).map values).sum := by
  unfold gateInputs XorGate.eval
  by_cases ht : r ∈ (p.get t).targets
  · simp only [if_pos ht, dif_pos ht, List.map_cons, List.sum_cons,
      gateInputMap_apply p t r hr, List.map_map, Finset.sum_map_toList]
    congr 1
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro c hc
    exact gateInputMap_apply p t c.val ((p.get t).controls_subset r ht c.property) values
  · simp only [if_neg ht, dif_neg ht, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, gateInputMap_apply p t r hr]

def inputList (p : List (XorGate R)) :
    (v : Vertex R p.length) → OutputPort p v → List (InputPort p v)
  | .source r, _ => [.inl ⟨r, rfl⟩]
  | .gate t, out => gateInputs p t out.val.2
      (outgoing_gate_port p t out.val out.property)
  | .pass t r, _ =>
      if hr : r ∈ (p.get t).ports then [] else
        [.inr ⟨incomingWire p t r,
          (incomingWire_head p t r).trans (stageVertex_pass p t r hr)⟩]
  | .sink _, _ => []

theorem localMap_eq_sum (p : List (XorGate R)) (v : Vertex R p.length)
    (out : OutputPort p v) (values : InputPort p v → Bit) :
    localMap p v values out = ((inputList p v out).map values).sum := by
  cases v with
  | source r =>
    simp only [inputList, localMap, LinearMap.pi_apply, LinearMap.proj_apply,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | gate t =>
    change (p.get t).eval (gateInputMap p t values) out.val.2 = _
    exact gateInputs_sum p t out.val.2
      (outgoing_gate_port p t out.val out.property) values
  | pass t r =>
    have hr := (outgoing_pass_index p t r out.val out.property).2
    simp only [inputList, localMap, dif_neg hr, LinearMap.pi_apply,
      LinearMap.proj_apply, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  | sink r => exact (no_outgoing_sink p r out.val out.property).elim

def ports (e : Edge) :
    List (InputPort (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e)) :=
  inputList (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e) ⟨e, rfl⟩

theorem localMap_ports (e : Edge)
    (values : InputPort (globalProgram Parameters.d)
      (wireTail (globalProgram Parameters.d) e) → Bit) :
    localMap (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) e)
      values ⟨e, rfl⟩ = ((ports e).map values).sum :=
  localMap_eq_sum _ _ _ _

end
end CodedSorting.CommonNetworkInputs
