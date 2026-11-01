import CodedSorting.NetworkCoding.Theorem32.Coding
import CodedSorting.Circuit.Composition.TensorFrameNetwork

/-! Selected-session address semantics of the concrete Construction network.  Physical
temporary registers may have arbitrary contents.  This file proves the
functional boundary consumed by the actual machine adapter; it does not
claim that an abstract array is a disk execution. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace CodedSorting.Construction.ExchangeSimulation

open Circuit CircuitProgram ProgramNetwork TensorLiftProgram TensorThreeRound
open ThreeCopySchedule TensorFrameGeometry

noncomputable section

section Generic
variable {Reg Addr Session : Type*} [Fintype Reg] [DecidableEq Reg]
variable (program : List (XorGate Reg))

/-- A physical file at a source frame represents these logical payloads. -/
def logicalInput (source : Reg → Equiv.Perm Addr) (input : Reg → Addr → Bit)
    (x : Addr) (r : Reg) : Bit := input r (source r x)

/-- The literal wire value, represented in its head vertex's address frame. -/
def physicalWire (location : Vertex Reg program.length → Equiv.Perm Addr)
    (input : Reg → Addr → Bit) (e : Wire Reg program.length) (x : Addr) : Bit :=
  wireValue program (logicalInput (fun r => location (.source r)) input
    ((location (wireHead program e)).symm x)) e

theorem selected_sink (sourceReg sinkReg : Session → Reg)
    (hprogram : ∀ input r, runProgram program input (sinkReg r) = input (sourceReg r))
    (location : Vertex Reg program.length → Equiv.Perm Addr)
    (input : Reg → Addr → Bit) (r : Session) (x : Addr) :
    physicalWire program location input (sinkWire program (sinkReg r)) x =
      input (sourceReg r)
        (location (.source (sourceReg r)) ((location (.sink (sinkReg r))).symm x)) := by
  rw [physicalWire, sinkWire_head, wireValue_sink, hprogram]
  rfl

/-- Once complementary frames give the same exchange at every selected
session, all of the actual network outputs have that exact address action. -/
theorem selected_sink_exchange (sourceReg sinkReg : Session → Reg)
    (hprogram : ∀ input r, runProgram program input (sinkReg r) = input (sourceReg r))
    (location : Vertex Reg program.length → Equiv.Perm Addr)
    (exchange : Equiv.Perm Addr)
    (hframe : ∀ r, (location (.sink (sinkReg r))).symm.trans
      (location (.source (sourceReg r))) = exchange)
    (input : Reg → Addr → Bit) (r : Session) (x : Addr) :
    physicalWire program location input (sinkWire program (sinkReg r)) x =
      input (sourceReg r) (exchange x) := by
  rw [selected_sink program sourceReg sinkReg hprogram]
  exact congrArg (input (sourceReg r)) (congrArg (fun e : Equiv.Perm Addr => e x) (hframe r))

end Generic

attribute [local irreducible] TensorFrameNetwork.program
  ConcreteLocalProgram.forward ConcreteLocalProgram.middle

/-- The concrete three-round word recovers each original session at its
designated output.  Its copied temporaries are not independent sessions and
are not required to begin at zero or to be restored. -/
theorem actual_selected_program (input : GlobalReg → Bit) (r : IndependentStream) :
    runProgram TensorFrameNetwork.program input (.inl (originalSwap r)) = input (.inl r) := by
  unfold TensorFrameNetwork.program
  rw [threeRound_original _ _ _ NetworkCodingResult.forward_verified NetworkCodingResult.middle_verified
    NetworkCodingResult.forward_verified, TensorNetwork.originalSwap_involutive]

theorem actual_selected_sink {Addr : Type*}
    (location : Vertex GlobalReg TensorFrameNetwork.program.length → Equiv.Perm Addr)
    (input : GlobalReg → Addr → Bit) (r : IndependentStream) (x : Addr) :
    physicalWire TensorFrameNetwork.program location input
      (sinkWire TensorFrameNetwork.program (.inl (originalSwap r))) x =
    input (.inl r) (location (.source (.inl r))
      ((location (.sink (.inl (originalSwap r)))).symm x)) :=
  selected_sink TensorFrameNetwork.program Sum.inl (fun r => .inl (originalSwap r))
    actual_selected_program location input r x

theorem actual_selected_exchange {Addr : Type*}
    (location : Vertex GlobalReg TensorFrameNetwork.program.length → Equiv.Perm Addr)
    (exchange : Equiv.Perm Addr)
    (hframe : ∀ r : IndependentStream,
      (location (.sink (.inl (originalSwap r)))).symm.trans
        (location (.source (.inl r))) = exchange)
    (input : GlobalReg → Addr → Bit) (r : IndependentStream) (x : Addr) :
    physicalWire TensorFrameNetwork.program location input
      (sinkWire TensorFrameNetwork.program (.inl (originalSwap r))) x =
      input (.inl r) (exchange x) :=
  selected_sink_exchange TensorFrameNetwork.program Sum.inl
    (fun r => .inl (originalSwap r)) actual_selected_program
    location exchange hframe input r x

#print axioms actual_selected_program
#print axioms actual_selected_sink
#print axioms actual_selected_exchange

end
end CodedSorting.Construction.ExchangeSimulation
