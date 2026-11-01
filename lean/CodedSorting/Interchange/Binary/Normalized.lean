import CodedSorting.Interchange.Recursion.Workspace
import CodedSorting.Interchange.Binary.Machine

/-! One normalization ratio supplies every base/cutoff condition for the
actual binary-field exchange.  Source separation, finite disk allocation,
and instruction capacity remain explicit.  The suffix consists of whole
machine words throughout the padding and arbitrary-width calls. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.BinaryNormalized
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open RecursiveParameters (chosenBase cutoff Normalized)
open CommonChunkLayout CommonFinitePermutation ExchangeSpecialization Circuit
noncomputable section
attribute [local irreducible] BinaryMachine.program BinaryMachine.space
  ControlledNormalization.runLogical streamCount ambientDimension 

def space (q : Configuration) (P u G S : ℕ) (hG : 0<G) (hS : 0<S)
    (hnormal : Normalized q) : ℕ :=
  BinaryMachine.space q (chosenBase q) (cutoff q) P u G S
    (RecursiveParameters.chosenBase_pos q hnormal) hG hS (le_refl _)
    (RecursiveCostRate.block_le_cutoff (width q) (cutoff q)
      (RecursiveParameters.cutoff_child q hnormal))
    (RecursiveParameters.chosenBase_fit q hnormal)
    (RecursiveParameters.chosenBase_startup q hnormal)

def normalizedProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (P u G S source buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (hnormal : Normalized q)
    (hs : source+count q (Volume P (2^u) G (S*q.w))≤buffer)
    (hw : buffer+space q P u G S hG hS hnormal≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (2^u) G (S*q.w)) source buffer limit
      (swap P (2^u) G (S*q.w)) :=
  BinaryMachine.program q reader (chosenBase q) (cutoff q) P u G S
    source buffer limit (RecursiveParameters.chosenBase_pos q hnormal) hG hS
    (le_refl _) (RecursiveCostRate.block_le_cutoff (width q) (cutoff q)
      (RecursiveParameters.cutoff_child q hnormal))
    (RecursiveParameters.chosenBase_fit q hnormal)
    (RecursiveParameters.chosenBase_startup q hnormal) hs hw hl

/-- This single actual run exchanges both binary fields, preserves the
external frame, halts, stays within resident RAM, and has the improved cost.
The base width is selected from the machine, not supplied by the caller. -/
theorem normalized_bound (q : Configuration) (reader : Fin q.inventory.readers)
    (P u G S source buffer limit : ℕ) (hP : 0<P) (hG : 0<G) (hS : 0<S)
    (hnormal : Normalized q)
    (hs : source+count q (Volume P (2^u) G (S*q.w))≤buffer)
    (hw : buffer+space q P u G S hG hS hnormal≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : BinaryMachine.bound q (chosenBase q) (cutoff q) P u G S≤q.N^q.exponent)
    (hpc : pc q s.ram=0) :
    let p := normalizedProgram q reader P u G S source buffer limit hG hS hnormal hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ y : Fin (Volume P (2^u) G (S*q.w)),
      readBit q result.1.disk source y.val=
        readBit q s.disk source (swap P (2^u) G (S*q.w) y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (Volume P (2^u) G (S*q.w))≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    (result.2 : ℝ)≤BinaryCost.binaryConstant 24 27 (6*(2*radix+6))*
      ArbitraryCost.scan (width q) (Volume P (2^u) G (S*q.w))*
        (1+((u : ℝ)/(chosenBase q))^(1-(Construction.epsilon : ℝ))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  exact BinaryMachine.complete_improved q reader (chosenBase q) (cutoff q) P u G S
    source buffer limit (RecursiveParameters.chosenBase_pos q hnormal) hP hG hS
    (le_refl _) (RecursiveCostRate.block_le_cutoff (width q) (cutoff q)
      (RecursiveParameters.cutoff_child q hnormal))
    (RecursiveParameters.chosenBase_fit q hnormal)
    (RecursiveParameters.chosenBase_startup q hnormal)
    (RecursiveParameters.cutoff_child q hnormal) hs hw hl s hsize hpc

/-- The same automatically chosen base is logarithmic in the available
payload-bank/block ratio. -/
theorem normalized_base_scale (q : Configuration) (hnormal : Normalized q) :
    0<chosenBase q ∧
      8*chosenBase q≤Nat.log radix (RecursiveParameters.ratio q) ∧
      Nat.log radix (RecursiveParameters.ratio q)<8*ambientDimension*chosenBase q :=
  ⟨RecursiveParameters.chosenBase_pos q hnormal,
    RecursiveParameters.chosenBase_log_sandwich q hnormal⟩

#print axioms normalized_bound
#print axioms normalized_base_scale

end
end CodedSorting.Construction.BinaryNormalized
