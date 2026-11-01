import CodedSorting.Shared.Memory.Buffered.Permutation
import CodedSorting.Interchange.Framework.Resident.Base
import CodedSorting.Interchange.Recursion.CallBridge

section BufferedLeaf
/-!
# Buffered leaves at the actual Construction specialization radix

The constructor instantiates the existing distribution and gather instructions
at an arbitrary radix. In particular the Construction prime is used directly; no equality
with the old circuit's radix is assumed. The gather returns the exchanged file
to the original source, and both transfers are included in the charge.

Resident bucket capacity and a disjoint finite disk arena are explicit numeric
requirements. This file does not assert that a whole recursion has that space.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveBufferedLeaf

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonBufferedBaseLayout
open CommonLeafProgram (Machine)
open ExchangeInterface

noncomputable section

/-- One shared bucket per ordered pair of exchanged field values. -/
def buckets (radix : ℕ) (c : Call) : ℕ :=
  (radix ^ c.fieldWidth) * (radix ^ c.fieldWidth)

/-- Actual fused distribution and reconstruction instructions. -/
def code (q : Configuration) (radix : ℕ)
    (reader : Fin q.inventory.readers) (c : Call)
    (hfit : buckets radix c * q.block ≤ CommonExchangeLeaf.bankWords q) :
    List (Instruction q) :=
  CommonBufferedCosts.code q hfit reader
    (indexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
    (outputIndexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
    c.source c.buffer

def charge (q : Configuration) (radix : ℕ) (c : Call) : ℕ :=
  4 * count q (volume radix c) + 2 * buckets radix c + 1

/-- Both the original-file transfers and every rounded bucket transfer are
charged, before replacing the exact bucket total by a convenient envelope. -/
theorem code_cost (q : Configuration) (radix : ℕ)
    (reader : Fin q.inventory.readers) (c : Call)
    (hfit : buckets radix c * q.block ≤ CommonExchangeLeaf.bankWords q) :
    cost q (code q radix reader c hfit) =
      2 * count q (volume radix c) +
        2 * buckets radix c * count q (bucketSize c.prefixCount c.gap c.suffix) :=
  CommonBufferedCosts.code_cost q hfit reader _ _ c.source c.buffer

/-- Rounded bucket files fit in one rounded source volume plus one block
per bucket. All quantities refer to the same finite machine's block size. -/
theorem bucket_space (q : Configuration) (radix : ℕ) (c : Call) :
    buckets radix c * count q (bucketSize c.prefixCount c.gap c.suffix) ≤
      count q (volume radix c) + buckets radix c :=
  exchange_bucket_blocks_le c.prefixCount (radix ^ c.fieldWidth)
    c.gap c.suffix (width q) (width_pos q)

theorem code_correct (q : Configuration) (radix : ℕ)
    (reader : Fin q.inventory.readers) (c : Call)
    (a : Allocation q radix c)
    (hfit : buckets radix c * q.block ≤ CommonExchangeLeaf.bankWords q)
    (hwork : c.buffer + count q (volume radix c) + buckets radix c ≤ c.limit)
    (initial : Machine q) :
    (∀ i : Fin (volume radix c),
      readBit q (executeRaw q (code q radix reader c hfit) initial).1.disk
        c.source i.val =
      readBit q initial.disk c.source (permutation radix c i).val) ∧
    (∀ z : Fin (q.N ^ q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) →
      (executeRaw q (code q radix reader c hfit) initial).1.disk z = initial.disk z) := by
  have hb := bucket_space q radix c
  have harena : c.buffer + buckets radix c *
      count q (bucketSize c.prefixCount c.gap c.suffix) ≤ q.N ^ q.exponent := by
    have := a.limit_fits
    omega
  obtain ⟨hbits, hframe⟩ := CommonBufferedCosts.code_correct q hfit reader
    (indexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
    (outputIndexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix)
    (fun k r s hrs => (inverse_lt_iff _ _ _ _ k r s).2 hrs)
    (fun k r s hrs => (output_inverse_lt_iff _ _ _ _ k r s).2 hrs)
    c.source c.buffer initial a.source_fits harena a.source_separate
  constructor
  · intro i
    have hp : (indexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix).symm
        (outputIndexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix i) =
        permutation radix c i :=
      (indexEquiv c.prefixCount (radix ^ c.fieldWidth) c.gap c.suffix).symm_apply_apply _
    exact (hbits i).trans
      (congrArg (readBit q initial.disk c.source) (congrArg Fin.val hp))
  · intro z hout hworkz
    exact hframe z hout (by omega)

/-- A complete actual-instruction leaf, including reconstruction to the
source, frame, PC safety, I/O count and compressed instruction length. -/
def program (q : Configuration) (radix : ℕ)
    (reader : Fin q.inventory.readers) (c : Call)
    (a : Allocation q radix c)
    (hfit : buckets radix c * q.block ≤ CommonExchangeLeaf.bankWords q)
    (hwork : c.buffer + count q (volume radix c) + buckets radix c ≤ c.limit) :
    Program q radix c where
  instructions := code q radix reader c hfit
  charge := charge q radix c
  correct := fun s => (code_correct q radix reader c a hfit hwork s).1
  frame := fun s => (code_correct q radix reader c a hfit hwork s).2
  safe := CommonBufferedCosts.code_safe q hfit reader _ _ c.source c.buffer
  cost_le := (CommonBufferedCosts.code_cost_le q hfit reader _ _ c.source c.buffer).trans
    (Nat.le_succ _)
  length_le := CommonBufferedCosts.code_length_le q hfit reader _ _ c.source c.buffer

theorem program_instructions (q : Configuration) (radix : ℕ)
    (reader : Fin q.inventory.readers) (c : Call) (a : Allocation q radix c)
    (hfit : buckets radix c * q.block ≤ CommonExchangeLeaf.bankWords q)
    (hwork : c.buffer + count q (volume radix c) + buckets radix c ≤ c.limit) :
    (program q radix reader c a hfit hwork).instructions = code q radix reader c hfit := rfl

theorem program_charge (q : Configuration) (radix : ℕ)
    (reader : Fin q.inventory.readers) (c : Call) (a : Allocation q radix c)
    (hfit : buckets radix c * q.block ≤ CommonExchangeLeaf.bankWords q)
    (hwork : c.buffer + count q (volume radix c) + buckets radix c ≤ c.limit) :
    (program q radix reader c a hfit hwork).charge = charge q radix c := rfl

private theorem count_le_div_add_one (q : Configuration) (V : ℕ) :
    count q V ≤ V / width q + 1 := by
  change (V + width q - 1) / width q ≤ V / width q + 1
  exact (Nat.div_le_div_right (Nat.sub_le (V + width q) 1)).trans
    (Nat.add_div_right V (width_pos q)).le

/-- The explicit startup condition suffices for the public leaf charge.
No buffer startup is omitted merely because the buffers fit in RAM. -/
theorem charge_le_scan (q : Configuration) (radix : ℕ) (c : Call)
    (hstartup : buckets radix c * width q ≤ volume radix c + width q) :
    charge q radix c ≤ 20 * (volume radix c / width q + 1) := by
  have hb : buckets radix c ≤ volume radix c / width q + 1 := by
    have h := (Nat.le_div_iff_mul_le (width_pos q)).2 hstartup
    simpa only [Nat.add_div_right _ (width_pos q)] using h
  have hc := count_le_div_add_one q (volume radix c)
  have envelope : ∀ n C K : ℕ, C ≤ n + 1 → K ≤ n + 1 →
      4 * C + 2 * K + 1 ≤ 20 * (n + 1) := by
    intro n C K hC hK
    omega
  exact envelope _ _ _ hc hb

theorem charge_le (q : Configuration) (radix cutoff : ℕ) (c : Call)
    (hlarge : cutoff < volume radix c)
    (hstartup : buckets radix c * width q ≤ cutoff + width q) :
    charge q radix c ≤ 20 * (volume radix c / width q + 1) :=
  charge_le_scan q radix c
    (hstartup.trans (Nat.add_le_add_right hlarge.le _))

/-- A depth-zero leaf that is above the resident cutoff meets the concrete
buffer capacity, and its actual charge fits the Construction recurrence's leaf bound. -/
theorem leafFits_conditions (q : Configuration) (radix cutoff : ℕ) (c : Call)
    (hlarge : cutoff < volume radix c) (hf : LeafFits q radix cutoff 0 c) :
    buckets radix c * q.block ≤ CommonExchangeLeaf.bankWords q ∧
      charge q radix c ≤ 20 * (volume radix c / width q + 1) := by
  have h := hf
  simp only [LeafFits, if_neg (Nat.not_le.mpr hlarge), true_and] at h
  constructor
  · simpa only [buckets, pow_two] using h.1
  · apply charge_le_scan
    have hs : buckets radix c * width q ≤ cutoff + width q := by
      simpa only [buckets, pow_two] using h.2
    exact hs.trans (Nat.add_le_add_right hlarge.le _)

/-- The buffered leaf for the Construction matrix family's actual common prime. -/
def e8Program (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (c : Call) (a : Allocation q ExchangeSpecialization.radix c)
    (hlarge : cutoff < volume ExchangeSpecialization.radix c)
    (hf : LeafFits q ExchangeSpecialization.radix cutoff 0 c)
    (hwork : c.buffer + count q (volume ExchangeSpecialization.radix c) +
      buckets ExchangeSpecialization.radix c ≤ c.limit) :
    Program q ExchangeSpecialization.radix c :=
  program q ExchangeSpecialization.radix reader c a
    (leafFits_conditions q ExchangeSpecialization.radix cutoff c hlarge hf).1 hwork

theorem e8Program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (c : Call) (a : Allocation q ExchangeSpecialization.radix c)
    (hlarge : cutoff < volume ExchangeSpecialization.radix c)
    (hf : LeafFits q ExchangeSpecialization.radix cutoff 0 c)
    (hwork : c.buffer + count q (volume ExchangeSpecialization.radix c) +
      buckets ExchangeSpecialization.radix c ≤ c.limit) :
    (e8Program q reader cutoff c a hlarge hf hwork).charge ≤
      20 * (volume ExchangeSpecialization.radix c / width q + 1) :=
  (leafFits_conditions q ExchangeSpecialization.radix cutoff c hlarge hf).2

end
end CodedSorting.Construction.RecursiveBufferedLeaf

#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.program
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.code_cost
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.charge_le_scan
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.e8Program
#print axioms CodedSorting.Construction.RecursiveBufferedLeaf.e8Program_charge_le
end BufferedLeaf

section ResidentLeaf
/-!
# Resident leaves for the Construction radix

The actual static leaf reads the complete rounded input into the existing
resident bank, applies the Construction call's permutation there, and writes rounded
scratch. An explicitly appended and charged copy returns only the live
file to its source interval. Three extra scratch blocks cover bank rounding.
Rounded source reads may overlap scratch: every read precedes every write.
Only the live source and copy-back scratch intervals must be disjoint.
No equality with the old recursive construction's radix is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveResidentLeaf

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonRecursiveExchange (copyCode)
open ExchangeInterface (Call Allocation)
open ExchangeSpecialization (radix)

noncomputable section

def leafCode (q : Configuration) (c : Call)
    (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q) :
    List (Instruction q) :=
  CommonStaticLeaf.code q _ hV (ExchangeInterface.permutation radix c)
    c.source c.buffer

def code (q : Configuration) (reader : Fin q.inventory.readers) (c : Call)
    (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q) :
    List (Instruction q) :=
  leafCode q c hV ++
    copyCode q reader (ExchangeInterface.volume radix c) c.buffer c.source

def charge (q : Configuration) (c : Call) : ℕ :=
  20 * (ExchangeInterface.volume radix c / width q + 1)

/-- One actual resident execution, exposed in the common literal disk-bit view. -/
theorem leaf_raw (q : Configuration) (c : Call)
    (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q)
    (s : Machine q)
    (hs : c.source + CommonResidentBase.blocks q _ hV ≤ q.N^q.exponent)
    (hb : c.buffer + CommonResidentBase.blocks q _ hV ≤ q.N^q.exponent) :
    (∀ y : Fin (ExchangeInterface.volume radix c),
      readBit q (executeRaw q (leafCode q c hV) s).1.disk c.buffer y.val =
      readBit q s.disk c.source (ExchangeInterface.permutation radix c y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      a.val < c.buffer ∨ c.buffer + CommonResidentBase.blocks q _ hV ≤ a.val →
      (executeRaw q (leafCode q c hV) s).1.disk a = s.disk a) := by
  obtain ⟨final,out,hr,hbits,hframe,_,_⟩ := CommonStaticLeaf.raw_complete q _ hV
    (ExchangeInterface.permutation radix c) c.source c.buffer (unpack s.ram) s.disk hs hb
  rw [CommonBlockPair.machine_eta q s] at hr
  change executeRaw q (leafCode q c hV) s = _ at hr
  rw [hr]
  refine ⟨?_,hframe⟩
  intro y
  have h := hbits y
  rw [CommonEdgeExecution.diskBits_eq_readBit q out c.buffer _
    (CommonEdgeExecution.bit_address_fits q _ hV c.buffer hb y),
    CommonEdgeExecution.diskBits_eq_readBit q s.disk c.source _
    (CommonEdgeExecution.bit_address_fits q _ hV c.source hs
      (ExchangeInterface.permutation radix c y))] at h
  exact h

/-- The returned live file and the disk frame refer to the same run, including copy-back. -/
theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers) (c : Call)
    (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q)
    (a : Allocation q radix c)
    (hpadding : c.buffer + count q (ExchangeInterface.volume radix c) + 3 ≤ c.limit)
    (s : Machine q) :
    (∀ y : Fin (ExchangeInterface.volume radix c),
      readBit q (executeRaw q (code q reader c hV) s).1.disk c.source y.val =
      readBit q s.disk c.source (ExchangeInterface.permutation radix c y).val) ∧
    (∀ x : Fin (q.N^q.exponent),
      (x.val < c.source ∨ c.source + count q (ExchangeInterface.volume radix c) ≤ x.val) →
      (x.val < c.buffer ∨ c.limit ≤ x.val) →
      (executeRaw q (code q reader c hV) s).1.disk x = s.disk x) := by
  have hk := CommonResidentBase.blocks_le q (ExchangeInterface.volume radix c) hV
  have hsep := a.source_separate
  have hlimit := a.limit_fits
  have hsource : c.source + CommonResidentBase.blocks q _ hV ≤ q.N^q.exponent := by omega
  have hbuffer : c.buffer + CommonResidentBase.blocks q _ hV ≤ q.N^q.exponent := by omega
  obtain ⟨hfirst,hfframe⟩ := leaf_raw q c hV s hsource hbuffer
  obtain ⟨hsecond,hsframe⟩ := CommonRecursiveExchange.copyCode_raw q reader
    (ExchangeInterface.volume radix c) c.buffer c.source
    (executeRaw q (leafCode q c hV) s).1 (by omega) (by omega) (Or.inr hsep)
  rw [code,CommonPermutationPairs.raw_append]
  constructor
  · intro y
    exact (hsecond y).trans (hfirst y)
  · intro x hs hb
    exact (hsframe x hs).trans (hfframe x (by omega))

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers) (c : Call)
    (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q) :
    ∀ i ∈ code q reader c hV, RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hf | hc
  · exact CommonStaticLeaf.safe q _ hV _ c.source c.buffer i hf
  · exact CommonRecursiveExchange.copyCode_safe q reader _ c.buffer c.source i hc

private theorem length_envelope (C R L D : ℕ) (hR : R ≤ C+3)
    (hC : C ≤ D+1) (hL : L ≤ 6*C) : 3*R+1+L ≤ 20*(D+1) := by omega

private theorem cost_envelope (C R L D : ℕ) (hR : R ≤ C+3)
    (hC : C ≤ D+1) (hL : L ≤ 6*C) : 2*R+L ≤ 20*(D+1) := by omega

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers) (c : Call)
    (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q) :
    (code q reader c hV).length ≤ charge q c := by
  have hr := CommonStaticLeaf.length_code q _ hV (ExchangeInterface.permutation radix c)
    c.source c.buffer
  have hc := CommonRecursiveExchange.copyCode_length q reader (ExchangeInterface.volume radix c)
    c.buffer c.source
  have hk := CommonResidentBase.blocks_le q (ExchangeInterface.volume radix c) hV
  have hb := CommonResidentBase.count_le_floor q (ExchangeInterface.volume radix c)
  rw [code,List.length_append]
  change (leafCode q c hV).length = _ at hr
  rw [hr]
  exact length_envelope _ _ _ _ hk hb hc

theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers) (c : Call)
    (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q)
    (a : Allocation q radix c)
    (hpadding : c.buffer + count q (ExchangeInterface.volume radix c) + 3 ≤ c.limit) :
    cost q (code q reader c hV) ≤ charge q c := by
  have hk := CommonResidentBase.blocks_le q (ExchangeInterface.volume radix c) hV
  have hsep := a.source_separate
  have hlimit := a.limit_fits
  have hsource : c.source + CommonResidentBase.blocks q _ hV ≤ q.N^q.exponent := by omega
  have hbuffer : c.buffer + CommonResidentBase.blocks q _ hV ≤ q.N^q.exponent := by omega
  have hr := CommonStaticLeaf.cost_code q _ hV (ExchangeInterface.permutation radix c)
    c.source c.buffer hsource hbuffer
  have hc := CommonRecursiveExchange.copyCode_cost q reader (ExchangeInterface.volume radix c)
    c.buffer c.source
  have hb := CommonResidentBase.count_le_floor q (ExchangeInterface.volume radix c)
  rw [code,CommonPermutationPairs.cost_append]
  change cost q (leafCode q c hV) = _ at hr
  rw [hr]
  exact cost_envelope _ _ _ _ hk hb hc

/-- Actual resident Construction leaf, with explicitly charged copy-back and rounded scratch. -/
def program (q : Configuration) (reader : Fin q.inventory.readers) (c : Call)
    (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q)
    (a : Allocation q radix c)
    (hpadding : c.buffer + count q (ExchangeInterface.volume radix c) + 3 ≤ c.limit) :
    ExchangeInterface.Program q radix c where
  instructions := code q reader c hV
  charge := charge q c
  correct := fun s => (raw_correct q reader c hV a hpadding s).1
  frame := fun s => (raw_correct q reader c hV a hpadding s).2
  safe := code_safe q reader c hV
  cost_le := code_cost q reader c hV a hpadding
  length_le := code_length q reader c hV

@[simp] theorem program_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (c : Call) (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q)
    (a : Allocation q radix c)
    (hpadding : c.buffer + count q (ExchangeInterface.volume radix c) + 3 ≤ c.limit) :
    (program q reader c hV a hpadding).instructions =
      leafCode q c hV ++ copyCode q reader (ExchangeInterface.volume radix c) c.buffer c.source := rfl

@[simp] theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (c : Call) (hV : ExchangeInterface.volume radix c ≤ CommonExchangeLeaf.bankBits q)
    (a : Allocation q radix c)
    (hpadding : c.buffer + count q (ExchangeInterface.volume radix c) + 3 ≤ c.limit) :
    (program q reader c hV a hpadding).charge =
      20 * (ExchangeInterface.volume radix c / width q + 1) := rfl

#print axioms program
#print axioms raw_correct
#print axioms code_cost
#print axioms code_length

end
end CodedSorting.Construction.RecursiveResidentLeaf
end ResidentLeaf

section LeafProgram
/-! Actual Construction leaf selection. The public numeric LeafFits condition selects
the appropriate implementation; the separately stated Workspace condition
accounts for rounding and bucket startup on disk. No execution specification
is supplied as an assumption. This is a leaf constructor, not a recursive
program or a proof of whole-tree workspace sufficiency. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveLeafProgram

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface
open ExchangeSpecialization (radix)

noncomputable section

def padding (cutoff : Nat) (c : Call) : Nat :=
  if volume radix c ≤ cutoff then 3 else RecursiveBufferedLeaf.buckets radix c

def Workspace (q : Configuration) (cutoff : Nat) (c : Call) : Prop :=
  c.buffer + count q (volume radix c) + padding cutoff c ≤ c.limit

def budget (q : Configuration) (c : Call) : Nat :=
  20 * (volume radix c / width q + 1)

theorem resident_fit {q : Configuration} {cutoff k : Nat} {c : Call}
    (hf : LeafFits q radix cutoff k c) (hs : volume radix c ≤ cutoff) :
    volume radix c ≤ CommonExchangeLeaf.bankBits q := by
  simpa only [LeafFits, if_pos hs] using hf

theorem buffered_fit {q : Configuration} {cutoff k : Nat} {c : Call}
    (hf : LeafFits q radix cutoff k c) (hs : ¬volume radix c ≤ cutoff) :
    k = 0 ∧ RecursiveBufferedLeaf.buckets radix c * q.block ≤
      CommonExchangeLeaf.bankWords q ∧
    RecursiveBufferedLeaf.buckets radix c * width q ≤ cutoff + width q := by
  simpa only [LeafFits, if_neg hs, RecursiveBufferedLeaf.buckets, pow_two] using hf

/-- Select the real resident or distribution/gather instruction list. -/
def program (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (hf : LeafFits q radix cutoff k c)
    (a : Allocation q radix c) (hw : Workspace q cutoff c) : Program q radix c := by
  by_cases hs : volume radix c ≤ cutoff
  · exact RecursiveResidentLeaf.program q reader c (resident_fit hf hs) a
      (by simpa only [Workspace, padding, if_pos hs] using hw)
  · exact RecursiveBufferedLeaf.program q radix reader c a (buffered_fit hf hs).2.1
      (by simpa only [Workspace, padding, if_neg hs] using hw)

theorem program_resident_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (hf : LeafFits q radix cutoff k c)
    (a : Allocation q radix c) (hw : Workspace q cutoff c)
    (hs : volume radix c ≤ cutoff) :
    (program q reader cutoff k c hf a hw).instructions =
      RecursiveResidentLeaf.code q reader c (resident_fit hf hs) := by
  simp only [program, dif_pos hs]
  rfl

theorem program_buffered_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (hf : LeafFits q radix cutoff k c)
    (a : Allocation q radix c) (hw : Workspace q cutoff c)
    (hs : ¬volume radix c ≤ cutoff) :
    (program q reader cutoff k c hf a hw).instructions =
      RecursiveBufferedLeaf.code q radix reader c (buffered_fit hf hs).2.1 := by
  simp only [program, dif_neg hs]
  rfl

theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (hf : LeafFits q radix cutoff k c)
    (a : Allocation q radix c) (hw : Workspace q cutoff c) :
    (program q reader cutoff k c hf a hw).charge ≤ budget q c := by
  by_cases hs : volume radix c ≤ cutoff
  · simp only [program, dif_pos hs, RecursiveResidentLeaf.program_charge, budget]
    exact Nat.le_refl _
  · simp only [program, dif_neg hs, RecursiveBufferedLeaf.program_charge]
    exact RecursiveBufferedLeaf.charge_le q radix cutoff c (Nat.lt_of_not_ge hs)
      (buffered_fit hf hs).2.2

/-- Correctness, untouched disk frame, halting, charge and RAM bound for
the same selected controlled execution. PC capacity is an explicit bound. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (hf : LeafFits q radix cutoff k c)
    (a : Allocation q radix c) (hw : Workspace q cutoff c)
    (s : Machine q) (hsize : budget q c ≤ q.N^q.exponent) (hpc : pc q s.ram = 0) :
    let p := program q reader cutoff k c hf a hw
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q s.disk c.source (permutation radix c y).val) ∧
    (∀ z : Fin (q.N^q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) → result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧ result.2 ≤ budget q c ∧
    Fintype.card (ResidentIndex q) ≤ q.M := by
  have hb := program_charge_le q reader cutoff k c hf a hw
  obtain ⟨hc, hf', hh, hcost, hram⟩ := CommonFinitePermutation.complete q
    (program q reader cutoff k c hf a hw) s (hb.trans hsize) hpc
  exact ⟨hc, hf', hh, hcost.trans hb, hram⟩

/-- The leaf can be plugged into an actual selected Construction child call. The
existing one-layer allocation is reused, with extra leaf workspace explicit. -/
def actualChildProgram {q : Configuration} {f rows G S source temporary : Nat}
    (reader : Fin q.inventory.readers) (cutoff k : Nat)
    (a : OneLevelExchange.Setup q f rows G S source temporary)
    (hroom : a.network.buffer +
      count q (OneLevelAssembly.localVolume q (radix^f) rows G S) ≤ a.network.limit)
    (child : OneLevelChildren.Child)
    (hf : LeafFits q radix cutoff k (OneLevelExchange.childCall a child))
    (hw : Workspace q cutoff (OneLevelExchange.childCall a child)) :
    Program q radix (OneLevelExchange.childCall a child) :=
  program q reader cutoff k (OneLevelExchange.childCall a child) hf
    (RecursiveCallAddress.childAllocation a hroom child) hw

theorem actualChildProgram_charge_le {q : Configuration}
    {f rows G S source temporary : Nat}
    (reader : Fin q.inventory.readers) (cutoff k : Nat)
    (a : OneLevelExchange.Setup q f rows G S source temporary)
    (hroom : a.network.buffer +
      count q (OneLevelAssembly.localVolume q (radix^f) rows G S) ≤ a.network.limit)
    (child : OneLevelChildren.Child)
    (hf : LeafFits q radix cutoff k (OneLevelExchange.childCall a child))
    (hw : Workspace q cutoff (OneLevelExchange.childCall a child)) :
    (actualChildProgram reader cutoff k a hroom child hf hw).charge ≤
      budget q (OneLevelExchange.childCall a child) :=
  program_charge_le q reader cutoff k _ hf
    (RecursiveCallAddress.childAllocation a hroom child) hw

end
end CodedSorting.Construction.RecursiveLeafProgram
end LeafProgram

section BuildConditions
/-! Public numerical admissibility for the concrete depth-bounded Construction
recursion. Every field is a proposition about dimensions or resources.
There is no supplied program, permutation implementation, or successful-run
assumption. Proving these conditions uniformly from the paper's global
parameters is a separate resource-analysis task. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace CodedSorting.Construction.RecursiveBuildConditions

open CommonSortingNormalization
open ExchangeInterface
open ExchangeSpecialization (radix)
open RecursiveCallShape RecursiveCallBridge

noncomputable section

/-- Exact numerical hypotheses of the already implemented leaf selector. -/
structure LeafReady (q : Configuration) (cutoff k : Nat) (c : Call) : Prop where
  allocation : Allocation q radix c
  fits : LeafFits q radix cutoff k c
  workspace : RecursiveLeafProgram.Workspace q cutoff c

/-- A node uses its canonical next setup and all actual selected children.
The predicate parameter is instantiated by admissibility at one less depth;
it contains no child code or semantic correctness certificate. -/
structure NodeReady (q : Configuration) (k : Nat) (c : Call)
    (childReady : Call → Prop) : Prop where
  shape : ShapeDepth q (k+1) c
  allocation : Allocation q radix c
  reserve : requiredLimit q c ≤ c.limit
  children : ∀ child : OneLevelChildren.Child,
    childReady (OneLevelExchange.childCall (nextSetup shape allocation reserve) child)

/-- Depth zero is a real leaf. At positive depth, the public volume cutoff
chooses either a resident leaf or the canonical node. No tree or choice of
children is supplied by the caller. -/
def Ready (q : Configuration) (cutoff : Nat) : Nat → Call → Prop
  | 0, c => LeafReady q cutoff 0 c
  | k+1, c => if volume radix c ≤ cutoff then LeafReady q cutoff (k+1) c
      else NodeReady q k c (Ready q cutoff k)

theorem zero_leaf {q : Configuration} {cutoff : Nat} {c : Call}
    (h : Ready q cutoff 0 c) : LeafReady q cutoff 0 c := h

theorem small_leaf {q : Configuration} {cutoff k : Nat} {c : Call}
    (h : Ready q cutoff k c) (hs : volume radix c ≤ cutoff) :
    LeafReady q cutoff k c := by
  cases k with
  | zero => exact h
  | succ k => simpa only [Ready, if_pos hs] using h

theorem large_node {q : Configuration} {cutoff k : Nat} {c : Call}
    (h : Ready q cutoff (k+1) c) (hs : ¬ volume radix c ≤ cutoff) :
    NodeReady q k c (Ready q cutoff k) := by
  simpa only [Ready, if_neg hs] using h

theorem of_zero_leaf {q : Configuration} {cutoff : Nat} {c : Call}
    (h : LeafReady q cutoff 0 c) : Ready q cutoff 0 c := h

theorem of_small_leaf {q : Configuration} {cutoff k : Nat} {c : Call}
    (hs : volume radix c ≤ cutoff) (h : LeafReady q cutoff k c) :
    Ready q cutoff k c := by
  cases k with
  | zero => exact h
  | succ k => simpa only [Ready, if_pos hs] using h

theorem of_large_node {q : Configuration} {cutoff k : Nat} {c : Call}
    (hs : ¬ volume radix c ≤ cutoff) (h : NodeReady q k c (Ready q cutoff k)) :
    Ready q cutoff (k+1) c := by
  simpa only [Ready, if_neg hs] using h

end
end CodedSorting.Construction.RecursiveBuildConditions
end BuildConditions

section Build
/-! The recursive exchange program is built from the remaining depth and numerical admissibility conditions. At depth zero it runs a base case. At positive depth it either stops at the data-size cutoff or builds the child programs and combines them using the one-level construction. 







-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.RecursiveBuild

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open ExchangeInterface
open ExchangeSpecialization (radix)
open RecursiveBuildConditions RecursiveCallBridge

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program TensorFrameNetwork.actualLabel
  MachineNetworkAdapter.physicalInputs OneLevelChildren.enumeration

/-- The leaf implementation takes only its public numerical requirements. -/
def leaf (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : LeafReady q cutoff k c) : Program q radix c :=
  RecursiveLeafProgram.program q reader cutoff k c h.fits h.allocation h.workspace

/-- Every recursive invocation uses the predecessor depth. Lean checks this
definition by structural recursion; no fuel-exhaustion fallback is present. -/
def build (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : Nat) :
    (k : Nat) → (c : Call) → Ready q cutoff k c → Program q radix c
  | 0, c, h => leaf q reader cutoff 0 c (zero_leaf h)
  | k+1, c, h =>
      if hs : volume radix c ≤ cutoff then
        leaf q reader cutoff (k+1) c (small_leaf h hs)
      else
        let hn := large_node h hs
        nextProgram reader hn.shape hn.allocation hn.reserve
          (fun child => build q reader cutoff k
            (OneLevelExchange.childCall (nextSetup hn.shape hn.allocation hn.reserve) child)
            (hn.children child))

/-- These child programs are generated by the same recursive builder. -/
def children (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : NodeReady q k c (Ready q cutoff k)) :
    OneLevelExchange.Children (nextSetup h.shape h.allocation h.reserve) :=
  fun child => build q reader cutoff k
    (OneLevelExchange.childCall (nextSetup h.shape h.allocation h.reserve) child)
    (h.children child)

theorem build_zero (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : Nat) (c : Call) (h : Ready q cutoff 0 c) :
    build q reader cutoff 0 c h = leaf q reader cutoff 0 c (zero_leaf h) := rfl

theorem build_small (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c)
    (hs : volume radix c ≤ cutoff) :
    build q reader cutoff k c h = leaf q reader cutoff k c (small_leaf h hs) := by
  cases k with
  | zero => rfl
  | succ k => simp only [build, dif_pos hs]

theorem build_node (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff (k+1) c)
    (hs : ¬ volume radix c ≤ cutoff) :
    build q reader cutoff (k+1) c h =
      nextProgram reader (large_node h hs).shape (large_node h hs).allocation
        (large_node h hs).reserve (children q reader cutoff k c (large_node h hs)) := by
  simp only [build, dif_neg hs, children]
  rfl

/-- Exact stop-branch code provenance, including charged copy-back/gather. -/
theorem build_zero_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : Nat) (c : Call) (h : Ready q cutoff 0 c) :
    (build q reader cutoff 0 c h).instructions =
      (RecursiveLeafProgram.program q reader cutoff 0 c
        h.fits h.allocation h.workspace).instructions := rfl

theorem build_small_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c)
    (hs : volume radix c ≤ cutoff) :
    (build q reader cutoff k c h).instructions =
      (RecursiveLeafProgram.program q reader cutoff k c
        (small_leaf h hs).fits (small_leaf h hs).allocation
        (small_leaf h hs).workspace).instructions := by
  rw [build_small q reader cutoff k c h hs]
  rfl

/-- The recursive branch contains exactly the one-level program fed with
recursively generated children, without any new scan or conversion. -/
theorem build_node_instructions (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff (k+1) c)
    (hs : ¬ volume radix c ≤ cutoff) :
    let hn := large_node h hs
    (build q reader cutoff (k+1) c h).instructions =
      (OneLevelExchange.program reader hn.shape.gap_pos
        (RecursiveCallShape.suffixWords_pos hn.shape)
        (nextSetup hn.shape hn.allocation hn.reserve)
        (nextSetup_room hn.shape hn.allocation hn.reserve)
        (children q reader cutoff k c hn)).instructions := by
  dsimp only
  rw [build_node q reader cutoff k c h hs]
  exact nextProgram_instructions reader _ _ _ _

theorem build_node_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff (k+1) c)
    (hs : ¬ volume radix c ≤ cutoff) :
    let hn := large_node h hs
    (build q reader cutoff (k+1) c h).charge =
      (OneLevelExchange.program reader hn.shape.gap_pos
        (RecursiveCallShape.suffixWords_pos hn.shape)
        (nextSetup hn.shape hn.allocation hn.reserve)
        (nextSetup_room hn.shape hn.allocation hn.reserve)
        (children q reader cutoff k c hn)).charge := by
  dsimp only
  rw [build_node q reader cutoff k c h hs]
  exact nextProgram_charge reader _ _ _ _

/-- The finite code and its execution do not depend on the proof supplied
for the same public numerical admissibility proposition. -/
theorem build_proof_independent (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h₁ h₂ : Ready q cutoff k c) :
    build q reader cutoff k c h₁ = build q reader cutoff k c h₂ := rfl

/-- For the constructed program itself, finite-PC capacity yields the
existing controlled-run guarantee. This does not bound the total charge by
the improved recurrence or establish globally sufficient workspace. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff k : Nat) (c : Call) (h : Ready q cutoff k c) (s : Machine q)
    (hsize : (build q reader cutoff k c h).charge ≤ q.N^q.exponent)
    (hpc : pc q s.ram = 0) :
    let p := build q reader cutoff k c h
    let result := ControlledNormalization.runLogical (policy q p.instructions)
      p.instructions.length s
    (∀ y : Fin (volume radix c), readBit q result.1.disk c.source y.val =
      readBit q s.disk c.source (permutation radix c y).val) ∧
    (∀ z : Fin (q.N^q.exponent),
      (z.val < c.source ∨ c.source + count q (volume radix c) ≤ z.val) →
      (z.val < c.buffer ∨ c.limit ≤ z.val) → result.1.disk z = s.disk z) ∧
    policy q p.instructions result.1.ram = none ∧ result.2 ≤ p.charge ∧
    Fintype.card (ResidentIndex q) ≤ q.M :=
  CommonFinitePermutation.complete q (build q reader cutoff k c h) s hsize hpc

end
end CodedSorting.Construction.RecursiveBuild
end Build
