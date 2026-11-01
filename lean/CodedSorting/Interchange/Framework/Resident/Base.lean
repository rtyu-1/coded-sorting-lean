import CodedSorting.Interchange.Framework.Recursion.OuterCopyFrame
import CodedSorting.Shared.Memory.EdgeReadBit

/-! A resident scalar exchange on the actual finite machine. The static
leaf reads its input into the existing bank, permutes there, and writes a
rounded scratch file. A separately charged copy returns precisely the
live file to its original region. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonResidentBase
open WordControl CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonRecursiveExchange (Program ScalarAddress copyCode)
open PhysicalFieldPacking RecursiveExchange Circuit Address
noncomputable section

def blocks (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q) : ℕ :=
  PhysicalStreamCursor.blockCount q.block (3*(CommonExchangeLeaf.roundedCount q V hV).val)

theorem blocks_le (q : Configuration) (V : ℕ) (hV : V≤CommonExchangeLeaf.bankBits q) :
    blocks q V hV≤count q V+3 :=
  CommonExchangeLeaf.rounded_blocks_bound q V hV

theorem count_le_floor (q : Configuration) (V : ℕ) :
    count q V≤V/(q.block*q.w)+1 := by
  apply LayoutConversion.blockCount_minimal _ _ _ (width_pos q)
  have hm := Nat.mod_lt V (width_pos q)
  change V%(q.block*q.w)<q.block*q.w at hm
  have he := Nat.div_add_mod V (q.block*q.w)
  change V≤(V/(q.block*q.w)+1)*(q.block*q.w)
  nlinarith

private theorem length_envelope (C R L D : ℕ) (hR : R≤C+3)
    (hC : C≤D+1) (hL : L≤6*C) : 3*R+1+L≤20*(D+1) := by omega

private theorem cost_envelope (C R L D : ℕ) (hR : R≤C+3)
    (hC : C≤D+1) (hL : L≤6*C) : 2*R+L≤20*(D+1) := by omega

def leafCode (q : Configuration) (f P G S : ℕ)
    (hV : ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q) (source buffer : ℕ) :
    List (Instruction q) :=
  CommonStaticLeaf.code q _ hV (CommonRecursiveBase.permutation f P G S) source buffer

def code (q : Configuration) (reader : Fin q.inventory.readers) (f P G S : ℕ)
    (hV : ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q) (source buffer : ℕ) :
    List (Instruction q) :=
  leafCode q f P G S hV source buffer ++
    copyCode q reader (ScalarVolume f P G S) buffer source

def charge (q : Configuration) (f P G S : ℕ) : ℕ :=
  20*(ScalarVolume f P G S/(q.block*q.w)+1)

theorem leaf_raw (q : Configuration) (f P G S : ℕ)
    (hV : ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (source buffer : ℕ) (s : Machine q)
    (hs : source+blocks q (ScalarVolume f P G S) hV≤q.N^q.exponent)
    (hb : buffer+blocks q (ScalarVolume f P G S) hV≤q.N^q.exponent) :
    (∀ a : ScalarAddress f P G S,
      readBit q (executeRaw q (leafCode q f P G S hV source buffer) s).1.disk
        buffer (scalarLayout f P G S a).val=
      readBit q s.disk source (scalarLayout f P G S (exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<buffer ∨
      buffer+blocks q (ScalarVolume f P G S) hV≤a.val →
      (executeRaw q (leafCode q f P G S hV source buffer) s).1.disk a=s.disk a) := by
  obtain ⟨final,out,hr,hbits,hframe,_,_⟩ := CommonStaticLeaf.raw_complete q _ hV
    (CommonRecursiveBase.permutation f P G S) source buffer (unpack s.ram) s.disk hs hb
  rw [CommonBlockPair.machine_eta q s] at hr
  change executeRaw q (leafCode q f P G S hV source buffer) s=_ at hr
  rw [hr]
  refine ⟨?_,hframe⟩
  intro a
  have h := hbits (scalarLayout f P G S a)
  rw [CommonRecursiveBase.permutation_encoded] at h
  rw [CommonEdgeExecution.diskBits_eq_readBit q out buffer _
    (CommonEdgeExecution.bit_address_fits q _ hV buffer hb (scalarLayout f P G S a)),
    CommonEdgeExecution.diskBits_eq_readBit q s.disk source _
    (CommonEdgeExecution.bit_address_fits q _ hV source hs
      (scalarLayout f P G S (exchange a)))] at h
  exact h

theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer limit : ℕ)
    (hV : ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+count q (ScalarVolume f P G S)+3≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q) :
    (∀ a : ScalarAddress f P G S,
      readBit q (executeRaw q (code q reader f P G S hV source buffer) s).1.disk
        source (scalarLayout f P G S a).val=
      readBit q s.disk source (scalarLayout f P G S (exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (ScalarVolume f P G S)≤a.val) →
      (a.val<buffer ∨ limit≤a.val) →
      (executeRaw q (code q reader f P G S hV source buffer) s).1.disk a=s.disk a) := by
  have hk := blocks_le q (ScalarVolume f P G S) hV
  have hsource : source+blocks q (ScalarVolume f P G S) hV≤q.N^q.exponent := by omega
  have hbuffer : buffer+blocks q (ScalarVolume f P G S) hV≤q.N^q.exponent := by omega
  obtain ⟨hfirst,hfframe⟩ := leaf_raw q f P G S hV source buffer s hsource hbuffer
  obtain ⟨hsecond,hsframe⟩ := CommonRecursiveExchange.copyCode_raw q reader
    (ScalarVolume f P G S) buffer source
    (executeRaw q (leafCode q f P G S hV source buffer) s).1
    (by omega) (by omega) (Or.inr hs)
  rw [code,CommonPermutationPairs.raw_append]
  constructor
  · intro a
    exact (hsecond (scalarLayout f P G S a)).trans (hfirst a)
  · intro a has hab
    exact (hsframe a has).trans (hfframe a (by omega))

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (source buffer : ℕ) :
    ∀ i∈code q reader f P G S hV source buffer,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hf|hc
  · exact CommonStaticLeaf.safe q _ hV _ source buffer i hf
  · exact CommonRecursiveExchange.copyCode_safe q reader _ buffer source i hc

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S : ℕ) (hV : ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (source buffer : ℕ) :
    (code q reader f P G S hV source buffer).length≤charge q f P G S := by
  have hr := CommonStaticLeaf.length_code q _ hV (CommonRecursiveBase.permutation f P G S)
    source buffer
  have hc := CommonRecursiveExchange.copyCode_length q reader (ScalarVolume f P G S)
    buffer source
  have hk := blocks_le q (ScalarVolume f P G S) hV
  have hb := count_le_floor q (ScalarVolume f P G S)
  rw [code,List.length_append]
  change (leafCode q f P G S hV source buffer).length=_ at hr
  rw [hr]
  change 3*blocks q (ScalarVolume f P G S) hV+1+
    (copyCode q reader (ScalarVolume f P G S) buffer source).length≤_
  exact length_envelope _ _ _ _ hk hb hc

theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer limit : ℕ)
    (hV : ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+count q (ScalarVolume f P G S)+3≤limit)
    (hl : limit≤q.N^q.exponent) :
    cost q (code q reader f P G S hV source buffer)≤charge q f P G S := by
  have hk := blocks_le q (ScalarVolume f P G S) hV
  have hsource : source+blocks q (ScalarVolume f P G S) hV≤q.N^q.exponent := by omega
  have hbuffer : buffer+blocks q (ScalarVolume f P G S) hV≤q.N^q.exponent := by omega
  have hr := CommonStaticLeaf.cost_code q _ hV (CommonRecursiveBase.permutation f P G S)
    source buffer hsource hbuffer
  have hc := CommonRecursiveExchange.copyCode_cost q reader (ScalarVolume f P G S)
    buffer source
  have hb := count_le_floor q (ScalarVolume f P G S)
  rw [code,CommonPermutationPairs.cost_append]
  change cost q (leafCode q f P G S hV source buffer)=_ at hr
  rw [hr]
  change 2*blocks q (ScalarVolume f P G S) hV+
    cost q (copyCode q reader (ScalarVolume f P G S) buffer source)≤_
  exact cost_envelope _ _ _ _ hk hb hc

/-- Fully proved resident leaf. Rounded scratch padding is disposable;
the live source interval alone is copied back. -/
def program (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer limit : ℕ)
    (hV : ScalarVolume f P G S≤CommonExchangeLeaf.bankBits q)
    (hs : source+count q (ScalarVolume f P G S)≤buffer)
    (hw : buffer+count q (ScalarVolume f P G S)+3≤limit)
    (hl : limit≤q.N^q.exponent) : Program q f P G S source buffer limit where
  instructions := code q reader f P G S hV source buffer
  charge := charge q f P G S
  correct := fun s => (raw_correct q reader f P G S source buffer limit hV hs hw hl s).1
  frame := fun s => (raw_correct q reader f P G S source buffer limit hV hs hw hl s).2
  safe := code_safe q reader f P G S hV source buffer
  cost_le := code_cost q reader f P G S source buffer limit hV hs hw hl
  length_le := code_length q reader f P G S hV source buffer

end
end CodedSorting.CommonResidentBase
