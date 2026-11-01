import CodedSorting.Interchange.Framework.Recursion.OuterProgram

section Base
/-! A concrete scalar-field exchange with no whole-file residency premise.

This is the finite-machine fallback for a stopped recursive call.  It uses
the proved public block-pair program and charges its full colour factor.
Its bound is `6 * (radix^f)^2 * ceil(V / (block*w))`; it is deliberately
not the constant-scan buffered leaf used by the paper's improved bound.
Spectator dimensions may be arbitrarily large within the finite disk.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonRecursiveBase
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open PhysicalFieldPacking RecursiveExchange Circuit Address
noncomputable section

abbrev ScalarAddress (f P G S : ℕ) :=
  FullAddress (Fin P) (Scalar f) (Fin G) (Fin S)

def permutation (f P G S : ℕ) : Equiv.Perm (Fin (ScalarVolume f P G S)) :=
  BaseExchangeProgram.permutation (P:=P) (Q:=radix^f) (G:=G) (S:=S)

def colour (f P G S : ℕ) : Fin (ScalarVolume f P G S) → Fin ((radix^f)*(radix^f)) :=
  BaseExchangeProgram.key (P:=P) (Q:=radix^f) (G:=G) (S:=S)

theorem increasing (f P G S : ℕ) (x y : Fin (ScalarVolume f P G S))
    (hxy : x<y) (hcolour : colour f P G S x=colour f P G S y) :
    permutation f P G S x<permutation f P G S y :=
  BaseExchangeProgram.increasing_streams x y hxy hcolour

theorem permutation_encoded (f P G S : ℕ) (a : ScalarAddress f P G S) :
    permutation f P G S (scalarLayout f P G S a)=
      scalarLayout f P G S (exchange a) :=
  PhysicalFieldPacking.leaf_realizes f P G S a

theorem permutation_inverse_encoded (f P G S : ℕ) (a : ScalarAddress f P G S) :
    (permutation f P G S).symm (scalarLayout f P G S a)=
      scalarLayout f P G S (exchange a) := by
  apply (permutation f P G S).injective
  rw [Equiv.apply_symm_apply,permutation_encoded]
  rfl

/-- The input-dependent bits occur only in the machine state, never in code. -/
def code (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source target : ℕ) : List (Instruction q) :=
  CommonPermutationScan.program q reader (permutation f P G S)
    (colour f P G S) source target

def charge (q : Configuration) (f P G S : ℕ) : ℕ :=
  6*((radix^f)*(radix^f))*count q (ScalarVolume f P G S)

theorem code_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source target : ℕ) :
    ∀ i∈code q reader f P G S source target,RespectsPC q i :=
  CommonPermutationScan.program_safe q reader _ _ source target

theorem code_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source target : ℕ) :
    (code q reader f P G S source target).length≤charge q f P G S :=
  CommonPermutationScan.program_length q reader _ _ source target (increasing f P G S)

theorem code_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source target : ℕ) :
    cost q (code q reader f P G S source target)≤charge q f P G S :=
  CommonPermutationScan.program_cost q reader _ _ source target (increasing f P G S)

theorem raw_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source target : ℕ) (s : Machine q)
    (hs : source+count q (ScalarVolume f P G S)≤q.N^q.exponent)
    (ht : target+count q (ScalarVolume f P G S)≤q.N^q.exponent)
    (hsep : source+count q (ScalarVolume f P G S)≤target ∨
      target+count q (ScalarVolume f P G S)≤source) :
    (∀ a : ScalarAddress f P G S,
      readBit q (executeRaw q (code q reader f P G S source target) s).1.disk target
        (scalarLayout f P G S a).val =
      readBit q s.disk source (scalarLayout f P G S (exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent), a.val<target ∨
      target+count q (ScalarVolume f P G S)≤a.val →
      (executeRaw q (code q reader f P G S source target) s).1.disk a=s.disk a) := by
  obtain ⟨hbits,hframe⟩ := CommonPermutationScan.raw_correct q reader
    (permutation f P G S) (colour f P G S) source target hs ht hsep s
  refine ⟨?_,hframe⟩
  intro a
  simpa only [permutation_inverse_encoded] using hbits (scalarLayout f P G S a)

/-- Complete fixed-policy execution for an arbitrary finite spectator
volume. Correctness, disk frame, halt, charge and RAM all concern one run. -/
theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source target : ℕ) (s : Machine q)
    (hs : source+count q (ScalarVolume f P G S)≤q.N^q.exponent)
    (ht : target+count q (ScalarVolume f P G S)≤q.N^q.exponent)
    (hsep : source+count q (ScalarVolume f P G S)≤target ∨
      target+count q (ScalarVolume f P G S)≤source)
    (hsize : charge q f P G S≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let program := code q reader f P G S source target
    let result := ControlledNormalization.runLogical (policy q program) program.length s
    (∀ a : ScalarAddress f P G S,
      readBit q result.1.disk target (scalarLayout f P G S a).val =
      readBit q s.disk source (scalarLayout f P G S (exchange a)).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨
      target+count q (ScalarVolume f P G S)≤a.val → result.1.disk a=s.disk a) ∧
    policy q program result.1.ram=none ∧ result.2≤charge q f P G S ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hbits,hframe,hhalt,hcost,hmemory⟩ := CommonPermutationScan.complete q reader
    (permutation f P G S) (colour f P G S) (increasing f P G S)
    source target hs ht hsep hsize s hpc
  refine ⟨?_,hframe,hhalt,hcost,hmemory⟩
  intro a
  simpa only [permutation_inverse_encoded] using hbits (scalarLayout f P G S a)

end
end CodedSorting.CommonRecursiveBase
end Base

section ExchangeBase
/-! Common finite-machine specification for recursive scalar exchange.
The exchanged file is returned to its source region.  A single interval
contains all disposable workspace, and every other disk block is framed.
The base constructor below executes both its exchange and its copy-back.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open PhysicalFieldPacking RecursiveExchange Circuit Address
noncomputable section

abbrev ScalarAddress := CommonRecursiveBase.ScalarAddress

/-- A specification of actual public instructions, including their disk
frame and charged execution. It supplies no assumed execution oracle. -/
structure Program (q : Configuration) (f P G S source buffer limit : ℕ) where
  instructions : List (Instruction q)
  charge : ℕ
  correct : ∀ (s : Machine q) (a : ScalarAddress f P G S),
    readBit q (executeRaw q instructions s).1.disk source (scalarLayout f P G S a).val =
      readBit q s.disk source (scalarLayout f P G S (exchange a)).val
  frame : ∀ (s : Machine q) (a : Fin (q.N^q.exponent)),
    (a.val<source ∨ source+count q (ScalarVolume f P G S)≤a.val) →
    (a.val<buffer ∨ limit≤a.val) →
    (executeRaw q instructions s).1.disk a=s.disk a
  safe : ∀ i∈instructions,RespectsPC q i
  cost_le : cost q instructions≤charge
  length_le : instructions.length≤charge

def copyCode (q : Configuration) (reader : Fin q.inventory.readers)
    (V source target : ℕ) : List (Instruction q) :=
  CommonPermutationScan.program q reader (Equiv.refl (Fin V)) (fun _ => (0 : Fin 1))
    source target

theorem copyCode_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (V source target : ℕ) (s : Machine q)
    (hs : source+count q V≤q.N^q.exponent)
    (ht : target+count q V≤q.N^q.exponent)
    (hsep : source+count q V≤target ∨ target+count q V≤source) :
    (∀ i : Fin V,readBit q (executeRaw q (copyCode q reader V source target) s).1.disk
      target i.val=readBit q s.disk source i.val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+count q V≤a.val →
      (executeRaw q (copyCode q reader V source target) s).1.disk a=s.disk a) :=
  CommonPermutationScan.raw_correct q reader _ _ source target hs ht hsep s

theorem copyCode_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (V source target : ℕ) :
    ∀ i∈copyCode q reader V source target,RespectsPC q i :=
  CommonPermutationScan.program_safe q reader _ _ source target

theorem copyCode_length (q : Configuration) (reader : Fin q.inventory.readers)
    (V source target : ℕ) :
    (copyCode q reader V source target).length≤6*count q V := by
  simpa only [Nat.mul_one] using CommonPermutationScan.program_length q reader
    (Equiv.refl (Fin V)) (fun _ => (0 : Fin 1)) source target (fun _ _ h _ => h)

theorem copyCode_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (V source target : ℕ) :
    cost q (copyCode q reader V source target)≤6*count q V := by
  simpa only [Nat.mul_one] using CommonPermutationScan.program_cost q reader
    (Equiv.refl (Fin V)) (fun _ => (0 : Fin 1)) source target (fun _ _ h _ => h)

def baseCode (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer : ℕ) : List (Instruction q) :=
  CommonRecursiveBase.code q reader f P G S source buffer ++
    copyCode q reader (ScalarVolume f P G S) buffer source

def baseCharge (q : Configuration) (f P G S : ℕ) : ℕ :=
  CommonRecursiveBase.charge q f P G S+6*count q (ScalarVolume f P G S)

theorem base_correct (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer limit : ℕ)
    (hsep : source+count q (ScalarVolume f P G S)≤buffer)
    (hwork : buffer+count q (ScalarVolume f P G S)≤limit)
    (hlimit : limit≤q.N^q.exponent) (s : Machine q) (a : ScalarAddress f P G S) :
    readBit q (executeRaw q (baseCode q reader f P G S source buffer) s).1.disk
      source (scalarLayout f P G S a).val =
    readBit q s.disk source (scalarLayout f P G S (exchange a)).val := by
  have hs : source+count q (ScalarVolume f P G S)≤q.N^q.exponent := by omega
  have ht : buffer+count q (ScalarVolume f P G S)≤q.N^q.exponent := by omega
  obtain ⟨hfirst,_⟩ := CommonRecursiveBase.raw_correct q reader f P G S source buffer s
    hs ht (Or.inl hsep)
  obtain ⟨hsecond,_⟩ := copyCode_raw q reader (ScalarVolume f P G S) buffer source
    (executeRaw q (CommonRecursiveBase.code q reader f P G S source buffer) s).1
    ht hs (Or.inr hsep)
  rw [baseCode,CommonPermutationPairs.raw_append,hsecond]
  exact hfirst a

theorem base_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer limit : ℕ)
    (hsep : source+count q (ScalarVolume f P G S)≤buffer)
    (hwork : buffer+count q (ScalarVolume f P G S)≤limit)
    (hlimit : limit≤q.N^q.exponent) (s : Machine q) (a : Fin (q.N^q.exponent))
    (hsource : a.val<source ∨ source+count q (ScalarVolume f P G S)≤a.val)
    (hbuffer : a.val<buffer ∨ limit≤a.val) :
    (executeRaw q (baseCode q reader f P G S source buffer) s).1.disk a=s.disk a := by
  have hs : source+count q (ScalarVolume f P G S)≤q.N^q.exponent := by omega
  have ht : buffer+count q (ScalarVolume f P G S)≤q.N^q.exponent := by omega
  obtain ⟨_,hfirst⟩ := CommonRecursiveBase.raw_correct q reader f P G S source buffer s
    hs ht (Or.inl hsep)
  obtain ⟨_,hsecond⟩ := copyCode_raw q reader (ScalarVolume f P G S) buffer source
    (executeRaw q (CommonRecursiveBase.code q reader f P G S source buffer) s).1
    ht hs (Or.inr hsep)
  rw [baseCode,CommonPermutationPairs.raw_append,hsecond a hsource]
  exact hfirst a (by omega)

theorem base_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer : ℕ) :
    ∀ i∈baseCode q reader f P G S source buffer,RespectsPC q i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact CommonRecursiveBase.code_safe q reader f P G S source buffer i hi
  · exact copyCode_safe q reader _ buffer source i hi

theorem base_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer : ℕ) :
    cost q (baseCode q reader f P G S source buffer)≤baseCharge q f P G S := by
  rw [baseCode,CommonPermutationPairs.cost_append]
  exact Nat.add_le_add (CommonRecursiveBase.code_cost q reader f P G S source buffer)
    (copyCode_cost q reader _ buffer source)

theorem base_length (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer : ℕ) :
    (baseCode q reader f P G S source buffer).length≤baseCharge q f P G S := by
  rw [baseCode,List.length_append]
  exact Nat.add_le_add (CommonRecursiveBase.code_length q reader f P G S source buffer)
    (copyCode_length q reader _ buffer source)

/-- Constructor with fully proved fields. No bound on total file residency
is imposed; its full `Q²` transfer coefficient remains visible. -/
def baseProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (f P G S source buffer limit : ℕ)
    (hsep : source+count q (ScalarVolume f P G S)≤buffer)
    (hwork : buffer+count q (ScalarVolume f P G S)≤limit)
    (hlimit : limit≤q.N^q.exponent) : Program q f P G S source buffer limit where
  instructions := baseCode q reader f P G S source buffer
  charge := baseCharge q f P G S
  correct := base_correct q reader f P G S source buffer limit hsep hwork hlimit
  frame := base_frame q reader f P G S source buffer limit hsep hwork hlimit
  safe := base_safe q reader f P G S source buffer
  cost_le := base_cost q reader f P G S source buffer
  length_le := base_length q reader f P G S source buffer

end
end CodedSorting.CommonRecursiveExchange
end ExchangeBase

section OuterCopyFrame
/-! Frame composition is checked with abstract program and allocation
arguments before a concrete network is supplied. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
namespace CodedSorting.CommonRecursiveExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonRecursiveOuter
attribute [local irreducible] CommonStaticSchedule.executeRaw
noncomputable section

/-- Preserve an unrelated disk block across the outer exchange and its
copy-back. `network` may contain all recursively generated child programs. -/
theorem outer_copy_frame (q : Configuration) (reader : Fin q.inventory.readers)
    (p : CommonRecursiveOuter.Setup q) (network : List (Instruction q)) (V limit : ℕ)
    (hV : V=parentBits q p)
    (hlimit : p.workspace+CommonResidentNetwork.fileCount*stride q p≤limit)
    (hn : ∀ (s : Machine q) (i : Fin (q.N^q.exponent)),
      i.val<p.workspace ∨ limit≤ i.val → (executeRaw q network s).1.disk i=s.disk i)
    (s : Machine q) (i : Fin (q.N^q.exponent))
    (hs : i.val<p.source ∨ p.source+count q V≤ i.val)
    (hw : i.val<p.temporary ∨ limit≤ i.val) :
    (executeRaw q (CommonRecursiveOuter.code q reader p network ++
      copyCode q reader V p.temporary p.source) s).1.disk i=s.disk i := by
  have hps : p.source+parentBlocks q p≤p.temporary := p.parents_separate
  have hpw : p.temporary+parentBlocks q p≤p.workspace := p.network_separate
  have hs' : i.val<p.source ∨ p.source+parentBlocks q p≤ i.val := by
    simpa only [hV] using hs
  have ht' : i.val<p.temporary ∨ p.temporary+parentBlocks q p≤ i.val := by omega
  have hw' : i.val<p.workspace ∨ p.workspace+CommonResidentNetwork.fileCount*stride q p≤ i.val := by omega
  have hf := CommonRecursiveOuter.raw_outside q reader p network i hs' ht' hw'
    (fun t => hn t i (by omega))
  have hsource : p.source+count q V≤q.N^q.exponent := by
    simpa only [hV] using source_fits q p
  have htemporary : p.temporary+count q V≤q.N^q.exponent := by
    simpa only [hV] using temporary_fits q p
  have hsep : p.source+count q V≤p.temporary := by simpa only [hV] using hps
  have hc : ∀ t : Machine q,
      (executeRaw q (copyCode q reader V p.temporary p.source) t).1.disk i=t.disk i := by
    intro t
    exact (copyCode_raw q reader V p.temporary p.source t htemporary hsource (Or.inr hsep)).2 i hs
  let P : Machine q→Prop := fun t => t.disk i=s.disk i
  have hA : ∀ t,P t→P (executeRaw q (CommonRecursiveOuter.code q reader p network) t).1 := by
    intro t ht
    exact (hf t).trans ht
  have hB : ∀ t,P t→P (executeRaw q (copyCode q reader V p.temporary p.source) t).1 := by
    intro t ht
    exact (hc t).trans ht
  exact CommonRawComposition.hoare_two q _ _ P P P hA hB s rfl

end
end CodedSorting.CommonRecursiveExchange
end OuterCopyFrame
