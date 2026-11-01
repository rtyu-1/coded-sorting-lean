import CodedSorting.Interchange.Framework.BorrowedMemory.Machine

section Machine
/-! A generated finite-machine exchange for every prime-radix field width.
The long-field branch executes borrowing, prefix padding, actual recursive
chunks, erasure, and restoration. The short-field branch executes actual
depth-zero chunks. All conclusions concern the generated instructions. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonArbitraryMachine
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonChunkLayout CommonFinitePermutation CommonArbitraryConditions
open RecursiveExchange Circuit ArbitrarySchedule PhysicalChunkExchange PhysicalFieldPacking
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m radix

def space (q : Configuration) (base cutoff P e G S : ℕ) (hb : 0<base)
    (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q) : ℕ :=
  let k := depth Parameters.m base e
  let ρ := borrowedWidth radix Parameters.W k
  if ρ<e then
    let cs := ArbitraryRecursive.calls base k (e-ρ)
    let P' := ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k
    CommonBorrowedChunks.space q cutoff cs P ρ P' G S hG hS
      (paddedConditions q cutoff base k (e-ρ) (P*((radix^ρ)*(radix^ρ)))
        hb hresident hfit hstartup)
  else
    CommonChunkExchange.space q cutoff (ArbitraryRecursive.baseCalls base e) P G S hG hS
      (baseConditions q cutoff base e P hb hresident hfit hstartup)

theorem borrowed_fields (base e k ρ : ℕ) (hρ : ρ≤e) :
    radix^ρ*fieldCount (ArbitraryRecursive.calls base k (e-ρ))=radix^e := by
  rw [fieldCount_width,ArbitraryRecursive.calls_width,←pow_add,Nat.add_sub_of_le hρ]

theorem base_fields (base e : ℕ) :
    fieldCount (ArbitraryRecursive.baseCalls base e)=radix^e := by
  rw [fieldCount_width,ArbitraryRecursive.baseCalls_width]

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P e G S source buffer limit : ℕ) (hb : 0<base)
    (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q)
    (hs : source+count q (Volume P (radix^e) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P e G S hb hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (radix^e) G (S*q.w)) source buffer limit
      (swap P (radix^e) G (S*q.w)) := by
  let k := depth Parameters.m base e
  let ρ := borrowedWidth radix Parameters.W k
  by_cases hborrow : ρ<e
  · let cs := ArbitraryRecursive.calls base k (e-ρ)
    let P' := ArbitraryRecursive.paddedRows (P*((radix^ρ)*(radix^ρ))) k
    let hc := paddedConditions q cutoff base k (e-ρ) (P*((radix^ρ)*(radix^ρ)))
      hb hresident hfit hstartup
    have hfields := borrowed_fields base e k ρ hborrow.le
    have hs' : source+count q (Volume P (radix^ρ*fieldCount cs) G (S*q.w))≤buffer := by
      simpa only [cs,hfields] using hs
    have hw' : buffer+CommonBorrowedChunks.space q cutoff cs P ρ P' G S hG hS hc≤limit := by
      simpa only [space,show borrowedWidth radix Parameters.W (depth Parameters.m base e)<e
        from hborrow,if_pos] using hw
    exact CommonExchangeShapeProgram.reshape q rfl hfields rfl rfl
      (CommonBorrowedChunks.program q reader cutoff cs P ρ P' G S source buffer limit
        hG hS (ArbitraryRecursive.original_rows_le_padded _ _) hc hs' hw' hl)
  · let hc := baseConditions q cutoff base e P hb hresident hfit hstartup
    have hfields := base_fields base e
    have hs' : source+count q (Volume P (fieldCount (ArbitraryRecursive.baseCalls base e)) G (S*q.w))≤buffer := by
      simpa only [hfields] using hs
    have hw' : buffer+CommonChunkExchange.space q cutoff (ArbitraryRecursive.baseCalls base e)
        P G S hG hS hc≤limit := by
      simpa only [space,show ¬borrowedWidth radix Parameters.W (depth Parameters.m base e)<e
        from hborrow,if_neg] using hw
    exact CommonExchangeShapeProgram.reshape q rfl hfields rfl rfl
      (CommonChunkExchange.program q reader cutoff (ArbitraryRecursive.baseCalls base e)
        P G S source buffer limit hG hS hc hs' hw' hl)

def bound (q : Configuration) (base cutoff P e G S : ℕ) : ℕ :=
  CommonArbitraryCost.bound base cutoff (width q) P e G (S*q.w) 24 27 (6*(2*radix+6))

end
end CodedSorting.CommonArbitraryMachine
end Machine

section MachineBound
/-! Correctness, completion and the improved bound for the same generated
finite-machine exchange, for every prime-radix field width.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonArbitraryMachine
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonChunkLayout CommonFinitePermutation CommonArbitraryConditions
open RecursiveExchange Circuit ArbitrarySchedule PhysicalChunkExchange
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m radix
  ControlledNormalization.runLogical

theorem borrowed_charge_le (q : Configuration) (cutoff : ℕ)
    (cs : List ArbitraryRecursive.Call) (P ρ P' G S : ℕ) :
    CommonBorrowedChunks.bound q cutoff cs P ρ P' G S≤
      CommonArbitraryCost.borrowedBound cutoff (width q) cs P ρ P' G (S*q.w)
        24 27 (6*(2*radix+6)) := by
  unfold CommonBorrowedChunks.bound CommonArbitraryCost.borrowedBound
    CommonArbitraryCost.overheadBound
  rw [← PhysicalBorrowLayout.original_volume]
  have hV := CommonRecursiveExchange.Pruned.count_le_scan q
    (Volume P (radix^ρ*fieldCount cs) G (S*q.w))
  have hV' := CommonRecursiveExchange.Pruned.count_le_scan q
    (Volume P' (fieldCount cs) G (S*q.w))
  have h1 := Nat.mul_le_mul_left (24+6*ρ*(2*radix+6)) hV
  have h2 := Nat.mul_le_mul_left 27 hV'
  nlinarith only [h1,h2]

theorem charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P e G S source buffer limit : ℕ) (hb : 0<base)
    (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q)
    (hs : source+count q (Volume P (radix^e) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P e G S hb hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) :
    (program q reader base cutoff P e G S source buffer limit hb hG hS
      hresident hfit hstartup hs hw hl).charge≤bound q base cutoff P e G S := by
  let k := depth Parameters.m base e
  let ρ := borrowedWidth radix Parameters.W k
  by_cases hborrow : ρ<e
  · simp only [program,show borrowedWidth radix Parameters.W (depth Parameters.m base e)<e
      from hborrow,↓reduceDIte,CommonExchangeShapeProgram.reshape_charge,
      CommonBorrowedChunks.program_charge,bound,CommonArbitraryCost.bound,↓reduceIte]
    exact borrowed_charge_le q cutoff _ _ _ _ _ _
  · simp only [program,show ¬borrowedWidth radix Parameters.W (depth Parameters.m base e)<e
      from hborrow,↓reduceDIte,CommonExchangeShapeProgram.reshape_charge,
      CommonChunkExchange.program_charge,bound,CommonArbitraryCost.bound,↓reduceIte,base_fields]
    exact le_rfl

attribute [local irreducible] program

theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P e G S source buffer limit : ℕ) (hb : 0<base)
    (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q)
    (hs : source+count q (Volume P (radix^e) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P e G S hb hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : bound q base cutoff P e G S≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader base cutoff P e G S source buffer limit hb hG hS
      hresident hfit hstartup hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ y : Fin (Volume P (radix^e) G (S*q.w)),
      readBit q result.1.disk source y.val=
        readBit q s.disk source (swap P (radix^e) G (S*q.w) y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (Volume P (radix^e) G (S*q.w))≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    result.2≤bound q base cutoff P e G S ∧ Fintype.card (ResidentIndex q)≤q.M := by
  have hc := charge_le q reader base cutoff P e G S source buffer limit hb hG hS
    hresident hfit hstartup hs hw hl
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ := CommonFinitePermutation.complete q
    (program q reader base cutoff P e G S source buffer limit hb hG hS
      hresident hfit hstartup hs hw hl) s (hc.trans hsize) hpc
  exact ⟨hout,hframe,hhalt,hcost.trans hc,hram⟩

theorem complete_improved (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P e G S source buffer limit : ℕ) (hb : 0<base)
    (hP : 0<P) (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : CommonRecursiveExchange.Pruned.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : CommonRecursiveExchange.Pruned.buckets base*width q≤cutoff+width q)
    (hcut : Parameters.W*width q≤cutoff)
    (hs : source+count q (Volume P (radix^e) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P e G S hb hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : bound q base cutoff P e G S≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader base cutoff P e G S source buffer limit hb hG hS
      hresident hfit hstartup hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ y : Fin (Volume P (radix^e) G (S*q.w)),
      readBit q result.1.disk source y.val=
        readBit q s.disk source (swap P (radix^e) G (S*q.w) y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (Volume P (radix^e) G (S*q.w))≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    (result.2 : ℝ)≤CommonArbitraryCost.finalConstant 24 27 (6*(2*radix+6))*
      PhysicalArbitraryBound.scan (width q) (Volume P (radix^e) G (S*q.w))*
        (1+((e : ℝ)/base)^(1-(Parameters.epsilon : ℝ))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ := complete q reader base cutoff P e G S
    source buffer limit hb hG hS hresident hfit hstartup hs hw hl s hsize hpc
  refine ⟨hout,hframe,hhalt,?_,hram⟩
  exact (Nat.cast_le.mpr hcost).trans
    (CommonArbitraryCost.bound_improved base cutoff (width q) P e G (S*q.w)
      24 27 (6*(2*radix+6)) (width_pos q) hb hP hcut)

end
end CodedSorting.CommonArbitraryMachine
end MachineBound
