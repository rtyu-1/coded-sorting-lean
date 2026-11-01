import CodedSorting.Interchange.Fields.Machine

/-! Correctness, completion and the improved bound for the same generated
finite-machine exchange, for every prime-radix field width.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.ArbitraryMachine
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonChunkLayout CommonFinitePermutation ArbitraryConditions
open ExchangeSpecialization ArbitrarySchedule ArbitraryCalls
noncomputable section
attribute [local irreducible] ControlledNormalization.runLogical

theorem borrowed_charge_le (q : Configuration) (cutoff : ℕ)
    (cs : List ArbitraryCalls.Call) (P ρ P' G S : ℕ) :
    BorrowedChunks.bound q cutoff cs P ρ P' G S≤
      ArbitraryCostRate.borrowedBound cutoff (width q) cs P ρ P' G (S*q.w)
        24 27 (6*(2*radix+6)) := by
  unfold BorrowedChunks.bound ArbitraryCostRate.borrowedBound
    ArbitraryCostRate.overheadBound
  have hV := CommonResidentBase.count_le_floor q
    (Volume P (radix^ρ*fieldCount cs) G (S*q.w))
  have hV' := CommonResidentBase.count_le_floor q
    (Volume P' (fieldCount cs) G (S*q.w))
  have h1 := Nat.mul_le_mul_left (24+6*ρ*(2*radix+6)) hV
  have h2 := Nat.mul_le_mul_left 27 hV'
  dsimp only [CommonPermutationPairs.width] at *
  nlinarith only [h1,h2]

theorem charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P e G S source buffer limit : ℕ) (hb : 0<base)
    (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q≤cutoff+width q)
    (hs : source+count q (Volume P (radix^e) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P e G S hb hG hS hresident hblock hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) :
    (program q reader base cutoff P e G S source buffer limit hb hG hS
      hresident hblock hfit hstartup hs hw hl).charge≤bound q base cutoff P e G S := by
  let k := depth ambientDimension base e
  let ρ := borrowedWidth radix streamCount k
  by_cases hborrow : ρ<e
  · simp only [program,show borrowedWidth radix streamCount (depth ambientDimension base e)<e
      from hborrow,↓reduceDIte,CommonExchangeShapeProgram.reshape_charge,
      bound,ArbitraryCostRate.bound,↓reduceIte]
    exact (BorrowedChunks.program_charge_le ..).trans (BorrowedChunks.bound_le_scan ..)
  · simp only [program,show ¬borrowedWidth radix streamCount (depth ambientDimension base e)<e
      from hborrow,↓reduceDIte,CommonExchangeShapeProgram.reshape_charge,
      bound,ArbitraryCostRate.bound,↓reduceIte]
    have hc := ChunkExchange.program_charge_le q reader cutoff (ArbitraryCalls.baseCalls base e)
      P G S source buffer limit hG hS
      (baseConditions q cutoff base e P hb hresident hblock hfit hstartup)
      (by simpa only [base_fields] using hs)
      (by simpa only [space,show ¬borrowedWidth radix streamCount (depth ambientDimension base e)<e
        from hborrow,if_neg] using hw) hl
    simpa only [base_fields] using hc

attribute [local irreducible] program

theorem complete (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P e G S source buffer limit : ℕ) (hb : 0<base)
    (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q≤cutoff+width q)
    (hs : source+count q (Volume P (radix^e) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P e G S hb hG hS hresident hblock hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : bound q base cutoff P e G S≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader base cutoff P e G S source buffer limit hb hG hS
      hresident hblock hfit hstartup hs hw hl
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
    hresident hblock hfit hstartup hs hw hl
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ := CommonFinitePermutation.complete q
    (program q reader base cutoff P e G S source buffer limit hb hG hS
      hresident hblock hfit hstartup hs hw hl) s (hc.trans hsize) hpc
  exact ⟨hout,hframe,hhalt,hcost.trans hc,hram⟩

theorem complete_improved (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P e G S source buffer limit : ℕ) (hb : 0<base)
    (hP : 0<P) (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q≤cutoff+width q)
    (hcut : streamCount*width q≤cutoff)
    (hs : source+count q (Volume P (radix^e) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P e G S hb hG hS hresident hblock hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) (s : Machine q)
    (hsize : bound q base cutoff P e G S≤q.N^q.exponent) (hpc : pc q s.ram=0) :
    let p := program q reader base cutoff P e G S source buffer limit hb hG hS
      hresident hblock hfit hstartup hs hw hl
    let result := ControlledNormalization.runLogical (policy q p.instructions) p.instructions.length s
    (∀ y : Fin (Volume P (radix^e) G (S*q.w)),
      readBit q result.1.disk source y.val=
        readBit q s.disk source (swap P (radix^e) G (S*q.w) y).val) ∧
    (∀ a : Fin (q.N^q.exponent),
      (a.val<source ∨ source+count q (Volume P (radix^e) G (S*q.w))≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → result.1.disk a=s.disk a) ∧
    policy q p.instructions result.1.ram=none ∧
    (result.2 : ℝ)≤ArbitraryCostRate.finalConstant 24 27 (6*(2*radix+6))*
      ArbitraryCost.scan (width q) (Volume P (radix^e) G (S*q.w))*
        (1+((e : ℝ)/base)^(1-(Construction.epsilon : ℝ))) ∧
    Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨hout,hframe,hhalt,hcost,hram⟩ := complete q reader base cutoff P e G S
    source buffer limit hb hG hS hresident hblock hfit hstartup hs hw hl s hsize hpc
  refine ⟨hout,hframe,hhalt,?_,hram⟩
  exact (Nat.cast_le.mpr hcost).trans
    (ArbitraryCostRate.bound_improved base cutoff (width q) P e G (S*q.w)
      24 27 (6*(2*radix+6)) (width_pos q) hb hP hcut)

end
end CodedSorting.Construction.ArbitraryMachine
