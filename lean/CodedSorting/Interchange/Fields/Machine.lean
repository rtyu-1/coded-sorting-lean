import CodedSorting.Interchange.Chunks.BorrowedChunks

section Conditions
/-! Discharge every chunk's numerical memory and prefix obligations from
one base-width choice. These are arithmetic conditions, not execution oracles. -/
set_option autoImplicit false
namespace CodedSorting.Construction.ArbitraryConditions
open CommonSortingNormalization CommonPermutationPairs
open ChunkExchange ArbitraryCalls ExchangeSpecialization
noncomputable section

theorem buckets_mono {a b : ℕ} (h : a≤b) : RecursiveWorkspaceBudget.buckets a≤RecursiveWorkspaceBudget.buckets b := by
  have hp := Nat.pow_le_pow_right radix_prime.pos h
  exact Nat.pow_le_pow_left hp 2

def baseConditions (q : Configuration) (cutoff base e P : ℕ) (hb : 0<base)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q≤cutoff+width q) :
    Conditions q cutoff (ArbitraryCalls.baseCalls base e) P where
  resident := hresident
  block := hblock
  divisible := ArbitraryCalls.baseCalls_fit P base e
  buffers := fun c hc => (Nat.mul_le_mul_right q.block
    (buckets_mono (baseCalls_base base e hb c hc))).trans hfit
  startup := fun c hc => (Nat.mul_le_mul_right (width q)
    (buckets_mono (baseCalls_base base e hb c hc))).trans hstartup

def paddedConditions (q : Configuration) (cutoff base k e P : ℕ) (hb : 0<base)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q≤cutoff+width q) :
    Conditions q cutoff (ArbitraryCalls.calls base k e)
      (ArbitraryCalls.paddedRows P k) where
  resident := hresident
  block := hblock
  divisible := ArbitraryCalls.calls_fit P base k e
  buffers := fun c hc => (Nat.mul_le_mul_right q.block
    (buckets_mono (ArbitraryCalls.calls_base base k e hb c hc))).trans hfit
  startup := fun c hc => (Nat.mul_le_mul_right (width q)
    (buckets_mono (ArbitraryCalls.calls_base base k e hb c hc))).trans hstartup

end
end CodedSorting.Construction.ArbitraryConditions
end Conditions

section Machine
/-! A generated finite-machine exchange for every prime-radix field width.
The long-field branch executes borrowing, prefix padding, actual recursive
chunks, erasure, and restoration. The short-field branch executes actual
depth-zero chunks. All conclusions concern the generated instructions. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.ArbitraryMachine
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonChunkLayout CommonFinitePermutation ArbitraryConditions
open ExchangeSpecialization ArbitrarySchedule ArbitraryCalls
noncomputable section

def space (q : Configuration) (base cutoff P e G S : ℕ) (hb : 0<base)
    (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q≤cutoff+width q) : ℕ :=
  let k := depth ambientDimension base e
  let ρ := borrowedWidth radix streamCount k
  if ρ<e then
    let cs := ArbitraryCalls.calls base k (e-ρ)
    let P' := ArbitraryCalls.paddedRows (P*((radix^ρ)*(radix^ρ))) k
    BorrowedChunks.space q cutoff cs P ρ P' G S hG hS
      (paddedConditions q cutoff base k (e-ρ) (P*((radix^ρ)*(radix^ρ)))
        hb hresident hblock hfit hstartup)
  else
    ChunkExchange.space q cutoff (ArbitraryCalls.baseCalls base e) P G S hG hS
      (baseConditions q cutoff base e P hb hresident hblock hfit hstartup)

theorem borrowed_fields (base e k ρ : ℕ) (hρ : ρ≤e) :
    radix^ρ*fieldCount (ArbitraryCalls.calls base k (e-ρ))=radix^e := by
  rw [fieldCount_width,ArbitraryCalls.calls_width,←pow_add,Nat.add_sub_of_le hρ]

theorem base_fields (base e : ℕ) :
    fieldCount (ArbitraryCalls.baseCalls base e)=radix^e := by
  rw [fieldCount_width,ArbitraryCalls.baseCalls_width]

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (base cutoff P e G S source buffer limit : ℕ) (hb : 0<base)
    (hG : 0<G) (hS : 0<S) (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : RecursiveWorkspaceBudget.buckets base*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : RecursiveWorkspaceBudget.buckets base*width q≤cutoff+width q)
    (hs : source+count q (Volume P (radix^e) G (S*q.w))≤buffer)
    (hw : buffer+space q base cutoff P e G S hb hG hS hresident hblock hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (radix^e) G (S*q.w)) source buffer limit
      (swap P (radix^e) G (S*q.w)) := by
  let k := depth ambientDimension base e
  let ρ := borrowedWidth radix streamCount k
  by_cases hborrow : ρ<e
  · let cs := ArbitraryCalls.calls base k (e-ρ)
    let P' := ArbitraryCalls.paddedRows (P*((radix^ρ)*(radix^ρ))) k
    let hc := paddedConditions q cutoff base k (e-ρ) (P*((radix^ρ)*(radix^ρ)))
      hb hresident hblock hfit hstartup
    have hfields := borrowed_fields base e k ρ hborrow.le
    have hs' : source+count q (Volume P (radix^ρ*fieldCount cs) G (S*q.w))≤buffer := by
      simpa only [cs,hfields] using hs
    have hw' : buffer+BorrowedChunks.space q cutoff cs P ρ P' G S hG hS hc≤limit := by
      simpa only [space,show borrowedWidth radix streamCount (depth ambientDimension base e)<e
        from hborrow,if_pos] using hw
    exact CommonExchangeShapeProgram.reshape q rfl hfields rfl rfl
      (BorrowedChunks.program q reader cutoff cs P ρ P' G S source buffer limit
        hG hS (ArbitraryCalls.original_rows_le_padded _ _) hc hs' hw' hl)
  · let hc := baseConditions q cutoff base e P hb hresident hblock hfit hstartup
    have hfields := base_fields base e
    have hs' : source+count q (Volume P (fieldCount (ArbitraryCalls.baseCalls base e)) G (S*q.w))≤buffer := by
      simpa only [hfields] using hs
    have hw' : buffer+ChunkExchange.space q cutoff (ArbitraryCalls.baseCalls base e)
        P G S hG hS hc≤limit := by
      simpa only [space,show ¬borrowedWidth radix streamCount (depth ambientDimension base e)<e
        from hborrow,if_neg] using hw
    exact CommonExchangeShapeProgram.reshape q rfl hfields rfl rfl
      (ChunkExchange.program q reader cutoff (ArbitraryCalls.baseCalls base e)
        P G S source buffer limit hG hS hc hs' hw' hl)

def bound (q : Configuration) (base cutoff P e G S : ℕ) : ℕ :=
  ArbitraryCostRate.bound base cutoff (width q) P e G (S*q.w) 24 27 (6*(2*radix+6))

end
end CodedSorting.Construction.ArbitraryMachine
end Machine
