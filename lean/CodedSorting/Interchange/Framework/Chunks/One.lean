import CodedSorting.Interchange.Framework.Pruned.RecursionComplete
import CodedSorting.Interchange.Framework.Memory.PhysicalBorrowedChunks
import CodedSorting.Interchange.Framework.Memory.ExchangeShapeProgram

section Workspace
/-! Public numerical preconditions and shared scratch space for unequal
field chunks. Sibling calls reuse the same workspace interval. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonChunkExchange
open CommonSortingNormalization CommonPermutationPairs
open CommonRecursiveExchange PhysicalFieldPacking PhysicalRecursiveExchange
open PhysicalChunkExchange RecursiveExchange Circuit BinaryPadding
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m

abbrev Call := ArbitraryRecursive.Call

structure Conditions (q : Configuration) (cutoff : ℕ) (cs : List Call) (P : ℕ) : Prop where
  resident : cutoff≤CommonExchangeLeaf.bankBits q
  divisible : ∀ c∈cs,Parameters.W^c.depth ∣ P
  buffers : ∀ c∈cs,Pruned.buckets c.baseWidth*q.block≤CommonExchangeLeaf.bankWords q
  startup : ∀ c∈cs,Pruned.buckets c.baseWidth*width q≤cutoff+width q

def Conditions.tail (q : Configuration) (cutoff : ℕ) (c : Call) (cs : List Call) (P : ℕ)
    (h : Conditions q cutoff (c::cs) P) :
    Conditions q cutoff cs (P*radix^c.width) where
  resident := h.resident
  divisible := fun d hd => dvd_mul_of_dvd_left (h.divisible d (by simp [hd])) _
  buffers := fun d hd => h.buffers d (by simp [hd])
  startup := fun d hd => h.startup d (by simp [hd])

def oneSpace (q : Configuration) (cutoff : ℕ) (c : Call) (P G S : ℕ)
    (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : Pruned.buckets c.baseWidth*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : Pruned.buckets c.baseWidth*width q≤cutoff+width q) : ℕ :=
  Pruned.space q (Pruned.canonicalFitted q cutoff c.baseWidth c.depth
    (P/Parameters.W^c.depth) G S hG hS hresident hfit hstartup).val

def space (q : Configuration) (cutoff : ℕ) :
    (cs : List Call) → (P G S : ℕ) → 0<G → 0<S → Conditions q cutoff cs P → ℕ
  | [],_,_,_,_,_,_ => 0
  | c::cs,P,G,S,hG,hS,h =>
      oneSpace q cutoff c P (fieldCount cs*G) (fieldCount cs*S)
        (Nat.mul_pos (fieldCount_pos cs) hG) (Nat.mul_pos (fieldCount_pos cs) hS)
        h.resident (h.buffers c (by simp)) (h.startup c (by simp))+
      space q cutoff cs (P*radix^c.width) (G*radix^c.width) S
        (Nat.mul_pos hG (pow_pos radix_prime.pos _)) hS (h.tail q cutoff c cs P)

theorem one_volume (c : Call) (P G S : ℕ) (hdiv : Parameters.W^c.depth ∣ P) :
    ScalarVolume (c.baseWidth*Parameters.m^c.depth)
      ((P/Parameters.W^c.depth)*Parameters.W^c.depth) G S=
      Volume P (radix^c.width) G S := by
  rw [Nat.div_mul_cancel hdiv]
  rfl

theorem head_workspace (q : Configuration) (cutoff : ℕ) (c : Call) (cs : List Call)
    (P G S buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (h : Conditions q cutoff (c::cs) P)
    (hw : buffer+space q cutoff (c::cs) P G S hG hS h≤limit) :
    buffer+oneSpace q cutoff c P (fieldCount cs*G) (fieldCount cs*S)
      (Nat.mul_pos (fieldCount_pos cs) hG) (Nat.mul_pos (fieldCount_pos cs) hS)
      h.resident (h.buffers c (by simp)) (h.startup c (by simp))≤limit := by
  dsimp only [space] at hw
  omega

theorem tail_workspace (q : Configuration) (cutoff : ℕ) (c : Call) (cs : List Call)
    (P G S buffer limit : ℕ) (hG : 0<G) (hS : 0<S)
    (h : Conditions q cutoff (c::cs) P)
    (hw : buffer+space q cutoff (c::cs) P G S hG hS h≤limit) :
    buffer+space q cutoff cs (P*radix^c.width) (G*radix^c.width) S
      (Nat.mul_pos hG (pow_pos radix_prime.pos _)) hS (h.tail q cutoff c cs P)≤limit := by
  dsimp only [space] at hw
  omega

end
end CodedSorting.CommonChunkExchange
end Workspace

section One
/-! One unequal-width call compiled to the same finite disk and source file.
The prefix divisibility changes only its numerical view; no rearrangement
instruction is inserted for the view conversion. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.CommonChunkExchange
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonRecursiveExchange PhysicalFieldPacking PhysicalRecursiveExchange
open CommonChunkLayout RecursiveExchange Circuit
noncomputable section
attribute [local irreducible] Parameters.W Parameters.m Pruned.canonicalProgram

def oneProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (c : Call) (P G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : Pruned.buckets c.baseWidth*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : Pruned.buckets c.baseWidth*width q≤cutoff+width q)
    (hdiv : Parameters.W^c.depth ∣ P)
    (hs : source+count q (Volume P (radix^c.width) G (S*q.w))≤buffer)
    (hw : buffer+oneSpace q cutoff c P G S hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) :
    CommonFinitePermutation.Program q (Volume P (radix^c.width) G (S*q.w))
      source buffer limit (swap P (radix^c.width) G (S*q.w)) := by
  have hp : P/Parameters.W^c.depth*Parameters.W^c.depth=P := Nat.div_mul_cancel hdiv
  have hvol := one_volume c P G (S*q.w) hdiv
  have hsource : source+count q (ScalarVolume (c.baseWidth*Parameters.m^c.depth)
      ((P/Parameters.W^c.depth)*Parameters.W^c.depth) G (S*q.w))≤buffer := by
    simpa only [hvol] using hs
  let p := Pruned.canonicalProgram q reader cutoff c.baseWidth c.depth
    (P/Parameters.W^c.depth) G S source buffer limit hG hS
    hresident hfit hstartup hsource hw hl
  have hc : p.charge≤Pruned.costBound (width q) cutoff c.depth
      (Volume P (radix^c.width) G (S*q.w)) :=
    (Pruned.canonical_charge_le q reader cutoff c.baseWidth c.depth
      (P/Parameters.W^c.depth) G S source buffer limit hG hS
      hresident hfit hstartup hsource hw hl).trans_eq
      (congrArg (fun V => Pruned.costBound (width q) cutoff c.depth V) hvol)
  refine {
    instructions := p.instructions
    charge := Pruned.costBound (width q) cutoff c.depth (Volume P (radix^c.width) G (S*q.w))
    correct := ?_
    frame := ?_
    safe := p.safe
    cost_le := p.cost_le.trans hc
    length_le := p.length_le.trans hc }
  · intro s
    have hn := scalar_correct_numeric (c.baseWidth*Parameters.m^c.depth)
      ((P/Parameters.W^c.depth)*Parameters.W^c.depth) G (S*q.w)
      (readBit q s.disk source)
      (readBit q (executeRaw q p.instructions s).1.disk source) (p.correct s)
    exact numeric_correct_cast _ _ _ _ P (radix^c.width) G (S*q.w)
      hp rfl rfl rfl _ _ hn
  · intro s a hout hwork
    exact p.frame s a (by simpa only [hvol] using hout) hwork

@[simp] theorem oneProgram_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (c : Call) (P G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q)
    (hfit : Pruned.buckets c.baseWidth*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : Pruned.buckets c.baseWidth*width q≤cutoff+width q)
    (hdiv : Parameters.W^c.depth ∣ P)
    (hs : source+count q (Volume P (radix^c.width) G (S*q.w))≤buffer)
    (hw : buffer+oneSpace q cutoff c P G S hG hS hresident hfit hstartup≤limit)
    (hl : limit≤q.N^q.exponent) :
    (oneProgram q reader cutoff c P G S source buffer limit hG hS
      hresident hfit hstartup hdiv hs hw hl).charge=
      Pruned.costBound (width q) cutoff c.depth (Volume P (radix^c.width) G (S*q.w)) := rfl

end
end CodedSorting.CommonChunkExchange
end One
