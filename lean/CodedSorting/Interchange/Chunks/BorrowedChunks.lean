import CodedSorting.Interchange.Fields.LogRate
import CodedSorting.Interchange.Recursion.Endpoint
import CodedSorting.Interchange.Framework.BorrowedMemory.Machine

section ChunkCompose
/-! Sequential machine composition for two physical field chunks.  The second
instruction list runs on the first list's actual resulting machine. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.ChunkCompose
open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonLeafProgram (Machine)
open CommonChunkLayout CommonFinitePermutation
noncomputable section

theorem head_word_volume (P Q R G S w : ℕ) :
    Volume P Q (R*G) ((R*S)*w)=Volume P (Q*R) G (S*w) := by
  unfold Volume BaseExchangeProgram.Volume
  ring

theorem tail_word_volume (P Q R G S w : ℕ) :
    Volume (P*Q) R (G*Q) (S*w)=Volume P (Q*R) G (S*w) := by
  unfold Volume BaseExchangeProgram.Volume
  ring

def emptyProgram (q : Configuration) (P G S source buffer limit : ℕ) :
    Program q (Volume P 1 G (S*q.w)) source buffer limit
      (swap P 1 G (S*q.w)) where
  instructions := []
  charge := 0
  correct := by intro s y; simp only [swap_one]; rfl
  frame := fun _ _ _ _ => rfl
  safe := by simp
  cost_le := Nat.le_refl 0
  length_le := Nat.le_refl 0

def combine (q : Configuration) (P Q R G S source buffer limit : ℕ)
    (p₁ : Program q (Volume P Q (R*G) ((R*S)*q.w)) source buffer limit
      (swap P Q (R*G) ((R*S)*q.w)))
    (p₂ : Program q (Volume (P*Q) R (G*Q) (S*q.w)) source buffer limit
      (swap (P*Q) R (G*Q) (S*q.w))) :
    Program q (Volume P (Q*R) G (S*q.w)) source buffer limit
      (swap P (Q*R) G (S*q.w)) where
  instructions := p₁.instructions++p₂.instructions
  charge := p₁.charge+p₂.charge
  correct := by
    intro s y
    rw [raw_append]
    exact head_tail_correct_words P Q R G S q.w
      (readBit q s.disk source)
      (readBit q (executeRaw q p₁.instructions s).1.disk source)
      (readBit q (executeRaw q p₂.instructions
        (executeRaw q p₁.instructions s).1).1.disk source)
      (p₁.correct s) (p₂.correct _) y
  frame := by
    intro s a hs hw
    have hs₁ : a.val<source ∨
        source+count q (Volume P Q (R*G) ((R*S)*q.w))≤a.val := by
      simpa only [head_word_volume] using hs
    have hs₂ : a.val<source ∨
        source+count q (Volume (P*Q) R (G*Q) (S*q.w))≤a.val := by
      simpa only [tail_word_volume] using hs
    rw [raw_append,p₂.frame _ a hs₂ hw,p₁.frame s a hs₁ hw]
  safe := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact p₁.safe i hi
    · exact p₂.safe i hi
  cost_le := by
    rw [cost_append]
    exact Nat.add_le_add p₁.cost_le p₂.cost_le
  length_le := by
    rw [List.length_append]
    exact Nat.add_le_add p₁.length_le p₂.length_le

@[simp] theorem combine_charge (q : Configuration) (P Q R G S source buffer limit : ℕ)
    (p₁ : Program q (Volume P Q (R*G) ((R*S)*q.w)) source buffer limit
      (swap P Q (R*G) ((R*S)*q.w)))
    (p₂ : Program q (Volume (P*Q) R (G*Q) (S*q.w)) source buffer limit
      (swap (P*Q) R (G*Q) (S*q.w))) :
    (combine q P Q R G S source buffer limit p₁ p₂).charge=p₁.charge+p₂.charge := rfl

end
end CodedSorting.Construction.ChunkCompose
end ChunkCompose

section ChunkOne
/-! Relocatable actual Construction chunks. A positive chunk runs the existing Construction
recursive builder at the caller's source and shared scratch addresses.
A zero-width chunk is the identity, including a zero remainder in a list.
The charge field is the proved numerical majorant; recharging changes no
instruction and does not assert that the majorant is the exact I/O cost. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.ChunkExchange

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonChunkLayout CommonFinitePermutation
open ExchangeSpecialization RecursiveWorkspaceBudget
open ArbitraryCalls

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs MachineNetworkActualEdges.localCoefficient

local notation "coefficient" =>
  (24*streamCount+36+MachineNetworkActualEdges.localCoefficient)

structure Conditions (q : Configuration) (cutoff : Nat)
    (cs : List ArbitraryCalls.Call) (P : Nat) : Prop where
  resident : cutoff ≤ CommonExchangeLeaf.bankBits q
  block : width q ≤ cutoff
  divisible : ∀ c ∈ cs, streamCount^c.depth ∣ P
  buffers : ∀ c ∈ cs, buckets c.baseWidth*q.block ≤ CommonExchangeLeaf.bankWords q
  startup : ∀ c ∈ cs, buckets c.baseWidth*width q ≤ cutoff+width q

def Conditions.tail (q : Configuration) (cutoff : Nat)
    (c : ArbitraryCalls.Call) (cs : List ArbitraryCalls.Call) (P : Nat)
    (h : Conditions q cutoff (c::cs) P) :
    Conditions q cutoff cs (P*radix^c.width) where
  resident := h.resident
  block := h.block
  divisible := fun d hd => dvd_mul_of_dvd_left (h.divisible d (by simp [hd])) _
  buffers := fun d hd => h.buffers d (by simp [hd])
  startup := fun d hd => h.startup d (by simp [hd])

/-- One shared linear reserve is sufficient for every sequential chunk. -/
def space (q : Configuration) (cutoff : Nat) (cs : List ArbitraryCalls.Call)
    (P G S : Nat) (_hG : 0<G) (_hS : 0<S) (_h : Conditions q cutoff cs P) : Nat :=
  RecursiveWorkspaceProgram.linearReserve q (Volume P (fieldCount cs) G (S*q.w))

def oneCall (q : Configuration) (c : ArbitraryCalls.Call)
    (P G S source buffer limit : Nat) : ExchangeInterface.Call :=
  ⟨c.width,P,G,S*q.w,source,buffer,limit⟩

theorem one_shape (q : Configuration) (c : ArbitraryCalls.Call)
    (P G S source buffer limit : Nat) (hb : 0<c.baseWidth)
    (hG : 0<G) (hS : 0<S) (hdiv : streamCount^c.depth ∣ P) :
    RecursiveCallShape.ShapeDepth q c.depth (oneCall q c P G S source buffer limit) := by
  refine ⟨dvd_mul_left _ _,hdiv,?_,hG,⟨S,hS,rfl⟩⟩
  exact Nat.mul_pos hb (pow_pos (by rw [ambientDimension_eq]; omega) _)

private def generatedOne (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : Nat) (c : ArbitraryCalls.Call) (P G S source buffer limit : Nat)
    (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : buckets c.baseWidth*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : buckets c.baseWidth*width q≤cutoff+width q)
    (hdiv : streamCount^c.depth ∣ P)
    (hs : source+count q (Volume P (radix^c.width) G (S*q.w))≤buffer)
    (hw : buffer+RecursiveWorkspaceProgram.linearReserve q
      (Volume P (radix^c.width) G (S*q.w))≤limit)
    (hl : limit≤q.N^q.exponent) :
    {p : Program q (Volume P (radix^c.width) G (S*q.w)) source buffer limit
      (swap P (radix^c.width) G (S*q.w)) //
      p.charge≤ExchangeInterface.costBound coefficient (width q) cutoff c.depth
        (Volume P (radix^c.width) G (S*q.w))} := by
  by_cases hz : c.baseWidth=0
  · have he : radix^c.width=1 := by simp only [ArbitraryCalls.Call.width,hz,zero_mul,pow_zero]
    let p := ChunkCompose.emptyProgram q P G S source buffer limit
    rw [he]
    exact ⟨p,Nat.zero_le _⟩
  · have hb : 0<c.baseWidth := Nat.pos_of_ne_zero hz
    let call := oneCall q c P G S source buffer limit
    let hp : LeafParameters q cutoff c.baseWidth := ⟨hresident,hfit,hstartup⟩
    have hshape := one_shape q c P G S source buffer limit hb hG hS hdiv
    have hwidth : call.fieldWidth=ambientDimension^c.depth*c.baseWidth :=
      Nat.mul_comm _ _
    let p := RecursiveWorkspaceProgram.program q reader cutoff c.baseWidth c.depth
      call hp hblock hshape hwidth hs hw hl
    exact ⟨p,RecursiveCostProgram.program_charge_le q reader cutoff c.baseWidth c.depth
      call hp hblock hshape hwidth hs hw hl⟩

/-- The exact same actual instructions, with a proved uniform charge bound. -/
def oneProgram (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : Nat) (c : ArbitraryCalls.Call) (P G S source buffer limit : Nat)
    (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : buckets c.baseWidth*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : buckets c.baseWidth*width q≤cutoff+width q)
    (hdiv : streamCount^c.depth ∣ P)
    (hs : source+count q (Volume P (radix^c.width) G (S*q.w))≤buffer)
    (hw : buffer+RecursiveWorkspaceProgram.linearReserve q
      (Volume P (radix^c.width) G (S*q.w))≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (radix^c.width) G (S*q.w)) source buffer limit
      (swap P (radix^c.width) G (S*q.w)) :=
  let t := generatedOne q reader cutoff c P G S source buffer limit hG hS
    hresident hblock hfit hstartup hdiv hs hw hl
  { t.val with
    charge := ExchangeInterface.costBound coefficient (width q) cutoff c.depth
      (Volume P (radix^c.width) G (S*q.w))
    cost_le := t.val.cost_le.trans t.property
    length_le := t.val.length_le.trans t.property }

theorem oneProgram_charge (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : Nat) (c : ArbitraryCalls.Call) (P G S source buffer limit : Nat)
    (hG : 0<G) (hS : 0<S)
    (hresident : cutoff≤CommonExchangeLeaf.bankBits q) (hblock : width q≤cutoff)
    (hfit : buckets c.baseWidth*q.block≤CommonExchangeLeaf.bankWords q)
    (hstartup : buckets c.baseWidth*width q≤cutoff+width q)
    (hdiv : streamCount^c.depth ∣ P)
    (hs : source+count q (Volume P (radix^c.width) G (S*q.w))≤buffer)
    (hw : buffer+RecursiveWorkspaceProgram.linearReserve q
      (Volume P (radix^c.width) G (S*q.w))≤limit)
    (hl : limit≤q.N^q.exponent) :
    (oneProgram q reader cutoff c P G S source buffer limit hG hS
      hresident hblock hfit hstartup hdiv hs hw hl).charge=
      ExchangeInterface.costBound coefficient (width q) cutoff c.depth
        (Volume P (radix^c.width) G (S*q.w)) := rfl

end
end CodedSorting.Construction.ChunkExchange
end ChunkOne

section ChunkExchange
/-! Sequential actual Construction chunks share one linear scratch interval. The
generic head/tail layout lemma changes only the coordinate interpretation;
the generated instruction list is the concatenation of the actual chunks. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace CodedSorting.Construction.ChunkExchange

open CommonSortingNormalization CommonStaticSchedule CommonPermutationPairs
open CommonChunkLayout CommonFinitePermutation
open ExchangeSpecialization ArbitraryCalls

noncomputable section

attribute [local irreducible] TensorFrameNetwork.program
  MachineNetworkAdapter.physicalInputs MachineNetworkActualEdges.localCoefficient

def generated (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : Nat)
    (cs : List ArbitraryCalls.Call) (P G S source buffer limit : Nat)
    (hG : 0<G) (hS : 0<S) (h : Conditions q cutoff cs P)
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P G S hG hS h≤limit)
    (hl : limit≤q.N^q.exponent) :
    {p : Program q (Volume P (fieldCount cs) G (S*q.w)) source buffer limit
      (swap P (fieldCount cs) G (S*q.w)) //
      p.charge=ArbitraryCost.totalBound cutoff (width q) cs
        (Volume P (fieldCount cs) G (S*q.w))} := by
  induction cs generalizing P G S with
  | nil => exact ⟨ChunkCompose.emptyProgram q P G S source buffer limit,rfl⟩
  | cons c cs ih =>
    have hs₁ : source+count q
        (Volume P (radix^c.width) (fieldCount cs*G) ((fieldCount cs*S)*q.w))≤buffer := by
      simpa only [ChunkCompose.head_word_volume,fieldCount] using hs
    have hs₂ : source+count q
        (Volume (P*radix^c.width) (fieldCount cs) (G*radix^c.width) (S*q.w))≤buffer := by
      simpa only [ChunkCompose.tail_word_volume,fieldCount] using hs
    have hw₁ : buffer+RecursiveWorkspaceProgram.linearReserve q
        (Volume P (radix^c.width) (fieldCount cs*G) ((fieldCount cs*S)*q.w))≤limit := by
      simpa only [ChunkCompose.head_word_volume,space,fieldCount] using hw
    have hw₂ : buffer+space q cutoff cs (P*radix^c.width) (G*radix^c.width) S
        (Nat.mul_pos hG (pow_pos radix_prime.pos _)) hS (h.tail q cutoff c cs P)≤limit := by
      simpa only [ChunkCompose.tail_word_volume,space,fieldCount] using hw
    let p₁ := oneProgram q reader cutoff c P (fieldCount cs*G) (fieldCount cs*S)
      source buffer limit (Nat.mul_pos (fieldCount_pos cs) hG)
      (Nat.mul_pos (fieldCount_pos cs) hS) h.resident h.block (h.buffers c (by simp))
      (h.startup c (by simp)) (h.divisible c (by simp)) hs₁ hw₁ hl
    let p₂ := ih (P*radix^c.width) (G*radix^c.width) S
      (Nat.mul_pos hG (pow_pos radix_prime.pos _)) hS
      (h.tail q cutoff c cs P) hs₂ hw₂
    refine ⟨ChunkCompose.combine q P (radix^c.width) (fieldCount cs) G S
      source buffer limit p₁ p₂.val,?_⟩
    change p₁.charge+p₂.val.charge=_
    rw [p₂.property]
    dsimp only [p₁]
    rw [oneProgram_charge,ChunkCompose.head_word_volume,
      ChunkCompose.tail_word_volume]
    rfl

def program (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : Nat)
    (cs : List ArbitraryCalls.Call) (P G S source buffer limit : Nat)
    (hG : 0<G) (hS : 0<S) (h : Conditions q cutoff cs P)
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P G S hG hS h≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (fieldCount cs) G (S*q.w)) source buffer limit
      (swap P (fieldCount cs) G (S*q.w)) :=
  (generated q reader cutoff cs P G S source buffer limit hG hS h hs hw hl).val

theorem program_charge (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : Nat)
    (cs : List ArbitraryCalls.Call) (P G S source buffer limit : Nat)
    (hG : 0<G) (hS : 0<S) (h : Conditions q cutoff cs P)
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P G S hG hS h≤limit)
    (hl : limit≤q.N^q.exponent) :
    (program q reader cutoff cs P G S source buffer limit hG hS h hs hw hl).charge=
      ArbitraryCost.totalBound cutoff (width q) cs
        (Volume P (fieldCount cs) G (S*q.w)) :=
  (generated q reader cutoff cs P G S source buffer limit hG hS h hs hw hl).property

theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers) (cutoff : Nat)
    (cs : List ArbitraryCalls.Call) (P G S source buffer limit : Nat)
    (hG : 0<G) (hS : 0<S) (h : Conditions q cutoff cs P)
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P G S hG hS h≤limit)
    (hl : limit≤q.N^q.exponent) :
    (program q reader cutoff cs P G S source buffer limit hG hS h hs hw hl).charge≤
      ArbitraryCost.totalBound cutoff (width q) cs
        (Volume P (fieldCount cs) G (S*q.w)) :=
  (program_charge q reader cutoff cs P G S source buffer limit hG hS h hs hw hl).le

end
end CodedSorting.Construction.ChunkExchange
end ChunkExchange

section PaddedChunks
/-! Prefix padding surrounds the actual common-machine chunk program.  Both
padding scans and their scratch files are included in the program and charge;
no successful child execution or zero initial scratch contents are assumed. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.PaddedChunks
open CommonSortingNormalization CommonPermutationPairs CommonFinitePermutation
open CommonChunkLayout ArbitraryCalls ChunkExchange ExchangeSpecialization
noncomputable section


/-- Two padded files, followed by the shared chunk workspace. -/
def space (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryCalls.Call) (P' G S : ℕ)
    (hG : 0<G) (hS : 0<S) (hc : Conditions q cutoff cs P') : ℕ :=
  count q (Volume P' (fieldCount cs) G (S*q.w))+
  count q (Volume P' (fieldCount cs) G (S*q.w))+
  ChunkExchange.space q cutoff cs P' G S hG hS hc

/-- Every actual padding instruction is charged in addition to the chunk calls. -/
def bound (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryCalls.Call) (P P' G S : ℕ) : ℕ :=
  ArbitraryCost.totalBound cutoff (width q) cs
    (Volume P' (fieldCount cs) G (S*q.w))+
  12*count q (Volume P (fieldCount cs) G (S*q.w))+
  27*count q (Volume P' (fieldCount cs) G (S*q.w))

theorem bound_le_scan (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryCalls.Call)
    (P P' G S : ℕ) :
    bound q cutoff cs P P' G S≤
      ArbitraryCost.totalBound cutoff (width q) cs
        (Volume P' (fieldCount cs) G (S*q.w))+
      12*(Volume P (fieldCount cs) G (S*q.w)/width q+1)+
      27*(Volume P' (fieldCount cs) G (S*q.w)/width q+1) := by
  have hs := CommonResidentBase.count_le_floor q (Volume P (fieldCount cs) G (S*q.w))
  have hl := CommonResidentBase.count_le_floor q (Volume P' (fieldCount cs) G (S*q.w))
  unfold bound
  change _≤_+12*(_/(q.block*q.w)+1)+27*(_/(q.block*q.w)+1)
  omega

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List ArbitraryCalls.Call) (P P' G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S) (hp : P≤P') (hc : Conditions q cutoff cs P')
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P' G S hG hS hc≤limit)
    (hl : limit≤q.N^q.exponent) :
    Program q (Volume P (fieldCount cs) G (S*q.w)) source buffer limit
      (swap P (fieldCount cs) G (S*q.w)) := by
  let C := count q (Volume P' (fieldCount cs) G (S*q.w))
  have hchild : buffer+C+C+
      ChunkExchange.space q cutoff cs P' G S hG hS hc≤limit := by
    simpa only [space,C,Nat.add_assoc] using hw
  let child := ChunkExchange.program q reader cutoff cs P' G S
    (buffer+C) (buffer+C+C) limit hG hS hc (le_refl _) hchild hl
  exact CommonPaddedPermutation.prefixProgram q reader P P' (fieldCount cs)
    G (S*q.w) hp source buffer limit child hs (by omega) hl

theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List ArbitraryCalls.Call) (P P' G S source buffer limit : ℕ)
    (hG : 0<G) (hS : 0<S) (hp : P≤P') (hc : Conditions q cutoff cs P')
    (hs : source+count q (Volume P (fieldCount cs) G (S*q.w))≤buffer)
    (hw : buffer+space q cutoff cs P' G S hG hS hc≤limit)
    (hl : limit≤q.N^q.exponent) :
    (program q reader cutoff cs P P' G S source buffer limit hG hS hp hc hs hw hl).charge≤
      bound q cutoff cs P P' G S := by
  unfold program
  dsimp only [CommonPaddedPermutation.prefixProgram, CommonPaddedPermutation.wrap]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (ChunkExchange.program_charge_le q reader cutoff cs P' G S
      (buffer+count q (Volume P' (fieldCount cs) G (S*q.w)))
      (buffer+count q (Volume P' (fieldCount cs) G (S*q.w))+
        count q (Volume P' (fieldCount cs) G (S*q.w))) limit hG hS hc (le_refl _)
      (by simpa only [space, Nat.add_assoc] using hw) hl) _) _

end
end CodedSorting.Construction.PaddedChunks
end PaddedChunks

section BorrowedChunks
/-! The actual high-digit path: borrow, pad the resulting prefix, execute
all unequal-width chunks, remove padding, and restore the high digits.
Every phase consumes the actual preceding machine state, and every transfer
is included in the final charge. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.BorrowedChunks
open CommonSortingNormalization CommonPermutationPairs CommonFinitePermutation
open CommonChunkLayout ArbitraryCalls ChunkExchange ExchangeSpecialization
noncomputable section


theorem borrowed_volume (O H L G S : ℕ) :
    Volume O (H * L) G S = Volume (O * (H * H)) L G S :=
  (PhysicalBorrowLayout.original_volume O H L G S).trans
    (PhysicalBorrowLayout.borrowed_volume O H L G S).symm

/-- All phases reuse one scratch interval. The sum is a public sufficient
allocation for the borrow file and the padded chunk program. -/
def space (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryCalls.Call)
    (O ρ P' G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (hc : Conditions q cutoff cs P') : ℕ :=
  count q (Volume O ((ExchangeSpecialization.radix ^ ρ) * fieldCount cs) G (S * q.w)) +
    PaddedChunks.space q cutoff cs P' G S hG hS hc

def bound (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryCalls.Call) (O ρ P' G S : ℕ) : ℕ :=
  ArbitraryCost.totalBound cutoff (width q) cs
    (Volume P' (fieldCount cs) G (S * q.w)) +
  (24 + 6 * ρ * (2 * ExchangeSpecialization.radix + 6)) *
    count q (Volume O ((ExchangeSpecialization.radix ^ ρ) * fieldCount cs) G (S * q.w)) +
  27 * count q (Volume P' (fieldCount cs) G (S * q.w))

def program (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List ArbitraryCalls.Call) (O ρ P' G S source buffer limit : ℕ)
    (hG : 0 < G) (hS : 0 < S)
    (hp : O * ((ExchangeSpecialization.radix ^ ρ) * (ExchangeSpecialization.radix ^ ρ)) ≤ P')
    (hc : Conditions q cutoff cs P')
    (hs : source + count q
      (Volume O ((ExchangeSpecialization.radix ^ ρ) * fieldCount cs) G (S * q.w)) ≤ buffer)
    (hw : buffer + space q cutoff cs O ρ P' G S hG hS hc ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    Program q (Volume O ((ExchangeSpecialization.radix ^ ρ) * fieldCount cs) G (S * q.w))
      source buffer limit (swap O ((ExchangeSpecialization.radix ^ ρ) * fieldCount cs) G (S * q.w)) := by
  let H := ExchangeSpecialization.radix ^ ρ
  have hsinner : source + count q (Volume (O * (H * H)) (fieldCount cs) G (S * q.w)) ≤ buffer := by
    simpa only [← borrowed_volume] using hs
  have hwpadded : buffer + PaddedChunks.space q cutoff cs P' G S hG hS hc ≤ limit := by
    dsimp only [space] at hw
    omega
  have hwborrow : buffer + count q (Volume O (H * fieldCount cs) G (S * q.w)) ≤ limit := by
    dsimp only [H]
    dsimp only [space] at hw
    omega
  let p := PaddedChunks.program q reader cutoff cs (O * (H * H)) P' G S
    source buffer limit hG hS hp hc hsinner hwpadded hl
  exact CommonBorrowedCore.program q reader O ExchangeSpecialization.radix ρ
    (fieldCount cs) G (S * q.w) source buffer limit p hs hwborrow hl

theorem program_charge_le (q : Configuration) (reader : Fin q.inventory.readers)
    (cutoff : ℕ) (cs : List ArbitraryCalls.Call) (O ρ P' G S source buffer limit : ℕ)
    (hG : 0 < G) (hS : 0 < S)
    (hp : O * ((ExchangeSpecialization.radix ^ ρ) * (ExchangeSpecialization.radix ^ ρ)) ≤ P')
    (hc : Conditions q cutoff cs P')
    (hs : source + count q
      (Volume O ((ExchangeSpecialization.radix ^ ρ) * fieldCount cs) G (S * q.w)) ≤ buffer)
    (hw : buffer + space q cutoff cs O ρ P' G S hG hS hc ≤ limit)
    (hl : limit ≤ q.N ^ q.exponent) :
    (program q reader cutoff cs O ρ P' G S source buffer limit hG hS hp hc hs hw hl).charge ≤
      bound q cutoff cs O ρ P' G S := by
  unfold program
  rw [CommonBorrowedCore.program_charge]
  have hp := PaddedChunks.program_charge_le q reader cutoff cs
    (O*((ExchangeSpecialization.radix^ρ)*(ExchangeSpecialization.radix^ρ))) P' G S
    source buffer limit hG hS hp hc
    (by simpa only [← borrowed_volume] using hs)
    (by dsimp only [space] at hw; omega) hl
  have hh := Nat.add_le_add_right hp
    (2*((3*(ρ*(2*ExchangeSpecialization.radix+6))+6)*
      count q (Volume O ((ExchangeSpecialization.radix^ρ)*fieldCount cs) G (S*q.w))))
  refine hh.trans_eq ?_
  unfold PaddedChunks.bound bound
  rw [← borrowed_volume]
  ring

/-- The actual transfer charge fits the arithmetic envelope used in the
arbitrary-width theorem, including both borrowing scans and both padding scans. -/
theorem bound_le_scan (q : Configuration) (cutoff : ℕ) (cs : List ArbitraryCalls.Call)
    (O ρ P' G S : ℕ) :
    bound q cutoff cs O ρ P' G S ≤
      ArbitraryCostRate.borrowedBound cutoff (width q) cs O ρ P' G (S * q.w)
        24 27 (6 * (2 * ExchangeSpecialization.radix + 6)) := by
  unfold bound ArbitraryCostRate.borrowedBound ArbitraryCostRate.overheadBound
  have hV := CommonResidentBase.count_le_floor q
    (Volume O ((ExchangeSpecialization.radix^ρ)*fieldCount cs) G (S*q.w))
  have hV' := CommonResidentBase.count_le_floor q
    (Volume P' (fieldCount cs) G (S*q.w))
  have h1 := Nat.mul_le_mul_left (24+6*ρ*(2*ExchangeSpecialization.radix+6)) hV
  have h2 := Nat.mul_le_mul_left 27 hV'
  dsimp only [CommonPermutationPairs.width] at *
  nlinarith only [h1,h2]

end
end CodedSorting.Construction.BorrowedChunks
end BorrowedChunks
