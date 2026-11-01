import CodedSorting.Shared.Memory.Leaf.Correctness
import CodedSorting.Interchange.Framework.Memory.BaseExchangeProgram
import CodedSorting.Shared.Words.WordConvention

/-! A concrete address exchange inside the existing resident leaf bank.
Bits keep their literal positions inside global words. The fixed CPU sees
only this bank; loading and output are actual finite-disk operations. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace CodedSorting.CommonExchangeLeaf
open WordControl CommonSortingNormalization CommonLeafProgram CommonLeafLoad CommonLeafWrite
open BitWordPacking Circuit

def bankWords (q : Configuration) := (512*q.height)*3
def bankBits (q : Configuration) := bankWords q*q.w

def payload (q : Configuration) (bank : CommonLeafTransform.Bank q) : Fin (bankBits q) → Bit :=
  blockBits (bankWords q) q.w (ResidentLeafBank.raw bank)

/-- This is just a view of the existing word-addressed disk, used in the
specification. It is never passed to the policy or the CPU. -/
def diskBits (q : Configuration) (disk : Disk q) (base : ℕ) : Fin (bankBits q) → Bit :=
  blockBits (bankWords q) q.w (fun j => diskWord q disk base j.val)

theorem diskBits_address (q : Configuration) (disk : Disk q) (base : ℕ)
    (j : Fin (bankWords q)) (i : Fin q.w) :
    diskBits q disk base (finProdFinEquiv (j,i))=
      wordBits q.w (diskWord q disk base j.val) i := blockBits_at _ _ _ j i

/-- Permute only the live prefix of bits; the remaining resident payload
is preserved. The header and every other source-RAM slot are unchanged. -/
def cpu (q : Configuration) (V : ℕ) (hV : V≤bankBits q) (π : Equiv.Perm (Fin V))
    (bank : CommonLeafTransform.Bank q) : CommonLeafTransform.Bank q :=
  Fin.append (ResidentLeafSort.header bank)
    ((blockBits (bankWords q) q.w).symm (fun i =>
      if h : i.val<V then payload q bank ((π ⟨i.val,h⟩).castLE hV) else payload q bank i))

@[simp] theorem cpu_header (q : Configuration) (V : ℕ) (hV : V≤bankBits q)
    (π : Equiv.Perm (Fin V)) (bank : CommonLeafTransform.Bank q) :
    ResidentLeafSort.header (cpu q V hV π bank)=ResidentLeafSort.header bank := by
  funext i
  simp only [cpu,ResidentLeafSort.header,Fin.append_left]

theorem cpu_bits (q : Configuration) (V : ℕ) (hV : V≤bankBits q)
    (π : Equiv.Perm (Fin V)) (bank : CommonLeafTransform.Bank q) (i : Fin V) :
    payload q (cpu q V hV π bank) (i.castLE hV)=payload q bank ((π i).castLE hV) := by
  have hraw : ResidentLeafBank.raw (cpu q V hV π bank)=
      (blockBits (bankWords q) q.w).symm (fun j =>
        if h : j.val<V then payload q bank ((π ⟨j.val,h⟩).castLE hV) else payload q bank j) := by
    funext j
    simp only [cpu,ResidentLeafBank.raw,Fin.append_right]
  simp only [payload,hraw,Equiv.apply_symm_apply,Fin.coe_castLE,i.isLt,↓reduceDIte]

theorem word_index_live (q : Configuration) (i : Fin (bankBits q)) (n : ℕ)
    (hi : i.val<n*q.w) : (finProdFinEquiv.symm i : Fin (bankWords q) × Fin q.w).1.val<n := by
  have he := bit_address (bankWords q) q.w
    (finProdFinEquiv.symm i : Fin (bankWords q) × Fin q.w).1
    (finProdFinEquiv.symm i : Fin (bankWords q) × Fin q.w).2
  rw [Prod.mk.eta,Equiv.apply_symm_apply] at he
  by_contra hn
  have hm := Nat.mul_le_mul_right q.w (show n≤(finProdFinEquiv.symm i : Fin (bankWords q) × Fin q.w).1.val by omega)
  omega

theorem payload_eq_diskBits (q : Configuration) (bank : CommonLeafTransform.Bank q)
    (disk : Disk q) (base n : ℕ)
    (hraw : ∀ j : Fin (bankWords q),j.val<n → ResidentLeafBank.raw bank j=diskWord q disk base j.val)
    (i : Fin (bankBits q)) (hi : i.val<n*q.w) :
    payload q bank i=diskBits q disk base i := by
  change wordBits q.w (ResidentLeafBank.raw bank (finProdFinEquiv.symm i).1) _=
    wordBits q.w (diskWord q disk base (finProdFinEquiv.symm i).1.val) _
  rw [hraw _ (word_index_live q i n hi)]

/-- Actual finite-disk execution of any fixed public bit permutation which
fits the resident prefix. This is instantiated by field exchange below. -/
theorem complete_permutation (q : Configuration) (z : Slots q)
    (V : ℕ) (hV : V≤bankBits q) (π : Equiv.Perm (Fin V))
    (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hin : inputCursor q z s=0) (hout : outputCursor q z s=0)
    (hlive : V≤words q s*q.w)
    (hsource : sourceBase q z s+blocks q s≤q.N^q.exponent)
    (htarget : targetBase q z s+blocks q s≤q.N^q.exponent) :
    ∃ (final : Store q) (out : Disk q),
      CommonLeafTransform.run q z (cpu q V hV π) (3*blocks q s+1) (machine q s disk)=
        (machine q final out,2*blocks q s) ∧
      CommonLeafTransform.policy q z (cpu q V hV π) (pack final)=none ∧
      (∀ i : Fin V,diskBits q out (targetBase q z s) (i.castLE hV)=
        diskBits q disk (sourceBase q z s) ((π i).castLE hV)) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<targetBase q z s ∨ targetBase q z s+blocks q s≤a.val → out a=disk a) ∧
      frameView q final=frameView q s := by
  obtain ⟨loaded,final,out,hr,hh,hread,hwrite,houtside,hframe⟩ :=
    CommonLeafTransform.complete q z (cpu q V hV π) (cpu_header q V hV π)
      s disk hp hin hout hsource htarget
  refine ⟨final,out,hr,hh,?_,houtside,hframe⟩
  intro i
  rw [←payload_eq_diskBits q (cpu q V hV π loaded.leaf) out (targetBase q z s) (words q s)
    (fun j hj => (hwrite j hj).symm) (i.castLE hV) (i.isLt.trans_le hlive),cpu_bits]
  exact payload_eq_diskBits q loaded.leaf disk (sourceBase q z s) (words q s)
    hread ((π i).castLE hV) ((π i).isLt.trans_le hlive)

/-- The concrete public leaf program exchanges the two designated fields;
prefix, gap and suffix retain their values. -/
def policy (q : Configuration) (z : Slots q) (P Q G S : ℕ)
    (hV : BaseExchangeProgram.Volume P Q G S≤bankBits q) : SourcePolicy q :=
  CommonLeafTransform.policy q z (cpu q _ hV (BaseExchangeProgram.permutation (P:=P) (Q:=Q) (G:=G) (S:=S)))


/-- The same concrete run returns the actual exchanged bits, halts, and
charges both scans. The header counts three-word slots only to reuse the
existing bank; no record tags or ordering assumptions are imposed. -/
theorem initialized_exchange (q : Configuration) (z : Slots q) (P Q G S : ℕ)
    (n : Fin (512*q.height+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hcover : BaseExchangeProgram.Volume P Q G S≤3*n.val*q.w)
    (hsource : source.val+PhysicalStreamCursor.blockCount q.block (3*n.val)≤q.N^q.exponent)
    (htarget : target.val+PhysicalStreamCursor.blockCount q.block (3*n.val)≤q.N^q.exponent) :
    ∃ (hV : BaseExchangeProgram.Volume P Q G S≤bankBits q) (final : Store q) (out : Disk q),
      ControlledNormalization.runLogical (policy q z P Q G S hV)
        (3*PhysicalStreamCursor.blockCount q.block (3*n.val)+1)
        (machine q (initialStore q z n source target s) disk)=
          (machine q final out,2*PhysicalStreamCursor.blockCount q.block (3*n.val)) ∧
      policy q z P Q G S hV (pack final)=none ∧
      (∀ a : Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin S),
        diskBits q out target.val ((CoordinateScans.lowLayout a).castLE hV)=
          diskBits q disk source.val ((CoordinateScans.lowLayout (Address.exchange a)).castLE hV)) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target.val ∨
        target.val+PhysicalStreamCursor.blockCount q.block (3*n.val)≤a.val → out a=disk a) ∧
      frameView q final=frameView q s ∧
      q.ramWords+q.B+q.block+4*q.digits+3≤q.M := by
  have hn : 3*n.val≤bankWords q := by have := n.isLt; unfold bankWords; omega
  have hV : BaseExchangeProgram.Volume P Q G S≤bankBits q :=
    hcover.trans (Nat.mul_le_mul_right q.w hn)
  let π := BaseExchangeProgram.permutation (P:=P) (Q:=Q) (G:=G) (S:=S)
  obtain ⟨final,out,hr,hh,hbits,houtside,hframe⟩ := complete_permutation q z
    _ hV π (initialStore q z n source target s) disk
    (CommonLeafInit.phase_initial q z n source target s)
    (CommonLeafInit.inputCursor_initial q z n source target s)
    (CommonLeafInit.outputCursor_initial q z n source target s)
    (by simpa only [CommonLeafInit.words_initial] using hcover)
    (by simpa only [CommonLeafInit.sourceBase_initial,CommonLeafInit.blocks_initial] using hsource)
    (by simpa only [CommonLeafInit.targetBase_initial,CommonLeafInit.blocks_initial] using htarget)
  refine ⟨hV,final,out,?_,hh,?_,?_,hframe,CommonLeafCorrectness.resident_word_bound q⟩
  · simpa only [CommonLeafInit.blocks_initial] using hr
  · intro a
    have h := hbits (CoordinateScans.lowLayout a)
    simpa only [CommonLeafInit.sourceBase_initial,CommonLeafInit.targetBase_initial,
      π,BaseExchangeProgram.permutation_encoded] using h
  · simpa only [CommonLeafInit.targetBase_initial,CommonLeafInit.blocks_initial] using houtside


/-- Canonical three-word-slot count, determined solely by the public bit
volume. It need not be stored as an unbounded natural number. -/
def roundedCount (q : Configuration) (V : ℕ) (hV : V≤bankBits q) : Fin (512*q.height+1) :=
  ⟨PhysicalStreamCursor.blockCount (3*q.w) V,by
    have hw : 0<3*q.w := by have := q.word_width; omega
    have hc : V≤(512*q.height)*(3*q.w) := by
      simpa only [bankBits,bankWords,Nat.mul_assoc] using hV
    have h := LayoutConversion.blockCount_minimal V (3*q.w) (512*q.height) hw hc
    change PhysicalStreamCursor.blockCount (3*q.w) V≤512*q.height at h
    omega⟩

theorem rounded_cover (q : Configuration) (V : ℕ) (hV : V≤bankBits q) :
    V≤3*(roundedCount q V hV).val*q.w := by
  have h := LayoutConversion.blockCount_covers V (3*q.w) (by have := q.word_width; omega)
  change V≤PhysicalStreamCursor.blockCount (3*q.w) V*(3*q.w) at h
  simpa only [roundedCount,Nat.mul_assoc,Nat.mul_comm 3] using h

/-- Three-word rounding adds at most three scanned word blocks. -/
theorem rounded_blocks_bound (q : Configuration) (V : ℕ) (hV : V≤bankBits q) :
    PhysicalStreamCursor.blockCount q.block (3*(roundedCount q V hV).val)≤
      PhysicalStreamCursor.blockCount (q.block*q.w) V+3 := by
  let n := (roundedCount q V hV).val
  let k := PhysicalStreamCursor.blockCount (q.block*q.w) V
  have hw : 0<q.w := by have := q.word_width; omega
  have hb := block_positive q
  have hv : V≤k*(q.block*q.w) :=
    LayoutConversion.blockCount_covers V (q.block*q.w) (Nat.mul_pos hb hw)
  have hn : 3*n≤k*q.block+3 := by
    by_cases hz : n=0
    · simp only [hz,Nat.mul_zero]; omega
    · have hprev : (n-1)*(3*q.w)<V :=
        (PhysicalStreamCursor.cursor_live_iff (3*q.w) V (n-1) (by omega)).1 (by
          change n-1<n
          omega)
      have he : n-1+1=n := by omega
      have hm : (3*n)*q.w<(k*q.block+3)*q.w := by nlinarith
      have hlt : 3*n<k*q.block+3 := Nat.lt_of_mul_lt_mul_right hm
      omega
  have hb3 : 3≤3*q.block := Nat.le_mul_of_pos_right 3 hb
  apply LayoutConversion.blockCount_minimal _ q.block (k+3) hb
  nlinarith

/-- The previous file-interpreter leaf envelope also covers this actual
word-machine implementation, including the three-word rounding. -/
theorem leaf_charge_bound (q : Configuration) (V : ℕ) (hV : V≤bankBits q) :
    2*PhysicalStreamCursor.blockCount q.block (3*(roundedCount q V hV).val)≤
      12*(V/(q.block*q.w)+1) := by
  have hb : 0<q.block*q.w := Nat.mul_pos (block_positive q) (by have := q.word_width; omega)
  have hk := rounded_blocks_bound q V hV
  have hceil : PhysicalStreamCursor.blockCount (q.block*q.w) V≤V/(q.block*q.w)+1 := by
    apply LayoutConversion.blockCount_minimal _ _ _ hb
    have hm := Nat.mod_lt V hb
    have he := Nat.div_add_mod V (q.block*q.w)
    nlinarith
  have hnonneg : 0≤V/(q.block*q.w) := Nat.zero_le _
  omega


/-- Public endpoint with the canonical rounded length. Correct output,
halting, the inherited leaf cost envelope and the resident-memory bound
are all attached to one actual SourcePolicy execution. -/
theorem rounded_exchange (q : Configuration) (z : Slots q) (P Q G S : ℕ)
    (hV : BaseExchangeProgram.Volume P Q G S≤bankBits q)
    (source target : Fin (q.N^q.exponent)) (s : Store q) (disk : Disk q)
    (hsource : source.val+PhysicalStreamCursor.blockCount q.block
      (3*(roundedCount q (BaseExchangeProgram.Volume P Q G S) hV).val)≤q.N^q.exponent)
    (htarget : target.val+PhysicalStreamCursor.blockCount q.block
      (3*(roundedCount q (BaseExchangeProgram.Volume P Q G S) hV).val)≤q.N^q.exponent) :
    let n := roundedCount q (BaseExchangeProgram.Volume P Q G S) hV
    let k := PhysicalStreamCursor.blockCount q.block (3*n.val)
    ∃ (final : Store q) (out : Disk q),
      ControlledNormalization.runLogical (policy q z P Q G S hV) (3*k+1)
        (machine q (initialStore q z n source target s) disk)=(machine q final out,2*k) ∧
      policy q z P Q G S hV (pack final)=none ∧
      (∀ a : Address.FullAddress (Fin P) (Fin Q) (Fin G) (Fin S),
        diskBits q out target.val ((CoordinateScans.lowLayout a).castLE hV)=
          diskBits q disk source.val ((CoordinateScans.lowLayout (Address.exchange a)).castLE hV)) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target.val ∨ target.val+k≤a.val → out a=disk a) ∧
      frameView q final=frameView q s ∧
      2*k≤12*(BaseExchangeProgram.Volume P Q G S/(q.block*q.w)+1) ∧
      q.ramWords+q.B+q.block+4*q.digits+3≤q.M := by
  dsimp only
  obtain ⟨_,final,out,hr,hh,hbits,houtside,hframe,hmemory⟩ := initialized_exchange
    q z P Q G S (roundedCount q _ hV) source target s disk
    (rounded_cover q _ hV) hsource htarget
  exact ⟨final,out,hr,hh,hbits,houtside,hframe,leaf_charge_bound q _ hV,hmemory⟩

end CodedSorting.CommonExchangeLeaf
