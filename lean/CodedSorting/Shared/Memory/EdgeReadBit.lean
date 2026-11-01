import CodedSorting.Shared.Programs.Static.Leaf
import Mathlib.Data.Nat.Log
import CodedSorting.Interchange.Framework.Memory.Reflection

section PhysicalFieldPacking
/-! Canonical address identities at recursive field boundaries, and the
actual adaptive leaf on the same scalar-field file layout. -/

set_option maxRecDepth 4096
namespace CodedSorting.PhysicalFieldPacking
open Circuit PhysicalRecursiveExchange RecursiveExchange RecursiveExchangeCost
open CoordinateLayoutBridge ScalarLayoutBridge CodedSimulation Address ScanProgram
noncomputable section

local instance : LinearOrder Index := RecursiveExchange.indexOrder
local instance : LE Index := RecursiveExchange.indexOrder.toLE
local instance : LT Index := RecursiveExchange.indexOrder.toLT
local instance : WellFoundedLT Index :=
  @Finite.to_wellFoundedLT Index inferInstance RecursiveExchange.indexOrder.toPreorder

abbrev ScalarVolume (f P G S : ℕ) := (P*(radix^f*G))*(radix^f*S)

def scalarLayout (f P G S : ℕ) :
    FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) ≃ Fin (ScalarVolume f P G S) :=
  (CommonAddressLayout.shape (Equiv.refl _) (digit f) (Equiv.refl _) (Equiv.refl _)).trans
    CoordinateScans.lowLayout

theorem ringPacking_val {A : Type} {n N : ℕ} [NeZero N]
    (packing : A ≃ Fin n) (h : n = N) (x : A) :
    ((ZMod.finEquiv N).symm
      ((packing.trans ((finCongr h).trans (ZMod.finEquiv N).toEquiv)) x)).val =
      (packing x).val := by
  simp only [Equiv.trans_apply,RingEquiv.toEquiv_eq_coe,RingEquiv.coe_toEquiv,
    RingEquiv.symm_apply_apply,finCongr_apply_coe]

/-- The long residue and its ordered block vector encode the same integer. -/
theorem blockPacking_val (f : ℕ) (x : Field f) :
    ((ZMod.finEquiv (radix^(Parameters.m*f))).symm (blockPacking f x)).val =
      (TriangularStreams.lexLayout (fieldVector f x)).val := by
  calc
    _ = (FieldPacking.vectorFinPacking Index radix f x).val :=
      ringPacking_val (FieldPacking.vectorFinPacking Index radix f) _ x
    _ = (LexBlocks.subvectorEncode (digitVector f x)).val :=
      congrArg Fin.val (FieldPacking.vectorFinPacking_eq_subvectorEncode Index radix f x)
    _ = _ := (field_code_val f x).symm

theorem packedVolume (f P G S : ℕ) :
    ScalarVolume (Parameters.m*f) P G S = longVolume f P G S := by
  have hp : radix^(Parameters.m*f) = (radix^f)^Parameters.m := by
    rw [Nat.mul_comm Parameters.m f,pow_mul]
  simp only [ScalarVolume,longVolume,hp]
  ring

/-- Packing all short fields only changes grouping: its linear file address
is identical before and after the operation. -/
theorem blockPacking_same_address (f P G S : ℕ)
    (a : EdgeAddress f P G S) :
    finCongr (packedVolume f P G S)
      (scalarLayout (Parameters.m*f) P G S
        (addressShape (Equiv.refl _) (blockPacking f) (Equiv.refl _) (Equiv.refl _) a)) =
      commonLayout f P G S a := by
  apply Fin.ext
  simp only [finCongr_apply_coe,scalarLayout,Equiv.trans_apply,CommonAddressLayout.shape,
    Equiv.coe_fn_mk,Equiv.refl_apply,addressShape,CoordinateScans.lowLayout_val,digit]
  simp only [RingEquiv.toEquiv_eq_coe,RingEquiv.coe_toEquiv]
  rw [commonLayout_val,blockPacking_val,blockPacking_val]
  rw [Nat.mul_comm Parameters.m f,pow_mul]

/-- A physical file is unchanged by the long-field/vector-field boundary.
This equality supplies no permutation instruction and charges no fake pass. -/
theorem blockPacking_same_file (f P G S B : ℕ) (hB : 0 < B)
    (F : EdgeAddress f P G S → Bit) :
    represented ((scalarLayout (Parameters.m*f) P G S).trans (finCongr (packedVolume f P G S)))
      B hB (F ∘ (addressShape (Equiv.refl _) (blockPacking f)
        (Equiv.refl _) (Equiv.refl _)).symm) = represented (commonLayout f P G S) B hB F := by
  exact represented_regroup (commonLayout f P G S)
    ((scalarLayout (Parameters.m*f) P G S).trans (finCongr (packedVolume f P G S)))
    (addressShape (Equiv.refl _) (blockPacking f) (Equiv.refl _) (Equiv.refl _))
    (blockPacking_same_address f P G S) B hB F

/-- The selected-coordinate child receives the very same file produced by
its preceding scalar scan, with all spectator coordinates in order. -/
theorem child_same_file (f P G S B : ℕ) (hB : 0 < B) (c : Child)
    (F : EdgeAddress f P G S → Bit) :
    represented ((childLayout f P G S c).trans (finCongr (child_volume f P G S c)))
      B hB (F ∘ (childRepack f c).symm) = represented (commonLayout f P G S) B hB F := by
  exact represented_regroup (commonLayout f P G S)
    ((childLayout f P G S c).trans (finCongr (child_volume f P G S c)))
    (childRepack f c) (child_common f P G S c) B hB F

theorem leaf_realizes (f P G S : ℕ) :
    Realizes (scalarLayout f P G S)
      (BaseExchangeProgram.program (P := P) (Q := radix^f) (G := G) (S := S)) exchangeEquiv := by
  intro a
  change BaseExchangeProgram.permutation
    (CoordinateScans.lowLayout (CommonAddressLayout.shape (Equiv.refl _) (digit f)
      (Equiv.refl _) (Equiv.refl _) a)) = _
  rw [BaseExchangeProgram.permutation_encoded]
  rfl

/-- A stopped recursive call executes the real RAM or Q²-stream leaf. Its
input is an existing file and its result is the canonical exchanged file.
The bucket startup condition remains explicit, as does the actual cost. -/
theorem leaf_execution (f P G S cutoff B : ℕ) (hB : 0 < B)
    (F : FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) → Bit)
    (source : File) (hs : source = represented (scalarLayout f P G S) B hB F)
    (hstartup : cutoff < ScalarVolume f P G S →
      ((radix^f)*(radix^f))*B ≤ ScalarVolume f P G S+B) :
    ∃ result : BaseExchangeProgram.LeafResult Bit,
      BaseExchangeProgram.adaptiveRun (P := P) (Q := radix^f) (G := G) (S := S)
        cutoff B source = some result ∧
      result.output.finish = represented (scalarLayout f P G S) B hB (transport exchangeEquiv F) ∧
      result.output.Valid B ∧ result.transfers*B ≤ 6*(ScalarVolume f P G S+B) := by
  obtain ⟨result,hr,ho,hv,hc⟩ := BaseExchangeProgram.adaptive_correct
    (encoded (scalarLayout f P G S) F) cutoff B hB hstartup
  have hin : BucketMachine.pack B hB (TagErasure.inputValues (encoded (scalarLayout f P G S) F)) =
      represented (scalarLayout f P G S) B hB F := by
    rw [represented,canonical,List.ofFn_eq_map]
    rfl
  have hm : (fun y => encoded (scalarLayout f P G S) F
      ((BaseExchangeProgram.permutation (P := P) (Q := radix^f) (G := G) (S := S)).symm y)) =
      encoded (scalarLayout f P G S) (transport exchangeEquiv F) := by
    rw [← realizes_eval (scalarLayout f P G S) _ exchangeEquiv (leaf_realizes f P G S) F]
    funext y
    simpa only [BaseExchangeProgram.destination_program] using
      (eval_eq_pullback (BaseExchangeProgram.program (P := P) (Q := radix^f) (G := G) (S := S))
        (encoded (scalarLayout f P G S) F) y).symm
  have hout : BucketMachine.pack B hB
      (TagErasure.outputValues BaseExchangeProgram.permutation (encoded (scalarLayout f P G S) F)) =
      represented (scalarLayout f P G S) B hB (transport exchangeEquiv F) := by
    unfold TagErasure.outputValues
    rw [hm,represented,canonical,List.ofFn_eq_map]
  exact ⟨result,by simpa only [hs,hin] using hr,ho.trans hout,hv,hc⟩

end
end CodedSorting.PhysicalFieldPacking
end PhysicalFieldPacking

section EdgeExecution
/-! Concrete edge execution at the lowest nonleaf network level. Each
edge stream is resident-size, so its complete matrix address change is
performed by one real read--RAM permutation--write fragment. No recursive
success callback or factorization scan is required at this base level. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace CodedSorting.CommonEdgeExecution
open WordControl CommonSortingNormalization CommonStaticSchedule
open CommonLeafProgram (Store Disk Machine machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open PhysicalRecursiveExchange CodedSimulation Address Circuit
noncomputable section

def move (f P G S : ℕ) (e : Edge) : Equiv.Perm (EdgeAddress f P G S) :=
  matrixLocation (reducedEdgeMatrix f e)

/-- Pullback on literal file-bit addresses. A value initially at a is
written at the physical address of `(H + A_e D,D)`. -/
def permutation (f P G S : ℕ) (e : Edge) : Equiv.Perm (Fin (longVolume f P G S)) :=
  (commonLayout f P G S).symm.trans ((move f P G S e).symm.trans (commonLayout f P G S))

theorem permutation_at (f P G S : ℕ) (e : Edge) (a : EdgeAddress f P G S) :
    permutation f P G S e (commonLayout f P G S a)=
      commonLayout f P G S ((move f P G S e).symm a) := by
  simp only [permutation,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem permutation_moved (f P G S : ℕ) (e : Edge) (a : EdgeAddress f P G S) :
    permutation f P G S e (commonLayout f P G S (move f P G S e a))=
      commonLayout f P G S a := by
  rw [permutation_at,Equiv.symm_apply_apply]

theorem move_coordinates (f P G S : ℕ) (e : Edge) (a : EdgeAddress f P G S) :
    move f P G S e a=⟨a.prefixCoord,a.high+(reducedEdgeMatrix f e).mulVec a.low,
      a.gap,a.low,a.suffix⟩ := rfl

def code (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ) :
    List (Instruction q) :=
  CommonStaticLeaf.code q _ hV (permutation f P G S e) source target

def blocks (q : Configuration) (f P G S : ℕ)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) : ℕ :=
  PhysicalStreamCursor.blockCount q.block (3*(CommonExchangeLeaf.roundedCount q _ hV).val)

@[simp] theorem code_length (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ) :
    (code q f P G S e hV source target).length=3*blocks q f P G S hV+1 :=
  CommonStaticLeaf.length_code q _ hV _ source target

theorem code_safe (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ) :
    ∀ i∈code q f P G S e hV source target,RespectsPC q i :=
  CommonStaticLeaf.safe q _ hV _ source target

theorem code_cost (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ)
    (hs : source+blocks q f P G S hV≤q.N^q.exponent)
    (ht : target+blocks q f P G S hV≤q.N^q.exponent) :
    cost q (code q f P G S e hV source target)=2*blocks q f P G S hV :=
  CommonStaticLeaf.cost_code q _ hV _ source target hs ht

/-- Complete actual edge fragment. Input and output messages are views of
the same finite disk execution, and the value reaches its shifted address. -/
theorem raw_complete (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ)
    (s : Store q) (disk : Disk q)
    (hs : source+blocks q f P G S hV≤q.N^q.exponent)
    (ht : target+blocks q f P G S hV≤q.N^q.exponent) :
    ∃ (final : Store q) (out : Disk q),
      executeRaw q (code q f P G S e hV source target) (machine q s disk)=
        (machine q final out,2*blocks q f P G S hV) ∧
      (∀ a : EdgeAddress f P G S,
        CommonExchangeLeaf.diskBits q out target
          ((commonLayout f P G S (move f P G S e a)).castLE hV)=
        CommonExchangeLeaf.diskBits q disk source ((commonLayout f P G S a).castLE hV)) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+blocks q f P G S hV≤a.val → out a=disk a) ∧
      CommonLeafWrite.frameView q final=CommonLeafWrite.frameView q s ∧
      2*blocks q f P G S hV≤12*(longVolume f P G S/(q.block*q.w)+1) := by
  obtain ⟨final,out,hr,hbits,houtside,hframe,_⟩ := CommonStaticLeaf.raw_complete q _ hV
    (permutation f P G S e) source target s disk hs ht
  refine ⟨final,out,hr,?_,houtside,hframe,CommonExchangeLeaf.leaf_charge_bound q _ hV⟩
  intro a
  simpa only [permutation_moved] using hbits (commonLayout f P G S (move f P G S e a))

/-- Direct bridge to the network interpreter's exact stream map. The
input function F is specification-only; the code receives no such function. -/
theorem raw_stream (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ)
    (s : Store q) (disk : Disk q) (F : EdgeStream f P G S)
    (hs : source+blocks q f P G S hV≤q.N^q.exponent)
    (ht : target+blocks q f P G S hV≤q.N^q.exponent)
    (hinput : ∀ a,CommonExchangeLeaf.diskBits q disk source ((commonLayout f P G S a).castLE hV)=F a) :
    let result := executeRaw q (code q f P G S e hV source target) (machine q s disk)
    (∀ a : EdgeAddress f P G S,
      CommonExchangeLeaf.diskBits q result.1.disk target ((commonLayout f P G S a).castLE hV)=
        transport (matrixLocation (reducedEdgeMatrix f e)) F a) ∧
    result.2=2*blocks q f P G S hV := by
  dsimp only
  obtain ⟨final,out,hr,hbits,_,_,_⟩ := raw_complete q f P G S e hV source target s disk hs ht
  rw [hr]
  refine ⟨?_,rfl⟩
  intro a
  have h := hbits ((move f P G S e).symm a)
  rw [Equiv.apply_symm_apply,hinput] at h
  exact h

end
end CodedSorting.CommonEdgeExecution
end EdgeExecution

section PhysicalLeafParameters
/-!
# Integer choices for the physical leaf threshold

The paper chooses t = floor(log_q(M/B)/8), then the largest power of m
not exceeding t.  These choices discharge the buffer-startup premise of
the actual adaptive leaf; no real logarithm or asymptotic premise is needed.
`reserve` specifies the inverse fraction of RAM assigned to the leaf.
The bounds below concern payload buffers, not the complete controller.
-/

set_option autoImplicit false

namespace CodedSorting.PhysicalLeafParameters

def widthLimit (q ratio : ℕ) : ℕ := Nat.log q ratio / 8

def baseWidth (m q ratio : ℕ) : ℕ := m ^ Nat.log m (widthLimit q ratio)

/-- A fixed sufficiently large normalization ratio. The second term also
ensures that every child of a non-RAM call contains a physical block. -/
def minimumRatio (q reserve lanes : ℕ) : ℕ :=
  max (q ^ (8 * (Nat.log q reserve + 1))) (reserve * lanes)

theorem widthLimit_lower (q reserve lanes ratio : ℕ) (hq : 1 < q)
    (h : minimumRatio q reserve lanes ≤ ratio) :
    Nat.log q reserve + 1 ≤ widthLimit q ratio := by
  have hp : q ^ (8 * (Nat.log q reserve + 1)) ≤ ratio :=
    (Nat.le_max_left _ _).trans h
  have hl := Nat.le_log_of_pow_le hq hp
  unfold widthLimit
  omega

theorem widthLimit_pos (q reserve lanes ratio : ℕ) (hq : 1 < q)
    (h : minimumRatio q reserve lanes ≤ ratio) : 0 < widthLimit q ratio := by
  have := widthLimit_lower q reserve lanes ratio hq h
  omega

theorem widthLimit_power (q ratio : ℕ) (hratio : 0 < ratio) :
    q ^ (8 * widthLimit q ratio) ≤ ratio := by
  apply Nat.pow_le_of_le_log (by omega)
  unfold widthLimit
  have := Nat.div_mul_le_self (Nat.log q ratio) 8
  omega

theorem baseWidth_bounds (m q reserve lanes ratio : ℕ) (hm : 1 < m) (hq : 1 < q)
    (h : minimumRatio q reserve lanes ≤ ratio) :
    0 < baseWidth m q ratio ∧ baseWidth m q ratio ≤ widthLimit q ratio ∧
      widthLimit q ratio < m * baseWidth m q ratio := by
  have ht := widthLimit_pos q reserve lanes ratio hq h
  refine ⟨pow_pos (by omega) _, Nat.pow_log_le_self m (by omega), ?_⟩
  have hp := Nat.lt_pow_succ_log_self hm (widthLimit q ratio)
  simpa only [baseWidth, pow_succ, Nat.mul_comm] using hp

/-- An exact integer form of t₀ = Θ(log_q ratio), with fixed m. -/
theorem baseWidth_log_sandwich (m q reserve lanes ratio : ℕ) (hm : 1 < m)
    (hq : 1 < q) (h : minimumRatio q reserve lanes ≤ ratio) :
    8*baseWidth m q ratio ≤ Nat.log q ratio ∧
      Nat.log q ratio < 8*m*baseWidth m q ratio := by
  obtain ⟨_,hlo,hhi⟩ := baseWidth_bounds m q reserve lanes ratio hm hq h
  have hdiv := Nat.div_mul_le_self (Nat.log q ratio) 8
  have hmod := Nat.mod_lt (Nat.log q ratio) (show 0 < 8 by omega)
  have hsplit := Nat.div_add_mod (Nat.log q ratio) 8
  unfold widthLimit at hlo hhi
  constructor <;> nlinarith

/-- The q^(2e) bucket count fits the reserved fraction for every allowed
leaf width, including the selected power-of-m base width. -/
theorem reserved_bucket_ratio (q reserve lanes ratio e : ℕ) (hq : 1 < q)
    (h : minimumRatio q reserve lanes ≤ ratio) (he : e ≤ widthLimit q ratio) :
    reserve * ((q ^ e) * (q ^ e)) ≤ ratio := by
  let t := widthLimit q ratio
  have ht : Nat.log q reserve + 1 ≤ t := widthLimit_lower q reserve lanes ratio hq h
  have hr : 0 < ratio := by
    have hp : 0 < q ^ (8 * (Nat.log q reserve + 1)) := pow_pos (by omega) _
    exact lt_of_lt_of_le hp ((Nat.le_max_left _ _).trans h)
  have hc : reserve ≤ q ^ (6*t) := by
    have hc0 := Nat.lt_pow_succ_log_self hq reserve
    have hpow : q ^ (Nat.log q reserve + 1) ≤ q ^ (6*t) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact (Nat.le_of_lt hc0).trans hpow
  have hb : q^e*q^e ≤ q^(2*t) := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by omega)
    change e ≤ t at he
    omega
  calc
    reserve * (q^e*q^e) ≤ q^(6*t)*q^(2*t) := Nat.mul_le_mul hc hb
    _ = q^(8*t) := by rw [← pow_add]; congr 1; omega
    _ ≤ ratio := widthLimit_power q ratio hr

theorem bucket_words (q reserve lanes M B e : ℕ) (hq : 1 < q)
    (hreserve : 0 < reserve)
    (h : minimumRatio q reserve lanes ≤ M / B) (he : e ≤ widthLimit q (M / B)) :
    ((q^e)*(q^e))*B ≤ M/reserve := by
  apply (Nat.le_div_iff_mul_le hreserve).2
  have hp := Nat.mul_le_mul_right B (reserved_bucket_ratio q reserve lanes (M/B) e hq h he)
  have hd := Nat.div_mul_le_self M B
  calc
    (q^e*q^e)*B*reserve = (reserve*(q^e*q^e))*B := by ring
    _ ≤ (M/B)*B := hp
    _ ≤ M := hd

theorem reserved_child_words (q reserve lanes M B : ℕ) (hreserve : 0 < reserve)
    (h : minimumRatio q reserve lanes ≤ M/B) : lanes*B ≤ M/reserve := by
  apply (Nat.le_div_iff_mul_le hreserve).2
  have hp := Nat.mul_le_mul_right B ((Nat.le_max_right
    (q^(8*(Nat.log q reserve+1))) (reserve*lanes)).trans h)
  have hd := Nat.div_mul_le_self M B
  nlinarith

/-- Words and bits are converted with the same global word size. -/
theorem bucket_bits (q reserve lanes M B w e : ℕ) (hq : 1 < q)
    (hreserve : 0 < reserve)
    (h : minimumRatio q reserve lanes ≤ M/B) (he : e ≤ widthLimit q (M/B)) :
    ((q^e)*(q^e))*(B*w) ≤ (M/reserve)*w := by
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_right w (bucket_words q reserve lanes M B e hq hreserve h he)

theorem leaf_startup (q reserve lanes M B w e V : ℕ) (hq : 1 < q)
    (hreserve : 0 < reserve)
    (h : minimumRatio q reserve lanes ≤ M/B) (he : e ≤ widthLimit q (M/B))
    (hlarge : (M/reserve)*w < V) : ((q^e)*(q^e))*(B*w) ≤ V+B*w := by
  have hb := bucket_bits q reserve lanes M B w e hq hreserve h he
  omega

theorem child_at_least_block (q reserve lanes M B w V : ℕ)
    (hreserve : 0 < reserve) (hlanes : 0 < lanes)
    (h : minimumRatio q reserve lanes ≤ M/B) (hlarge : (M/reserve)*w < V) :
    B*w ≤ V/lanes := by
  apply (Nat.le_div_iff_mul_le hlanes).2
  have hp := Nat.mul_le_mul_right w (reserved_child_words q reserve lanes M B hreserve h)
  nlinarith

/-- Two streaming buffers fit in addition to the reserved payload area.
This deliberately leaves all controller/metadata obligations separate. -/
theorem cutoff_payload_fits (reserve M B w : ℕ) (hreserve : 2 ≤ reserve)
    (hratio : 4*B ≤ M) : (M/reserve)*w+2*(B*w) ≤ M*w := by
  have hdiv : (M/reserve)*reserve ≤ M := Nat.div_mul_le_self M reserve
  have hd : 2*(M/reserve) ≤ M := by nlinarith
  have hh : M/reserve+2*B ≤ M := by omega
  have hw := Nat.mul_le_mul_right w hh
  nlinarith

theorem adaptive_payload_fits (q reserve lanes M B w e P G S : ℕ) (hq : 1 < q)
    (hreserve : 2 ≤ reserve) (hratio : 4*B ≤ M)
    (h : minimumRatio q reserve lanes ≤ M/B) (he : e ≤ widthLimit q (M/B)) :
    BaseExchangeProgram.adaptiveResident (P := P) (Q := q^e) (G := G) (S := S)
      ((M/reserve)*w) (B*w) ≤ M*w := by
  apply BaseExchangeProgram.adaptive_memory_fits
  · exact cutoff_payload_fits reserve M B w hreserve hratio
  · intro _
    have hb := bucket_bits q reserve lanes M B w e hq (by omega) h he
    have hm := cutoff_payload_fits reserve M B w hreserve hratio
    nlinarith

/-- The normalized parameter threshold supplies four whole block buffers. -/
theorem normalized_four_blocks (q reserve lanes M B : ℕ) (hreserve : 4 ≤ reserve)
    (hlanes : 0 < lanes) (h : minimumRatio q reserve lanes ≤ M/B) : 4*B ≤ M := by
  have hp : reserve*lanes ≤ M/B := (Nat.le_max_right _ _).trans h
  have hc : 4 ≤ M/B := by nlinarith
  have hd := Nat.div_mul_le_self M B
  have hh := Nat.mul_le_mul_right B hc
  omega

open Circuit PhysicalRecursiveExchange PhysicalFieldPacking RecursiveExchange
open CodedSimulation Address

/-- The actual canonical-file leaf now has its startup premise discharged
by the paper's explicit integer parameter choice. The resident assertion
is the existing leaf PAYLOAD bound; this is not a full controller theorem. -/
theorem normalized_leaf_execution (reserve lanes M B w e P G S : ℕ)
    (hreserve : 4 ≤ reserve) (hlanes : 0 < lanes) (hB : 0 < B) (hw : 0 < w)
    (h : minimumRatio radix reserve lanes ≤ M/B) (he : e ≤ widthLimit radix (M/B))
    (F : FullAddress (Fin P) (Scalar e) (Fin G) (Fin S) → Bit)
    (source : File)
    (hs : source = represented (scalarLayout e P G S) (B*w) (Nat.mul_pos hB hw) F) :
    ∃ result : BaseExchangeProgram.LeafResult Bit,
      BaseExchangeProgram.adaptiveRun (P := P) (Q := radix^e) (G := G) (S := S)
        ((M/reserve)*w) (B*w) source = some result ∧
      result.output.finish = represented (scalarLayout e P G S) (B*w) (Nat.mul_pos hB hw)
        (transport exchangeEquiv F) ∧
      result.output.Valid (B*w) ∧
      result.transfers*(B*w) ≤ 6*(ScalarVolume e P G S+B*w) ∧
      BaseExchangeProgram.adaptiveResident (P := P) (Q := radix^e) (G := G) (S := S)
        ((M/reserve)*w) (B*w) ≤ M*w := by
  obtain ⟨r,hr,ho,hv,hc⟩ := leaf_execution e P G S ((M/reserve)*w) (B*w)
    (Nat.mul_pos hB hw) F source hs
    (leaf_startup radix reserve lanes M B w e (ScalarVolume e P G S)
      radix_prime.one_lt (by omega) h he)
  exact ⟨r,hr,ho,hv,hc,adaptive_payload_fits radix reserve lanes M B w e P G S
    radix_prime.one_lt (by omega) (normalized_four_blocks radix reserve lanes M B
      hreserve hlanes h) h he⟩

end CodedSorting.PhysicalLeafParameters
end PhysicalLeafParameters

section EdgeReadBit
/-! The resident edge executor exposed in the common literal disk-bit view.
The view is specification-only and does not enter the generated code. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CodedSorting.CommonEdgeExecution
open WordControl CommonSortingNormalization CommonStaticSchedule BitWordPacking
open CommonLeafProgram (Store Disk Machine machine)
open RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open PhysicalRecursiveExchange CodedSimulation Address Circuit
noncomputable section

theorem diskBits_eq_readBit (q : Configuration) (disk : Disk q) (base : ℕ)
    (i : Fin (CommonExchangeLeaf.bankBits q))
    (hfit : base+i.val/(q.block*q.w)<q.N^q.exponent) :
    CommonExchangeLeaf.diskBits q disk base i=
      CommonPermutationPairs.readBit q disk base i.val := by
  have hd : i.val/q.w/q.block=i.val/(q.block*q.w) := by
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm q.w q.block]
  have ha : base+i.val/q.w/q.block<q.N^q.exponent := by rw [hd]; exact hfit
  change wordBits q.w (CommonLeafLoad.diskWord q disk base (i.val/q.w))
      ⟨i.val%q.w,_⟩=
    wordBits q.w (disk (CommonColumnSplit.address q base (i.val/(q.block*q.w)))
      ⟨i.val%(q.block*q.w)/q.w,_⟩) ⟨i.val%(q.block*q.w)%q.w,_⟩
  simp only [CommonLeafLoad.diskWord,ha,↓reduceDIte,CommonColumnSplit.address,hfit,
    Nat.mod_mul_left_div_self,Nat.mod_mul_left_mod,hd]

theorem count_le_blocks (q : Configuration) (f P G S : ℕ)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) :
    CommonPermutationPairs.count q (longVolume f P G S)≤blocks q f P G S hV := by
  apply LayoutConversion.blockCount_minimal _ _ _ (CommonPermutationPairs.width_pos q)
  have hc := CommonExchangeLeaf.rounded_cover q (longVolume f P G S) hV
  have hk : 3*(CommonExchangeLeaf.roundedCount q (longVolume f P G S) hV).val≤
      blocks q f P G S hV*q.block :=
    LayoutConversion.blockCount_covers _ _ (CommonLeafProgram.block_positive q)
  have hm := Nat.mul_le_mul_right q.w hk
  change longVolume f P G S≤blocks q f P G S hV*(q.block*q.w)
  nlinarith

/-- The rounded allocation contains every live bit, including the last
partial word and the final three-word bank slot. -/
theorem bit_address_fits (q : Configuration) (V : ℕ)
    (hV : V≤CommonExchangeLeaf.bankBits q) (base : ℕ)
    (hfit : base+PhysicalStreamCursor.blockCount q.block
      (3*(CommonExchangeLeaf.roundedCount q V hV).val)≤q.N^q.exponent)
    (i : Fin V) : base+i.val/(q.block*q.w)<q.N^q.exponent := by
  let K := PhysicalStreamCursor.blockCount q.block (3*(CommonExchangeLeaf.roundedCount q V hV).val)
  have hc := CommonExchangeLeaf.rounded_cover q V hV
  have hk : 3*(CommonExchangeLeaf.roundedCount q V hV).val≤K*q.block :=
    LayoutConversion.blockCount_covers _ _ (CommonLeafProgram.block_positive q)
  have hm := Nat.mul_le_mul_right q.w hk
  have hi : i.val<K*(q.block*q.w) := by
    have := i.isLt
    nlinarith [hc]
  have hb := CommonPermutationPairs.width_pos q
  have hx : i.val/(q.block*q.w)<K := (Nat.div_lt_iff_lt_mul hb).2 hi
  omega

/-- One actual edge fragment, in the shared literal bit view. The input
specification is read from the initial disk; no payload enters the code.
The same execution supplies its transport semantics, frame, and I/O cost. -/
theorem raw_stream_outside (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ)
    (s : Machine q) (F : EdgeStream f P G S)
    (hs : source+blocks q f P G S hV≤q.N^q.exponent)
    (ht : target+blocks q f P G S hV≤q.N^q.exponent)
    (hinput : ∀ a,CommonPermutationPairs.readBit q s.disk source
      (commonLayout f P G S a).val=F a) :
    let result := executeRaw q (code q f P G S e hV source target) s
    (∀ a : EdgeAddress f P G S,
      CommonPermutationPairs.readBit q result.1.disk target (commonLayout f P G S a).val=
        transport (matrixLocation (reducedEdgeMatrix f e)) F a) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+blocks q f P G S hV≤a.val →
      result.1.disk a=s.disk a) ∧
    result.2=2*blocks q f P G S hV := by
  have eta := CommonBlockPair.machine_eta q s
  obtain ⟨final,out,hr,hbits,houtside,_,_⟩ := raw_complete q f P G S e hV
    source target (unpack s.ram) s.disk hs ht
  rw [eta] at hr
  dsimp only
  rw [hr]
  refine ⟨?_,houtside,rfl⟩
  intro a
  have h := hbits ((move f P G S e).symm a)
  rw [Equiv.apply_symm_apply] at h
  rw [diskBits_eq_readBit q out target _
      (bit_address_fits q _ hV target ht (commonLayout f P G S a)),
    diskBits_eq_readBit q s.disk source _
      (bit_address_fits q _ hV source hs (commonLayout f P G S ((move f P G S e).symm a)))] at h
  simp only [Fin.coe_castLE] at h
  rw [hinput] at h
  exact h

/-- Literal-address form, with no separately supplied input stream. -/
theorem raw_bits (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ)
    (s : Machine q)
    (hs : source+blocks q f P G S hV≤q.N^q.exponent)
    (ht : target+blocks q f P G S hV≤q.N^q.exponent) :
    let result := executeRaw q (code q f P G S e hV source target) s
    (∀ i : Fin (longVolume f P G S),
      CommonPermutationPairs.readBit q result.1.disk target i.val=
        CommonPermutationPairs.readBit q s.disk source (permutation f P G S e i).val) ∧
    (∀ a : Fin (q.N^q.exponent),a.val<target ∨ target+blocks q f P G S hV≤a.val →
      result.1.disk a=s.disk a) ∧
    result.2=2*blocks q f P G S hV := by
  obtain ⟨hbits,houtside,hcost⟩ := raw_stream_outside q f P G S e hV source target s
    (fun a => CommonPermutationPairs.readBit q s.disk source (commonLayout f P G S a).val)
    hs ht (fun _ => rfl)
  refine ⟨?_,houtside,hcost⟩
  intro i
  have h := hbits ((commonLayout f P G S).symm i)
  simpa only [Equiv.apply_symm_apply,transport,permutation,Equiv.trans_apply,move] using h

theorem raw_outside (q : Configuration) (f P G S : ℕ) (e : Edge)
    (hV : longVolume f P G S≤CommonExchangeLeaf.bankBits q) (source target : ℕ)
    (s : Machine q)
    (hs : source+blocks q f P G S hV≤q.N^q.exponent)
    (ht : target+blocks q f P G S hV≤q.N^q.exponent)
    (a : Fin (q.N^q.exponent))
    (ha : a.val<target ∨ target+blocks q f P G S hV≤a.val) :
    (executeRaw q (code q f P G S e hV source target) s).1.disk a=s.disk a :=
  (raw_bits q f P G S e hV source target s hs ht).2.1 a ha

end
end CodedSorting.CommonEdgeExecution
end EdgeReadBit
